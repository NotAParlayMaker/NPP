import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic.FinCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9498_aux.Cycle.Interval

abbrev Vertex := Fin 18

def neighborhood (v : Vertex) : ℕ :=
  ([12, 12, 3, 99, 96, 24, 792, 768, 192, 6336, 6144, 1536, 50688, 49152, 12288, 143360, 131072, 98304] : List ℕ).getD v.val 0

def bank (v : Vertex) : Bool := (145635 : ℕ).testBit v.val

def vertices : List Vertex := List.finRange 18

def path (a b c d : Vertex) : Bool :=
  (neighborhood a).testBit b.val && (neighborhood b).testBit c.val &&
    (neighborhood c).testBit d.val && !(neighborhood a).testBit d.val

def obstructionMasks : List ℕ := [45, 46, 57, 58, 77, 78, 89, 90, 329, 330, 360, 368, 456, 464, 585, 586, 616, 624, 712, 720, 2632, 2640, 2880, 2944, 3648, 3712, 4680, 4688, 4928, 4992, 5696, 5760, 21056, 21120, 23040, 23552, 29184, 29696, 37440, 37504, 39424, 39936, 45568, 46080, 168448, 168960, 184320, 188416, 233472, 237568]

def clean (U : ℕ) : Bool := !(obstructionMasks.any (fun p => (U &&& p) == p))

def classOf (U : ℕ) (a : Vertex) : ℕ :=
  (vertices.filter fun b => U.testBit b.val && bank a == bank b &&
    (neighborhood a &&& U) == (neighborhood b &&& U)).foldl
      (fun s b => s ||| (1 <<< b.val)) 0

def move (U : ℕ) (a : Vertex) : ℕ := if U.testBit a.val then U ^^^ classOf U a else U

def reachable : ℕ → ℕ → Bool
  | 0, U => clean U
  | t+1, U => clean U || vertices.any (fun a => reachable t (move U a))

def full : ℕ := 262143

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma initial_0 : reachable 3 (move full 0) = false := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma initial_1 : reachable 3 (move full 1) = false := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma initial_2 : reachable 3 (move full 2) = false := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma initial_3 : reachable 3 (move full 3) = false := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma initial_4 : reachable 3 (move full 4) = false := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma initial_5 : reachable 3 (move full 5) = false := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma initial_6 : reachable 3 (move full 6) = false := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma initial_7 : reachable 3 (move full 7) = false := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma initial_8 : reachable 3 (move full 8) = false := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma initial_9 : reachable 3 (move full 9) = false := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma initial_10 : reachable 3 (move full 10) = false := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma initial_11 : reachable 3 (move full 11) = false := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma initial_12 : reachable 3 (move full 12) = false := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma initial_13 : reachable 3 (move full 13) = false := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma initial_14 : reachable 3 (move full 14) = false := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma initial_15 : reachable 3 (move full 15) = false := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma initial_16 : reachable 3 (move full 16) = false := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma initial_17 : reachable 3 (move full 17) = false := by decide +kernel

end PEqualNP.Outside.L_meta_9498_aux.Cycle.Interval

namespace PEqualNP.Outside.L_meta_9498_aux.Cycle.Interval

theorem initial (a : Vertex) : reachable 3 (move full a) = false := by
  have cover : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10 ∨ a = 11 ∨ a = 12 ∨ a = 13 ∨ a = 14 ∨ a = 15 ∨ a = 16 ∨ a = 17 := by
    simp only [Fin.ext_iff]
    have := a.isLt
    omega
  rcases cover with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17
  · rw [h0]; exact initial_0
  · rw [h1]; exact initial_1
  · rw [h2]; exact initial_2
  · rw [h3]; exact initial_3
  · rw [h4]; exact initial_4
  · rw [h5]; exact initial_5
  · rw [h6]; exact initial_6
  · rw [h7]; exact initial_7
  · rw [h8]; exact initial_8
  · rw [h9]; exact initial_9
  · rw [h10]; exact initial_10
  · rw [h11]; exact initial_11
  · rw [h12]; exact initial_12
  · rw [h13]; exact initial_13
  · rw [h14]; exact initial_14
  · rw [h15]; exact initial_15
  · rw [h16]; exact initial_16
  · rw [h17]; exact initial_17

theorem at_least_five : reachable 4 full = false := by
  have allFalse (ls : List Vertex) : ls.any (fun a => reachable 3 (move full a)) = false := by
    induction ls with
    | nil => rfl
    | cons a rest ih =>
      change (reachable 3 (move full a) || rest.any (fun b => reachable 3 (move full b))) = false
      rw [initial a, ih]
      rfl
  have z : clean full = false := by decide +kernel
  change (clean full || vertices.any (fun a => reachable 3 (move full a))) = false
  rw [z,allFalse]
  rfl
end PEqualNP.Outside.L_meta_9498_aux.Cycle.Interval

namespace PEqualNP.Outside.L_meta_9498_aux.Cycle

inductive Tree (V : Type) where
  | input : V → Tree V
  | all : Tree V → Tree V → Tree V
  | any : Tree V → Tree V → Tree V

namespace Tree
variable {V : Type} [DecidableEq V]

def leaves : Tree V → Finset V
  | .input u => {u}
  | .all a b | .any a b => a.leaves ∪ b.leaves

def linear : Tree V → Prop
  | .input _ => True
  | .all a b | .any a b => a.linear ∧ b.linear ∧ Disjoint a.leaves b.leaves

def eval (A : Finset V) : Tree V → Bool
  | .input u => decide (u∈A)
  | .all a b => eval A a && eval A b
  | .any a b => eval A a || eval A b

lemma eval_congr (T : Tree V) (A B : Finset V)
    (h : ∀ w ∈ T.leaves, w∈A ↔ w∈B) : T.eval A = T.eval B := by
  induction T with
  | input u => simpa [leaves,eval] using h u (by simp [leaves])
  | all l r il ir =>
    simp only [eval]
    rw [il (fun w hw => h w (by simp [leaves,hw])),
        ir (fun w hw => h w (by simp [leaves,hw]))]
  | any l r il ir =>
    simp only [eval]
    rw [il (fun w hw => h w (by simp [leaves,hw])),
        ir (fun w hw => h w (by simp [leaves,hw]))]

lemma eval_empty (T : Tree V) : T.eval ∅ = false := by
  induction T with
  | input u => simp [eval]
  | all a b ha hb => simp [eval,ha,hb]
  | any a b ha hb => simp [eval,ha,hb]

lemma pair_missing (T : Tree V) (a b : V) (ha : a∉T.leaves) :
    T.eval {a,b} = T.eval {b} := by
  apply eval_congr
  intro v hv
  have ne : v≠a := fun h => ha (h ▸ hv)
  simp [ne]

lemma pair_swap (T : Tree V) (a b : V) :
    T.eval {a,b} = T.eval {b,a} := by rw [Finset.pair_comm]

lemma pair_present (T : Tree V) (a b : V) (yes : T.eval {a,b} = true) :
    a∈T.leaves ∨ b∈T.leaves := by
  by_contra no
  push Not at no
  have e : T.eval {a,b} = T.eval ∅ := by
    apply eval_congr
    intro v hv
    have na : v≠a := fun h => no.1 (h ▸ hv)
    have nb : v≠b := fun h => no.2 (h ▸ hv)
    simp [na,nb]
  rw [e,eval_empty] at yes
  contradiction

lemma pair_needs_both (T : Tree V) (zero : ∀ a, T.eval {a} = false)
    (a b : V) (yes : T.eval {a,b} = true) : a∈T.leaves ∧ b∈T.leaves := by
  constructor
  · by_contra no
    rw [pair_missing T a b no,zero] at yes
    contradiction
  · by_contra no
    rw [pair_swap, pair_missing T b a no,zero] at yes
    contradiction

lemma both_cross (L R : Tree V) (dis : Disjoint L.leaves R.leaves)
    (a b : V) (left : L.eval {a,b}=true) (right : R.eval {a,b}=true) :
    (a∈L.leaves ∧ b∈R.leaves) ∨ (a∈R.leaves ∧ b∈L.leaves) := by
  have nd := Finset.disjoint_left.mp dis
  rcases pair_present L a b left with La | Lb
  · rcases pair_present R a b right with Ra | Rb
    · exact (nd La Ra).elim
    · exact Or.inl ⟨La,Rb⟩
  · rcases pair_present R a b right with Ra | Rb
    · exact Or.inr ⟨Ra,Lb⟩
    · exact (nd Lb Rb).elim

lemma or_truth {a b : Bool} : (a || b)=true ↔ a=true ∨ b=true := by
  cases a <;> cases b <;> decide

lemma and_truth {a b : Bool} : (a && b)=true ↔ a=true ∧ b=true := by
  cases a <;> cases b <;> decide

theorem linear_no_induced_path (T : Tree V) (linearT : T.linear)
    (zero : ∀ i, T.eval {i}=false) (a b c d : V)
    (ab : T.eval {a,b}=true) (bc : T.eval {b,c}=true) (cd : T.eval {c,d}=true)
    (ad : T.eval {a,d}=false) : False := by
  induction T with
  | input u =>
    have bad := (pair_needs_both (.input u) zero a b ab).1
    have e : a=u := by simpa [leaves] using bad
    subst a
    have h := zero u
    simp [eval] at h
  | any L R ihL ihR =>
    obtain ⟨linearL,linearR,dis⟩ := linearT
    have nd := Finset.disjoint_left.mp dis
    have parts (A : Finset V) (h : (L.eval A || R.eval A)=false) :
        L.eval A=false ∧ R.eval A=false := by
      cases ea : L.eval A <;> cases eb : R.eval A <;> simp_all
    have noL (w : V) : L.eval {w}=false := (parts {w} (zero w)).1
    have noR (w : V) : R.eval {w}=false := (parts {w} (zero w)).2
    have negL : L.eval {a,d}=false := (parts {a,d} ad).1
    have negR : R.eval {a,d}=false := (parts {a,d} ad).2
    change (L.eval {a,b} || R.eval {a,b})=true at ab
    change (L.eval {b,c} || R.eval {b,c})=true at bc
    change (L.eval {c,d} || R.eval {c,d})=true at cd
    rcases or_truth.mp ab with lab | rab
    · have bl := (pair_needs_both L noL a b lab).2
      have lbc : L.eval {b,c}=true := (or_truth.mp bc).resolve_right
        (fun h => nd bl (pair_needs_both R noR b c h).1)
      have cl := (pair_needs_both L noL b c lbc).2
      have lcd : L.eval {c,d}=true := (or_truth.mp cd).resolve_right
        (fun h => nd cl (pair_needs_both R noR c d h).1)
      exact ihL linearL noL lab lbc lcd negL
    · have br := (pair_needs_both R noR a b rab).2
      have rbc : R.eval {b,c}=true := (or_truth.mp bc).resolve_left
        (fun h => nd (pair_needs_both L noL b c h).1 br)
      have cr := (pair_needs_both R noR b c rbc).2
      have rcd : R.eval {c,d}=true := (or_truth.mp cd).resolve_left
        (fun h => nd (pair_needs_both L noL c d h).1 cr)
      exact ihR linearR noR rab rbc rcd negR
  | all L R ihL ihR =>
    obtain ⟨linearL,linearR,dis⟩ := linearT
    have nd := Finset.disjoint_left.mp dis
    change (L.eval {a,b} && R.eval {a,b})=true at ab
    change (L.eval {b,c} && R.eval {b,c})=true at bc
    change (L.eval {c,d} && R.eval {c,d})=true at cd
    change (L.eval {a,d} && R.eval {a,d})=false at ad
    obtain ⟨al,ar⟩ := and_truth.mp ab
    obtain ⟨bl,br⟩ := and_truth.mp bc
    obtain ⟨cl,cr⟩ := and_truth.mp cd
    rcases both_cross L R dis a b al ar with ⟨aL,bR⟩ | ⟨aR,bL⟩
    · have cL := ((both_cross L R dis b c bl br).resolve_left (fun h => nd h.1 bR)).2
      have dR := ((both_cross L R dis c d cl cr).resolve_right (fun h => nd cL h.1)).2
      have ansL : L.eval {a}=true := by rwa [pair_swap, pair_missing L b a (fun h => nd h bR)] at al
      have ansR : R.eval {d}=true := by rwa [pair_missing R c d (nd cL)] at cr
      rw [pair_swap L a d,pair_missing L d a (fun h => nd h dR),pair_missing R a d (nd aL),
        ansL,ansR] at ad
      contradiction
    · have cR := ((both_cross L R dis b c bl br).resolve_right (fun h => nd bL h.1)).2
      have dL := ((both_cross L R dis c d cl cr).resolve_left (fun h => nd h.1 cR)).2
      have ansR : R.eval {a}=true := by rwa [pair_swap,pair_missing R b a (nd bL)] at ar
      have ansL : L.eval {d}=true := by rwa [pair_missing L c d (fun h => nd h cR)] at cl
      rw [pair_missing L a d (fun h => nd h aR),pair_swap R a d,pair_missing R d a (nd dL),
        ansR,ansL] at ad
      contradiction
end Tree
end PEqualNP.Outside.L_meta_9498_aux.Cycle

namespace PEqualNP.Outside.L_meta_9498_aux.Cycle.Interval

lemma reachable_succ (k U : ℕ) (yes : reachable k U = true) :
    reachable (k+1) U = true := by
  induction k generalizing U with
  | zero =>
    change clean U = true at yes
    change (clean U || _) = true
    rw [yes]
    rfl
  | succ k ih =>
    change (clean U || vertices.any (fun w => reachable k (move U w))) = true at yes
    change (clean U || vertices.any (fun w => reachable (k+1) (move U w))) = true
    apply Tree.or_truth.mpr
    rcases Tree.or_truth.mp yes with ok | child
    · exact Or.inl ok
    · obtain ⟨a,ha,next⟩ := List.any_eq_true.mp child
      exact Or.inr (List.any_eq_true.mpr ⟨a,ha,ih _ next⟩)

lemma reachable_mono (k j U : ℕ) (hk : k ≤ j) (yes : reachable k U=true) :
    reachable j U=true := by
  induction hk with
  | refl => exact yes
  | step _ prev => exact reachable_succ _ _ prev

lemma follow_reachable (xs : List Vertex) (U : ℕ)
    (endClean : clean (xs.foldl move U) = true) : reachable xs.length U=true := by
  induction xs generalizing U with
  | nil => exact endClean
  | cons a tail ih =>
    change clean (tail.foldl move (move U a)) = true at endClean
    have h := ih (move U a) endClean
    change (clean U || vertices.any (fun w => reachable tail.length (move U w))) = true
    exact Tree.or_truth.mpr (Or.inr (List.any_eq_true.mpr ⟨a, by simp [vertices], h⟩))

theorem survive_a_path_after_four (xs : List Vertex) (small : xs.length ≤ 4) :
    ∃ p ∈ obstructionMasks, (xs.foldl move full &&& p)=p := by
  set U := xs.foldl move full
  have notClean : clean U ≠ true := by
    intro on
    have h := reachable_mono xs.length 4 full small (follow_reachable xs full on)
    rw [at_least_five] at h
    contradiction
  have hit : obstructionMasks.any (fun p => (U &&& p) == p) = true := by
    unfold clean at notClean
    cases h : obstructionMasks.any (fun p => (U &&& p) == p)
    · simp [h] at notClean
    · rfl
  obtain ⟨p,hp,eq⟩ := List.any_eq_true.mp hit
  exact ⟨p,hp,beq_iff_eq.mp eq⟩

abbrev PathRecord := ℕ × Vertex × Vertex × Vertex × Vertex

def records : List PathRecord := [
  (45,5,3,0,2),
  (46,5,3,1,2),
  (57,4,5,3,0),
  (58,4,5,3,1),
  (77,6,3,0,2),
  (78,6,3,1,2),
  (89,4,6,3,0),
  (90,4,6,3,1),
  (329,8,6,3,0),
  (330,8,6,3,1),
  (360,8,6,3,5),
  (368,8,6,4,5),
  (456,7,8,6,3),
  (464,7,8,6,4),
  (585,9,6,3,0),
  (586,9,6,3,1),
  (616,9,6,3,5),
  (624,9,6,4,5),
  (712,7,9,6,3),
  (720,7,9,6,4),
  (2632,11,9,6,3),
  (2640,11,9,6,4),
  (2880,11,9,6,8),
  (2944,11,9,7,8),
  (3648,10,11,9,6),
  (3712,10,11,9,7),
  (4680,12,9,6,3),
  (4688,12,9,6,4),
  (4928,12,9,6,8),
  (4992,12,9,7,8),
  (5696,10,12,9,6),
  (5760,10,12,9,7),
  (21056,14,12,9,6),
  (21120,14,12,9,7),
  (23040,14,12,9,11),
  (23552,14,12,10,11),
  (29184,13,14,12,9),
  (29696,13,14,12,10),
  (37440,15,12,9,6),
  (37504,15,12,9,7),
  (39424,15,12,9,11),
  (39936,15,12,10,11),
  (45568,13,15,12,9),
  (46080,13,15,12,10),
  (168448,17,15,12,9),
  (168960,17,15,12,10),
  (184320,17,15,12,14),
  (188416,17,15,13,14),
  (233472,16,17,15,12),
  (237568,16,17,15,13)
]

lemma masks_records : obstructionMasks = records.map (fun r => r.1) := by decide +kernel

lemma record_correct : ∀ (r : PathRecord), r∈records →
    path r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2 = true ∧
    r.1=((1 <<< r.2.1.val) ||| (1 <<< r.2.2.1.val) |||
      (1 <<< r.2.2.2.1.val) ||| (1 <<< r.2.2.2.2.val)) := by
  have verified : records.all (fun r =>
      path r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2 &&
      r.1==((1 <<< r.2.1.val) ||| (1 <<< r.2.2.1.val) |||
        (1 <<< r.2.2.2.1.val) ||| (1 <<< r.2.2.2.2.val))) = true := by decide +kernel
  intro r hr
  have h := List.all_eq_true.mp verified r hr
  obtain ⟨p,e⟩ := Tree.and_truth.mp h
  exact ⟨p,beq_iff_eq.mp e⟩

theorem interval_four_paths (xs : List Vertex) (small : xs.length ≤ 4) :
    ∃ a b c d : Vertex, path a b c d = true ∧
      let p := ((1 <<< a.val) ||| (1 <<< b.val) ||| (1 <<< c.val) ||| (1 <<< d.val))
      (xs.foldl move full &&& p) = p := by
  obtain ⟨p,mem,hit⟩ := survive_a_path_after_four xs small
  rw [masks_records] at mem
  obtain ⟨rec, hr, hrec⟩ := List.mem_map.mp mem
  obtain ⟨ok,encode⟩ := record_correct rec hr
  refine ⟨rec.2.1,rec.2.2.1,rec.2.2.2.1,rec.2.2.2.2,ok,?_⟩
  change (xs.foldl move full &&& _) = _
  rw [← encode,hrec]
  exact hit
end PEqualNP.Outside.L_meta_9498_aux.Cycle.Interval

namespace PEqualNP.Outside.L_meta_9498_aux.Cycle.CycleNine
open PEqualNP.Outside.L_meta_9498_aux.Cycle.Interval
abbrev V := Fin 54

def side (v : V) : Bool := decide (v.val < 27)

def target (a b : Fin 27) : Bool :=
  decide (∃ i : Fin 9, ((a.val = i.val ∨ a.val = 9 + i.val) ∧
    (b.val = (i.val + 1) % 9 ∨ b.val = 18 + i.val)) ∨
    ((b.val = i.val ∨ b.val = 9 + i.val) ∧
      (a.val = (i.val + 1) % 9 ∨ a.val = 18 + i.val)))

def adjacent (u v : V) : Bool :=
  if hu : u.val < 27 then
    if hv : v.val < 27 then false else
      target ⟨u.val,hu⟩ ⟨v.val - 27, by have := v.isLt; omega⟩
  else if hv : v.val < 27 then
    target ⟨v.val,hv⟩ ⟨u.val - 27, by have := u.isLt; omega⟩
  else false

theorem adjacent_symm (u v : V) : adjacent u v = adjacent v u := by
  unfold adjacent
  by_cases hu : u.val < 27 <;> by_cases hv : v.val < 27 <;> simp [hu,hv]

theorem adjacent_opposite (u v : V) (h : adjacent u v = true) : side u ≠ side v := by
  unfold adjacent at h
  by_cases hu : u.val < 27 <;> by_cases hv : v.val < 27 <;> simp [side,hu,hv] at h ⊢

/-- Six successive blocks, omitting the final main vertex that starts the next region. -/
def locate (r : Fin 3) (a : Vertex) : V :=
  let step := 6*r.val + a.val/3
  let base := if step % 2 = 0 then 0 else 27
  let i := step % 9
  Fin.ofNat 54 (if a.val % 3 = 0 then base + i
    else if a.val % 3 = 1 then base + 9 + i
    else 27 - base + 18 + i)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem internal : ∀ (r : Fin 3) (a b : Vertex),
    adjacent (locate r a) (locate r b) = (neighborhood a).testBit b.val := by
  intro r
  fin_cases r <;> decide +kernel

theorem bank_locate : ∀ (r : Fin 3) (a : Vertex), side (locate r a) = bank a := by
  decide +kernel

set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem locate_injective : ∀ (r s : Fin 3) (a b : Vertex),
    locate r a = locate s b → r=s ∧ a=b := by
  intro r s
  fin_cases r <;> fin_cases s <;> decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem boundary : ∀ (r s : Fin 3), r ≠ s → ∀ (a b : Vertex),
    adjacent (locate r a) (locate s b) = true →
      if s=r+1 then side (locate r a)=false ∧ side (locate s b)=true
      else side (locate r a)=true ∧ side (locate s b)=false := by
  intro r s
  fin_cases r <;> fin_cases s <;> decide +kernel

theorem locate_surjective : ∀ v : V, ∃ r : Fin 3, ∃ a : Vertex, locate r a = v := by
  decide +kernel

def project (r : Fin 3) (A : Finset V) : Finset Vertex :=
  Finset.univ.filter (fun x => locate r x ∈ A)

theorem project_mem (r : Fin 3) (A : Finset V) (x : Vertex) :
    x ∈ project r A ↔ locate r x ∈ A := by simp [project]

theorem project_univ (r : Fin 3) : project r Finset.univ = Finset.univ := by simp [project]

theorem project_diff (r : Fin 3) (A R : Finset V) :
    project r (A \ R) = project r A \ project r R := by
  ext x
  simp [project]
end PEqualNP.Outside.L_meta_9498_aux.Cycle.CycleNine

-- Gate bypass and wire semantics adapted from checked L-meta-2668.
-- Bypass helpers adapted from willakone, L-meta-1499, PR 3112.
namespace PEqualNP.Outside.L_meta_9498_aux.Bypass

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt2 (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt2 gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, foldl_getD_lt2 gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt2 _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

lemma val_prefix {n : ℕ} {C D : Circuit} {x : List Bool} (hx : x.length = n) {m : ℕ}
    (hmC : m ≤ C.gates.length) (hmD : m ≤ D.gates.length)
    (hg : ∀ k < m, gateAt D k = gateAt C k) : ∀ u, u < n + m → val D x u = val C x u := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu
    by_cases hun : u < n
    · rw [val_input hx hun, val_input hx hun]
    · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
      have hk : k < m := by omega
      rw [val_gate hx (by omega), val_gate hx (by omega), hg k hk]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < n + k
      · rw [if_pos hi, if_pos hi]; exact ih i hi (by omega)
      · rw [if_neg hi, if_neg hi]

def aliasWire (w i u : ℕ) : ℕ := if u = w then i else if w < u then u - 1 else u

def aliasGate (w i : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (aliasWire w i)⟩

def bypass (n : ℕ) (C : Circuit) (r i : ℕ) : Circuit :=
  ⟨(List.range (C.gates.length - 1)).map (fun k =>
      if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1))),
    aliasWire (n + r) i C.output⟩

lemma bypass_length (n : ℕ) (C : Circuit) (r i : ℕ) :
    (bypass n C r i).gates.length = C.gates.length - 1 := by simp [bypass]

lemma bypass_output (n : ℕ) (C : Circuit) (r i : ℕ) :
    (bypass n C r i).output = aliasWire (n + r) i C.output := rfl

lemma gateAt_bypass {n : ℕ} {C : Circuit} {r i k : ℕ} (hk : k < C.gates.length - 1) :
    gateAt (bypass n C r i) k =
      if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1)) := by
  have hk' : k < (bypass n C r i).gates.length := by rw [bypass_length]; exact hk
  rw [gateAt_eq hk']
  simp [bypass]

lemma bypass_val_lt {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r i : ℕ}
    (hr : r < C.gates.length) : ∀ u, u < n + r → val (bypass n C r i) x u = val C x u := by
  apply val_prefix hx (by omega) (by rw [bypass_length]; omega)
  intro k hk
  rw [gateAt_bypass (by omega), if_pos hk]

lemma aliasWire_self (w i : ℕ) : aliasWire w i w = i := by simp [aliasWire]

lemma aliasWire_lt_self {w i u : ℕ} (hu : u < w) : aliasWire w i u = u := by
  unfold aliasWire; rw [if_neg (by omega), if_neg (by omega)]

lemma aliasWire_gt_self {w i u : ℕ} (hu : w < u) : aliasWire w i u = u - 1 := by
  unfold aliasWire; rw [if_neg (by omega), if_pos hu]

lemma bypass_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
    {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : (∃ k, r < k ∧ k < C.gates.length ∧ n + r ∈ (gateAt C k).inputs) →
      R (val C x (n + r)) (val C x i)) :
    ∀ u, u ≠ n + r → R (val C x u) (val (bypass n C r i) x (aliasWire (n + r) i u)) := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hne
    by_cases hlt : u < n + r
    · rw [aliasWire_lt_self hlt, bypass_val_lt hx hr u hlt]; exact hrefl _
    · rw [aliasWire_gt_self (by omega)]
      by_cases hge : n + C.gates.length ≤ u
      · rw [val_ge hx hge, val_ge hx (by rw [bypass_length]; omega)]; exact hrefl _
      · obtain ⟨k, rfl⟩ : ∃ k, u = n + (k + 1) := ⟨u - n - 1, by omega⟩
        have hk1 : k + 1 < C.gates.length := by omega
        have hkr : ¬ k < r := by omega
        have e : n + (k + 1) - 1 = n + k := by omega
        rw [e, val_gate hx hk1, val_gate hx (by rw [bypass_length]; omega),
          gateAt_bypass (by omega), if_neg hkr]
        simp only [aliasGate, List.map_map]
        refine hmono _ (hAO _ hk1) _ _ _ ?_
        intro i' hi'
        simp only [Function.comp_apply]
        by_cases h1 : i' = n + r
        · subst h1
          rw [aliasWire_self, if_pos (by omega)]
          have hgi : (if i < n + k then val (bypass n C r i) x i else false) = val C x i := by
            rcases hi with hi | hi
            · rw [if_pos (by omega), bypass_val_lt hx hr i hi]
            · rw [if_neg (by omega), val_ge hx hi]
          rw [hgi]
          exact hR ⟨k + 1, by omega, hk1, hi'⟩
        · by_cases h2 : i' < n + r
          · rw [aliasWire_lt_self h2, if_pos (by omega), if_pos (by omega),
              bypass_val_lt hx hr i' h2]
            exact hrefl _
          · by_cases h3 : i' < n + (k + 1)
            · have key := ih i' h3 h1
              rw [aliasWire_gt_self (by omega)] at key
              rw [aliasWire_gt_self (by omega), if_pos h3, if_pos (by omega)]
              exact key
            · rw [aliasWire_gt_self (by omega), if_neg h3, if_neg (by omega)]
              exact hrefl _

lemma bypass_eval_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
    {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : R (val C x (n + r)) (val C x i)) :
    R (C.eval x) ((bypass n C r i).eval x) := by
  rw [eval_eq_val, eval_eq_val, bypass_output]
  by_cases h : C.output = n + r
  · have hgi : val (bypass n C r i) x i = val C x i := by
      rcases hi with hi | hi
      · exact bypass_val_lt hx hr i hi
      · rw [val_ge hx hi, val_ge hx (by rw [bypass_length]; omega)]
    rw [h, aliasWire_self, hgi]; exact hR
  · exact bypass_rel hrefl hmono hx hAO hr hi (fun _ => hR) _ h

lemma bypass_eval_eq {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : val C x (n + r) = val C x i) :
    (bypass n C r i).eval x = C.eval x :=
  (bypass_eval_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi hR).symm

lemma bypass_eval_unread {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hout : C.output ≠ n + r)
    (hno : ∀ k, r < k → k < C.gates.length → n + r ∉ (gateAt C k).inputs) :
    (bypass n C r i).eval x = C.eval x := by
  rw [eval_eq_val, eval_eq_val, bypass_output]
  exact (bypass_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi
    (fun ⟨k, hrk, hk, hm⟩ => absurd hm (hno k hrk hk)) _ hout).symm

lemma bypass_AO {n : ℕ} {C : Circuit} {r i : ℕ} (hr : r < C.gates.length)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) :
    ∀ k < (bypass n C r i).gates.length,
      (gateAt (bypass n C r i) k).op = GateOp.and ∨
        (gateAt (bypass n C r i) k).op = GateOp.or := by
  intro k hk
  rw [bypass_length] at hk
  rw [gateAt_bypass hk]
  split_ifs with h
  · exact hAO k (by omega)
  · exact hAO (k + 1) (by omega)

lemma bypass_mem {n : ℕ} {C : Circuit} {r i : ℕ} :
    ∀ g ∈ (bypass n C r i).gates, ∃ g' ∈ C.gates, g.op = g'.op ∧
      g.inputs.length = g'.inputs.length := by
  intro g hg
  simp only [bypass, List.mem_map, List.mem_range] at hg
  obtain ⟨k, hk, rfl⟩ := hg
  split_ifs with h
  · exact ⟨gateAt C k, gateAt_mem (by omega), rfl, rfl⟩
  · exact ⟨gateAt C (k + 1), gateAt_mem (by omega), rfl, by simp [aliasGate]⟩

lemma aliasWire_lt {w i u m : ℕ} (hi : i < w) (hwm : w ≤ m) (hu : u < m + 1) :
    aliasWire w i u < m := by
  unfold aliasWire; split_ifs <;> omega

lemma bypass_readsBack {n : ℕ} {C : Circuit} {r i : ℕ} (hi : i < n + r)
    (hRB : ∀ k < C.gates.length, ∀ u ∈ (gateAt C k).inputs, u < n + k) :
    ∀ k < (bypass n C r i).gates.length,
      ∀ u ∈ (gateAt (bypass n C r i) k).inputs, u < n + k := by
  intro k hk u hu
  rw [bypass_length] at hk
  rw [gateAt_bypass hk] at hu
  split_ifs at hu with h
  · exact hRB k (by omega) u hu
  · simp only [aliasGate, List.mem_map] at hu
    obtain ⟨u', hu', rfl⟩ := hu
    have := hRB (k + 1) (by omega) u' hu'
    exact aliasWire_lt hi (by omega) (by omega)


lemma erase_eq_bypass (n : ℕ) (C : Circuit) (r i : ℕ) (hr : r < C.gates.length) :
    PEqualNP.CircuitMoves.eraseGate n C r i = bypass n C r i := by
  unfold PEqualNP.CircuitMoves.eraseGate
  rw [if_pos hr]
  change Circuit.mk _ (aliasWire (n + r) i C.output) = Circuit.mk _ (aliasWire (n + r) i C.output)
  congr 1
  apply List.ext_getElem
  · simp [bypass]; omega
  · intro k hk hk'
    have hlen : (C.gates.take r).length = r := by simp; omega
    have hklen : k < C.gates.length - 1 := by simpa [bypass] using hk'
    simp only [bypass, List.getElem_map, List.getElem_range]
    by_cases hkr : k < r
    · rw [if_pos hkr, List.getElem_append_left (by omega), List.getElem_take,
        gateAt_eq (by omega)]
    · rw [if_neg hkr, List.getElem_append_right (by omega), List.getElem_map,
        List.getElem_drop]
      simp only [hlen]
      have he : r + 1 + (k - r) = k + 1 := by omega
      simp only [he]
      rw [gateAt_eq (by omega : k + 1 < C.gates.length)]
      rfl

lemma mono_ops {C : Circuit} (hM : Monotone2 C) :
    ∀ k < C.gates.length, (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or := by
  intro k hk
  exact (hM _ (gateAt_mem hk)).1

lemma wire_monotone (n : ℕ) (C : Circuit) (hM : Monotone2 C) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ u, val C (List.ofFn x) u = true → val C (List.ofFn y) u = true := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    by_cases hun : u < n
    · rw [val_input (n := n) (by simp) hun, val_input (n := n) (by simp) hun]
      simpa [hun] using hxy ⟨u, hun⟩
    · by_cases hge : n + C.gates.length ≤ u
      · rw [val_ge (n := n) (by simp) hge]
        intro h; cases h
      · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
        have hk : k < C.gates.length := by omega
        rw [val_gate (n := n) (by simp) hk, val_gate (n := n) (by simp) hk]
        apply opMono_imp _ (mono_ops hM k hk)
        intro i hi
        by_cases hil : i < n + k
        · rw [if_pos hil, if_pos hil]
          exact ih i hil
        · rw [if_neg hil, if_neg hil]
          exact id

lemma circuit_monotone (n : ℕ) (C : Circuit) (hM : Monotone2 C) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) : C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true :=
  wire_monotone n C hM x y hxy C.output

lemma opMono_reverse : OpMono (fun a b => b = true → a = true) := by
  intro op hop l f g h
  exact opMono_imp op hop l g f h

lemma bypass_mono {n : ℕ} {C : Circuit} {r i : ℕ} (hM : Monotone2 C) :
    Monotone2 (bypass n C r i) := by
  intro g hg
  obtain ⟨g', hg', hop, hlen⟩ := bypass_mem g hg
  rw [hop, hlen]
  exact hM g' hg'

lemma graph_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ p l, G.Adj p l ∧ x p = true ∧ x l = true := by
  simp [graphFun]

lemma pair_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (p l : Fin n)
    (hp : G.Adj p l) : graphFun G ∅ (PEqualNP.EdgeOwnership.pairInput p l) = true := by
  rw [graph_true]
  exact ⟨p, l, hp, by simp [PEqualNP.EdgeOwnership.pairInput], by simp [PEqualNP.EdgeOwnership.pairInput]⟩


end PEqualNP.Outside.L_meta_9498_aux.Bypass

namespace PEqualNP.Outside.L_meta_9498_aux.Cycle.Initial
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover PEqualNP.Outside.L_meta_9498_aux.Bypass

variable {n : ℕ}

def left (u : Fin n) : Fin (n+n) := u.castAdd n
def right (u : Fin n) : Fin (n+n) := u.natAdd n

lemma left_right (u v : Fin n) : left u ≠ right v := by
  intro e
  have h := congrArg Fin.val e
  change u.val = n+v.val at h
  have := u.isLt
  omega

def row (u v : Fin n) (w : Fin (n+n)) : Bool := decide (w=left u ∨ w=right v)

lemma row_eq (u v : Fin n) : List.ofFn (row u v) = oneEach u v := by
  unfold oneEach
  rw [List.ofFn_add]
  have hLeft : (fun i : Fin n => row u v (i.castLE (Nat.le_add_right n n))) =
      (fun i => decide (i=u)) := by
    funext i
    change row u v (left i) = decide (i=u)
    have p : left i = left u ↔ i=u := ⟨fun h => Fin.ext (congrArg (fun j : Fin (n+n) => j.val) h),congrArg left⟩
    simp [row,left_right,p]
  have hRight : (fun i : Fin n => row u v (i.natAdd n)) =
      (fun i => decide (i=v)) := by
    funext i
    change row u v (right i) = decide (i=v)
    have p : right i = right v ↔ i=v := by
      constructor
      · intro h
        have h' := congrArg Fin.val h
        change n+i.val=n+v.val at h'
        exact Fin.ext (by omega)
      · exact congrArg right
    have neq : right i ≠ left u := Ne.symm (left_right u i)
    simp [row,neq,p]
  rw [hLeft,hRight]

lemma val_raw {k : ℕ} (C : Circuit) (x : Fin k → Bool) (v : Fin k) :
    val C (List.ofFn x) v.val = x v := by
  rw [val_input (n:=k) (by simp) v.isLt,List.getD_eq_getElem _ _ (by simpa using v.isLt)]
  simp

lemma eval_row (A : Fin n → Fin n → Bool) (C : Circuit) (exactA : Represents A C)
    (u v : Fin n) : C.eval (List.ofFn (row u v)) = A u v := by
  rw [row_eq]
  exact exactA u v

lemma diag_contains (w : Fin (n+n)) : ∃ i : Fin n, row i i w = true := by
  refine Fin.addCases ?_ ?_ w
  · intro u
    exact ⟨u,by simp [row,left]⟩
  · intro u
    exact ⟨u,by simp [row,right]⟩

theorem singleton_false (A : Fin n → Fin n → Bool) (C : Circuit) (mono : Monotone2 C)
    (exactA : Represents A C) (diag : ∀ i,A i i=false) (w : Fin (n+n)) :
    C.eval (List.ofFn (fun i : Fin (n+n) => decide (i=w))) = false := by
  obtain ⟨i,active⟩ := diag_contains w
  apply Bool.eq_false_iff.mpr
  intro h
  have atDiag := circuit_monotone (n+n) C mono (fun v => decide (v=w)) (row i i)
    (fun a yes => by have same : a=w := of_decide_eq_true yes; subst a; exact active) h
  rw [eval_row A C exactA,diag] at atDiag
  contradiction

theorem output_nonraw (A : Fin n → Fin n → Bool) (C : Circuit) (mono : Monotone2 C)
    (exactA : Represents A C) (diag : ∀ i,A i i=false) : n+n ≤ C.output := by
  by_contra bad
  let w : Fin (n+n) := ⟨C.output,by omega⟩
  have neg := singleton_false A C mono exactA diag w
  change val C (List.ofFn (fun i : Fin (n+n) => decide (i=w))) w.val = false at neg
  rw [val_raw] at neg
  simp at neg

theorem output_earlier (A : Fin n → Fin n → Bool) (C : Circuit)
    (exactA : Represents A C) (pos : ∃ u v,A u v=true) :
    C.output < (n+n)+C.gates.length := by
  obtain ⟨u,v,yes⟩ := pos
  by_contra bad
  have h := eval_row A C exactA u v
  rw [yes,eval_eq_val,val_ge (n:=n+n) (by simp) (by omega)] at h
  contradiction

lemma positive_negative (A : Fin n → Fin n → Bool)
    (sym : ∀ a b,A a b = A b a) (good : ∀ a,∃ b,A a b=true) (w : Fin (n+n)) :
    ∃ a b k : Fin n, A a b=true ∧
      ∀ v : Fin (n+n), v≠w → row a b v=true → row k k v=true := by
  refine Fin.addCases ?_ ?_ w
  · intro a
    obtain ⟨b,yes⟩ := good a
    refine ⟨a,b,b,yes,?_⟩
    intro j notA on
    change j ≠ left a at notA
    have e : j=left a ∨ j=right b := of_decide_eq_true on
    rw [e.resolve_left notA]
    simp [row]
  · intro a
    obtain ⟨b,yes⟩ := good a
    refine ⟨b,a,b,(sym b a).trans yes,?_⟩
    intro j notA on
    change j ≠ right a at notA
    have e : j=left b ∨ j=right a := of_decide_eq_true on
    rw [e.resolve_right notA]
    simp [row]

lemma no_reader {n : ℕ} (C : Circuit) (v : Fin n)
    (none : ∀ j, j < C.gates.length → v.val ∉ (gateAt C j).inputs)
    (x y : Fin n → Bool) (agree : ∀ u, u ≠ v → x u = y u) :
    ∀ w, w ≠ v.val → val C (List.ofFn x) w = val C (List.ofFn y) w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hne
    by_cases raw : w < n
    · let u : Fin n := ⟨w, raw⟩
      change val C (List.ofFn x) u.val = val C (List.ofFn y) u.val
      rw [val_raw, val_raw]
      exact agree u (fun e => hne (congrArg Fin.val e))
    by_cases outside : n + C.gates.length ≤ w
    · rw [val_ge (n := n) (by simp) outside, val_ge (n := n) (by simp) outside]
    obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    have hj : j < C.gates.length := by omega
    rw [val_gate (n := n) (by simp) hj, val_gate (n := n) (by simp) hj]
    congr 1
    apply List.map_congr_left
    intro i hi
    by_cases early : i < n + j
    · simp only [if_pos early]
      exact ih i early (fun he => none j hj (he ▸ hi))
    · simp only [if_neg early]

theorem every_raw_read (A : Fin n → Fin n → Bool) (C : Circuit) (mono : Monotone2 C)
    (exactA : Represents A C) (symmetric : ∀ a b,A a b=A b a) (diag : ∀ i,A i i=false)
    (inc : ∀ a,∃ b,A a b=true) (w : Fin (n+n)) :
    ∃ j < C.gates.length, w.val ∈ (gateAt C j).inputs := by
  by_contra hn
  push Not at hn
  obtain ⟨a,b,k,yes,comp⟩ := positive_negative A symmetric inc w
  let x := row a b
  let y := row k k
  let off : Fin (n+n) → Bool := fun i => if i=w then false else x i
  have same := no_reader C w hn x off (fun i ne => by simp [off,ne]) C.output
    (by have := output_nonraw A C mono exactA diag; have := w.isLt; omega)
  have onX : C.eval (List.ofFn x)=true := (eval_row A C exactA a b).trans yes
  have onOff : C.eval (List.ofFn off)=true := same.symm.trans onX
  have onY : C.eval (List.ofFn y)=true := by
    apply circuit_monotone (n+n) C mono off y _ onOff
    intro i on
    by_cases e : i=w
    · simp [off,e] at on
    · exact comp i e (by simpa [off,e] using on)
  have noY : C.eval (List.ofFn y)=false := (eval_row A C exactA k k).trans (diag k)
  rw [noY] at onY
  contradiction
end PEqualNP.Outside.L_meta_9498_aux.Cycle.Initial

namespace PEqualNP.Outside.L_meta_9498_aux.Cycle.Initial
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover PEqualNP.Outside.L_meta_9498_aux.Bypass
variable {n : ℕ}

def MinRep (A : Fin n → Fin n → Bool) (C : Circuit) : Prop :=
  ∀ D : Circuit, Monotone2 D → Represents A D → C.size ≤ D.size

lemma minimum_of_witness (A : Fin n → Fin n → Bool) (size : ℕ)
    (has : RepSizeAtMost A size) :
    ∃ C : Circuit, Monotone2 C ∧ Represents A C ∧ MinRep A C ∧ C.size ≤ size := by
  classical
  let witness (s : ℕ) := ∃ C : Circuit, Monotone2 C ∧ Represents A C ∧ C.size = s
  have ex : ∃ s, witness s := by
    obtain ⟨D, hm, _, hr⟩ := has
    exact ⟨D.size, D, hm, hr, rfl⟩
  obtain ⟨C, hm, hr, hc⟩ := Nat.find_spec ex
  have min : MinRep A C := by
    intro D hd he
    rw [hc]
    exact Nat.find_min' ex (show witness D.size from ⟨D, hd, he, rfl⟩)
  obtain ⟨D, hmD, szD, hrD⟩ := has
  exact ⟨C, hm, hr, min, (min D hmD hrD).trans szD⟩

theorem output_last (A : Fin n → Fin n → Bool) (C : Circuit)
    (mono : Monotone2 C) (correct : Represents A C) (min : MinRep A C)
    (diag : ∀ i, A i i=false) (pos : ∃ u v, A u v=true) :
    C.output + 1 = (n+n) + C.gates.length := by
  have lo := output_nonraw A C mono correct diag
  have hi := output_earlier A C correct pos
  let m := C.output - (n+n) + 1
  have hm : m ≤ C.gates.length := by omega
  let D : Circuit := ⟨C.gates.take m, C.output⟩
  have len : D.gates.length = m := by simp [D, Nat.min_eq_left hm]
  have hd : Monotone2 D := fun g hg => mono g (List.mem_of_mem_take hg)
  have hg (k : ℕ) (hk : k < m) : gateAt D k = gateAt C k := by
    have kd : k < D.gates.length := by omega
    have kc : k < C.gates.length := by omega
    rw [gateAt_eq kd, gateAt_eq kc]
    simp [D, List.getElem_take]
  have exactD : Represents A D := by
    intro i j
    rw [← row_eq]
    have same := val_prefix (n := n+n) (C := C) (D := D)
      (x := List.ofFn (row i j)) (by simp) hm (by omega) hg C.output (by omega)
    change D.eval (List.ofFn (row i j)) = C.eval (List.ofFn (row i j)) at same
    exact same.trans (eval_row A C correct i j)
  have hsize := min D hd exactD
  change C.gates.length ≤ D.gates.length at hsize
  omega

theorem live_reader (A : Fin n → Fin n → Bool) (C : Circuit)
    (mono : Monotone2 C) (correct : Represents A C) (min : MinRep A C)
    (j : ℕ) (hj : j < C.gates.length) (notOut : (n+n)+j ≠ C.output) :
    ∃ k, j < k ∧ k < C.gates.length ∧ (n+n)+j ∈ (gateAt C k).inputs := by
  by_contra hn
  push Not at hn
  let D := bypass (n+n) C j ((n+n) + C.gates.length)
  have same : Represents A D := by
    intro i l
    rw [← row_eq]
    exact (bypass_eval_unread (n := n+n) (C := C) (by simp) (mono_ops mono) hj
      (Or.inr le_rfl) notOut.symm hn).trans (eval_row A C correct i l)
  have hsize := min D (bypass_mono mono) same
  change C.gates.length ≤ (bypass (n+n) C j ((n+n)+C.gates.length)).gates.length at hsize
  rw [bypass_length] at hsize
  omega

def Live (A : Fin n → Fin n → Bool) (C : Circuit) : Prop :=
  Monotone2 C ∧ Represents A C ∧
  C.output + 1 = (n+n) + C.gates.length ∧
  ∀ w < C.output, ∃ j < C.gates.length, w < (n+n) + j ∧ w ∈ (gateAt C j).inputs

theorem minimum_live (A : Fin n → Fin n → Bool) (C : Circuit)
    (mono : Monotone2 C) (correct : Represents A C) (min : MinRep A C)
    (sym : ∀ a b, A a b = A b a) (diag : ∀ a, A a a=false)
    (inc : ∀ a, ∃ b, A a b=true) (pos : ∃ a b, A a b=true) :
    Live A C := by
  refine ⟨mono, correct, output_last A C mono correct min diag pos, ?_⟩
  intro w hw
  by_cases raw : w < n+n
  · let v : Fin (n+n) := ⟨w, raw⟩
    obtain ⟨j, hj, read⟩ := every_raw_read A C mono correct sym diag inc v
    exact ⟨j, hj, by omega, read⟩
  · obtain ⟨k, rfl⟩ : ∃ k, w = (n+n)+k := ⟨w-(n+n), by omega⟩
    have last := output_last A C mono correct min diag pos
    obtain ⟨j, kj, hj, read⟩ := live_reader A C mono correct min k (by omega) (by omega)
    exact ⟨j, hj, by omega, read⟩

def cycle (k : ℕ) (a b : Fin (3*k)) : Bool :=
  decide (∃ i : Fin k,
    ((a.val=i.val ∨ a.val=k+i.val) ∧ (b.val=(i.val+1)%k ∨ b.val=2*k+i.val)) ∨
    ((b.val=i.val ∨ b.val=k+i.val) ∧ (a.val=(i.val+1)%k ∨ a.val=2*k+i.val)))

lemma cycle_sym (k : ℕ) (a b : Fin (3*k)) : cycle k a b = cycle k b a := by
  apply Bool.eq_iff_iff.mpr
  simp only [cycle,decide_eq_true_eq]
  constructor <;> rintro ⟨i,h⟩ <;> exact ⟨i,h.symm⟩

lemma cycle9_diag : ∀ i : Fin 27, cycle 9 i i=false := by decide +kernel
lemma cycle9_inc : ∀ i : Fin 27, ∃ j, cycle 9 i j=true := by decide +kernel
lemma cycle13_diag : ∀ i : Fin 39, cycle 13 i i=false := by decide +kernel
lemma cycle13_inc : ∀ i : Fin 39, ∃ j, cycle 13 i j=true := by decide +kernel

theorem cycle9_live (s : ℕ) (has : RepSizeAtMost (cycle 9) s) :
    ∃ C : Circuit, Live (cycle 9) C ∧ C.size ≤ s := by
  obtain ⟨C,mono,correct,min,sz⟩ := minimum_of_witness _ _ has
  exact ⟨C,minimum_live _ C mono correct min (cycle_sym 9) cycle9_diag cycle9_inc
    ⟨0, (cycle9_inc 0).choose,(cycle9_inc 0).choose_spec⟩,sz⟩

theorem cycle13_live (s : ℕ) (has : RepSizeAtMost (cycle 13) s) :
    ∃ C : Circuit, Live (cycle 13) C ∧ C.size ≤ s := by
  obtain ⟨C,mono,correct,min,sz⟩ := minimum_of_witness _ _ has
  exact ⟨C,minimum_live _ C mono correct min (cycle_sym 13) cycle13_diag cycle13_inc
    ⟨0, (cycle13_inc 0).choose,(cycle13_inc 0).choose_spec⟩,sz⟩
end PEqualNP.Outside.L_meta_9498_aux.Cycle.Initial

namespace PEqualNP.Outside.L_meta_9498_aux

open Finset

abbrev Parents (N : ℕ) := Fin N → List (Fin N)

def fanout {N : ℕ} (P : Parents N) (w : Fin N) : ℕ := ∑ j, (P j).count w

def slots {N : ℕ} (P : Parents N) : ℕ := ∑ j, (P j).length

def excess {N : ℕ} (P : Parents N) : ℕ := ∑ w, (fanout P w - 1)

private theorem sum_counts {N : ℕ} (L : List (Fin N)) :
    (∑ w, L.count w) = L.length := by
  induction L with
  | nil => simp
  | cons a l ih =>
    have ck (w : Fin N) : (a :: l).count w = l.count w + if w = a then 1 else 0 := by
      by_cases h : w = a
      · subst w
        simp
      · simp [h, Ne.symm h]
    simp [ck, Finset.sum_add_distrib, ih]

theorem sum_fanout {N : ℕ} (P : Parents N) : (∑ w, fanout P w) = slots P := by
  unfold fanout slots
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun j _ => sum_counts (P j))

private theorem count_sub {N : ℕ} (w : Fin N) {a b : List (Fin N)}
    (h : a.Sublist b) : a.count w ≤ b.count w := by
  induction h with
  | slnil => simp
  | cons a h ih =>
    rw [List.count_cons]
    omega
  | cons_cons a h ih =>
    rw [List.count_cons,List.count_cons]
    omega

theorem fanout_mono {N : ℕ} {P Q : Parents N}
    (sub : ∀ v, (Q v).Sublist (P v)) (w : Fin N) : fanout Q w ≤ fanout P w :=
  Finset.sum_le_sum fun j _ => count_sub w (sub j)

theorem excess_strict {N : ℕ} {P Q : Parents N}
    (sub : ∀ v, (Q v).Sublist (P v)) (pivot : Fin N)
    (repeated : 2 ≤ fanout P pivot) (gone : fanout Q pivot = 0) : excess Q < excess P := by
  unfold excess
  apply Finset.sum_lt_sum
  · intro w _
    exact Nat.sub_le_sub_right (fanout_mono sub w) 1
  · exact ⟨pivot, Finset.mem_univ _, by omega⟩

/-- Delete references to false or dead wires. Retaining unary positions as indexed nodes
ensures all lists of incoming references are sublists of their previous values. -/
def filtered {N : ℕ} (P : Parents N) (keep : Fin N → Bool) : Parents N :=
  fun v => if keep v then (P v).filter keep else []

theorem filtered_sub {N : ℕ} (P : Parents N) (keep : Fin N → Bool) (v : Fin N) :
    (filtered P keep v).Sublist (P v) := by
  unfold filtered
  split
  · exact List.filter_sublist
  · exact List.nil_sublist _

theorem no_fanout_after_filter {N : ℕ} (P : Parents N) (keep : Fin N → Bool)
    (w : Fin N) (gone : keep w = false) : fanout (filtered P keep) w = 0 := by
  unfold fanout
  apply Finset.sum_eq_zero
  intro j _
  apply Nat.eq_zero_of_not_pos
  intro pos
  have mem := List.count_pos_iff.mp pos
  unfold filtered at mem
  split at mem
  · have h := (List.mem_filter.mp mem).2
    simp [gone] at h
  · cases mem

theorem excess_decreases_on_pin {N : ℕ} (P : Parents N) (keep : Fin N → Bool)
    (pivot : Fin N) (repeated : 2 ≤ fanout P pivot) (gone : keep pivot = false) :
    excess (filtered P keep) < excess P :=
  excess_strict (filtered_sub P keep) pivot repeated (no_fanout_after_filter P keep pivot gone)

theorem excess_eq_slots {N : ℕ} (P : Parents N) (output : Fin N)
    (reads : ∀ w ≠ output, 1 ≤ fanout P w) (out : fanout P output = 0) :
    excess P + (N-1) = slots P := by
  let e (w : Fin N) := if w = output then 0 else 1
  have sumE : (∑ w, e w) = N-1 := by
    have split := Finset.sum_erase_add (Finset.univ : Finset (Fin N)) e (Finset.mem_univ output)
    have a : (∑ w ∈ (Finset.univ : Finset (Fin N)).erase output, e w) =
        ((Finset.univ : Finset (Fin N)).erase output).card := by
      calc
        _ = ∑ _w ∈ (Finset.univ : Finset (Fin N)).erase output, (1 : ℕ) :=
          Finset.sum_congr rfl (fun w m => by simp [e, (Finset.mem_erase.mp m).1])
        _ = _ := by simp
    rw [a, Finset.card_erase_of_mem (Finset.mem_univ output)] at split
    simpa [e] using split.symm
  calc
    excess P + (N-1) = (∑ w, ((fanout P w - 1) + e w)) := by
      simp only [excess, Finset.sum_add_distrib, sumE]
    _ = ∑ w, fanout P w := by
      apply Finset.sum_congr rfl
      intro w _
      by_cases h : w=output
      · subst w
        simp [out,e]
      · have hr := reads w h
        simp only [e, if_neg h]
        omega
    _ = slots P := sum_fanout P

theorem initial_excess_le_seven {g : ℕ} (P : Parents (78+g)) (output : Fin (78+g))
    (reads : ∀ w ≠ output, 1 ≤ fanout P w) (out : fanout P output = 0)
    (arity : slots P ≤ 2*g) (small : g ≤ 84) : excess P ≤ 7 := by
  have balance := excess_eq_slots P output reads out
  omega

inductive InCone {N : ℕ} (P : Parents N) : Fin N → Fin N → Prop
  | self (v) : InCone P v v
  | step {u v w} : u ∈ P v → InCone P v w → InCone P u w

theorem cone_order {N : ℕ} {P : Parents N}
    (back : ∀ v u, u ∈ P v → u < v) {u v : Fin N} (h : InCone P u v) : u ≤ v := by
  induction h with
  | self => exact le_rfl
  | step mem _ ih => exact (back _ _ mem).le.trans ih

theorem exists_cone_reader {N : ℕ} {P : Parents N} {u v : Fin N}
    (h : InCone P u v) (hne : u ≠ v) : ∃ r, u ∈ P r ∧ InCone P r v := by
  cases h with
  | self => exact (hne rfl).elim
  | step mem path => exact ⟨_,mem,path⟩

theorem unique_reader {N : ℕ} (P : Parents N) {u a b : Fin N} (single : fanout P u ≤ 1)
    (ha : u ∈ P a) (hb : u ∈ P b) : a = b := by
  by_contra hne
  have sub : ({a,b} : Finset (Fin N)) ⊆ Finset.univ := by simp
  have fees := Finset.sum_le_sum_of_subset_of_nonneg sub
    (fun (j : Fin N) _ _ => Nat.zero_le ((P j).count u))
  simp [hne, fanout] at fees single
  have a_pos := List.count_pos_iff.mpr ha
  have b_pos := List.count_pos_iff.mpr hb
  omega

/-- Every nonpivot ancestor of the earliest multiply-read wire has its unique reader
inside the same cone. With live trimming, its raw ancestors are exclusive to that cone. -/
theorem earliest_cone_closed {N : ℕ} (P : Parents N) (pivot u r : Fin N)
    (back : ∀ v i, i ∈ P v → i < v)
    (early : ∀ i < pivot, fanout P i ≤ 1)
    (path : InCone P u pivot) (notPivot : u ≠ pivot) (reads : u ∈ P r) :
    InCone P r pivot := by
  have lt := lt_of_le_of_ne (cone_order back path) notPivot
  obtain ⟨s,mem,rest⟩ := exists_cone_reader path notPivot
  exact (unique_reader P (early _ lt) mem reads) ▸ rest

theorem pinned_cone_zero {N : ℕ} (P : Parents N) (pivot : Fin N) (val : Fin N → Bool)
    (back : ∀ v u, u ∈ P v → u < v)
    (pin : ∀ v, InCone P v pivot → P v = [] → val v = false)
    (zero : ∀ v, P v ≠ [] → (∀ u ∈ P v, val u = false) → val v = false) :
    val pivot = false := by
  have h : ∀ v, InCone P v pivot → val v = false := by
    intro v
    induction v using WellFoundedLT.induction with
    | ind v ih =>
      intro path
      by_cases h : P v = []
      · exact pin v path h
      · exact zero v h (fun u m => ih u (back v u m) (.step m path))
  exact h pivot (.self pivot)

theorem pinned_support_excess_drops {N : ℕ} (P : Parents N) (pivot : Fin N)
    (val : Fin N → Bool) (repeated : 2 ≤ fanout P pivot)
    (back : ∀ v u, u ∈ P v → u < v)
    (pin : ∀ v, InCone P v pivot → P v = [] → val v = false)
    (zero : ∀ v, P v ≠ [] → (∀ u ∈ P v, val u = false) → val v = false) :
    excess (filtered P val) < excess P :=
  excess_decreases_on_pin P val pivot repeated (pinned_cone_zero P pivot val back pin zero)

end PEqualNP.Outside.L_meta_9498_aux

namespace PEqualNP.Outside.L_meta_9498_aux

open Finset

theorem no_repeats_iff_zero {N : ℕ} (P : Parents N) :
    excess P = 0 ↔ ∀ w, fanout P w ≤ 1 := by
  unfold excess
  constructor
  · intro no w
    have single : fanout P w - 1 ≤ (∑ v, (fanout P v - 1)) :=
      Finset.single_le_sum (f:=fun v => fanout P v - 1)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ w)
    omega
  · intro h
    apply Finset.sum_eq_zero
    intro w _
    have small := h w
    omega

theorem earliest_repeat_exists {N : ℕ} (P : Parents N) (positive : 0 < excess P) :
    ∃ pivot, 2 ≤ fanout P pivot ∧ ∀ i < pivot, fanout P i ≤ 1 := by
  classical
  let R : Finset (Fin N) := Finset.univ.filter (fun i => 2 ≤ fanout P i)
  have nonempty : R.Nonempty := by
    by_contra no
    have empty : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp no
    have h (i : Fin N) : fanout P i ≤ 1 := by
      by_contra more
      have mem : i ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
      rw [empty] at mem
      exact (Finset.notMem_empty i) mem
    exact (Nat.ne_of_gt positive) ((no_repeats_iff_zero P).mpr h)
  let p := R.min' nonempty
  refine ⟨p, (Finset.mem_filter.mp (Finset.min'_mem R nonempty)).2, ?_⟩
  intro i hi
  by_contra h
  have m : i ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩
  exact (not_le_of_gt hi) (Finset.min'_le R i m)

theorem filtered_back {N : ℕ} (P : Parents N) (keep : Fin N → Bool)
    (back : ∀ j u, u ∈ P j → u < j) :
    ∀ j u, u ∈ filtered P keep j → u < j :=
  fun j u hu => back j u ((filtered_sub P keep j).subset hu)

theorem only_pivot_exits {N : ℕ} (P : Parents N) (pivot u r : Fin N)
    (back : ∀ v i, i ∈ P v → i < v)
    (early : ∀ i < pivot, fanout P i ≤ 1)
    (path : InCone P u pivot) (reads : u ∈ P r)
    (outside : ¬InCone P r pivot) : u = pivot := by
  by_contra notPivot
  exact outside (earliest_cone_closed P pivot u r back early path notPivot reads)

/-- Two operand cones of a gate cannot overlap if every wire before that gate
has at most one reader slot. -/
theorem one_reader_unique_last {N : ℕ} (P : Parents N) (root : Fin N)
    (back : ∀ v i, i ∈ P v → i < v) (before : ∀ i < root, fanout P i ≤ 1)
    {u a b : Fin N} (ma : a ∈ P root) (mb : b ∈ P root)
    (ua : InCone P u a) (ub : InCone P u b) : a=b := by
  induction ua with
  | self v =>
    by_contra ne
    obtain ⟨s,mem,rest⟩ := exists_cone_reader ub ne
    have eq := unique_reader P (before v (back root v ma)) mem ma
    have h := cone_order back rest
    rw [eq] at h
    exact (not_le_of_gt (back root b mb)) h
  | @step v r a vm ra ih =>
    have vr := back r v vm
    have ar := back root a ma
    have sr : r < root := (cone_order back ra).trans_lt ar
    by_cases ne : v = b
    · subst b
      have eq := unique_reader P (before v (vr.trans sr)) vm mb
      rw [eq] at sr
      exact (lt_irrefl _ sr).elim
    · obtain ⟨s,mem,rest⟩ := exists_cone_reader ub ne
      have eq := unique_reader P (before v (vr.trans sr)) mem vm
      exact ih ma (eq ▸ rest)

end PEqualNP.Outside.L_meta_9498_aux

namespace PEqualNP.Outside.L_meta_9498_aux.Cycle

variable {V : Type} [DecidableEq V]

def folded (S : Finset V) (h : Finset V → Bool) (g : Finset V → Bool → Bool)
    (A : Finset V) : Bool := g (A \ S) (h (A ∩ S))

lemma split_cross (S : Finset V) (u v : V) (uS : u ∈ S) (vS : v ∉ S) :
    ({u,v} : Finset V) \ S = {v} ∧ ({u,v} : Finset V) ∩ S = {u} := by
  constructor <;> ext i
  all_goals
    by_cases eu : i=u
    · subst i
      have ne : u ≠ v := fun eq => vS (eq ▸ uS)
      simp [uS,ne]
    · by_cases ev : i=v
      · subst i
        simp [vS,eu]
      · simp [eu,ev]

lemma split_outside (S : Finset V) (v : V) (vS : v ∉ S) :
    ({v} : Finset V) \ S = {v} ∧ ({v} : Finset V) ∩ S = ∅ := by
  constructor <;> ext i
  all_goals
    by_cases eq : i=v
    · subst i; simp [vS]
    · simp [eq]

lemma split_inside (S A : Finset V) (inside : A ⊆ S) : A \ S = ∅ ∧ A ∩ S = A := by
  constructor <;> ext i
  all_goals
    by_cases h : i ∈ A
    · simp [h,inside h]
    · simp [h]

lemma cross_values (S : Finset V) (h : Finset V → Bool) (g : Finset V → Bool → Bool)
    (mono : ∀ A B, A ⊆ B → h A = true → h B = true)
    (single : ∀ a, folded S h g {a} = false)
    (u v : V) (uS : u∈S) (vS : v∉S) (hit : folded S h g {u,v} = true) :
    h ∅ = false ∧ h {u} = true := by
  obtain ⟨a,b⟩ := split_cross S u v uS vS
  obtain ⟨c,d⟩ := split_outside S v vS
  have neg := single v
  unfold folded at hit neg
  rw [a,b] at hit
  rw [c,d] at neg
  have diff : h {u} ≠ h ∅ := by
    intro eq
    rw [eq,neg] at hit
    contradiction
  cases z : h ∅
  · refine ⟨rfl,?_⟩
    cases p : h {u}
    · exact False.elim (diff (p.trans z.symm))
    · rfl
  · exact False.elim (diff ((mono ∅ {u} (Finset.empty_subset _) z).trans z.symm))

theorem exclusive_independent (G : SimpleGraph V) (S : Finset V)
    (h : Finset V → Bool) (g : Finset V → Bool → Bool)
    (mono : ∀ A B, A ⊆ B → h A = true → h B = true)
    (outer : ∀ A, g A false = true → g A true = true)
    (single : ∀ a, folded S h g {a} = false)
    (positive : ∀ a b, G.Adj a b → folded S h g {a,b} = true)
    (cross : ∃ a∈S, ∃ b∉S, G.Adj a b) :
    (∀ a∈S, ∀ b∈S, ¬ G.Adj a b) := by
  obtain ⟨u,uS,v,vS,edge⟩ := cross
  obtain ⟨zero,one⟩ := cross_values S h g mono single u v uS vS (positive u v edge)
  have forbidden : g ∅ true = false := by
    have sub : ({u} : Finset V) ⊆ S := by simpa using uS
    have m := single u
    obtain ⟨a,b⟩ := split_inside S {u} sub
    unfold folded at m
    rwa [a,b,one] at m
  have independent : ∀ a∈S, ∀ b∈S, ¬ G.Adj a b := by
    intro a aS b bS adj
    have sub : ({a,b} : Finset V) ⊆ S := by
      intro k hk
      rw [Finset.mem_insert,Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact aS
      · exact bS
    have pp := positive a b adj
    obtain ⟨c,d⟩ := split_inside S {a,b} sub
    unfold folded at pp
    rw [c,d] at pp
    cases hh : h {a,b}
    · rw [hh] at pp
      have impossible := outer ∅ pp
      rw [forbidden] at impossible
      contradiction
    · rw [hh,forbidden] at pp
      contradiction
  exact independent

theorem exclusive_support_or (G : SimpleGraph V) (S : Finset V)
    (h : Finset V → Bool) (g : Finset V → Bool → Bool)
    (mono : ∀ A B, A ⊆ B → h A = true → h B = true)
    (outer : ∀ A, g A false = true → g A true = true)
    (single : ∀ a, folded S h g {a} = false)
    (positive : ∀ a b, G.Adj a b → folded S h g {a,b} = true)
    (incident : ∀ a ∈ S, ∃ b, G.Adj a b)
    (cross : ∃ a∈S, ∃ b∉S, G.Adj a b) :
    (∀ a∈S, ∀ b∈S, ¬ G.Adj a b) ∧
      (∀ A ⊆ S, h A = decide A.Nonempty) := by
  obtain ⟨u,uS,v,vS,edge⟩ := cross
  obtain ⟨zero,one⟩ := cross_values S h g mono single u v uS vS (positive u v edge)
  have forbidden : g ∅ true = false := by
    have sub : ({u} : Finset V) ⊆ S := by simpa using uS
    have m := single u
    obtain ⟨a,b⟩ := split_inside S {u} sub
    unfold folded at m
    rwa [a,b,one] at m
  have independent : ∀ a∈S, ∀ b∈S, ¬ G.Adj a b := by
    intro a aS b bS adj
    have sub : ({a,b} : Finset V) ⊆ S := by
      intro k hk
      rw [Finset.mem_insert,Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact aS
      · exact bS
    have pp := positive a b adj
    obtain ⟨c,d⟩ := split_inside S {a,b} sub
    unfold folded at pp
    rw [c,d] at pp
    cases hh : h {a,b}
    · rw [hh] at pp
      have impossible := outer ∅ pp
      rw [forbidden] at impossible
      contradiction
    · rw [hh,forbidden] at pp
      contradiction
  refine ⟨independent,?_⟩
  intro A incl
  by_cases ne : A.Nonempty
  · obtain ⟨a,ha⟩ := ne
    obtain ⟨b,adj⟩ := incident a (incl ha)
    have bS : b∉S := fun bs => independent a (incl ha) b bs adj
    have oneA := (cross_values S h g mono single a b (incl ha) bS (positive a b adj)).2
    rw [decide_eq_true (show A.Nonempty from ⟨a,ha⟩)]
    exact mono {a} A (by simpa) oneA
  · rw [Finset.not_nonempty_iff_eq_empty.mp ne,zero]
    simp
end PEqualNP.Outside.L_meta_9498_aux.Cycle

namespace PEqualNP.Outside.L_meta_9498_aux

open PEqualNP.Outside.L_meta_9498_aux.Cycle

inductive Node (V : Type) (N : ℕ) where
  | zero
  | input (x : V)
  | copy (a : Fin N)
  | all (a b : Fin N)
  | any (a b : Fin N)

def Node.wires {V N} : Node V N → List (Fin N)
  | .zero | .input _ => []
  | .copy a => [a]
  | .all a b | .any a b => [a,b]

structure Dag (V : Type) (N : ℕ) where
  code : Fin N → Node V N
  back : ∀ j i, i ∈ (code j).wires → i < j
  inputs_unique : ∀ i j (x : V), code i = .input x → code j = .input x → i=j

namespace Dag
variable {V : Type} {N : ℕ}

def parents (D : Dag V N) : Parents N := fun i => (D.code i).wires

theorem edgeCopy (D : Dag V N) {w a : Fin N} (edge : D.code w = .copy a) :
    a ∈ D.parents w := by simp [parents, edge, Node.wires]

theorem edgeAll (D : Dag V N) {w a b : Fin N} (edge : D.code w = .all a b) :
    a ∈ D.parents w ∧ b ∈ D.parents w := by simp [parents, edge, Node.wires]

theorem edgeAny (D : Dag V N) {w a b : Fin N} (edge : D.code w = .any a b) :
    a ∈ D.parents w ∧ b ∈ D.parents w := by simp [parents, edge, Node.wires]

def eval (D : Dag V N) (raw : V → Bool) (patch : Fin N → Option Bool) (w : Fin N) : Bool :=
  match patch w with
  | some b => b
  | none =>
    match h : D.code w with
    | .zero => false
    | .input x => raw x
    | .copy a => eval D raw patch a
    | .all a b => eval D raw patch a && eval D raw patch b
    | .any a b => eval D raw patch a || eval D raw patch b
termination_by w.val
decreasing_by
  · exact D.back w _ (D.edgeCopy h)
  · exact D.back w _ (D.edgeAll h).1
  · exact D.back w _ (D.edgeAll h).2
  · exact D.back w _ (D.edgeAny h).1
  · exact D.back w _ (D.edgeAny h).2

def blank (_ : Fin N) : Option Bool := none

def stamp (p : Fin N) (b : Bool) (w : Fin N) : Option Bool :=
  if w=p then some b else none

def value [DecidableEq V] (D : Dag V N) (A : Finset V) (w : Fin N) : Bool :=
  D.eval (fun x => decide (x∈A)) blank w

theorem eval_in_cone (D : Dag V N) (u : Fin N) (raw1 raw2 : V → Bool)
    (patch1 patch2 : Fin N → Option Bool)
    (sameRaw : ∀ w x, InCone D.parents w u → D.code w = .input x → raw1 x = raw2 x)
    (samePatch : ∀ w, InCone D.parents w u → patch1 w = patch2 w) :
    D.eval raw1 patch1 u = D.eval raw2 patch2 u := by
  have go (w : Fin N) (inside : InCone D.parents w u) :
      D.eval raw1 patch1 w = D.eval raw2 patch2 w := by
    induction w using WellFoundedLT.induction with
    | ind w ih =>
      rw [eval,eval,samePatch w inside]
      cases patched : patch2 w
      · cases h : D.code w with
        | zero => rfl
        | input x => exact sameRaw w x inside h
        | copy a =>
          have m := D.edgeCopy h
          exact ih a (D.back w a m) (.step m inside)
        | all a b =>
          obtain ⟨ma,mb⟩ := D.edgeAll h
          change (D.eval raw1 patch1 a && D.eval raw1 patch1 b) =
            (D.eval raw2 patch2 a && D.eval raw2 patch2 b)
          rw [ih a (D.back w a ma) (.step ma inside), ih b (D.back w b mb) (.step mb inside)]
        | any a b =>
          obtain ⟨ma,mb⟩ := D.edgeAny h
          change (D.eval raw1 patch1 a || D.eval raw1 patch1 b) =
            (D.eval raw2 patch2 a || D.eval raw2 patch2 b)
          rw [ih a (D.back w a ma) (.step ma inside), ih b (D.back w b mb) (.step mb inside)]
      · rfl
  exact go u (.self u)

def PatchLE (a b : Option Bool) : Prop :=
  match a,b with
  | none, none => True
  | some x, some y => x = true → y = true
  | _, _ => False

theorem eval_mono (D : Dag V N) (raw1 raw2 : V→Bool) (patch1 patch2 : Fin N→Option Bool)
    (rle : ∀ x, raw1 x=true → raw2 x=true) (ple : ∀ j, PatchLE (patch1 j) (patch2 j))
    (w : Fin N) : D.eval raw1 patch1 w = true → D.eval raw2 patch2 w = true := by
  induction w using WellFoundedLT.induction with
  | ind w ih =>
    rw [eval,eval]
    have t := ple w
    cases h1 : patch1 w <;> cases h2 : patch2 w
    · cases h : D.code w with
      | zero => simp
      | input x => exact rle x
      | copy a => exact ih a (D.back w a (D.edgeCopy h))
      | all a b =>
        obtain ⟨ma,mb⟩ := D.edgeAll h
        intro x
        exact Tree.and_truth.mpr
          ⟨ih a (D.back w a ma) (Tree.and_truth.mp x).1,
            ih b (D.back w b mb) (Tree.and_truth.mp x).2⟩
      | any a b =>
        obtain ⟨ma,mb⟩ := D.edgeAny h
        intro x
        exact Tree.or_truth.mpr
          ((Tree.or_truth.mp x).imp (ih a (D.back w a ma)) (ih b (D.back w b mb)))
    · simp [PatchLE,h1,h2] at t
    · simp [PatchLE,h1,h2] at t
    · simpa [PatchLE,h1,h2] using t

theorem value_mono [DecidableEq V] (D : Dag V N) (w : Fin N) :
    ∀ A B : Finset V, A ⊆ B → D.value A w = true → D.value B w = true := by
  intro A B sub
  apply D.eval_mono
  · intro x hx
    exact decide_eq_true (sub (of_decide_eq_true hx))
  · intro j
    trivial

noncomputable def support [DecidableEq V] (D : Dag V N) (p : Fin N) : Finset V := by
  classical
  exact Finset.univ.biUnion (fun j =>
    if InCone D.parents j p then match D.code j with
      | .input x => {x}
      | _ => ∅
    else ∅)

theorem support_iff [DecidableEq V] (D : Dag V N) (p : Fin N) (x : V) :
    x ∈ D.support p ↔ ∃ j, InCone D.parents j p ∧ D.code j = .input x := by
  classical
  unfold support
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j,h⟩
    by_cases m : InCone D.parents j p
    · simp only [if_pos m] at h
      cases code : D.code j <;> simp [code] at h
      rename_i y
      obtain rfl : x=y := h
      exact ⟨j,m,code⟩
    · simp [m] at h
  · rintro ⟨j,m,h⟩
    exact ⟨j, by simp [m,h]⟩

theorem value_support [DecidableEq V] (D : Dag V N) (p : Fin N) (A : Finset V) :
    D.value A p = D.value (A ∩ D.support p) p := by
  unfold value
  apply D.eval_in_cone p
  · intro j x mem r
    simp [(D.support_iff p x).mpr ⟨j,mem,r⟩]
  · intro _ _
    rfl

end Dag
end PEqualNP.Outside.L_meta_9498_aux

namespace PEqualNP.Outside.L_meta_9498_aux

open CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover TopForm

def apparentInputs (n : ℕ) (C : Circuit) (j : Fin (n+C.gates.length)) : List ℕ :=
  if j.val < n then [] else (gateAt C (j.val-n)).inputs

def parentsOf (n : ℕ) (C : Circuit) : Parents (n+C.gates.length) :=
  fun j => (apparentInputs n C j).filterMap fun i =>
    if h : i < n+C.gates.length then some ⟨i,h⟩ else none

theorem parentsOf_mem (n : ℕ) (C : Circuit) (j i : Fin (n+C.gates.length)) :
    i ∈ parentsOf n C j ↔ i.val ∈ apparentInputs n C j := by
  unfold parentsOf
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨a,ha, eq⟩
    split at eq
    · exact (congrArg Fin.val (Option.some.inj eq)) ▸ ha
    · cases eq
  · intro h
    refine ⟨i.val,h,?_⟩
    simp [i.isLt]

theorem apparent_back {n : ℕ} {C : Circuit} (back : ReadsBack n C)
    {j : Fin (n+C.gates.length)} {i : ℕ} (mem : i ∈ apparentInputs n C j) : i < j.val := by
  unfold apparentInputs at mem
  split at mem
  · cases mem
  · rename_i lower
    have bound := j.isLt
    have hj : j.val-n < C.gates.length := by omega
    have hi := back _ hj i mem
    omega

theorem parentsOf_back {n : ℕ} {C : Circuit} (back : ReadsBack n C) :
    ∀ j i, i ∈ parentsOf n C j → i < j :=
  fun j i mem => apparent_back back ((parentsOf_mem n C j i).mp mem)

theorem parentsOf_vals {n : ℕ} {C : Circuit} (back : ReadsBack n C)
    (j : Fin (n+C.gates.length)) :
    (parentsOf n C j).map Fin.val = apparentInputs n C j := by
  unfold parentsOf
  generalize hlist : apparentInputs n C j = ins
  have bound (i : ℕ) (hit : i ∈ ins) : i < n+C.gates.length := by
    rw [←hlist] at hit
    exact (apparent_back back hit).trans j.isLt
  clear hlist
  induction ins with
  | nil => rfl
  | cons a l ih =>
    simp only [List.filterMap_cons, dif_pos (bound a (by simp)),
      List.map_cons]
    rw [ih (fun i mem => bound i (List.mem_cons_of_mem _ mem))]

theorem circuit_slot_bound {n : ℕ} {C : Circuit} (ha : IsAO2 n C) :
    slots (parentsOf n C) ≤ 2*C.gates.length := by
  unfold slots
  have rb (j : Fin (n+C.gates.length)) :
      (parentsOf n C j).length ≤ if j.val < n then 0 else 2 := by
    rw [← List.length_map (f := (Fin.val : Fin (n+C.gates.length) → ℕ)),
      parentsOf_vals ha.2.1]
    unfold apparentInputs
    split
    · simp
    · rename_i notRaw
      have hj : j.val-n < C.gates.length := by have h := j.isLt; omega
      have member : gateAt C (j.val-n) ∈ C.gates := by
        simp [gateAt, List.getD_eq_getElem?_getD, hj, List.getElem_mem]
      exact (ha.2.2 _ member).le
  have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ => rb j)
  refine h.trans ?_
  rw [Fin.sum_univ_add]
  have raw (j : Fin n) :
      (if (Fin.castAdd C.gates.length j).val < n then 0 else 2) = 0 := if_pos j.isLt
  have gate (j : Fin C.gates.length) :
      (if (Fin.natAdd n j).val < n then 0 else 2) = 2 := by
    apply if_neg
    change ¬ n+j.val < n
    omega
  simp only [raw,gate]
  simp [Nat.mul_comm]

theorem live_fanout {n : ℕ} {C : Circuit} (ha : IsAO2 n C)
    (last : C.output+1=n+C.gates.length)
    (live : ∀ w < C.output, ∃ j < C.gates.length, w ∈ (gateAt C j).inputs) :
    let o : Fin (n+C.gates.length) := ⟨C.output,by omega⟩
    (∀ w ≠ o, 1 ≤ fanout (parentsOf n C) w) ∧ fanout (parentsOf n C) o = 0 := by
  dsimp only
  refine ⟨?_,?_⟩
  · intro w ne
    have h := w.isLt
    have nd : w.val ≠ C.output := fun he => ne (Fin.ext he)
    obtain ⟨j,jl,mem⟩ := live w.val (by omega)
    let dst : Fin (n+C.gates.length) := ⟨n+j, by omega⟩
    have input : w ∈ parentsOf n C dst := by
      rw [parentsOf_mem]
      simpa [apparentInputs, dst] using mem
    have hpos := List.count_pos_iff.mpr input
    unfold fanout
    exact hpos.trans_le (Finset.single_le_sum (f := fun j => (parentsOf n C j).count w)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ dst))
  · unfold fanout
    apply Finset.sum_eq_zero
    intro j _
    apply Nat.eq_zero_of_not_pos
    intro h
    have mem := List.count_pos_iff.mp h
    have hw := parentsOf_back ha.2.1 j _ mem
    have hj := j.isLt
    change C.output < j.val at hw
    omega

theorem circuit_initial_excess (C : Circuit) (ha : IsAO2 78 C)
    (small : C.size ≤ 84) (last : C.output+1=78+C.gates.length)
    (live : ∀ w < C.output, ∃ j < C.gates.length, w ∈ (gateAt C j).inputs) :
    excess (parentsOf 78 C) ≤ 7 := by
  obtain ⟨every, gone⟩ := live_fanout ha last live
  exact initial_excess_le_seven _ _ every gone (circuit_slot_bound ha) small

theorem circuit_excess_le {n : ℕ} (C : Circuit) (ha : IsAO2 n C)
    (last : C.output+1=n+C.gates.length)
    (live : ∀ w < C.output, ∃ j < C.gates.length, w ∈ (gateAt C j).inputs) :
    excess (parentsOf n C) ≤ C.size + 1 - n := by
  obtain ⟨every, gone⟩ := live_fanout ha last live
  have balance := excess_eq_slots (parentsOf n C) _ every gone
  have cap := circuit_slot_bound ha
  change _ ≤ C.gates.length + 1 - n
  omega

end PEqualNP.Outside.L_meta_9498_aux

namespace PEqualNP.Outside.L_meta_9498_aux.Cycle.CircuitDag

open CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover TopForm
open PEqualNP.Outside.L_meta_9498_aux
open PEqualNP.Outside.L_meta_9498_aux.Bypass

variable {n : ℕ} {C : Circuit}

def code (n : ℕ) (C : Circuit) (j : Fin (n+C.gates.length)) :
    Node (Fin n) (n+C.gates.length) :=
  if h : j.val < n then .input ⟨j.val,h⟩
  else match parentsOf n C j with
    | [a,b] => match (gateAt C (j.val-n)).op with
      | .and => .all a b
      | _ => .any a b
    | _ => .zero

theorem parent_pair (ao : IsAO2 n C) (j : Fin (n+C.gates.length))
    (ng : ¬ j.val < n) :
    ∃ a b, parentsOf n C j = [a,b] := by
  have hj : j.val-n < C.gates.length := by have h := j.isLt; omega
  have hlen : (parentsOf n C j).length = 2 := by
    rw [← List.length_map (f := Fin.val), parentsOf_vals ao.2.1, apparentInputs, if_neg ng]
    exact ao.2.2 _ (gateAt_mem hj)
  generalize he : parentsOf n C j = l at hlen ⊢
  cases l with
  | nil => simp at hlen
  | cons a l =>
    cases l with
    | nil => simp at hlen
    | cons b l =>
      cases l with
      | nil => exact ⟨a,b,rfl⟩
      | cons c l => simp at hlen

theorem code_parents (ao : IsAO2 n C) (j : Fin (n+C.gates.length)) :
    (code n C j).wires = parentsOf n C j := by
  by_cases hr : j.val<n
  · simp [code, hr, Node.wires, parentsOf, apparentInputs]
  · obtain ⟨a,b,hs⟩ := parent_pair ao j hr
    have hj : j.val-n < C.gates.length := by have h := j.isLt; omega
    rcases ao.1 _ (gateAt_mem hj) with ha | ha <;>
      simp [code, hr, hs, ha, Node.wires]

def dag (ao : IsAO2 n C) : Dag (Fin n) (n+C.gates.length) where
  code := code n C
  back j i h := parentsOf_back ao.2.1 j i ((code_parents ao j).symm ▸ h)
  inputs_unique i j x hi hj := by
    have aux (w : Fin (n+C.gates.length)) (hx : code n C w = .input x) : w.val=x.val := by
      by_cases hr : w.val<n
      · simp [code,hr] at hx
        exact congrArg Fin.val hx
      · obtain ⟨a,b,hs⟩ := parent_pair ao w hr
        have hw : w.val-n < C.gates.length := by have h := w.isLt; omega
        rcases ao.1 _ (gateAt_mem hw) with ha | ha <;> simp [code,hr,hs,ha] at hx
    exact Fin.ext ((aux i hi).trans (aux j hj).symm)

theorem parents_eq (ao : IsAO2 n C) : (dag ao).parents = parentsOf n C :=
  funext (code_parents ao)

theorem raw_code (ao : IsAO2 n C) (u : Fin n) :
    (dag ao).code (u.castAdd C.gates.length) = .input u := by
  have h : (u.castAdd C.gates.length).val < n := u.isLt
  simp [dag, code, h]

theorem evalWire (ao : IsAO2 n C) (x : Fin n → Bool) (w : Fin (n+C.gates.length)) :
    (dag ao).eval x (fun _ => none) w = val C (List.ofFn x) w.val := by
  have hx : (List.ofFn x).length = n := List.length_ofFn
  induction w using WellFoundedLT.induction with
  | ind w ih =>
    by_cases hr : w.val<n
    · have hcode : (dag ao).code w = .input ⟨w.val,hr⟩ := by
        change code n C w = _
        unfold code
        rw [dif_pos hr]
      rw [val_input hx hr, Dag.eval]
      cases hc : (dag ao).code w <;> simp [hc] at hcode
      subst_vars
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, hr]
    · obtain ⟨a,b,hs⟩ := parent_pair ao w hr
      have ha : a < w := parentsOf_back ao.2.1 w a (by simp [hs])
      have hb : b < w := parentsOf_back ao.2.1 w b (by simp [hs])
      have hj : w.val-n < C.gates.length := by have h := w.isLt; omega
      have hw : n+(w.val-n)=w.val := by omega
      have vals := parentsOf_vals ao.2.1 w
      rw [hs, apparentInputs, if_neg hr] at vals
      change [a.val,b.val] = (gateAt C (w.val-n)).inputs at vals
      have run := val_gate (C := C) hx hj
      rw [hw, ← vals] at run
      have hla : a.val < w.val := ha
      have hlb : b.val < w.val := hb
      rw [run, Dag.eval]
      rcases ao.1 _ (gateAt_mem hj) with hop | hop
      · have hcode : (dag ao).code w = .all a b := by simp [dag,code,hr,hs,hop]
        cases hc : (dag ao).code w <;> simp [hc] at hcode
        obtain ⟨ea,eb⟩ := hcode
        subst_vars
        simp [hop, GateOp.eval, hla, hlb, ih _ ha, ih _ hb]
      · have hcode : (dag ao).code w = .any a b := by simp [dag,code,hr,hs,hop]
        cases hc : (dag ao).code w <;> simp [hc] at hcode
        obtain ⟨ea,eb⟩ := hcode
        subst_vars
        simp [hop, GateOp.eval, hla, hlb, ih _ ha, ih _ hb]

theorem evalOutput (ao : IsAO2 n C) (valid : C.output < n+C.gates.length)
    (x : Fin n → Bool) : (dag ao).eval x (fun _ => none) ⟨C.output,valid⟩ =
      C.eval (List.ofFn x) := evalWire ao x _

end PEqualNP.Outside.L_meta_9498_aux.Cycle.CircuitDag

-- The fold compiler is adapted from the public Shannon, Support, and Elim helpers.
namespace PEqualNP.Outside.L_meta_9498_aux.Normalize

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

/-- What a gate becomes, given the statuses of the wires it reads; `m` is the number of the
next new wire. The result is the gate to emit, if any, and the status of the gate's wire. -/
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

/-- One step of the pass: `acc.1` holds the statuses of the old wires, `acc.2` the new gates. -/
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

/-- If the status of old wire `k` is a constant and some gate reads wire `k`, one gate is
saved. -/
theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Stat.const _, _ => trivial
  | Stat.wire _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Stat.const _, _ => rfl
  | Stat.wire _, hj => List.getD_append _ _ _ _ hj

/-- The invariant of the pass, for one input `y` of the new circuit: `w` are the old wires,
and every old wire has a valid status whose value on the new wires is the old value. -/
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

/-- Fold missing inputs, constants, and copies, emitting a backward binary AND/OR list. -/
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

end PEqualNP.Outside.L_meta_9498_aux.Normalize

namespace PEqualNP.Outside.L_meta_9498_aux.Normalize

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_9498_aux.Cycle.Initial

/-- A least representative of a nonempty irreflexive symmetric promise relation
can be chosen in binary backward form, with every wire below its output read. -/
theorem binary_live_of_rep {n : ℕ} (A : Fin n → Fin n → Bool) {s : ℕ}
    (has : RepSizeAtMost A s) (sym : ∀ a b, A a b = A b a) (diag : ∀ a, A a a = false)
    (inc : ∀ a, ∃ b, A a b = true) (pos : ∃ a b, A a b = true) :
    ∃ D : Circuit, IsAO2 (n+n) D ∧ Represents A D ∧ D.size ≤ s ∧
      D.output+1 = n+n+D.gates.length ∧
      ∀ w < D.output, ∃ j < D.gates.length, w ∈ (gateAt D j).inputs := by
  obtain ⟨C, hm, hr, hmin, hc⟩ := minimum_of_witness A s has
  obtain ⟨u,v,huv⟩ := pos
  have different : C.eval (oneEach u v) ≠ C.eval (oneEach u u) := by
    change ∀ _ : C.eval (oneEach u v) = C.eval (oneEach u u), False
    rw [hr u v, hr u u, huv, diag]
    decide
  obtain ⟨D,hD,hDC,_,same⟩ := normalize_nonconstant hm
    (n := n+n) (x := oneEach u v) (y := oneEach u u)
    (by simp [oneEach]) (by simp [oneEach]) different
  have md : Monotone2 D := fun g hg => ⟨hD.1 g hg, by rw [hD.2.2 g hg]⟩
  have rd : Represents A D := fun a b =>
    (same _ (by simp [oneEach])).trans (hr a b)
  have dmin : MinRep A D := fun Q hQ rQ => hDC.trans (hmin Q hQ rQ)
  have full := minimum_live A D md rd dmin sym diag inc ⟨u,v,huv⟩
  refine ⟨D,hD,rd,hDC.trans hc,full.2.2.1,?_⟩
  intro w hw
  obtain ⟨j,hj,_,rw⟩ := full.2.2.2 w hw
  exact ⟨j,hj,rw⟩

theorem cycle13_binary_live {s : ℕ} (has : RepSizeAtMost (cycle 13) s) :
    ∃ D : Circuit, IsAO2 78 D ∧ Represents (cycle 13) D ∧ D.size ≤ s ∧
      D.output+1 = 78+D.gates.length ∧
      ∀ w < D.output, ∃ j < D.gates.length, w ∈ (gateAt D j).inputs :=
  binary_live_of_rep (cycle 13) has (cycle_sym 13) cycle13_diag cycle13_inc
    ⟨0,(cycle13_inc 0).choose,(cycle13_inc 0).choose_spec⟩

theorem cycle9_binary_live {s : ℕ} (has : RepSizeAtMost (cycle 9) s) :
    ∃ D : Circuit, IsAO2 54 D ∧ Represents (cycle 9) D ∧ D.size ≤ s ∧
      D.output+1 = 54+D.gates.length ∧
      ∀ w < D.output, ∃ j < D.gates.length, w ∈ (gateAt D j).inputs :=
  binary_live_of_rep (cycle 9) has (cycle_sym 9) cycle9_diag cycle9_inc
    ⟨0,(cycle9_inc 0).choose,(cycle9_inc 0).choose_spec⟩

end PEqualNP.Outside.L_meta_9498_aux.Normalize

namespace PEqualNP.Outside.L_meta_9498_aux.Cycle.CycleNine

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.TopForm PEqualNP.Outside.L_meta_9498_aux
open PEqualNP.Outside.L_meta_9498_aux.Cycle.Initial


def rawIndex (u : V) : Fin 27 := ⟨u.val % 27,Nat.mod_lt _ (by decide)⟩

theorem shore_cases :
    (∀ v : V, side v = true → v=left (rawIndex v)) ∧
    (∀ v : V, side v = false → v=right (rawIndex v)) := by decide +kernel

set_option maxRecDepth 10000 in
theorem adjacent_cycle : ∀ i j : Fin 27, adjacent (left i) (right j) = cycle 9 i j := by
  intro i j
  change adjacent (left i) (right j) = target i j
  unfold adjacent
  have hi : (left i).val < 27 := i.isLt
  have hj : ¬ (right j).val < 27 := by change ¬ 27+j.val<27; omega
  rw [dif_pos hi,dif_neg hj]
  congr 1
  apply Fin.ext
  change 27+j.val-27=j.val
  omega

def rowEval (C : Circuit) (A : Finset V) :=
  C.eval (List.ofFn (fun i : V => decide (i∈A)))

theorem rowEval_cycle {C : Circuit} (h : Represents (cycle 9) C) (i j : Fin 27) :
    rowEval C {left i,right j} = cycle 9 i j := by
  have eq : (fun x : V => decide (x∈({left i,right j} : Finset V))) = row i j := by
    funext x
    simp [row]
  unfold rowEval
  rw [eq]
  exact eval_row _ _ h _ _

def Fits (f : Finset V → Bool) : Prop :=
  (∀ a, f {a}=false) ∧ ∀ a b, side a ≠ side b → f {a,b}=adjacent a b

theorem initial_fit (C : Circuit) (ao : IsAO2 54 C) (rep : Represents (cycle 9) C) :
    Fits (rowEval C) := by
  have mono : Monotone2 C := fun g hg => ⟨ao.1 g hg, by rw [ao.2.2 g hg]⟩
  constructor
  · intro a
    simpa [rowEval] using singleton_false _ C mono rep cycle9_diag a
  · intro a b diff
    cases ca : side a <;> cases cb : side b
    · exact False.elim (diff (ca.trans cb.symm))
    · have aa := shore_cases.2 a ca
      have bb := shore_cases.1 b cb
      calc
        rowEval C {a,b} = rowEval C {left (rawIndex b),right (rawIndex a)} := by
          rw [Finset.pair_comm a b]
          exact congrArg (rowEval C) (congrArg₂ (fun x y : V => ({x,y}:Finset V)) bb aa)
        _ = cycle 9 (rawIndex b) (rawIndex a) := rowEval_cycle rep _ _
        _ = adjacent (left (rawIndex b)) (right (rawIndex a)) := (adjacent_cycle _ _).symm
        _ = adjacent a b := by rw [←bb,←aa,adjacent_symm]
    · have aa := shore_cases.1 a ca
      have bb := shore_cases.2 b cb
      calc
        rowEval C {a,b} = rowEval C {left (rawIndex a),right (rawIndex b)} :=
          congrArg (rowEval C) (congrArg₂ (fun x y : V => ({x,y}:Finset V)) aa bb)
        _ = cycle 9 (rawIndex a) (rawIndex b) := rowEval_cycle rep _ _
        _ = adjacent (left (rawIndex a)) (right (rawIndex b)) := (adjacent_cycle _ _).symm
        _ = adjacent a b := by rw [←aa,←bb]
    · exact False.elim (diff (ca.trans cb.symm))

theorem bounded_dag {s : ℕ} (has : RepSizeAtMost (cycle 9) s) :
    ∃ (N : ℕ) (D : Dag V N) (out : Fin N), (∀ p, p≤out) ∧
      Fits (fun A => D.value A out) ∧ excess D.parents ≤ s+1-54 := by
  obtain ⟨C,ao,rep,sz,final,live⟩ :=
    PEqualNP.Outside.L_meta_9498_aux.Normalize.cycle9_binary_live has
  have valid : C.output < 54+C.gates.length := by omega
  let D := CircuitDag.dag ao
  let out : Fin (54+C.gates.length) := ⟨C.output, valid⟩
  refine ⟨_,D,out,?_,?_,?_⟩
  · intro p
    change p.val≤C.output
    have := p.isLt
    omega
  · have eq : (fun A => D.value A out) = rowEval C := by
      funext A
      exact CircuitDag.evalOutput ao valid _
    rw [eq]
    exact initial_fit C ao rep
  · change excess (CircuitDag.dag ao).parents ≤ _
    rw [CircuitDag.parents_eq ao]
    have b := circuit_excess_le C ao final live
    omega

end PEqualNP.Outside.L_meta_9498_aux.Cycle.CycleNine

namespace PEqualNP.Outside.L_meta_9498_aux.Cycle.CycleNine

open PEqualNP.Outside.L_meta_9498_aux.Cycle.Interval

def incident (A : Finset V) (x : V) : Prop :=
  ∃ y ∈ A, adjacent x y = true

def TwinStep (A R : Finset V) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, x ∈ R → y ∈ R → incident A x → incident A y →
    side x = side y → ∀ z ∈ A, adjacent x z = adjacent y z

def Homogeneous (R : Finset V) (b : Bool) : Prop := ∀ x ∈ R, side x = b

def hitsRegion (A R : Finset V) (r : Fin 3) : Prop :=
  ∃ x ∈ project r A, x ∈ project r R ∧
    ∃ y ∈ project r A, adjacent (locate r x) (locate r y) = true

theorem twin_mono {A B R T : Finset V} (h : TwinStep A R)
    (a : B ⊆ A) (r : T ⊆ R) : TwinStep B T := by
  intro x hx y hy xr yr xi yi sideEq z hz
  obtain ⟨u,hu,xu⟩ := xi
  obtain ⟨v,hv,yv⟩ := yi
  exact h x (a hx) y (a hy) (r xr) (r yr)
    ⟨u,a hu,xu⟩ ⟨v,a hv,yv⟩ sideEq z (a hz)

theorem one_region {A R : Finset V} (twin : TwinStep A R) {bank : Bool}
    (hom : Homogeneous R bank) {r s : Fin 3}
    (rx : hitsRegion A R r) (sx : hitsRegion A R s) : r=s := by
  by_contra ne
  obtain ⟨x,xa,xr,x',x'a,xedge⟩ := rx
  obtain ⟨y,ya,yr,y',y'a,yedge⟩ := sx
  have X := (project_mem r A x).mp xa
  have XR := (project_mem r R x).mp xr
  have X' := (project_mem r A x').mp x'a
  have Y := (project_mem s A y).mp ya
  have YR := (project_mem s R y).mp yr
  have Y' := (project_mem s A y').mp y'a
  have same := twin (locate r x) X (locate s y) Y XR YR
    ⟨_, X', xedge⟩ ⟨_,Y',yedge⟩ ((hom _ XR).trans (hom _ YR).symm)
  have crossOne : adjacent (locate r x) (locate s y') = true :=
    (same _ Y').trans yedge
  have crossTwo : adjacent (locate r x') (locate s y) = true :=
    (adjacent_symm _ _).trans ((same _ X').symm.trans xedge)
  have a := boundary r s ne x y' crossOne
  have b := boundary r s ne x' y crossTwo
  have diff := adjacent_opposite _ _ xedge
  by_cases h : s=r+1 <;> simp [h] at a b
  all_goals exact diff (a.1.trans b.1.symm)

noncomputable def regionsHit (A R : Finset V) : Finset (Fin 3) := by
  classical
  exact Finset.univ.filter (hitsRegion A R)

theorem one_charge {A R : Finset V} (twin : TwinStep A R) {b : Bool}
    (hom : Homogeneous R b) : (regionsHit A R).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro r hr s hs
  exact one_region twin hom (Finset.mem_filter.mp hr).2 (Finset.mem_filter.mp hs).2

def colourSlice (R : Finset V) (b : Bool) : Finset V :=
  R.filter (fun x => side x = b)

theorem slice_subset (R : Finset V) (b : Bool) : colourSlice R b ⊆ R :=
  Finset.filter_subset _ _

theorem slice_common (R : Finset V) (b : Bool) : Homogeneous (colourSlice R b) b :=
  fun _ hx => (Finset.mem_filter.mp hx).2

theorem split_remove (A R : Finset V) :
    (A \ colourSlice R false) \ colourSlice R true = A \ R := by
  ext x
  cases h : side x <;> simp [colourSlice,h]

theorem one_twin_two_charges {A R : Finset V} (twin : TwinStep A R) :
    (regionsHit A (colourSlice R false)).card +
    (regionsHit (A \ colourSlice R false) (colourSlice R true)).card ≤ 2 := by
  have left := one_charge (twin_mono twin (fun _ h => h) (slice_subset R false)) (slice_common R false)
  have right : (regionsHit (A \ colourSlice R false) (colourSlice R true)).card ≤ 1 := one_charge (twin_mono twin (Finset.sdiff_subset) (slice_subset R true)) (slice_common R true)
  omega
end PEqualNP.Outside.L_meta_9498_aux.Cycle.CycleNine

namespace PEqualNP.Outside.L_meta_9498_aux.Cycle.CycleNine

def graph : SimpleGraph V where
  Adj a b := adjacent a b = true
  symm := ⟨by intro a b h; exact (adjacent_symm b a).trans h⟩
  loopless := ⟨fun a h => adjacent_opposite a a h rfl⟩

instance : DecidableRel graph.Adj :=
  fun a b => inferInstanceAs (Decidable (adjacent a b = true))

theorem bip (a b : V) (adj : graph.Adj a b) : side a ≠ side b :=
  adjacent_opposite a b adj

def Obstruction (A : Finset V) : Prop :=
  ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, ∃ d ∈ A,
    adjacent a b = true ∧ adjacent b c = true ∧ adjacent c d = true ∧ adjacent a d = false

def FreeStep (A R : Finset V) : Prop :=
  (∀ x ∈ A ∩ R, ∀ y ∈ A \ R, adjacent x y = false) ∧ ¬ Obstruction (A ∩ R)

abbrev GlobalMove := Bool × Finset V

def GlobalStep (A : Finset V) (m : GlobalMove) : Prop :=
  if m.1 then TwinStep A m.2 ∧ ∃ b, Homogeneous m.2 b else FreeStep A m.2

def GlobalSteps (A : Finset V) : List GlobalMove → Prop
  | [] => True
  | m :: rest => GlobalStep A m ∧ GlobalSteps (A \ m.2) rest

def globalRemaining (A : Finset V) : List GlobalMove → Finset V
  | [] => A
  | m :: rest => globalRemaining (A \ m.2) rest

def classCount : List GlobalMove → ℕ
  | [] => 0
  | m :: rest => (if m.1 then 1 else 0) + classCount rest

theorem prepend_twin {A R : Finset V} {rs : List GlobalMove}
    (twin : TwinStep A R) (rest : GlobalSteps (A \ R) rs) :
    GlobalSteps A ((true,colourSlice R false) :: (true,colourSlice R true) :: rs) := by
  refine ⟨?_,?_,?_⟩
  · exact ⟨twin_mono twin (fun _ h => h) (slice_subset R false),false,slice_common R false⟩
  · exact ⟨twin_mono twin Finset.sdiff_subset (slice_subset R true),true,slice_common R true⟩
  · rwa [split_remove]

theorem prepend_free {A R : Finset V} {rs : List GlobalMove}
    (free : FreeStep A R) (rest : GlobalSteps (A \ R) rs) :
    GlobalSteps A ((false,R) :: rs) :=
  ⟨free,rest⟩

theorem remaining_prepend_twin (A R : Finset V) (rs : List GlobalMove) :
    globalRemaining A ((true,colourSlice R false) :: (true,colourSlice R true) :: rs) =
      globalRemaining (A \ R) rs := by
  simp only [globalRemaining,split_remove]

theorem remaining_prepend_free (A R : Finset V) (rs : List GlobalMove) :
    globalRemaining A ((false,R) :: rs) = globalRemaining (A \ R) rs := rfl

theorem count_prepend_twin (R : Finset V) (rs : List GlobalMove) :
    classCount ((true,colourSlice R false) :: (true,colourSlice R true) :: rs) = classCount rs + 2 := by
  simp [classCount]
  omega

theorem count_prepend_free (R : Finset V) (rs : List GlobalMove) :
    classCount ((false,R) :: rs) = classCount rs := by simp [classCount]
end PEqualNP.Outside.L_meta_9498_aux.Cycle.CycleNine

namespace PEqualNP.Outside.L_meta_9498_aux.Cycle.CycleNine
def graphOn (W : Finset V) : SimpleGraph V where
  Adj a b := a∈W ∧ b∈W ∧ adjacent a b=true
  symm := ⟨fun a b h => ⟨h.2.1,h.1,(adjacent_symm _ _).symm ▸ h.2.2⟩⟩
  loopless := ⟨fun v h => adjacent_opposite v v h.2.2 rfl⟩
instance (W : Finset V) : DecidableRel (graphOn W).Adj :=
  fun a b => inferInstanceAs (Decidable (a∈W ∧ b∈W ∧ adjacent a b=true))
theorem bipOn (W : Finset V) (a b : V) (h : (graphOn W).Adj a b) : side a ≠ side b := by
  exact adjacent_opposite a b h.2.2
def Describes (W : Finset V) (f : Finset V → Bool) := (∀ a, f {a}=false) ∧
  ∀ a b, side a ≠ side b → f {a,b} = decide ((graphOn W).Adj a b)
theorem restrict_describes {W S : Finset V} {f : Finset V → Bool}
    (h : Describes W f) (zero : f ∅=false) : Describes (W \ S) (fun A => f (A \ S)) := by
  have one (a : V) : ({a} : Finset V) \ S = if a∈S then ∅ else {a} := by
    ext v
    by_cases ha : a∈S <;> by_cases eq : v=a <;> simp_all
  have two (a b : V) : ({a,b} : Finset V) \ S = (({a} : Finset V) \ S) ∪ (({b} : Finset V) \ S) := by
    ext v
    simp only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_singleton,Finset.mem_union]
    tauto
  constructor
  · intro a
    change f (({a} : Finset V) \ S) = false
    rw [one]
    split <;> first | exact zero | exact h.1 _
  · intro a b diff
    change f (({a,b} : Finset V) \ S) = _
    rw [two,one,one]
    by_cases aS : a∈S <;> by_cases bS : b∈S
    · simp [aS,bS,zero,graphOn]
    · simp [aS,bS,h.1,graphOn]
    · simp [aS,bS,h.1,graphOn]
    · by_cases aw : a∈W <;> by_cases bw : b∈W <;> cases ev : adjacent a b <;> simpa [aS,bS,aw,bw,ev,graphOn] using h.2 a b diff
end PEqualNP.Outside.L_meta_9498_aux.Cycle.CycleNine

namespace PEqualNP.Outside.L_meta_9498_aux.Cycle.Interval


def adj (x y : Vertex) : Bool := (neighborhood x).testBit y.val

theorem adj_sym : ∀ x y, adj x y = adj y x := by decide +kernel

theorem neighborhood_bound : ∀ x : Vertex, neighborhood x < 2^18 := by decide +kernel

def Incident (A : Finset Vertex) (x : Vertex) : Prop := ∃ y ∈ A, adj x y = true

def Charge (A R : Finset Vertex) : Prop := ∃ x ∈ A, x ∈ R ∧ Incident A x

instance (A R : Finset Vertex) : Decidable (Charge A R) := by
  unfold Charge Incident
  infer_instance

def ClassStep (A R : Finset Vertex) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, x ∈ R → y ∈ R → Incident A x → Incident A y →
    bank x = bank y ∧ ∀ z ∈ A, adj x z = adj y z

def act (U : ℕ) : Finset Vertex := Finset.univ.filter (fun x => U.testBit x.val)

theorem mem_act {U : ℕ} {x : Vertex} : x ∈ act U ↔ U.testBit x.val = true := by
  simp [act]

theorem act_full : act full = Finset.univ := by
  ext x
  rw [mem_act]
  have h := x.isLt
  change (2^18-1 : ℕ).testBit x.val = true ↔ x ∈ Finset.univ
  rw [Nat.testBit_two_pow_sub_one]
  simp [h]

def LiveIn (U : ℕ) (A : Finset Vertex) : Prop :=
  ∀ x ∈ act U, Incident (act U) x → x ∈ A

theorem one_bit (x y : Vertex) :
    (1 <<< x.val : ℕ).testBit y.val = decide (x = y) := by
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]
  simp [Fin.ext_iff]

theorem fold_bits (l : List Vertex) (a : ℕ) (x : Vertex) :
    ((l.foldl (fun s b => s ||| (1 <<< b.val)) a).testBit x.val = true) ↔
      a.testBit x.val = true ∨ x ∈ l := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    rw [List.foldl_cons, ih, Nat.testBit_or, one_bit, Bool.or_eq_true, decide_eq_true_eq]
    rw [List.mem_cons]
    constructor
    · rintro ((ha | he) | hl)
      · exact Or.inl ha
      · exact Or.inr (Or.inl he.symm)
      · exact Or.inr (Or.inr hl)
    · rintro (ha | he | hl)
      · exact Or.inl (Or.inl ha)
      · exact Or.inl (Or.inr he.symm)
      · exact Or.inr hl

theorem class_bit (U : ℕ) (a b : Vertex) :
    (classOf U a).testBit b.val = true ↔
    b ∈ act U ∧ bank a = bank b ∧
      (neighborhood a &&& U) = (neighborhood b &&& U) := by
  unfold classOf
  rw [fold_bits]
  simp [vertices, mem_act, Bool.and_eq_true, and_assoc]

theorem class_test (U : ℕ) (a b : Vertex) (hb : b ∈ act U)
    (hs : bank a = bank b) (eqs : ∀ w ∈ act U, adj a w = adj b w) :
    (classOf U a).testBit b.val = true := by
  refine (class_bit _ _ _).mpr ⟨hb,hs,Nat.eq_of_testBit_eq ?_⟩
  intro i
  rw [Nat.testBit_and,Nat.testBit_and]
  by_cases hi : i < 18
  · let w : Vertex := ⟨i,hi⟩
    cases on : U.testBit i with
    | false => simp [on]
    | true =>
      have wmem : w ∈ act U := mem_act.mpr on
      simpa only [Bool.and_true,adj,w] using eqs w wmem
  · have hp : (2^18 : ℕ) ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow ((neighborhood_bound a).trans_le hp),
      Nat.testBit_lt_two_pow ((neighborhood_bound b).trans_le hp)]

theorem move_bits (U : ℕ) (a b : Vertex) (ha : a ∈ act U) :
    b ∈ act (move U a) ↔ b ∈ act U ∧ (classOf U a).testBit b.val = false := by
  have on := mem_act.mp ha
  simp only [move, on, if_pos, mem_act, Nat.testBit_xor]
  cases hU : U.testBit b.val <;> cases hC : (classOf U a).testBit b.val <;> simp
  have hb := (class_bit U a b).mp hC
  simp [mem_act, hU] at hb

theorem preserve_neighbor {U : ℕ} {A : Finset Vertex} (sim : LiveIn U A)
    {x : Vertex} (hx : x ∈ act U) (hi : Incident (act U) x) : Incident A x := by
  obtain ⟨y,hy,hxy⟩ := hi
  have yhit : Incident (act U) y := ⟨x,hx,(adj_sym y x).trans hxy⟩
  exact ⟨y,sim y hy yhit,hxy⟩

theorem may_move (U : ℕ) (A R : Finset Vertex) (sim : LiveIn U A)
    (step : ClassStep A R) :
    (LiveIn U (A \ R)) ∨ (Charge A R ∧ ∃ a : Vertex, LiveIn (move U a) (A \ R)) := by
  classical
  by_cases hit : ∃ a ∈ act U, a ∈ R ∧ Incident (act U) a
  · obtain ⟨a,ha,ar,ai⟩ := hit
    have aA := sim a ha ai
    have aI := preserve_neighbor sim ha ai
    refine Or.inr ⟨⟨a,aA,ar,aI⟩,a,?_⟩
    intro b hb bi
    obtain ⟨bU,bStay⟩ := (move_bits U a b ha).mp hb
    have biU : Incident (act U) b := by
      obtain ⟨z,hz,edge⟩ := bi
      exact ⟨z,((move_bits U a z ha).mp hz).1,edge⟩
    have bA := sim b bU biU
    refine Finset.mem_sdiff.mpr ⟨bA,?_⟩
    intro br
    obtain ⟨shore,equal⟩ := step a aA b bA ar br aI (preserve_neighbor sim bU biU)
    have eqU : ∀ z ∈ act U, adj a z = adj b z := by
      intro z hz
      by_cases zi : Incident (act U) z
      · exact equal z (sim z hz zi)
      · have neither (w : Vertex) (hw : w ∈ act U) : adj w z = false := by
          cases hwz : adj w z
          · rfl
          · exfalso
            exact zi ⟨w,hw,(adj_sym z w).trans hwz⟩
        rw [neither _ ha, neither _ bU]
    have gone := class_test U a b bU shore eqU
    exact Bool.noConfusion (bStay.symm.trans gone)
  · left
    intro b hb bi
    exact Finset.mem_sdiff.mpr ⟨sim b hb bi, fun br => hit ⟨b,hb,br,bi⟩⟩

def ClassSteps (A : Finset Vertex) : List (Finset Vertex) → Prop
  | [] => True
  | R :: rs => ClassStep A R ∧ ClassSteps (A \ R) rs

def chargeCount (A : Finset Vertex) : List (Finset Vertex) → ℕ
  | [] => 0
  | R :: rs => (if Charge A R then 1 else 0) + chargeCount (A \ R) rs

def remaining (A : Finset Vertex) (rs : List (Finset Vertex)) : Finset Vertex :=
  rs.foldl (· \ ·) A

theorem simulate (rs : List (Finset Vertex)) (U : ℕ) (A : Finset Vertex)
    (sim : LiveIn U A) (good : ClassSteps A rs) :
    ∃ xs : List Vertex, xs.length ≤ chargeCount A rs ∧
      LiveIn (xs.foldl move U) (remaining A rs) := by
  induction rs generalizing U A with
  | nil => exact ⟨[],Nat.zero_le _,sim⟩
  | cons R rs ih =>
    rcases may_move U A R sim good.1 with skip | ⟨pay,a,h⟩
    · obtain ⟨xs,bound,keep⟩ := ih U (A \ R) skip good.2
      refine ⟨xs, bound.trans ?_,keep⟩
      exact Nat.le_add_left _ _
    · obtain ⟨xs,bound,keep⟩ := ih (move U a) (A \ R) h good.2
      refine ⟨a::xs, ?_,keep⟩
      simp only [List.length_cons, chargeCount, if_pos pay]
      omega

theorem path_of_small_charge (rs : List (Finset Vertex))
    (good : ClassSteps Finset.univ rs) (small : chargeCount Finset.univ rs ≤ 4) :
    let U := remaining Finset.univ rs
    ∃ a b c d : Vertex, a∈U ∧ b∈U ∧ c∈U ∧ d∈U ∧ path a b c d = true := by
  have live : LiveIn full Finset.univ := fun x _ _ => Finset.mem_univ x
  obtain ⟨xs,hxs,stay⟩ := simulate rs full Finset.univ live good
  obtain ⟨a,b,c,d,hpath,hp⟩ := interval_four_paths xs (hxs.trans small)
  let U := xs.foldl move full
  let p := ((1 <<< a.val) ||| (1 <<< b.val) ||| (1 <<< c.val) ||| (1 <<< d.val))
  change U &&& p = p at hp
  have has (w : Vertex) (hpw : p.testBit w.val = true) : w ∈ act U := by
    have h := congrArg (fun v : ℕ => v.testBit w.val) hp
    simp only [Nat.testBit_and, hpw, Bool.and_true] at h
    exact mem_act.mpr h
  have ha : a∈act U := has a (by simp [p, Nat.testBit_or, one_bit])
  have hb : b∈act U := has b (by simp [p, Nat.testBit_or, one_bit])
  have hc : c∈act U := has c (by simp [p, Nat.testBit_or, one_bit])
  have hd : d∈act U := has d (by simp [p, Nat.testBit_or, one_bit])
  change (adj a b && adj b c && adj c d && !(adj a d)) = true at hpath
  simp only [Bool.and_eq_true] at hpath
  exact ⟨a,b,c,d,stay a ha ⟨b,hb,hpath.1.1.1⟩,stay b hb ⟨c,hc,hpath.1.1.2⟩,
    stay c hc ⟨d,hd,hpath.1.2⟩,stay d hd ⟨c,hc,(adj_sym d c).trans hpath.1.2⟩,
    by simpa only [path, adj, Bool.and_eq_true] using hpath⟩

end PEqualNP.Outside.L_meta_9498_aux.Cycle.Interval

namespace PEqualNP.Outside.L_meta_9498_aux.Cycle.Interval


def NoPath (A : Finset Vertex) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, path a b c d ≠ true

def SafeStep (A R : Finset Vertex) : Prop :=
  (∀ x∈A ∩ R, ∀ y∈A \ R, adj x y=false) ∧ NoPath (A ∩ R)

abbrev Move := Bool × Finset Vertex

def Steps (A : Finset Vertex) : List Move → Prop
  | [] => True
  | (kind,R) :: rs => (if kind then ClassStep A R else SafeStep A R) ∧ Steps (A \ R) rs

def charge (A : Finset Vertex) : List Move → ℕ
  | [] => 0
  | (kind,R) :: rs => (if kind = true ∧ Charge A R then 1 else 0) + charge (A \ R) rs

def final (A : Finset Vertex) : List Move → Finset Vertex
  | [] => A
  | (_,R) :: rs => final (A \ R) rs

structure Valid (U : ℕ) (A : Finset Vertex) : Prop where
  closed : ∀ {x y}, x∈act U → y∈act U → adj x y=true → (x∈A ↔ y∈A)
  clean : NoPath (act U \ A)

theorem path_adjs {a b c d : Vertex} (h : path a b c d=true) :
    adj a b=true ∧ adj b c=true ∧ adj c d=true := by
  change (adj a b && adj b c && adj c d && !(adj a d)) = true at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1,h.1.1.2,h.1.2⟩

theorem path_mem {U A} (ok : Valid U A) {a b c d : Vertex}
    (ha : a∈act U) (hb : b∈act U) (hc : c∈act U) (hd : d∈act U)
    (h : path a b c d=true) : (a∈A ↔ b∈A) ∧ (a∈A ↔ c∈A) ∧ (a∈A ↔ d∈A) := by
  obtain ⟨ab,bc,cd⟩ := path_adjs h
  have h₁ := ok.closed ha hb ab
  have h₂ := h₁.trans (ok.closed hb hc bc)
  exact ⟨h₁,h₂,h₂.trans (ok.closed hc hd cd)⟩

theorem safe_valid {U A R} (ok : Valid U A) (step : SafeStep A R) :
    Valid U (A \ R) := by
  constructor
  · intro x y hx hy hxy
    have old := ok.closed hx hy hxy
    constructor
    · intro xB
      obtain ⟨xA,xNR⟩ := Finset.mem_sdiff.mp xB
      refine Finset.mem_sdiff.mpr ⟨old.mp xA,?_⟩
      intro yR
      have no := step.1 y (Finset.mem_inter.mpr ⟨old.mp xA,yR⟩) x xB
      have yes := (adj_sym y x).trans hxy
      exact Bool.noConfusion (no.symm.trans yes)
    · intro yB
      obtain ⟨yA,yNR⟩ := Finset.mem_sdiff.mp yB
      refine Finset.mem_sdiff.mpr ⟨old.mpr yA,?_⟩
      intro xR
      have no := step.1 x (Finset.mem_inter.mpr ⟨old.mpr yA,xR⟩) y yB
      exact Bool.noConfusion (no.symm.trans hxy)
  · intro a ha b hb c hc d hd hp
    obtain ⟨haU,haN⟩ := Finset.mem_sdiff.mp ha
    obtain ⟨hbU,hbN⟩ := Finset.mem_sdiff.mp hb
    obtain ⟨hcU,hcN⟩ := Finset.mem_sdiff.mp hc
    obtain ⟨hdU,hdN⟩ := Finset.mem_sdiff.mp hd
    obtain ⟨ab,ac,ad⟩ := path_mem ok haU hbU hcU hdU hp
    by_cases ca : a∈A
    · have join (x : Vertex) (xA : x∈A) (xN : x∉A \ R) : x∈A ∩ R :=
        Finset.mem_inter.mpr ⟨xA, by
          by_contra no
          exact xN (Finset.mem_sdiff.mpr ⟨xA,no⟩)⟩
      exact step.2 a (join a ca haN) b (join b (ab.mp ca) hbN)
        c (join c (ac.mp ca) hcN) d (join d (ad.mp ca) hdN) hp
    · exact ok.clean a (Finset.mem_sdiff.mpr ⟨haU,ca⟩)
        b (Finset.mem_sdiff.mpr ⟨hbU,fun h => ca (ab.mpr h)⟩)
        c (Finset.mem_sdiff.mpr ⟨hcU,fun h => ca (ac.mpr h)⟩)
        d (Finset.mem_sdiff.mpr ⟨hdU,fun h => ca (ad.mpr h)⟩) hp

theorem real_neighbor {U A} (ok : Valid U A) {x : Vertex} (hx : x∈act U)
    (xA : x∈A) (xi : Incident (act U) x) : Incident A x := by
  obtain ⟨y,hy,hxy⟩ := xi
  exact ⟨y,(ok.closed hx hy hxy).mp xA,hxy⟩

theorem restrict_valid {U V A R} (ok : Valid U A) (sub : act V ⊆ act U)
    (protect : ∀ x∈act V, Incident (act V) x → x∈A → x∉R) : Valid V (A \ R) := by
  constructor
  · intro x y hx hy hxy
    have h := ok.closed (sub hx) (sub hy) hxy
    have xi : Incident (act V) x := ⟨y,hy,hxy⟩
    have yi : Incident (act V) y := ⟨x,hx,(adj_sym y x).trans hxy⟩
    constructor
    · intro xB
      have yA := h.mp (Finset.mem_sdiff.mp xB).1
      exact Finset.mem_sdiff.mpr ⟨yA,protect y hy yi yA⟩
    · intro yB
      have xA := h.mpr (Finset.mem_sdiff.mp yB).1
      exact Finset.mem_sdiff.mpr ⟨xA,protect x hx xi xA⟩
  · intro a ha b hb c hc d hd hp
    obtain ⟨haU,haN⟩ := Finset.mem_sdiff.mp ha
    obtain ⟨hbU,hbN⟩ := Finset.mem_sdiff.mp hb
    obtain ⟨hcU,hcN⟩ := Finset.mem_sdiff.mp hc
    obtain ⟨hdU,hdN⟩ := Finset.mem_sdiff.mp hd
    obtain ⟨ab,bc,cd⟩ := path_adjs hp
    have old (x : Vertex) (hx : x∈act V) (xi : Incident (act V) x)
        (xN : x∉A \ R) : x∈act U \ A :=
      Finset.mem_sdiff.mpr ⟨sub hx,fun xA => xN (Finset.mem_sdiff.mpr
        ⟨xA,protect x hx xi xA⟩)⟩
    exact ok.clean a (old a haU ⟨b,hbU,ab⟩ haN) b (old b hbU ⟨c,hcU,bc⟩ hbN)
      c (old c hcU ⟨d,hdU,cd⟩ hcN) d (old d hdU ⟨c,hcU,(adj_sym d c).trans cd⟩ hdN) hp

theorem class_valid {U A R} (ok : Valid U A) (step : ClassStep A R) :
    (Valid U (A \ R)) ∨ (Charge A R ∧ ∃ a : Vertex, Valid (move U a) (A \ R)) := by
  classical
  by_cases hit : ∃ a ∈ act U, a ∈ A ∧ a ∈ R ∧ Incident (act U) a
  · obtain ⟨a,ha,aA,ar,ai⟩ := hit
    have aI := real_neighbor ok ha aA ai
    refine Or.inr ⟨⟨a,aA,ar,aI⟩,a,restrict_valid ok (fun {_} hx => (move_bits _ _ _ ha |>.mp hx).1) ?_⟩
    intro b hb bi bA br
    obtain ⟨bU,bStay⟩ := (move_bits U a b ha).mp hb
    have biU : Incident (act U) b := by
      obtain ⟨z,hz,edge⟩ := bi
      exact ⟨z,((move_bits U a z ha).mp hz).1,edge⟩
    obtain ⟨shore,equal⟩ := step a aA b bA ar br aI (real_neighbor ok bU bA biU)
    have eqU : ∀ z ∈ act U, adj a z = adj b z := by
      intro z hz
      by_cases zA : z∈A
      · exact equal z zA
      · have neither (w : Vertex) (hw : w∈act U) (wA : w∈A) : adj w z=false := by
          cases hwz : adj w z
          · rfl
          · exact False.elim (zA ((ok.closed hw hz hwz).mp wA))
        rw [neither _ ha aA, neither _ bU bA]
    have gone := class_test U a b bU shore eqU
    exact Bool.noConfusion (bStay.symm.trans gone)
  · left
    apply restrict_valid ok (fun {_} hx => hx)
    intro b hb bi bA br
    exact hit ⟨b,hb,bA,br,bi⟩

theorem simulate_safe (rs : List Move) (U : ℕ) (A : Finset Vertex)
    (ok : Valid U A) (good : Steps A rs) :
    ∃ xs : List Vertex, xs.length ≤ charge A rs ∧ Valid (xs.foldl move U) (final A rs) := by
  induction rs generalizing U A with
  | nil => exact ⟨[],Nat.zero_le _,ok⟩
  | cons r rs ih =>
    obtain ⟨kind,R⟩ := r
    cases kind
    · have hh : SafeStep A R ∧ Steps (A \ R) rs := good
      obtain ⟨xs,bound,keep⟩ := ih U (A \ R) (safe_valid ok hh.1) hh.2
      exact ⟨xs,by simpa [charge] using bound,keep⟩
    · have hh : ClassStep A R ∧ Steps (A \ R) rs := good
      rcases class_valid ok hh.1 with skip | ⟨pay,a,h⟩
      · obtain ⟨xs,bound,keep⟩ := ih U (A \ R) skip hh.2
        refine ⟨xs, bound.trans ?_,keep⟩
        apply Nat.le_add_left
      · obtain ⟨xs,bound,keep⟩ := ih (move U a) (A \ R) h hh.2
        refine ⟨a::xs, ?_,keep⟩
        simp only [List.length_cons, charge, true_and, if_pos pay]
        omega

theorem safe_path_of_small_charge (rs : List Move)
    (good : Steps Finset.univ rs) (small : charge Finset.univ rs ≤ 4) :
    let A := final Finset.univ rs
    ∃ a b c d : Vertex, a∈A ∧ b∈A ∧ c∈A ∧ d∈A ∧ path a b c d = true := by
  have init : Valid full Finset.univ := by
    constructor
    · simp
    · intro a ha
      simp at ha
  obtain ⟨xs,hxs,stay⟩ := simulate_safe rs full Finset.univ init good
  obtain ⟨a,b,c,d,hpath,hp⟩ := interval_four_paths xs (hxs.trans small)
  let U := xs.foldl move full
  let A : Finset Vertex := final Finset.univ rs
  let p := ((1 <<< a.val) ||| (1 <<< b.val) ||| (1 <<< c.val) ||| (1 <<< d.val))
  change U &&& p = p at hp
  have has (w : Vertex) (hpw : p.testBit w.val = true) : w ∈ act U := by
    have h := congrArg (fun v : ℕ => v.testBit w.val) hp
    simp only [Nat.testBit_and, hpw, Bool.and_true] at h
    exact mem_act.mpr h
  have ha : a∈act U := has a (by simp [p, Nat.testBit_or, one_bit])
  have hb : b∈act U := has b (by simp [p, Nat.testBit_or, one_bit])
  have hc : c∈act U := has c (by simp [p, Nat.testBit_or, one_bit])
  have hd : d∈act U := has d (by simp [p, Nat.testBit_or, one_bit])
  obtain ⟨ab,ac,ad⟩ := path_mem stay ha hb hc hd hpath
  have aA : a∈A := by
    by_contra no
    exact stay.clean a (Finset.mem_sdiff.mpr ⟨ha,no⟩)
      b (Finset.mem_sdiff.mpr ⟨hb,fun h => no (ab.mpr h)⟩)
      c (Finset.mem_sdiff.mpr ⟨hc,fun h => no (ac.mpr h)⟩)
      d (Finset.mem_sdiff.mpr ⟨hd,fun h => no (ad.mpr h)⟩) hpath
  exact ⟨a,b,c,d,aA,ab.mp aA,ac.mp aA,ad.mp aA,hpath⟩

end PEqualNP.Outside.L_meta_9498_aux.Cycle.Interval

namespace PEqualNP.Outside.L_meta_9498_aux.Cycle.CycleNine

open PEqualNP.Outside.L_meta_9498_aux.Cycle.Interval

def localMoves (r : Fin 3) (rs : List GlobalMove) : List Move :=
  rs.map fun m => (m.1,project r m.2)

theorem local_charge (r : Fin 3) (A R : Finset V) :
    Charge (project r A) (project r R) ↔ hitsRegion A R r := by
  simp only [Charge, Incident, hitsRegion, adj, internal]

theorem local_class (r : Fin 3) {A R : Finset V} (twin : TwinStep A R) {b : Bool}
    (hom : Homogeneous R b) : ClassStep (project r A) (project r R) := by
  intro x xa y ya xr yr xi yi
  have X := (project_mem r A x).mp xa
  have Y := (project_mem r A y).mp ya
  have XR := (project_mem r R x).mp xr
  have YR := (project_mem r R y).mp yr
  have eq := (hom _ XR).trans (hom _ YR).symm
  refine ⟨by rwa [← bank_locate r x, ← bank_locate r y], ?_⟩
  obtain ⟨u,ua,hu⟩ := xi
  obtain ⟨v,va,hv⟩ := yi
  have xPos : incident A (locate r x) := ⟨_, (project_mem r A u).mp ua, by simpa [adj,internal] using hu⟩
  have yPos : incident A (locate r y) := ⟨_, (project_mem r A v).mp va, by simpa [adj,internal] using hv⟩
  intro z za
  simpa [adj,internal] using twin _ X _ Y XR YR xPos yPos eq _ ((project_mem r A z).mp za)

private theorem path_four_bits {a b c d : Vertex} (h : path a b c d = true) :
    adj a b = true ∧ adj b c = true ∧ adj c d = true ∧ adj a d = false := by
  change (adj a b && adj b c && adj c d && !(adj a d)) = true at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  tauto

theorem mapped_path (r : Fin 3) {A : Finset V} {a b c d : Vertex}
    (ma : a ∈ project r A) (mb : b ∈ project r A)
    (mc : c ∈ project r A) (md : d ∈ project r A) (p : path a b c d = true) :
    Obstruction A := by
  obtain ⟨ab,bc,cd,ad⟩ := path_four_bits p
  refine ⟨_, (project_mem r A a).mp ma, _, (project_mem r A b).mp mb,
    _, (project_mem r A c).mp mc, _, (project_mem r A d).mp md, ?_, ?_, ?_, ?_⟩
  all_goals simpa [adj,internal] using ‹_›

theorem local_free (r : Fin 3) {A R : Finset V} (free : FreeStep A R) :
    SafeStep (project r A) (project r R) := by
  have both {x : Vertex} (mem : x∈project r A ∩ project r R) : x∈project r (A∩R) := by
    simpa [project] using mem
  refine ⟨?_,?_⟩
  · intro x xm y ym
    rw [← project_diff] at ym
    have no := free.1 _ ((project_mem r (A∩R) x).mp (both xm)) _ ((project_mem r (A\R) y).mp ym)
    simpa [internal,adj] using no
  · intro a ma b mb c mc d md pp
    exact free.2 (mapped_path r (both ma) (both mb) (both mc) (both md) pp)

theorem project_steps (r : Fin 3) (A : Finset V) (rs : List GlobalMove)
    (good : GlobalSteps A rs) : Steps (project r A) (localMoves r rs) := by
  induction rs generalizing A with
  | nil => trivial
  | cons m rest ih =>
    obtain ⟨step,later⟩ := good
    obtain ⟨flag,R⟩ := m
    change (if flag then ClassStep (project r A) (project r R)
      else SafeStep (project r A) (project r R)) ∧
        Steps (project r A \ project r R) (localMoves r rest)
    refine ⟨?_,?_⟩
    · cases flag
      · exact local_free r step
      · obtain ⟨twins,b,hom⟩ := step
        exact local_class r twins hom
    · rw [←project_diff]
      exact ih (A\R) later

theorem local_final (r : Fin 3) (A : Finset V) (rs : List GlobalMove) :
    final (project r A) (localMoves r rs) = project r (globalRemaining A rs) := by
  induction rs generalizing A with
  | nil => rfl
  | cons m rest ih =>
    obtain ⟨flag,R⟩ := m
    change final (project r A \ project r R) (localMoves r rest) =
      project r (globalRemaining (A\R) rest)
    rw [←project_diff]
    exact ih (A\R)

theorem charge_sum_le (A : Finset V) (rs : List GlobalMove) (good : GlobalSteps A rs) :
    (∑ r : Fin 3, charge (project r A) (localMoves r rs)) ≤ classCount rs := by
  classical
  induction rs generalizing A with
  | nil => simp [charge,localMoves,classCount]
  | cons m rest ih =>
    obtain ⟨flag,R⟩ := m
    obtain ⟨this,more⟩ := good
    have tail := ih (A\R) more
    have head : (∑ r : Fin 3, (if flag = true ∧ Charge (project r A) (project r R)
        then 1 else 0 : ℕ)) ≤ if flag then 1 else 0 := by
      cases flag
      · simp
      · obtain ⟨twin,s,hom⟩ := this
        have bound := one_charge twin hom
        unfold regionsHit at bound
        rw [Finset.card_filter] at bound
        simpa [local_charge] using bound
    change (∑ r : Fin 3,
      ((if flag = true ∧ Charge (project r A) (project r R) then 1 else 0) +
        charge (project r A \ project r R) (localMoves r rest))) ≤
        (if flag then 1 else 0) + classCount rest
    rw [Finset.sum_add_distrib]
    simp only [←project_diff]
    exact Nat.add_le_add head tail

theorem global_path_of_14 (rs : List GlobalMove) (good : GlobalSteps Finset.univ rs)
    (small : classCount rs ≤ 14) : Obstruction (globalRemaining Finset.univ rs) := by
  have bound := (charge_sum_le Finset.univ rs good).trans small
  have existsSmall : ∃ r : Fin 3, charge (project r Finset.univ) (localMoves r rs) ≤ 4 := by
    by_contra no
    have key (r : Fin 3) : 5 ≤ charge (project r Finset.univ) (localMoves r rs) := by
      by_contra not
      exact no ⟨r,by omega⟩
    have all := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 3))) (fun r _ => key r)
    have left : (∑ _r : Fin 3, (5 : ℕ)) = 15 := by decide
    rw [left] at all
    omega
  obtain ⟨r,hr⟩ := existsSmall
  have steps := project_steps r Finset.univ rs good
  rw [project_univ] at hr steps
  obtain ⟨a,b,c,d,ma,mb,mc,md,pp⟩ := safe_path_of_small_charge _ steps hr
  have lift := local_final r Finset.univ rs
  rw [project_univ] at lift
  exact mapped_path r (lift ▸ ma) (lift ▸ mb) (lift ▸ mc) (lift ▸ md) pp

end PEqualNP.Outside.L_meta_9498_aux.Cycle.CycleNine

namespace PEqualNP.Outside.L_meta_9498_aux.Cycle.CycleNine

open PEqualNP.Represents
open PEqualNP.Outside.L_meta_9498_aux
open PEqualNP.Outside.L_meta_9498_aux.Cycle.Initial

theorem describes_of_fit {f : Finset V → Bool} (fit : Fits f) : Describes Finset.univ f := by
  refine ⟨fit.1,?_⟩
  intro a b diff
  rw [fit.2 a b diff]
  change adjacent a b = decide (a∈(Finset.univ : Finset V) ∧ b∈Finset.univ ∧ adjacent a b=true)
  cases h : adjacent a b <;> simp [h]

theorem no_small_cycle9_of_peel
    (peel : ∀ {N : ℕ} (D : Dag V N) (out : Fin N) (last : ∀ p,p≤out)
      (W : Finset V) (desc : Describes W (fun A => D.value A out)),
      ∃ moves, GlobalSteps W moves ∧ classCount moves ≤ 2*excess D.parents ∧
        ¬Obstruction (globalRemaining W moves)) :
    ¬ RepSizeAtMost (cycle 9) 60 := by
  intro has
  obtain ⟨N,D,out,last,fit,ex⟩ := bounded_dag has
  obtain ⟨moves,good,small,gone⟩ := peel D out last Finset.univ (describes_of_fit fit)
  exact gone (global_path_of_14 moves good (by omega))

end PEqualNP.Outside.L_meta_9498_aux.Cycle.CycleNine

namespace PEqualNP.Outside.L_meta_9498_aux.Cycle
variable {V : Type} [DecidableEq V]

def Path4 (G : SimpleGraph V) (a b c d : V) : Prop :=
  G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ ¬ G.Adj a d

lemma opposite_ends (G : SimpleGraph V) (colour : V → Bool)
    (bip : ∀ a b, G.Adj a b → colour a ≠ colour b)
    {a b c d : V} (p : Path4 G a b c d) : colour a ≠ colour d := by
  have ab := bip a b p.1
  have bc := bip b c p.2.1
  have cd := bip c d p.2.2.1
  cases ea : colour a <;> cases eb : colour b <;>
    cases ec : colour c <;> cases ed : colour d <;> simp_all

lemma exclusive_no_cross {G : SimpleGraph V} [DecidableRel G.Adj]
    (colour : V → Bool) (bip : ∀ a b, G.Adj a b → colour a ≠ colour b)
    (S : Finset V) (h : Finset V → Bool) (g : Finset V → Bool → Bool)
    (zer : folded S h g ∅=false) (single : ∀ a, folded S h g {a}=false)
    (correct : ∀ a b, colour a ≠ colour b → folded S h g {a,b}=decide (G.Adj a b))
    (T : Tree V) (linear : T.linear) (deps : T.leaves ⊆ S)
    (core : ∀ A ⊆ S, h A=T.eval A)
    (noCross : ∀ a∈S, ∀ b∉S, ¬ G.Adj a b)
    {a b c d : V} (p : Path4 G a b c d) :
    a∉S ∧ b∉S ∧ c∉S ∧ d∉S := by
  have reach {u v : V} (adj : G.Adj u v) (mem : u∈S) : v∈S :=
    by by_contra no; exact noCross u mem v no adj
  have noA : a∉S := by
    intro aS
    have bS := reach p.1 aS
    have cS := reach p.2.1 bS
    have dS := reach p.2.2.1 cS
    have collapse (A : Finset V) (subset : A ⊆ S) :
        folded S h g A = g ∅ (T.eval A) := by
      obtain ⟨outside,inside⟩ := split_inside S A subset
      unfold folded
      rw [outside,inside,core A subset]
    have pair_sub {u v : V} (hu : u ∈ S) (hv : v ∈ S) :
        ({u,v} : Finset V) ⊆ S := by
      intro w hw
      rw [Finset.mem_insert,Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact hu
      · exact hv
    have g0 : g ∅ false = false := by
      rwa [collapse ∅ (Finset.empty_subset _),Tree.eval_empty] at zer
    have g1 : g ∅ true = true := by
      have hit := correct a b (bip a b p.1)
      rw [collapse {a,b} (pair_sub aS bS), decide_eq_true p.1] at hit
      cases ev : T.eval {a,b}
      · rw [ev,g0] at hit
        contradiction
      · exact ev ▸ hit
    have go (A : Finset V) (sub : A ⊆ S) : folded S h g A = T.eval A := by
      rw [collapse A sub]
      cases e : T.eval A <;> assumption
    have one (u : V) : T.eval {u}=false := by
      by_cases mem : u∈S
      · rw [← go {u} (by simpa using mem)]
        exact single u
      · rw [← Tree.eval_empty T]
        apply Tree.eval_congr
        intro w hw
        have ne : w≠u := fun eq => mem (eq ▸ deps hw)
        simp [ne]
    have ab : T.eval {a,b}=true := by
      rw [← go {a,b} (pair_sub aS bS), correct a b (bip a b p.1),decide_eq_true p.1]
    have bc : T.eval {b,c}=true := by
      rw [← go {b,c} (pair_sub bS cS), correct b c (bip b c p.2.1),decide_eq_true p.2.1]
    have cd : T.eval {c,d}=true := by
      rw [← go {c,d} (pair_sub cS dS), correct c d (bip c d p.2.2.1),decide_eq_true p.2.2.1]
    have ad : T.eval {a,d}=false := by
      rw [← go {a,d} (pair_sub aS dS), correct a d (opposite_ends G colour bip p),
        decide_eq_false p.2.2.2]
    exact Tree.linear_no_induced_path T linear one a b c d ab bc cd ad
  have noB : b∉S := fun inB => noA (reach p.1.symm inB)
  have noC : c∉S := fun inC => noB (reach p.2.1.symm inC)
  have noD : d∉S := fun inD => noC (reach p.2.2.1.symm inD)
  exact ⟨noA,noB,noC,noD⟩

theorem exclusive_cut_twins {G : SimpleGraph V} [DecidableRel G.Adj]
    (colour : V → Bool) (bip : ∀ a b, G.Adj a b → colour a ≠ colour b)
    (S : Finset V) (h : Finset V → Bool) (g : Finset V → Bool → Bool)
    (mono : ∀ A B, A ⊆ B → h A = true → h B = true)
    (outer : ∀ A, g A false = true → g A true = true)
    (single : ∀ a, folded S h g {a}=false)
    (correct : ∀ a b, colour a ≠ colour b → folded S h g {a,b}=decide (G.Adj a b))
    (incident : ∀ a∈S, ∃ b, G.Adj a b) (cross : ∃ a∈S, ∃ b∉S, G.Adj a b) :
    (∀ a∈S, ∀ b∈S, ¬ G.Adj a b) ∧
      (∀ u∈S, ∀ v∈S, colour u=colour v → ∀ w, G.Adj u w ↔ G.Adj v w) := by
  have positive (a b : V) (adj : G.Adj a b) : folded S h g {a,b}=true := by
    rw [correct a b (bip a b adj),decide_eq_true adj]
  obtain ⟨indep,core⟩ := exclusive_support_or G S h g mono outer single positive incident cross
  refine ⟨indep,?_⟩
  intro u uS v vS same w
  by_cases inS : w ∈ S
  · exact (iff_of_false (indep u uS w inS) (indep v vS w inS))
  by_cases eq : colour u = colour w
  · exact iff_of_false (fun adj => (bip u w adj) eq) (fun adj => (bip v w adj) (same.symm.trans eq))
  have val (a : V) (aS : a∈S) : folded S h g {a,w}=g {w} true := by
    obtain ⟨x,y⟩ := split_cross S a w aS inS
    unfold folded
    rw [x,y,core {a} (by simpa using aS)]
    simp
  have sameBool : decide (G.Adj u w) = decide (G.Adj v w) := by
    rw [← correct u w eq,← correct v w (fun e => eq (same.trans e)),val u uS,val v vS]
  constructor
  · intro h
    apply of_decide_eq_true
    rwa [← sameBool, decide_eq_true h]
  · intro h
    apply of_decide_eq_true
    rwa [sameBool, decide_eq_true h]

theorem exclusive_cut_twins_incident {G : SimpleGraph V} [DecidableRel G.Adj]
    (colour : V → Bool) (bip : ∀ a b, G.Adj a b → colour a ≠ colour b)
    (S : Finset V) (h : Finset V → Bool) (g : Finset V → Bool → Bool)
    (mono : ∀ A B, A ⊆ B → h A = true → h B = true)
    (outer : ∀ A, g A false = true → g A true = true)
    (single : ∀ a, folded S h g {a}=false)
    (correct : ∀ a b, colour a ≠ colour b → folded S h g {a,b}=decide (G.Adj a b))
    (cross : ∃ a∈S, ∃ b∉S, G.Adj a b) :
    (∀ a∈S, ∀ b∈S, ¬ G.Adj a b) ∧
      (∀ u∈S, ∀ v∈S, (∃ q, G.Adj u q) → (∃ q, G.Adj v q) →
        colour u=colour v → ∀ w, G.Adj u w ↔ G.Adj v w) := by
  have positive (a b : V) (adj : G.Adj a b) : folded S h g {a,b}=true := by
    rw [correct a b (bip a b adj),decide_eq_true adj]
  have indep := exclusive_independent G S h g mono outer single positive cross
  refine ⟨indep,?_⟩
  intro u uS v vS uActive vActive same w
  by_cases inS : w ∈ S
  · exact (iff_of_false (indep u uS w inS) (indep v vS w inS))
  by_cases eq : colour u = colour w
  · exact iff_of_false (fun adj => (bip u w adj) eq) (fun adj => (bip v w adj) (same.symm.trans eq))
  have val (a : V) (aS : a∈S) (active : ∃ q, G.Adj a q) :
      folded S h g {a,w}=g {w} true := by
    obtain ⟨q,hq⟩ := active
    have qout : q∉S := fun qs => indep a aS q qs hq
    have yes := (cross_values S h g mono single a q aS qout (positive a q hq)).2
    obtain ⟨x,y⟩ := split_cross S a w aS inS
    unfold folded
    rw [x,y,yes]
  have sameBool : decide (G.Adj u w) = decide (G.Adj v w) := by
    rw [← correct u w eq,← correct v w (fun e => eq (same.trans e)),val u uS uActive,val v vS vActive]
  constructor
  · intro h
    apply of_decide_eq_true
    rwa [← sameBool, decide_eq_true h]
  · intro h
    apply of_decide_eq_true
    rwa [sameBool, decide_eq_true h]
end PEqualNP.Outside.L_meta_9498_aux.Cycle

namespace PEqualNP.Outside.L_meta_9498_aux.Cycle.CycleNine

open PEqualNP.Outside.L_meta_9498_aux.Cycle

private theorem pathOfObstruction {W : Finset V} {a b c d : V}
    (aW : a∈W) (bW : b∈W) (cW : c∈W) (dW : d∈W)
    (ab : adjacent a b=true) (bc : adjacent b c=true) (cd : adjacent c d=true)
    (ad : adjacent a d=false) : Path4 (graphOn W) a b c d := by
  refine ⟨⟨aW,bW,ab⟩,⟨bW,cW,bc⟩,⟨cW,dW,cd⟩,?_⟩
  intro h
  have test := h.2.2
  rw [ad] at test
  contradiction

private theorem positive_folded {W S : Finset V} {h : Finset V → Bool} {g : Finset V → Bool → Bool}
    (desc : Describes W (folded S h g)) {a b : V} (edge : (graphOn W).Adj a b) :
    folded S h g {a,b}=true :=
  (desc.2 a b (bipOn W a b edge)).trans (decide_eq_true edge)

private theorem zero_cut_no_edge {W S : Finset V} {h : Finset V → Bool} {g : Finset V → Bool → Bool}
    (desc : Describes W (folded S h g)) (zero : folded S h g ∅ = false)
    (allzero : ∀ A, h A = false) {a b : V} (aS : a ∈ S) (edge : (graphOn W).Adj a b) :
    False := by
  have agree (A B : Finset V) (same : A\S=B\S) : folded S h g A = folded S h g B := by
    simp only [folded, allzero, same]
  have yes := positive_folded desc edge
  by_cases bS : b∈S
  · have sub : ({a,b} : Finset V) ⊆ S := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl|rfl
      · exact aS
      · exact bS
    rw [agree {a,b} ∅ ((split_inside S {a,b} sub).1.trans (by simp)),zero] at yes
    contradiction
  · have ab := (split_cross S a b aS bS).1
    have b0 := (split_outside S b bS).1
    rw [agree {a,b} {b} (ab.trans b0.symm),desc.1 b] at yes
    contradiction

theorem support_move {W S : Finset V} (h : Finset V → Bool) (g : Finset V → Bool → Bool)
    (desc : Describes W (folded S h g)) (zero : folded S h g ∅ = false)
    (mono : ∀ A B, A ⊆ B → h A = true → h B = true)
    (outer : ∀ A, g A false = true → g A true = true)
    (core : (∀ A, h A = false) ∨
      ∃ T : PEqualNP.Outside.L_meta_9498_aux.Cycle.Tree V, T.linear ∧ T.leaves ⊆ S ∧ ∀ A, h A = T.eval A) :
    TwinStep W S ∨ FreeStep W S := by
  rcases core with allzero | ⟨T,lin,deps,ev⟩
  · right
    constructor
    · intro a ha b hb
      apply Bool.eq_false_iff.mpr
      intro yes
      exact zero_cut_no_edge desc zero allzero (Finset.mem_inter.mp ha).2
        ⟨(Finset.mem_inter.mp ha).1,(Finset.mem_sdiff.mp hb).1,yes⟩
    · rintro ⟨a,ha,b,hb,_,_,_,_,ab,_,_,_⟩
      exact zero_cut_no_edge desc zero allzero (Finset.mem_inter.mp ha).2
        ⟨(Finset.mem_inter.mp ha).1,(Finset.mem_inter.mp hb).1,ab⟩
  · by_cases cross : ∃ a∈S, ∃ b∉S, (graphOn W).Adj a b
    · left
      have tails := exclusive_cut_twins_incident side (bipOn W) S h g mono outer desc.1 desc.2 cross
      intro x xW y yW xS yS xi yi eq z zW
      obtain ⟨a,aW,xa⟩ := xi
      obtain ⟨b,bW,yb⟩ := yi
      have ep := tails.2 x xS y yS ⟨a,xW,aW,xa⟩ ⟨b,yW,bW,yb⟩ eq z
      apply Bool.eq_iff_iff.mpr
      simpa [graphOn,xW,yW,zW] using ep
    · right
      have noCross (a : V) (aS : a∈S) (b : V) (bS : b∉S) : ¬(graphOn W).Adj a b :=
        fun e => cross ⟨a,aS,b,bS,e⟩
      constructor
      · intro a ha b hb
        obtain ⟨aW,aS⟩ := Finset.mem_inter.mp ha
        obtain ⟨bW,bS⟩ := Finset.mem_sdiff.mp hb
        exact Bool.eq_false_iff.mpr (fun e => noCross a aS b bS ⟨aW,bW,e⟩)
      · rintro ⟨a,ha,b,hb,c,hc,d,hd,ab,bc,cd,ad⟩
        have plo := pathOfObstruction (Finset.mem_inter.mp ha).1 (Finset.mem_inter.mp hb).1
          (Finset.mem_inter.mp hc).1 (Finset.mem_inter.mp hd).1 ab bc cd ad
        have out := exclusive_no_cross side (bipOn W) S h g zero desc.1 desc.2
          T lin deps (fun A _ => ev A) noCross plo
        exact out.1 (Finset.mem_inter.mp ha).2

theorem terminal_no_obstruction {W : Finset V} {f : Finset V → Bool}
    (desc : Describes W f) (core : (∀ A, f A=false) ∨
      ∃ T : PEqualNP.Outside.L_meta_9498_aux.Cycle.Tree V, T.linear ∧ ∀ A, f A=T.eval A) : ¬ Obstruction W := by
  rintro ⟨a,ha,b,hb,c,hc,d,hd,ab,bc,cd,ad⟩
  have order := pathOfObstruction ha hb hc hd ab bc cd ad
  have ends := opposite_ends (graphOn W) side (bipOn W) order
  have p (x y : V) (edge : (graphOn W).Adj x y) : f {x,y}=true :=
    (desc.2 x y (bipOn W x y edge)).trans (decide_eq_true edge)
  rcases core with no | ⟨T,lin,ev⟩
  · have bad := p a b order.1
    rw [no] at bad
    contradiction
  · have cold (x : V) : T.eval {x}=false := (ev _).symm.trans (desc.1 x)
    exact PEqualNP.Outside.L_meta_9498_aux.Cycle.Tree.linear_no_induced_path T lin cold a b c d
      ((ev _).symm.trans (p a b order.1))
      ((ev _).symm.trans (p b c order.2.1))
      ((ev _).symm.trans (p c d order.2.2.1))
      ((ev _).symm.trans ((desc.2 a d ends).trans (decide_eq_false order.2.2.2)))

end PEqualNP.Outside.L_meta_9498_aux.Cycle.CycleNine

namespace PEqualNP.Outside.L_meta_9498_aux
open Finset
variable {V : Type} [DecidableEq V] [Fintype V] {N : ℕ}
namespace Node
def keepCode (S : Finset V) (keep : Fin N → Bool) : Node V N → Node V N
  | .zero => .zero
  | .input v => if v∈S then .zero else .input v
  | .copy a => if keep a then .copy a else .zero
  | .all a b => if keep a && keep b then .all a b else .zero
  | .any a b => if keep a then (if keep b then .any a b else .copy a) else
       (if keep b then .copy b else .zero)
theorem wires_sub (S : Finset V) (keep : Fin N → Bool) (c : Node V N) :
    ((keepCode S keep c).wires).Sublist c.wires := by
  cases c <;> simp only [keepCode] <;> (try split_ifs) <;> simp [wires]
theorem retained_wire (S : Finset V) (keep : Fin N → Bool) (c : Node V N) (w : Fin N) :
    w ∈ (keepCode S keep c).wires → keep w = true := by
  cases c <;> simp only [keepCode] <;> (try split_ifs) <;> simp_all [wires,Bool.and_eq_true] <;>
    rintro (rfl|rfl) <;> tauto
theorem retained_input (S : Finset V) (keep : Fin N → Bool) (c : Node V N) (v : V) :
    keepCode S keep c = .input v → c = .input v := by
  cases c <;> simp only [keepCode] <;> (try split_ifs) <;> simp
def valOf (raw : V → Bool) (w : Fin N → Bool) : Node V N → Bool
  | .zero => false
  | .input v => raw v
  | .copy a => w a
  | .all a b => w a && w b
  | .any a b => w a || w b
theorem val_congr (c : Node V N) (raw : V → Bool) (w z : Fin N → Bool)
    (h : ∀ a∈c.wires, w a=z a) : valOf raw w c=valOf raw z c := by
  cases c <;> simp_all [wires,valOf]
theorem keep_val (S A : Finset V) (keep : Fin N→Bool) (w : Fin N→Bool)
    (dead : ∀a, keep a=false → w a=false) (c : Node V N) :
    valOf (fun v=>decide (v∈A)) w (keepCode S keep c) =
    valOf (fun v=>decide (v∈A \ S)) w c := by
  cases c with
  | zero => rfl
  | input v => by_cases pin : v∈S <;> simp [keepCode,valOf,pin]
  | copy a => cases h : keep a <;> simp_all [keepCode,valOf]
  | all a b => cases ha : keep a <;> cases hb : keep b <;> simp_all [keepCode,valOf]
  | any a b => cases ha : keep a <;> cases hb : keep b <;> simp_all [keepCode,valOf]
end Node
namespace Dag
theorem value_eq (D : Dag V N) (A : Finset V) (w : Fin N) :
    D.value A w = Node.valOf (fun x => decide (x∈A)) (D.value A) (D.code w) := by
  unfold value
  rw [eval]
  cases h : D.code w <;> simp [blank,h,Node.valOf]
theorem value_empty (D : Dag V N) (w : Fin N) : D.value ∅ w=false := by
  induction w using WellFoundedLT.induction with
  | ind w ih =>
    rw [value_eq]
    cases h : D.code w with
    | zero => rfl
    | input x => simp [Node.valOf]
    | copy a => exact ih a (D.back w a (D.edgeCopy h))
    | all a b => simp [Node.valOf, ih a (D.back w a (D.edgeAll h).1)]
    | any a b => simp [Node.valOf, ih a (D.back w a (D.edgeAny h).1),ih b (D.back w b (D.edgeAny h).2)]
def keepAlive (D : Dag V N) (S : Finset V) (w : Fin N) := D.value (Finset.univ \ S) w
def restrict (D : Dag V N) (S : Finset V) : Dag V N where
  code := fun w => Node.keepCode S (D.keepAlive S) (D.code w)
  back := fun w a hw => D.back w a ((Node.wires_sub S _ _).subset hw)
  inputs_unique := fun i j x hi hj => D.inputs_unique i j x
    (Node.retained_input S _ _ x hi) (Node.retained_input S _ _ x hj)
theorem restricted_value (D : Dag V N) (A S : Finset V) (out : Fin N) :
    (D.restrict S).value A out=D.value (A \ S) out := by
  have dead (w : Fin N) (x : D.keepAlive S w=false) : D.value (A \ S) w=false := by
    by_contra! yes
    have sub : A \ S ⊆ Finset.univ \ S := fun v h => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,(Finset.mem_sdiff.mp h).2⟩
    have h := D.value_mono w _ _ sub (by simpa using yes)
    change D.value (Finset.univ \ S) w=false at x
    simp [x] at h
  induction out using WellFoundedLT.induction with
  | ind w ih =>
    rw [value_eq, value_eq D]
    change Node.valOf _ _ (Node.keepCode S _ (D.code w)) = _
    rw [Node.val_congr _ _ _ (D.value (A \ S)) (fun a ha =>
      ih a (D.back w a ((Node.wires_sub S _ _).subset ha)))]
    exact Node.keep_val S A _ _ dead _
theorem support_pin_decrease (D : Dag V N) (p : Fin N) (multi : 2≤fanout D.parents p) :
    excess (D.restrict (D.support p)).parents < excess D.parents := by
  let S := D.support p
  have off : D.keepAlive S p=false := by
    unfold keepAlive
    rw [D.value_support p]
    have z : (Finset.univ \ S) ∩ D.support p=∅ := by ext x; simp [S]
    rw [z,D.value_empty]
  apply excess_strict (fun w => Node.wires_sub S _ (D.code w)) p multi
  unfold fanout
  apply Finset.sum_eq_zero
  intro w _
  apply List.count_eq_zero.mpr
  intro hp
  have on := Node.retained_wire S (D.keepAlive S) (D.code w) p hp
  simp [off] at on
end Dag
end PEqualNP.Outside.L_meta_9498_aux

namespace PEqualNP.Outside.L_meta_9498_aux.Dag

open PEqualNP.Outside.L_meta_9498_aux.Cycle

variable {V : Type} {N : ℕ} [DecidableEq V]

private theorem cone_append {P : Parents N} {i a w : Fin N}
    (path : InCone P i a) (edge : a ∈ P w) : InCone P i w := by
  induction path with
  | self => exact .step edge (.self w)
  | step m _ ih => exact .step m (ih edge)

theorem support_sub (D : Dag V N) {a w : Fin N} (edge : a ∈ D.parents w) :
    D.support a ⊆ D.support w := by
  intro x hx
  obtain ⟨j,path,r⟩ := (D.support_iff a x).mp hx
  exact (D.support_iff w x).mpr ⟨j,cone_append path edge,r⟩

theorem distinct_children (D : Dag V N) {w a b : Fin N}
    (children : D.parents w = [a,b]) (before : ∀ i < w, fanout D.parents i ≤ 1) : a≠b := by
  intro e
  subst b
  have m : a ∈ D.parents w := by simp [children]
  have counts : 2 ≤ fanout D.parents a := by
    have low := Finset.single_le_sum (f := fun j => (D.parents j).count a)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ w)
    simpa [children,fanout] using low
  have high := before a (D.back w a m)
  omega

theorem disjoint_supports (D : Dag V N) {w a b : Fin N}
    (ma : a ∈ D.parents w) (mb : b ∈ D.parents w) (ne : a ≠ b)
    (early : ∀ i < w, fanout D.parents i ≤ 1) :
    Disjoint (D.support a) (D.support b) := by
  apply Finset.disjoint_left.mpr
  intro x ha hb
  obtain ⟨i,ia,iv⟩ := (D.support_iff a x).mp ha
  obtain ⟨j,jb,jv⟩ := (D.support_iff b x).mp hb
  have e := D.inputs_unique i j x iv jv
  exact ne (one_reader_unique_last D.parents w D.back early ma mb ia (e.symm ▸ jb))

def ForTree (D : Dag V N) (w : Fin N) (T : PEqualNP.Outside.L_meta_9498_aux.Cycle.Tree V) : Prop :=
  T.linear ∧ T.leaves ⊆ D.support w ∧ ∀ A, D.value A w = T.eval A

def AsTree (D : Dag V N) (w : Fin N) : Prop :=
  (∀ A, D.value A w = false) ∨ ∃ T, ForTree D w T

private theorem binaryTree (D : Dag V N) {w a b : Fin N} (op : Bool)
    (h : D.code w = if op then .any a b else .all a b)
    (early : ∀ i < w, fanout D.parents i ≤ 1)
    (left : AsTree D a) (right : AsTree D b) : AsTree D w := by
  have parentsEq : D.parents w = [a,b] := by
    cases op <;> simp [parents,h,Node.wires]
  have ma : a ∈ D.parents w := by simp [parentsEq]
  have mb : b ∈ D.parents w := by simp [parentsEq]
  have val (A : Finset V) : D.value A w =
      if op then D.value A a || D.value A b else D.value A a && D.value A b := by
    unfold value
    cases op <;> simp only [Bool.false_eq_true, ite_false, ite_true] at h ⊢
    all_goals rw [eval, show blank w = none from rfl, h]
  rcases left with za | ⟨L,ll,ld,lv⟩ <;> rcases right with zb | ⟨R,rl,rd,rv⟩
  · exact Or.inl fun A => by rw [val,za,zb]; cases op <;> rfl
  · cases op
    · exact Or.inl fun A => by simp [val,za]
    · exact Or.inr ⟨R,rl,rd.trans (D.support_sub mb),fun A => by simp [val,za,rv]⟩
  · cases op
    · exact Or.inl fun A => by simp [val,zb]
    · exact Or.inr ⟨L,ll,ld.trans (D.support_sub ma),fun A => by simp [val,zb,lv]⟩
  · have dis : Disjoint L.leaves R.leaves :=
      (D.disjoint_supports ma mb (D.distinct_children parentsEq early) early).mono ld rd
    have incl : L.leaves ∪ R.leaves ⊆ D.support w :=
      Finset.union_subset (ld.trans (D.support_sub ma)) (rd.trans (D.support_sub mb))
    cases op
    · exact Or.inr ⟨PEqualNP.Outside.L_meta_9498_aux.Cycle.Tree.all L R,⟨ll,rl,dis⟩,incl,fun A => by simp [val,lv,rv,PEqualNP.Outside.L_meta_9498_aux.Cycle.Tree.eval]⟩
    · exact Or.inr ⟨PEqualNP.Outside.L_meta_9498_aux.Cycle.Tree.any L R,⟨ll,rl,dis⟩,incl,fun A => by simp [val,lv,rv,PEqualNP.Outside.L_meta_9498_aux.Cycle.Tree.eval]⟩

/-- An evaluation cone before the first repeat is either false everywhere or a linear tree. -/
theorem cone_tree (D : Dag V N) (w : Fin N) (early : ∀ i < w, fanout D.parents i ≤ 1) :
    AsTree D w := by
  induction w using WellFoundedLT.induction with
  | ind w ih =>
    have child (u : Fin N) (m : u ∈ D.parents w) : AsTree D u :=
      ih u (D.back w u m) (fun i hi => early i (hi.trans (D.back w u m)))
    cases gate : D.code w with
    | zero => exact Or.inl fun A => by rw [value,eval,show blank w = none from rfl,gate]
    | input x =>
      refine Or.inr ⟨PEqualNP.Outside.L_meta_9498_aux.Cycle.Tree.input x,trivial,?_,fun A => ?_⟩
      · intro y hy
        have e : y=x := by simpa [PEqualNP.Outside.L_meta_9498_aux.Cycle.Tree.leaves] using hy
        subst y
        exact (D.support_iff w x).mpr ⟨w,.self w,gate⟩
      · rw [value,eval,show blank w = none from rfl,gate]
        rfl
    | copy a =>
      have m := D.edgeCopy gate
      have hval (A : Finset V) : D.value A w = D.value A a := by
        unfold value
        rw [eval,show blank w = none from rfl,gate]
      rcases child a m with zero | ⟨T,tl,ts,tv⟩
      · exact Or.inl fun A => (hval A).trans (zero A)
      · exact Or.inr ⟨T,tl,ts.trans (D.support_sub m),fun A => (hval A).trans (tv A)⟩
    | all a b =>
      have m := D.edgeAll gate
      exact binaryTree D false gate early (child a m.1) (child b m.2)
    | any a b =>
      have m := D.edgeAny gate
      exact binaryTree D true gate early (child a m.1) (child b m.2)

def outer (D : Dag V N) (p out : Fin N) (A : Finset V) (b : Bool) : Bool :=
  D.eval (fun x => decide (x∈A)) (stamp p b) out

theorem outer_mono (D : Dag V N) (p out : Fin N) (A : Finset V) :
    D.outer p out A false=true → D.outer p out A true=true := by
  apply D.eval_mono
  · intro _ h
    exact h
  · intro i
    by_cases h : i=p <;> simp [stamp,PatchLE,h]

theorem factorize (D : Dag V N) (p out : Fin N) (le : p ≤ out)
    (early : ∀ i < p, fanout D.parents i ≤ 1) (A : Finset V) :
    D.value A out = folded (D.support p) (fun X => D.value X p) (D.outer p out) A := by
  unfold folded outer
  let S := D.support p
  let bit := D.value (A ∩ S) p
  let visible (w : Fin N) := ¬InCone D.parents w p ∨ w=p
  have childVisible {w a : Fin N} (outside : ¬InCone D.parents w p) (m : a ∈ D.parents w) :
      visible a := by
    by_cases h : InCone D.parents a p
    · exact Or.inr (only_pivot_exits D.parents p a w D.back early h m outside)
    · exact Or.inl h
  have eq (w : Fin N) (vis : visible w) :
      D.value A w = D.eval (fun x => decide (x∈A\S)) (stamp p bit) w := by
    induction w using WellFoundedLT.induction with
    | ind w ih =>
      rcases vis with outside | eqWp
      · have ne : w≠p := fun h => outside (h.symm ▸ InCone.self p)
        have noStamp : stamp p bit w = none := by simp [stamp,ne]
        have go (a : Fin N) (m : a ∈ D.parents w) :=
          ih a (D.back w a m) (childVisible outside m)
        unfold value
        rw [eval,eval,noStamp]
        simp only [blank]
        cases rule : D.code w with
        | zero => rfl
        | input x =>
          have xout : x ∉ S := by
            intro xin
            obtain ⟨j,path,same⟩ := (D.support_iff p x).mp xin
            exact outside (D.inputs_unique j w x same rule ▸ path)
          simp [xout]
        | copy a => exact go a (D.edgeCopy rule)
        | all a b =>
          obtain ⟨ma,mb⟩ := D.edgeAll rule
          change (D.value A a && D.value A b) =
            (D.eval (fun x => decide (x∈A\S)) (stamp p bit) a &&
             D.eval (fun x => decide (x∈A\S)) (stamp p bit) b)
          rw [←go a ma,←go b mb]
        | any a b =>
          obtain ⟨ma,mb⟩ := D.edgeAny rule
          change (D.value A a || D.value A b) =
            (D.eval (fun x => decide (x∈A\S)) (stamp p bit) a ||
             D.eval (fun x => decide (x∈A\S)) (stamp p bit) b)
          rw [←go a ma,←go b mb]
      · subst w
        rw [eval, show stamp p bit p = some bit by simp [stamp]]
        exact D.value_support p A
  apply eq
  by_cases h : out=p
  · exact Or.inr h
  · exact Or.inl fun path => h (le_antisymm (cone_order D.back path) le)

theorem no_repeat_output (D : Dag V N) (out : Fin N) (zero : excess D.parents=0) :
    AsTree D out :=
  D.cone_tree out (fun i _ => (no_repeats_iff_zero _).mp zero i)

end PEqualNP.Outside.L_meta_9498_aux.Dag

namespace PEqualNP.Outside.L_meta_9498_aux.Cycle.CycleNine
open PEqualNP.Outside.L_meta_9498_aux
theorem dag_moves {N} (D : Dag V N) (out : Fin N) (last : ∀ p,p≤out)
    (W : Finset V) (desc : Describes W (fun A => D.value A out)) :
    ∃ rs, GlobalSteps W rs ∧ classCount rs ≤ 2*excess D.parents ∧ ¬Obstruction (globalRemaining W rs) := by
  generalize ey : excess D.parents = k
  induction k using Nat.strong_induction_on generalizing D W with
  | ind k ih =>
    by_cases zero : k=0
    · have t := D.no_repeat_output out (ey.trans zero)
      refine ⟨[],True.intro,Nat.zero_le _,terminal_no_obstruction desc ?_⟩
      rcases t with const|⟨T,lin,_,he⟩
      · exact Or.inl const
      · exact Or.inr ⟨T,lin,he⟩
    · obtain ⟨p,multi,early⟩ := earliest_repeat_exists D.parents (by omega)
      let S := D.support p
      let f := fun A => D.value A p
      let g := D.outer p out
      have same : (fun A => D.value A out) = folded S f g := funext (D.factorize p out (last p) early)
      have hd : Describes W (folded S f g) := same ▸ desc
      have he : folded S f g ∅=false := (congrFun same ∅).symm.trans (D.value_empty out)
      have moves : TwinStep W S ∨ FreeStep W S :=
        support_move f g hd he (D.value_mono p) (D.outer_mono p out) (D.cone_tree p early)
      have next : Describes (W \ S) (fun A => (D.restrict S).value A out) := by
        have id : (fun A => (D.restrict S).value A out) = (fun A => D.value (A \ S) out) :=
          funext (fun A => D.restricted_value A S out)
        rw [id]
        exact restrict_describes desc (D.value_empty out)
      have dec : excess (D.restrict S).parents < k := by simpa [S,ey] using D.support_pin_decrease p multi
      obtain ⟨rs,good,small,done⟩ := ih (excess (D.restrict S).parents) dec (D.restrict S) (W \ S) next rfl
      rcases moves with twins|free
      · refine ⟨(true,colourSlice S false)::(true,colourSlice S true)::rs,prepend_twin twins good,?_,?_⟩
        · rw [count_prepend_twin]; omega
        · rwa [remaining_prepend_twin]
      · refine ⟨(false,S)::rs,prepend_free free good,?_,done⟩
        rw [count_prepend_free]; omega
end PEqualNP.Outside.L_meta_9498_aux.Cycle.CycleNine

namespace PEqualNP.Outside.L_meta_9498_aux.Cycle.CycleNine

theorem no_small_cycle9 :
    ¬ PEqualNP.Represents.RepSizeAtMost (Initial.cycle 9) 60 :=
  no_small_cycle9_of_peel (fun D out last W desc => dag_moves D out last W desc)

end PEqualNP.Outside.L_meta_9498_aux.Cycle.CycleNine

theorem PEqualNP.Outside.L_meta_9498 : ¬ PEqualNP.Represents.RepSizeAtMost (fun a b : Fin 27 => decide (∃ i : Fin 9, ((a.val = i.val ∨ a.val = 9 + i.val) ∧ (b.val = (i.val + 1) % 9 ∨ b.val = 18 + i.val)) ∨ ((b.val = i.val ∨ b.val = 9 + i.val) ∧ (a.val = (i.val + 1) % 9 ∨ a.val = 18 + i.val)))) 60 :=
  PEqualNP.Outside.L_meta_9498_aux.Cycle.CycleNine.no_small_cycle9
