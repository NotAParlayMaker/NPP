import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_15091

-- The signed circuit search uses the live-wire compression from L-meta-1423.
-- A NOT gate costs one gate in the given circuit and zero in the signed search.
-- The live-wire compression argument follows the project proof of L-meta-703.
-- The live-wire reduction and circuit semantics follow the merged L-meta-1429.
-- Each finite search layer below is checked against the next layer of smaller states.
section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

-- The upper and lower halves represent opposite target labels on 36 pairs of assignments.
abbrev W := BitVec 72
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 36 := ((x >>> 36) ^^^ x).setWidth 36
def cuts (ws : List W) : BitVec 36 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 36) ++ (0 : BitVec 36)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 36) (w : W) : Prop :=
  w.getLsbD (36+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 36) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 36+i.val < 72 := by omega
  have hi' : i.val < 72 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 36) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 36)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def insertW (v : W) : List W → List W
  | [] => [v]
  | x :: xs => if v ≤ x then v :: x :: xs else x :: insertW v xs

def ordered (ws : List W) := ws.foldr insertW []

theorem insertW_perm (v : W) (ws : List W) : (insertW v ws).Perm (v :: ws) := by
  induction ws with
  | nil => exact .refl _
  | cons x xs ih =>
    simp only [insertW]
    split
    · exact .refl _
    · exact (ih.cons x).trans (.swap _ _ _)

theorem ordered_perm (ws : List W) : (ordered ws).Perm ws := by
  induction ws with
  | nil => exact .refl _
  | cons x xs ih => exact (insertW_perm x (ordered xs)).trans (ih.cons x)

def children (k : ℕ) (ws : List W) : List (List W) := (pairs ws).flatMap fun (a,b,r) =>
  (ops a b).flatMap fun z =>
    (keepChoices a b r).filterMap fun kept =>
      if kept.length ≤ k ∧ cuts (z :: kept) = -1 then some (ordered (z :: kept)) else none

def earlier : List W → List W → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: l, b :: r => if a = b then earlier l r else decide (a.toNat < b.toNat)

def containsKey (q : List W) : BinaryTree (List W) → Bool
  | .nil => false
  | .node a l r => if q = a then true else if earlier q a then containsKey q l else containsKey q r

def everyKey (f : List W → Bool) : BinaryTree (List W) → Bool
  | .nil => true
  | .node a l r => f a && everyKey f l && everyKey f r

theorem every_at {f : List W → Bool} {q : List W} (tr : BinaryTree (List W))
    (ha : everyKey f tr = true) (hm : containsKey q tr = true) : f q = true := by
  induction tr with
  | nil => contradiction
  | node a l r il ir =>
    simp only [everyKey,Bool.and_eq_true] at ha
    simp only [containsKey] at hm
    split at hm
    next e => simpa [e] using ha.1.1
    next e =>
      split at hm
      · exact il ha.1.2 hm
      · exact ir ha.2 hm

def Closed (k : Nat) (tr : BinaryTree (List W)) : Prop :=
  ∀ (g : W), g = goal ∨ g = ~~~goal → ∀ ws : List W,
    ws.Nodup → ws.length ≤ 9 → containsKey ws tr = true → ¬ live basicOps g k ws.toFinset

def doneTest (s : List W) : Bool := s == [goal] || s == [~~~goal]

theorem closed_nil (tr : BinaryTree (List W)) (hc : everyKey (fun q => !doneTest q) tr = true) :
    Closed 0 tr := by
  intro g hg ws hn hl hm h
  have hy := every_at tr hc hm
  have eq := singleton_list hn h
  rcases hg with rfl | rfl <;> simp [eq,doneTest] at hy

def rowOK (k : Nat) (tr : BinaryTree (List W)) (ws : List W) :=
  !doneTest ws && (children k ws).all (fun child => containsKey child tr)

theorem perm_set {u v : List W} (p : u.Perm v) : u.toFinset = v.toFinset := by
  ext a
  simpa only [List.mem_toFinset] using (p.mem_iff : a ∈ u ↔ a ∈ v)

theorem closed_next (k : Nat) (hk : k < 9) (tr next : BinaryTree (List W))
    (hnext : Closed k next) (hc : everyKey (rowOK k next) tr = true) :
    Closed (k+1) tr := by
  intro g hg ws hn hl hm h
  have hy := every_at tr hc hm
  simp only [rowOK,Bool.and_eq_true,List.all_eq_true] at hy
  rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
  · have eq := singleton_list hn done
    rcases hg with rfl | rfl <;> simp [eq,doneTest] at hy
  · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
    have go {a b : W} (hp : ws.Perm (a :: b :: r)) (hmem : (a,b,r) ∈ pairs ws)
        (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) : False := by
      obtain ⟨kept, hkeep, hnk, hfin⟩ := recover_kept hp hn hset
      have hznew : z ∉ kept := by
        intro hu
        apply hout
        rw [hset]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
      have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
      have hraw : live basicOps g k (z :: kept).toFinset := by simpa [hfin] using tail
      have hc := live_card hraw
      rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
      have hp' := ordered_perm (z :: kept)
      have mem : ordered (z :: kept) ∈ children k ws := by
        apply List.mem_flatMap.mpr
        refine ⟨(a,b,r),hmem,List.mem_flatMap.mpr ⟨z,List.mem_toFinset.mp hop,?_⟩⟩
        exact List.mem_filterMap.mpr ⟨kept,hkeep,by simp [show kept.length ≤ k by omega,cuts_full hg hraw]⟩
      have sz : (ordered (z :: kept)).length ≤ 9 := by rw [hp'.length_eq]; simp only [List.length_cons]; omega
      apply hnext g hg _ (hp'.nodup_iff.mpr hnd) sz (hy.2 _ mem)
      rwa [perm_set hp']
    rcases hm with direct | swap
    · exact go hp direct hs hz
    · exact go (hp.trans (.swap _ _ _)) swap (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)

def startOK (n : Nat) (tr : BinaryTree (List W)) (ws : List W) : Bool :=
  !(decide (ws.length ≤ n+1) && (cuts ws == -1)) || containsKey (ordered ws) tr

theorem no_build (n : Nat) (tr : BinaryTree (List W)) (ins : List W) (nd : ins.Nodup)
    (small : ins.length ≤ 9) (hc : Closed n tr) (hi : ins.sublists.all (startOK n tr) = true)
    (g : W) (hg : g = goal ∨ g = ~~~goal) : ¬ build basicOps g n ins.toFinset := by
  intro hb
  classical
  obtain ⟨s,hs,hl⟩ := compress hb
  let ws := ins.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd := nd.filter (fun u => decide (u ∈ s))
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have size := live_card hl'
  rw [List.toFinset_card_of_nodup (show ws.Nodup from hnd)] at size
  have sub : ws.Sublist ins := List.filter_sublist ..
  have key := List.all_eq_true.mp hi ws (List.mem_sublists.mpr sub)
  have perm := ordered_perm ws
  apply hc g hg (ordered ws) (perm.nodup_iff.mpr hnd) (by rw [perm.length_eq]; exact sub.length_le.trans small) ?_
  · rwa [perm_set perm]
  · simpa [startOK,size,cuts_full hg hl'] using key

open PEqualNP.CircuitLowerBounds

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 72 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 72)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 72) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 72) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

theorem evalAnd (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
theorem evalOr (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
theorem evalNot (xs : List Bool) : GateOp.not.eval xs = !(xs.headD false) := rfl

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 72) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#72)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, evalAnd, evalOr, evalNot, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      BitVec.getElem_zero,bit0,Bool.not_false] <;> rfl

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : goal ≠ 0) zero)
    · exact False.elim ((by decide : goal ≠ ~~~0) ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by rw [eq, BitVec.not_not]), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩
theorem bound_from_search (T n : ℕ) (ins : List W) (nd : ins.Nodup)
    (row : ∀ j : Fin 72, Nat.testBit T (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
    (width : ins.length = 6) (rejection : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z n ins.toFinset)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 6, if x i then 2^(i : ℕ) else 0)) : n < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ ins, holds ins.toFinset u := fun u hu =>
    .inr (.inr ⟨u,List.mem_toFinset.mpr hu,.inl rfl⟩)
  have evaluate (k : Fin 72) :
      (gs.foldl step (ins.map (bit k))).getD o false = bit k goal := by
    let x (i : Fin 6) : Bool := bit k (ins.getD i.val 0)
    have same : List.ofFn x = ins.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < ins.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (ins.map (bit k)) = bit k goal
    rw [← same, he]
    exact row k
  obtain ⟨t,ht,run⟩ := compile gs o hg ins ins.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a ins.toFinset) : build basicOps t b ins.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact rejection t ht (lift low run)

theorem replace (T m : ℕ) (ins : List W) (nd : ins.Nodup)
    (row : ∀ j : Fin 72, Nat.testBit T (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
    (width : ins.length = 6) (rejection : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z (m-2) ins.toFinset)
    (upper : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
      ∧ gs.length = m ∧ ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
        Nat.testBit T (∑ i : Fin 6, if x i then 2^(i : ℕ) else 0))
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 6, if x i then 2^(i : ℕ) else 0)) :
    ∃ (ds : List Gate) (p : ℕ), (∀ g ∈ ds, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
      ∧ ds.length ≤ gs.length ∧ ∀ x : Fin 6 → Bool, Circuit.eval ⟨ds,p⟩ (List.ofFn x) =
        Nat.testBit T (∑ i : Fin 6, if x i then 2^(i : ℕ) else 0) := by
  by_cases present : ∃ g ∈ gs, g.op = .not
  · obtain ⟨g,hm,hn⟩ := present
    have cut : binaryCost gs < gs.length := (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr ⟨g,hm,by simp [isBinary, hn]⟩
    have b := bound_from_search T (m-2) ins nd row width rejection gs o hg he
    obtain ⟨ds,p,ok,size,ev⟩ := upper
    exact ⟨ds,p,ok,by omega,ev⟩
  · refine ⟨gs,o,?_,le_rfl,he⟩
    intro g hm
    obtain ⟨hop,cap⟩ := hg g hm
    exact ⟨hop.elim Or.inl (fun h => h.elim Or.inr (fun eq => (present ⟨g,hm,eq⟩).elim)),cap⟩

def signal0 : W := (0x0 : BitVec 36) ++ (0xa42129080 : BitVec 36)
def signal1 : W := (0x0 : BitVec 36) ++ (0xc42131080 : BitVec 36)
def signal2 : W := (0x0 : BitVec 36) ++ (0xe02038080 : BitVec 36)
def signal3 : W := (0x0 : BitVec 36) ++ (0xe40039000 : BitVec 36)
def signal4 : W := (0x0 : BitVec 36) ++ (0xe42100000 : BitVec 36)
def signal5 : W := (0x0 : BitVec 36) ++ (0xe42139080 : BitVec 36)
def signal6 : W := (0xa9 : BitVec 36) ++ (0x7f : BitVec 36)
def signal7 : W := (0xa9 : BitVec 36) ++ (0x9f : BitVec 36)
def signal8 : W := (0xa9 : BitVec 36) ++ (0xe7 : BitVec 36)
def signal9 : W := (0x1502 : BitVec 36) ++ (0xf07 : BitVec 36)
def signal10 : W := (0x1502 : BitVec 36) ++ (0x1307 : BitVec 36)
def signal11 : W := (0x1502 : BitVec 36) ++ (0x1c07 : BitVec 36)
def signal12 : W := (0x215ab : BitVec 36) ++ (0x21087 : BitVec 36)
def signal13 : W := (0x2b7bb : BitVec 36) ++ (0x31f : BitVec 36)
def signal14 : W := (0x2b7bb : BitVec 36) ++ (0x2939f : BitVec 36)
def signal15 : W := (0x2b7bb : BitVec 36) ++ (0xa4212939f : BitVec 36)
def signal16 : W := (0x35deb : BitVec 36) ++ (0xc67 : BitVec 36)
def signal17 : W := (0x35deb : BitVec 36) ++ (0x31ce7 : BitVec 36)
def signal18 : W := (0x35deb : BitVec 36) ++ (0xc42131ce7 : BitVec 36)
def signal19 : W := (0x3eaf9 : BitVec 36) ++ (0x3e0f8 : BitVec 36)
def signal20 : W := (0x3ff52 : BitVec 36) ++ (0x3ff00 : BitVec 36)
def signal21 : W := (0x3fffb : BitVec 36) ++ (0x6f7f : BitVec 36)
def signal22 : W := (0x3fffb : BitVec 36) ++ (0x2ffff : BitVec 36)
def signal23 : W := (0x3fffb : BitVec 36) ++ (0x37fff : BitVec 36)
def signal24 : W := (0x3fffb : BitVec 36) ++ (0x39fff : BitVec 36)
def signal25 : W := (0x3fffb : BitVec 36) ++ (0x3efff : BitVec 36)
def signal26 : W := (0x3fffb : BitVec 36) ++ (0x3f3ff : BitVec 36)
def signal27 : W := (0x3fffb : BitVec 36) ++ (0x3fcff : BitVec 36)
def signal28 : W := (0x3fffb : BitVec 36) ++ (0x3ff7f : BitVec 36)
def signal29 : W := (0x3fffb : BitVec 36) ++ (0x3ff9f : BitVec 36)
def signal30 : W := (0x3fffb : BitVec 36) ++ (0x3ffe7 : BitVec 36)
def signal31 : W := (0x3fffb : BitVec 36) ++ (0xe42106f7f : BitVec 36)
def signal32 : W := (0x1c0004 : BitVec 36) ++ (0x1c0000 : BitVec 36)
def signal33 : W := (0x2a000a9 : BitVec 36) ++ (0x1e0007f : BitVec 36)
def signal34 : W := (0x2a000a9 : BitVec 36) ++ (0x3e000f8 : BitVec 36)
def signal35 : W := (0x2a000a9 : BitVec 36) ++ (0x3e000ff : BitVec 36)
def signal36 : W := (0x2bc0004 : BitVec 36) ++ (0x1ec0000 : BitVec 36)
def signal37 : W := (0x2bc0004 : BitVec 36) ++ (0x2740000 : BitVec 36)
def signal38 : W := (0x2bc0004 : BitVec 36) ++ (0x3980000 : BitVec 36)
def signal39 : W := (0x2bc0004 : BitVec 36) ++ (0x3fc0000 : BitVec 36)
def signal40 : W := (0x2bc0004 : BitVec 36) ++ (0xe43fc0000 : BitVec 36)
def signal41 : W := (0x2bc00ad : BitVec 36) ++ (0x1ec007f : BitVec 36)
def signal42 : W := (0x2bc00ad : BitVec 36) ++ (0x274009f : BitVec 36)
def signal43 : W := (0x2bc00ad : BitVec 36) ++ (0x39800e7 : BitVec 36)
def signal44 : W := (0x2bc00ad : BitVec 36) ++ (0x3ec00ff : BitVec 36)
def signal45 : W := (0x2bc00ad : BitVec 36) ++ (0x3f400ff : BitVec 36)
def signal46 : W := (0x2bc00ad : BitVec 36) ++ (0x3f800ff : BitVec 36)
def signal47 : W := (0x2bc00ad : BitVec 36) ++ (0x3fc007f : BitVec 36)
def signal48 : W := (0x2bc00ad : BitVec 36) ++ (0x3fc00f8 : BitVec 36)
def signal49 : W := (0x2bc00ad : BitVec 36) ++ (0x3fc00ff : BitVec 36)
def signal50 : W := (0x2bc00ad : BitVec 36) ++ (0xe41ef907f : BitVec 36)
def signal51 : W := (0x2bfff56 : BitVec 36) ++ (0x3ffff00 : BitVec 36)
def signal52 : W := (0x54001502 : BitVec 36) ++ (0x3c000f07 : BitVec 36)
def signal53 : W := (0x54001502 : BitVec 36) ++ (0x7c001f00 : BitVec 36)
def signal54 : W := (0x54001502 : BitVec 36) ++ (0x7c001f07 : BitVec 36)
def signal55 : W := (0x541c0004 : BitVec 36) ++ (0x3c0c0000 : BitVec 36)
def signal56 : W := (0x541c0004 : BitVec 36) ++ (0x4c140000 : BitVec 36)
def signal57 : W := (0x541c0004 : BitVec 36) ++ (0x70180000 : BitVec 36)
def signal58 : W := (0x541c0004 : BitVec 36) ++ (0x7c1c0000 : BitVec 36)
def signal59 : W := (0x541c0004 : BitVec 36) ++ (0xe7e1c0000 : BitVec 36)
def signal60 : W := (0x541c1506 : BitVec 36) ++ (0x3c0c0f07 : BitVec 36)
def signal61 : W := (0x541c1506 : BitVec 36) ++ (0x4c141307 : BitVec 36)
def signal62 : W := (0x541c1506 : BitVec 36) ++ (0x70181c07 : BitVec 36)
def signal63 : W := (0x541c1506 : BitVec 36) ++ (0x7c0c1f07 : BitVec 36)
def signal64 : W := (0x541c1506 : BitVec 36) ++ (0x7c141f07 : BitVec 36)
def signal65 : W := (0x541c1506 : BitVec 36) ++ (0x7c181f07 : BitVec 36)
def signal66 : W := (0x541c1506 : BitVec 36) ++ (0x7c1c0f07 : BitVec 36)
def signal67 : W := (0x541c1506 : BitVec 36) ++ (0x7c1c1f00 : BitVec 36)
def signal68 : W := (0x541c1506 : BitVec 36) ++ (0x7c1c1f07 : BitVec 36)
def signal69 : W := (0x541c1506 : BitVec 36) ++ (0xe3e0f8f87 : BitVec 36)
def signal70 : W := (0x541feafd : BitVec 36) ++ (0x7c1fe0f8 : BitVec 36)
def signal71 : W := (0x56a015ab : BitVec 36) ++ (0x7fe01ff8 : BitVec 36)
def signal72 : W := (0x56bc0004 : BitVec 36) ++ (0x7ffc0000 : BitVec 36)
def signal73 : W := (0x56bc15af : BitVec 36) ++ (0x7ffc1ff8 : BitVec 36)
def signal74 : W := (0x288400000 : BitVec 36) ++ (0x38c640000 : BitVec 36)
def signal75 : W := (0x28840a210 : BitVec 36) ++ (0x18c646318 : BitVec 36)
def signal76 : W := (0x28840a210 : BitVec 36) ++ (0x20c648318 : BitVec 36)
def signal77 : W := (0x28840a210 : BitVec 36) ++ (0x38060e018 : BitVec 36)
def signal78 : W := (0x28840a210 : BitVec 36) ++ (0x38c00e300 : BitVec 36)
def signal79 : W := (0x28840a210 : BitVec 36) ++ (0x38c646318 : BitVec 36)
def signal80 : W := (0x28840a210 : BitVec 36) ++ (0x38c64e318 : BitVec 36)
def signal81 : W := (0x28840a210 : BitVec 36) ++ (0xdce777398 : BitVec 36)
def signal82 : W := (0x28842b7bb : BitVec 36) ++ (0x20c66939f : BitVec 36)
def signal83 : W := (0x288435deb : BitVec 36) ++ (0x38c671ce7 : BitVec 36)
def signal84 : W := (0x28843fffb : BitVec 36) ++ (0x18c646f7f : BitVec 36)
def signal85 : W := (0x28afc0004 : BitVec 36) ++ (0x38ffc0000 : BitVec 36)
def signal86 : W := (0x28afca2bd : BitVec 36) ++ (0x38f98e3e7 : BitVec 36)
def signal87 : W := (0x2dc5c0004 : BitVec 36) ++ (0x3fc7c0000 : BitVec 36)
def signal88 : W := (0x2dc5cb716 : BitVec 36) ++ (0x3f078fc1f : BitVec 36)
def signal89 : W := (0x521000000 : BitVec 36) ++ (0x5b1880000 : BitVec 36)
def signal90 : W := (0x521014840 : BitVec 36) ++ (0x1b1886c60 : BitVec 36)
def signal91 : W := (0x521014840 : BitVec 36) ++ (0x431890c60 : BitVec 36)
def signal92 : W := (0x521014840 : BitVec 36) ++ (0x581816060 : BitVec 36)
def signal93 : W := (0x521014840 : BitVec 36) ++ (0x5b0016c00 : BitVec 36)
def signal94 : W := (0x521014840 : BitVec 36) ++ (0x5b1886c60 : BitVec 36)
def signal95 : W := (0x521014840 : BitVec 36) ++ (0x5b1896c60 : BitVec 36)
def signal96 : W := (0x521014840 : BitVec 36) ++ (0xbf39afce0 : BitVec 36)
def signal97 : W := (0x52102b7bb : BitVec 36) ++ (0x5b18a939f : BitVec 36)
def signal98 : W := (0x521035deb : BitVec 36) ++ (0x4318b1ce7 : BitVec 36)
def signal99 : W := (0x52103fffb : BitVec 36) ++ (0x1b1886f7f : BitVec 36)
def signal100 : W := (0x523bc0004 : BitVec 36) ++ (0x5b3fc0000 : BitVec 36)
def signal101 : W := (0x523bd48ed : BitVec 36) ++ (0x5b2756c9f : BitVec 36)
def signal102 : W := (0x5751c0004 : BitVec 36) ++ (0x5fd9c0000 : BitVec 36)
def signal103 : W := (0x5751d5d46 : BitVec 36) ++ (0x5cd957367 : BitVec 36)
def signal104 : W := (0x7a941ea50 : BitVec 36) ++ (0x63ded8f78 : BitVec 36)
def signal105 : W := (0x856bc0004 : BitVec 36) ++ (0x842100000 : BitVec 36)
def signal106 : W := (0x856be15af : BitVec 36) ++ (0x842121087 : BitVec 36)
def signal107 : W := (0xa8ae2a2b9 : BitVec 36) ++ (0xa02628098 : BitVec 36)
def signal108 : W := (0xa8ae2b7bb : BitVec 36) ++ (0xa0262939f : BitVec 36)
def signal109 : W := (0xadc42b712 : BitVec 36) ++ (0xa4c029300 : BitVec 36)
def signal110 : W := (0xadc42b7bb : BitVec 36) ++ (0xa4c02939f : BitVec 36)
def signal111 : W := (0xadefc0004 : BitVec 36) ++ (0xc640000 : BitVec 36)
def signal112 : W := (0xadefc0004 : BitVec 36) ++ (0xa4e740000 : BitVec 36)
def signal113 : W := (0xadefc0004 : BitVec 36) ++ (0xa4e769080 : BitVec 36)
def signal114 : W := (0xadefc0004 : BitVec 36) ++ (0xa4ffc0000 : BitVec 36)
def signal115 : W := (0xadefc0004 : BitVec 36) ++ (0xa7e7c0000 : BitVec 36)
def signal116 : W := (0xadefc0004 : BitVec 36) ++ (0xbce740000 : BitVec 36)
def signal117 : W := (0xadefc0004 : BitVec 36) ++ (0xe4e740000 : BitVec 36)
def signal118 : W := (0xadefca214 : BitVec 36) ++ (0xa4e748318 : BitVec 36)
def signal119 : W := (0xadefea2bd : BitVec 36) ++ (0xa4e768098 : BitVec 36)
def signal120 : W := (0xadefeb716 : BitVec 36) ++ (0xa4e769300 : BitVec 36)
def signal121 : W := (0xadefeb7bf : BitVec 36) ++ (0xc64031f : BitVec 36)
def signal122 : W := (0xadefeb7bf : BitVec 36) ++ (0xc66939f : BitVec 36)
def signal123 : W := (0xadefeb7bf : BitVec 36) ++ (0xe74039f : BitVec 36)
def signal124 : W := (0xadefeb7bf : BitVec 36) ++ (0x4c74131f : BitVec 36)
def signal125 : W := (0xadefeb7bf : BitVec 36) ++ (0x20c64831f : BitVec 36)
def signal126 : W := (0xadefeb7bf : BitVec 36) ++ (0x84e76139f : BitVec 36)
def signal127 : W := (0xadefeb7bf : BitVec 36) ++ (0xa0e66839f : BitVec 36)
def signal128 : W := (0xadefeb7bf : BitVec 36) ++ (0xa4272909f : BitVec 36)
def signal129 : W := (0xadefeb7bf : BitVec 36) ++ (0xa4c66931f : BitVec 36)
def signal130 : W := (0xadefeb7bf : BitVec 36) ++ (0xa4e129387 : BitVec 36)
def signal131 : W := (0xadefeb7bf : BitVec 36) ++ (0xa4e74031f : BitVec 36)
def signal132 : W := (0xadefeb7bf : BitVec 36) ++ (0xa4e769398 : BitVec 36)
def signal133 : W := (0xadefeb7bf : BitVec 36) ++ (0xa4e76939f : BitVec 36)
def signal134 : W := (0xadefeb7bf : BitVec 36) ++ (0xe4e76939f : BitVec 36)
def signal135 : W := (0xadefeb7bf : BitVec 36) ++ (0xe4e77939f : BitVec 36)
def signal136 : W := (0xd23a348e9 : BitVec 36) ++ (0xc038300e0 : BitVec 36)
def signal137 : W := (0xd23a35deb : BitVec 36) ++ (0xc03831ce7 : BitVec 36)
def signal138 : W := (0xd75035d42 : BitVec 36) ++ (0xc70031c00 : BitVec 36)
def signal139 : W := (0xd75035deb : BitVec 36) ++ (0xc70031ce7 : BitVec 36)
def signal140 : W := (0xd77bc0004 : BitVec 36) ++ (0x31880000 : BitVec 36)
def signal141 : W := (0xd77bc0004 : BitVec 36) ++ (0xc73980000 : BitVec 36)
def signal142 : W := (0xd77bc0004 : BitVec 36) ++ (0xc739b1080 : BitVec 36)
def signal143 : W := (0xd77bc0004 : BitVec 36) ++ (0xc73fc0000 : BitVec 36)
def signal144 : W := (0xd77bc0004 : BitVec 36) ++ (0xc7f9c0000 : BitVec 36)
def signal145 : W := (0xd77bc0004 : BitVec 36) ++ (0xdf3980000 : BitVec 36)
def signal146 : W := (0xd77bc0004 : BitVec 36) ++ (0xe73980000 : BitVec 36)
def signal147 : W := (0xd77bd4844 : BitVec 36) ++ (0xc73990c60 : BitVec 36)
def signal148 : W := (0xd77bf48ed : BitVec 36) ++ (0xc739b00e0 : BitVec 36)
def signal149 : W := (0xd77bf5d46 : BitVec 36) ++ (0xc739b1c00 : BitVec 36)
def signal150 : W := (0xd77bf5def : BitVec 36) ++ (0x31880c67 : BitVec 36)
def signal151 : W := (0xd77bf5def : BitVec 36) ++ (0x318b1ce7 : BitVec 36)
def signal152 : W := (0xd77bf5def : BitVec 36) ++ (0x33980ce7 : BitVec 36)
def signal153 : W := (0xd77bf5def : BitVec 36) ++ (0x71981c67 : BitVec 36)
def signal154 : W := (0xd77bf5def : BitVec 36) ++ (0x431890c67 : BitVec 36)
def signal155 : W := (0xd77bf5def : BitVec 36) ++ (0x8739a1ce7 : BitVec 36)
def signal156 : W := (0xd77bf5def : BitVec 36) ++ (0xc338b0ce7 : BitVec 36)
def signal157 : W := (0xd77bf5def : BitVec 36) ++ (0xc439310e7 : BitVec 36)
def signal158 : W := (0xd77bf5def : BitVec 36) ++ (0xc718b1c67 : BitVec 36)
def signal159 : W := (0xd77bf5def : BitVec 36) ++ (0xc72131c87 : BitVec 36)
def signal160 : W := (0xd77bf5def : BitVec 36) ++ (0xc73980c67 : BitVec 36)
def signal161 : W := (0xd77bf5def : BitVec 36) ++ (0xc739b1ce0 : BitVec 36)
def signal162 : W := (0xd77bf5def : BitVec 36) ++ (0xc739b1ce7 : BitVec 36)
def signal163 : W := (0xd77bf5def : BitVec 36) ++ (0xe739b1ce7 : BitVec 36)
def signal164 : W := (0xd77bf5def : BitVec 36) ++ (0xe739b9ce7 : BitVec 36)
def signal165 : W := (0xfa943ea50 : BitVec 36) ++ (0xf8003e000 : BitVec 36)
def signal166 : W := (0xfa943eaf9 : BitVec 36) ++ (0xf8003e0f8 : BitVec 36)
def signal167 : W := (0xfa943ff52 : BitVec 36) ++ (0xf8003ff00 : BitVec 36)
def signal168 : W := (0xfabe00000 : BitVec 36) ++ (0xf83e00000 : BitVec 36)
def signal169 : W := (0xfabe3eaf9 : BitVec 36) ++ (0x181e06078 : BitVec 36)
def signal170 : W := (0xfabe3eaf9 : BitVec 36) ++ (0x181e3e0f8 : BitVec 36)
def signal171 : W := (0xfabe3eaf9 : BitVec 36) ++ (0x183e060f8 : BitVec 36)
def signal172 : W := (0xfabe3eaf9 : BitVec 36) ++ (0x381e0e078 : BitVec 36)
def signal173 : W := (0xfabe3eaf9 : BitVec 36) ++ (0x581e16078 : BitVec 36)
def signal174 : W := (0xfabe3eaf9 : BitVec 36) ++ (0xb83e2e0f8 : BitVec 36)
def signal175 : W := (0xfabe3eaf9 : BitVec 36) ++ (0xd83e360f8 : BitVec 36)
def signal176 : W := (0xfabe3eaf9 : BitVec 36) ++ (0xe03e380f8 : BitVec 36)
def signal177 : W := (0xfabe3eaf9 : BitVec 36) ++ (0xf81e3e078 : BitVec 36)
def signal178 : W := (0xfabe3eaf9 : BitVec 36) ++ (0xf8263e098 : BitVec 36)
def signal179 : W := (0xfabe3eaf9 : BitVec 36) ++ (0xf8383e0e0 : BitVec 36)
def signal180 : W := (0xfabe3eaf9 : BitVec 36) ++ (0xf83e06078 : BitVec 36)
def signal181 : W := (0xfabe3eaf9 : BitVec 36) ++ (0xf83e3e0f8 : BitVec 36)
def signal182 : W := (0xfabe3eaf9 : BitVec 36) ++ (0xfc3e3f0f8 : BitVec 36)
def signal183 : W := (0xfabe3eaf9 : BitVec 36) ++ (0xfc3f3e0f8 : BitVec 36)
def signal184 : W := (0xfabe3eaf9 : BitVec 36) ++ (0xfc3f3f0f8 : BitVec 36)
def signal185 : W := (0xfabe3fffb : BitVec 36) ++ (0x181e06f7f : BitVec 36)
def signal186 : W := (0xfabe3fffb : BitVec 36) ++ (0xf83e3efff : BitVec 36)
def signal187 : W := (0xfabe3fffb : BitVec 36) ++ (0xf83e3f3ff : BitVec 36)
def signal188 : W := (0xfabe3fffb : BitVec 36) ++ (0xf83e3fcff : BitVec 36)
def signal189 : W := (0xfabfc0004 : BitVec 36) ++ (0xf83fc0000 : BitVec 36)
def signal190 : W := (0xfabffeafd : BitVec 36) ++ (0x181ec6078 : BitVec 36)
def signal191 : W := (0xfabffeafd : BitVec 36) ++ (0x183fc6078 : BitVec 36)
def signal192 : W := (0xfabffeafd : BitVec 36) ++ (0xf83efe0f8 : BitVec 36)
def signal193 : W := (0xfabffeafd : BitVec 36) ++ (0xf83f7e0f8 : BitVec 36)
def signal194 : W := (0xfabffeafd : BitVec 36) ++ (0xf83fbe0f8 : BitVec 36)
def signal195 : W := (0xfabffeafd : BitVec 36) ++ (0xf83ffe0f8 : BitVec 36)
def signal196 : W := (0xfabffeafd : BitVec 36) ++ (0xfc3ffe0f8 : BitVec 36)
def signal197 : W := (0xffd400000 : BitVec 36) ++ (0xffc000000 : BitVec 36)
def signal198 : W := (0xffd43ff52 : BitVec 36) ++ (0x1bc006f00 : BitVec 36)
def signal199 : W := (0xffd43ff52 : BitVec 36) ++ (0x1bc03ff00 : BitVec 36)
def signal200 : W := (0xffd43ff52 : BitVec 36) ++ (0x1fc007f00 : BitVec 36)
def signal201 : W := (0xffd43ff52 : BitVec 36) ++ (0x3bc00ef00 : BitVec 36)
def signal202 : W := (0xffd43ff52 : BitVec 36) ++ (0x5bc016f00 : BitVec 36)
def signal203 : W := (0xffd43ff52 : BitVec 36) ++ (0xbfc02ff00 : BitVec 36)
def signal204 : W := (0xffd43ff52 : BitVec 36) ++ (0xdfc037f00 : BitVec 36)
def signal205 : W := (0xffd43ff52 : BitVec 36) ++ (0xe7c039f00 : BitVec 36)
def signal206 : W := (0xffd43ff52 : BitVec 36) ++ (0xfbc03ef00 : BitVec 36)
def signal207 : W := (0xffd43ff52 : BitVec 36) ++ (0xfcc03f300 : BitVec 36)
def signal208 : W := (0xffd43ff52 : BitVec 36) ++ (0xff003fc00 : BitVec 36)
def signal209 : W := (0xffd43ff52 : BitVec 36) ++ (0xffc006f00 : BitVec 36)
def signal210 : W := (0xffd43ff52 : BitVec 36) ++ (0xffc03ff00 : BitVec 36)
def signal211 : W := (0xffd43ff52 : BitVec 36) ++ (0xffe03ff80 : BitVec 36)
def signal212 : W := (0xffd43ff52 : BitVec 36) ++ (0xffe13ff00 : BitVec 36)
def signal213 : W := (0xffd43ff52 : BitVec 36) ++ (0xffe13ff80 : BitVec 36)
def signal214 : W := (0xffd43fffb : BitVec 36) ++ (0x1bc006f7f : BitVec 36)
def signal215 : W := (0xffd43fffb : BitVec 36) ++ (0xffc03ff7f : BitVec 36)
def signal216 : W := (0xffd43fffb : BitVec 36) ++ (0xffc03ff9f : BitVec 36)
def signal217 : W := (0xffd43fffb : BitVec 36) ++ (0xffc03ffe7 : BitVec 36)
def signal218 : W := (0xffd5c0004 : BitVec 36) ++ (0xffc1c0000 : BitVec 36)
def signal219 : W := (0xffd5fff56 : BitVec 36) ++ (0x1bc0c6f00 : BitVec 36)
def signal220 : W := (0xffd5fff56 : BitVec 36) ++ (0x1fc1c6f00 : BitVec 36)
def signal221 : W := (0xffd5fff56 : BitVec 36) ++ (0xffc0fff00 : BitVec 36)
def signal222 : W := (0xffd5fff56 : BitVec 36) ++ (0xffc17ff00 : BitVec 36)
def signal223 : W := (0xffd5fff56 : BitVec 36) ++ (0xffc1bff00 : BitVec 36)
def signal224 : W := (0xffd5fff56 : BitVec 36) ++ (0xffc1fff00 : BitVec 36)
def signal225 : W := (0xffd5fff56 : BitVec 36) ++ (0xffe1fff00 : BitVec 36)
def signal226 : W := (0xfffe3fffb : BitVec 36) ++ (0xfffe3fff8 : BitVec 36)
def signal227 : W := (0xffffc0004 : BitVec 36) ++ (0x1bdec0000 : BitVec 36)
def signal228 : W := (0xffffc0004 : BitVec 36) ++ (0x1bffc0000 : BitVec 36)
def signal229 : W := (0xffffc0004 : BitVec 36) ++ (0x1fdfc0000 : BitVec 36)
def signal230 : W := (0xffffc0004 : BitVec 36) ++ (0x3bdec0000 : BitVec 36)
def signal231 : W := (0xffffc0004 : BitVec 36) ++ (0x5bdec0000 : BitVec 36)
def signal232 : W := (0xffffc0004 : BitVec 36) ++ (0xbfffc0000 : BitVec 36)
def signal233 : W := (0xffffc0004 : BitVec 36) ++ (0xdfffc0000 : BitVec 36)
def signal234 : W := (0xffffc0004 : BitVec 36) ++ (0xe7ffc0000 : BitVec 36)
def signal235 : W := (0xffffc0004 : BitVec 36) ++ (0xfbfec0000 : BitVec 36)
def signal236 : W := (0xffffc0004 : BitVec 36) ++ (0xfcff40000 : BitVec 36)
def signal237 : W := (0xffffc0004 : BitVec 36) ++ (0xff3f80000 : BitVec 36)
def signal238 : W := (0xffffc0004 : BitVec 36) ++ (0xffdec0000 : BitVec 36)
def signal239 : W := (0xffffc0004 : BitVec 36) ++ (0xffe740000 : BitVec 36)
def signal240 : W := (0xffffc0004 : BitVec 36) ++ (0xfff980000 : BitVec 36)
def signal241 : W := (0xffffc0004 : BitVec 36) ++ (0xffffc0000 : BitVec 36)
def signal242 : W := (0xffffc0004 : BitVec 36) ++ (0xffffe9080 : BitVec 36)
def signal243 : W := (0xffffc0004 : BitVec 36) ++ (0xfffff1080 : BitVec 36)
def signal244 : W := (0xffffc0004 : BitVec 36) ++ (0xfffff8080 : BitVec 36)
def signal245 : W := (0xffffc0004 : BitVec 36) ++ (0xfffff9000 : BitVec 36)
def signal246 : W := (0xffffc00ad : BitVec 36) ++ (0xffffc00f8 : BitVec 36)
def signal247 : W := (0xffffc1506 : BitVec 36) ++ (0xffffc1f00 : BitVec 36)
def signal248 : W := (0xffffca214 : BitVec 36) ++ (0x1bdec6318 : BitVec 36)
def signal249 : W := (0xffffca214 : BitVec 36) ++ (0xffffc6318 : BitVec 36)
def signal250 : W := (0xffffca214 : BitVec 36) ++ (0xffffc8318 : BitVec 36)
def signal251 : W := (0xffffca214 : BitVec 36) ++ (0xffffce018 : BitVec 36)
def signal252 : W := (0xffffca214 : BitVec 36) ++ (0xffffce300 : BitVec 36)
def signal253 : W := (0xffffd4844 : BitVec 36) ++ (0x1bdec6c60 : BitVec 36)
def signal254 : W := (0xffffd4844 : BitVec 36) ++ (0xffffc6c60 : BitVec 36)
def signal255 : W := (0xffffd4844 : BitVec 36) ++ (0xffffd0c60 : BitVec 36)
def signal256 : W := (0xffffd4844 : BitVec 36) ++ (0xffffd6060 : BitVec 36)
def signal257 : W := (0xffffd4844 : BitVec 36) ++ (0xffffd6c00 : BitVec 36)
def signal258 : W := (0xffffea2bd : BitVec 36) ++ (0xffffe8098 : BitVec 36)
def signal259 : W := (0xffffeb716 : BitVec 36) ++ (0xffffe9300 : BitVec 36)
def signal260 : W := (0xffffeb7bf : BitVec 36) ++ (0xffffe939f : BitVec 36)
def signal261 : W := (0xfffff48ed : BitVec 36) ++ (0xfffff00e0 : BitVec 36)
def signal262 : W := (0xfffff5d46 : BitVec 36) ++ (0xfffff1c00 : BitVec 36)
def signal263 : W := (0xfffff5def : BitVec 36) ++ (0xfffff1ce7 : BitVec 36)
def signal264 : W := (0xfffffea54 : BitVec 36) ++ (0xfffffe000 : BitVec 36)
def signal265 : W := (0xfffffeafd : BitVec 36) ++ (0x1bdec6078 : BitVec 36)
def signal266 : W := (0xfffffeafd : BitVec 36) ++ (0xfbfefe0f8 : BitVec 36)
def signal267 : W := (0xfffffeafd : BitVec 36) ++ (0xfc3f3e0f8 : BitVec 36)
def signal268 : W := (0xfffffeafd : BitVec 36) ++ (0xfcff7e0f8 : BitVec 36)
def signal269 : W := (0xfffffeafd : BitVec 36) ++ (0xff3fbe0f8 : BitVec 36)
def signal270 : W := (0xfffffeafd : BitVec 36) ++ (0xffffc6078 : BitVec 36)
def signal271 : W := (0xfffffeafd : BitVec 36) ++ (0xfffffe0f8 : BitVec 36)
def signal272 : W := (0xfffffff56 : BitVec 36) ++ (0x1bdec6f00 : BitVec 36)
def signal273 : W := (0xfffffff56 : BitVec 36) ++ (0xffdefff00 : BitVec 36)
def signal274 : W := (0xfffffff56 : BitVec 36) ++ (0xffe13ff00 : BitVec 36)
def signal275 : W := (0xfffffff56 : BitVec 36) ++ (0xffe77ff00 : BitVec 36)
def signal276 : W := (0xfffffff56 : BitVec 36) ++ (0xfff9bff00 : BitVec 36)
def signal277 : W := (0xfffffff56 : BitVec 36) ++ (0xffffc6f00 : BitVec 36)
def signal278 : W := (0xfffffff56 : BitVec 36) ++ (0xfffffff00 : BitVec 36)
def signal279 : W := (0xfffffffff : BitVec 36) ++ (0x3dec0f7f : BitVec 36)
def signal280 : W := (0xfffffffff : BitVec 36) ++ (0x18de4637f : BitVec 36)
def signal281 : W := (0xfffffffff : BitVec 36) ++ (0x1b1e86c7f : BitVec 36)
def signal282 : W := (0xfffffffff : BitVec 36) ++ (0x1bc646f1f : BitVec 36)
def signal283 : W := (0xfffffffff : BitVec 36) ++ (0x1bd886f67 : BitVec 36)
def signal284 : W := (0xfffffffff : BitVec 36) ++ (0x1bdec6f78 : BitVec 36)
def signal285 : W := (0xfffffffff : BitVec 36) ++ (0x1bdec6f7f : BitVec 36)
def signal286 : W := (0xfffffffff : BitVec 36) ++ (0xbfffeffff : BitVec 36)
def signal287 : W := (0xfffffffff : BitVec 36) ++ (0xdffff7fff : BitVec 36)
def signal288 : W := (0xfffffffff : BitVec 36) ++ (0xe7fff9fff : BitVec 36)
def signal289 : W := (0xfffffffff : BitVec 36) ++ (0xfbfefefff : BitVec 36)
def signal290 : W := (0xfffffffff : BitVec 36) ++ (0xfcff7f3ff : BitVec 36)
def signal291 : W := (0xfffffffff : BitVec 36) ++ (0xff3fbfcff : BitVec 36)
def signal292 : W := (0xfffffffff : BitVec 36) ++ (0xffdefff7f : BitVec 36)
def signal293 : W := (0xfffffffff : BitVec 36) ++ (0xffe77ff9f : BitVec 36)
def signal294 : W := (0xfffffffff : BitVec 36) ++ (0xfff9bffe7 : BitVec 36)
def signal295 : W := (0xfffffffff : BitVec 36) ++ (0xffffc6f7f : BitVec 36)
def signal296 : W := (0xfffffffff : BitVec 36) ++ (0xffffffff8 : BitVec 36)

def ins : List W := [signal285,signal133,signal162,signal181,signal210,signal241]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer0 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok0 : everyKey (fun q => !doneTest q) layer0=true := by decide +kernel
theorem closed0 : Closed 0 layer0 := closed_nil _ ok0
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer1 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok1 : everyKey (rowOK 0 layer0) layer1=true := by decide +kernel
theorem closed1 : Closed 1 layer1 := closed_next 0 (by decide) _ _ closed0 ok1
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer2 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok2 : everyKey (rowOK 1 layer1) layer2=true := by decide +kernel
theorem closed2 : Closed 2 layer2 := closed_next 1 (by decide) _ _ closed1 ok2
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer3 : BinaryTree (List W) := (.node [signal133,signal150,signal169,signal224] (.node [signal121,signal162,signal181,signal220] (.node [signal121,signal162,signal169,signal224] (.node [signal121,signal150,signal181,signal224] (.node [signal73,signal133,signal162,signal285] .nil .nil) (.node [signal121,signal150,signal195,signal210] .nil .nil)) (.node [signal121,signal162,signal181,signal219] (.node [signal121,signal162,signal169,signal225] .nil .nil) .nil)) (.node [signal121,signal162,signal195,signal198] (.node [signal121,signal162,signal191,signal210] (.node [signal121,signal162,signal190,signal210] .nil .nil) .nil) (.node [signal132,signal162,signal165,signal285] (.node [signal121,signal162,signal196,signal198] .nil .nil) .nil))) (.node [signal133,signal150,signal195,signal198] (.node [signal133,signal150,signal181,signal220] (.node [signal133,signal150,signal181,signal219] (.node [signal133,signal150,signal169,signal225] .nil .nil) .nil) (.node [signal133,signal150,signal191,signal210] (.node [signal133,signal150,signal190,signal210] .nil .nil) .nil)) (.node [signal133,signal162,signal165,signal284] (.node [signal133,signal161,signal165,signal285] (.node [signal133,signal150,signal196,signal198] .nil .nil) .nil) (.node [signal133,signal162,signal190,signal198] (.node [signal133,signal162,signal169,signal219] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok3 : everyKey (rowOK 2 layer2) layer3=true := by decide +kernel
theorem closed3 : Closed 3 layer3 := closed_next 2 (by decide) _ _ closed2 ok3
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer4 : BinaryTree (List W) := (.node [signal121,signal150,signal181,signal210,signal241] (.node [signal60,signal121,signal150,signal210,signal241] (.node [signal39,signal121,signal150,signal181,signal210] (.node [signal17,signal121,signal162,signal169,signal210] (.node [signal14,signal133,signal150,signal169,signal210] (.node [signal14,signal121,signal150,signal181,signal210] (.node [signal13,signal121,signal162,signal169,signal210] (.node [signal13,signal121,signal150,signal181,signal210] .nil .nil) (.node [signal13,signal121,signal162,signal181,signal198] .nil .nil)) (.node [signal14,signal121,signal162,signal181,signal198] (.node [signal14,signal121,signal162,signal169,signal210] .nil .nil) .nil)) (.node [signal16,signal133,signal150,signal169,signal210] (.node [signal16,signal121,signal150,signal181,signal210] (.node [signal14,signal133,signal150,signal181,signal198] .nil .nil) .nil) (.node [signal17,signal121,signal150,signal181,signal210] (.node [signal16,signal133,signal150,signal181,signal198] .nil .nil) .nil))) (.node [signal21,signal133,signal150,signal169,signal210] (.node [signal21,signal121,signal150,signal181,signal210] (.node [signal17,signal133,signal150,signal169,signal210] (.node [signal17,signal121,signal162,signal181,signal198] .nil .nil) (.node [signal17,signal133,signal150,signal181,signal198] .nil .nil)) (.node [signal21,signal121,signal162,signal181,signal198] (.node [signal21,signal121,signal162,signal169,signal210] .nil .nil) .nil)) (.node [signal33,signal133,signal162,signal181,signal285] (.node [signal31,signal133,signal162,signal181,signal210] (.node [signal21,signal133,signal150,signal181,signal198] .nil .nil) .nil) (.node [signal35,signal133,signal162,signal181,signal285] (.node [signal34,signal67,signal133,signal162,signal285] .nil .nil) .nil)))) (.node [signal41,signal133,signal162,signal195,signal285] (.node [signal41,signal121,signal150,signal181,signal241] (.node [signal39,signal133,signal150,signal181,signal198] (.node [signal39,signal121,signal162,signal181,signal198] (.node [signal39,signal121,signal162,signal169,signal210] .nil .nil) (.node [signal39,signal133,signal150,signal169,signal210] .nil .nil)) (.node [signal40,signal133,signal150,signal181,signal198] (.node [signal40,signal121,signal162,signal181,signal198] .nil .nil) .nil)) (.node [signal41,signal133,signal162,signal181,signal214] (.node [signal41,signal133,signal150,signal169,signal241] (.node [signal41,signal121,signal162,signal169,signal241] .nil .nil) .nil) (.node [signal41,signal133,signal162,signal192,signal285] (.node [signal41,signal133,signal162,signal181,signal272] .nil .nil) .nil))) (.node [signal58,signal121,signal162,signal169,signal210] (.node [signal52,signal133,signal162,signal210,signal285] (.node [signal50,signal133,signal162,signal181,signal241] (.node [signal48,signal53,signal133,signal162,signal285] .nil .nil) (.node [signal51,signal133,signal162,signal181,signal285] .nil .nil)) (.node [signal58,signal121,signal150,signal181,signal210] (.node [signal54,signal133,signal162,signal210,signal285] .nil .nil) .nil)) (.node [signal58,signal133,signal150,signal181,signal198] (.node [signal58,signal133,signal150,signal169,signal210] (.node [signal58,signal121,signal162,signal181,signal198] .nil .nil) .nil) (.node [signal59,signal133,signal150,signal169,signal210] (.node [signal59,signal121,signal162,signal169,signal210] .nil .nil) .nil))))) (.node [signal101,signal162,signal181,signal241,signal285] (.node [signal75,signal133,signal195,signal210,signal285] (.node [signal69,signal133,signal162,signal210,signal241] (.node [signal60,signal133,signal162,signal210,signal265] (.node [signal60,signal133,signal150,signal198,signal241] (.node [signal60,signal121,signal162,signal198,signal241] .nil .nil) (.node [signal60,signal133,signal162,signal185,signal210] .nil .nil)) (.node [signal60,signal133,signal162,signal224,signal285] (.node [signal60,signal133,signal162,signal221,signal285] .nil .nil) .nil)) (.node [signal75,signal121,signal169,signal210,signal241] (.node [signal71,signal133,signal162,signal241,signal285] (.node [signal70,signal133,signal162,signal210,signal285] .nil .nil) .nil) (.node [signal75,signal133,signal181,signal224,signal285] (.node [signal75,signal121,signal181,signal198,signal241] .nil .nil) .nil))) (.node [signal90,signal150,signal181,signal198,signal241] (.node [signal86,signal133,signal181,signal241,signal285] (.node [signal83,signal133,signal181,signal210,signal285] (.node [signal81,signal133,signal181,signal210,signal241] .nil .nil) (.node [signal84,signal133,signal150,signal181,signal210] .nil .nil)) (.node [signal90,signal150,signal169,signal210,signal241] (.node [signal88,signal133,signal210,signal241,signal285] .nil .nil) .nil)) (.node [signal96,signal162,signal181,signal210,signal241] (.node [signal90,signal162,signal195,signal210,signal285] (.node [signal90,signal162,signal181,signal224,signal285] .nil .nil) .nil) (.node [signal99,signal121,signal162,signal181,signal210] (.node [signal97,signal162,signal181,signal210,signal285] .nil .nil) .nil)))) (.node [signal112,signal121,signal150,signal181,signal210] (.node [signal107,signal162,signal210,signal241,signal280] (.node [signal106,signal181,signal205,signal241,signal285] (.node [signal104,signal181,signal210,signal241,signal285] (.node [signal103,signal162,signal210,signal241,signal285] .nil .nil) (.node [signal106,signal176,signal210,signal241,signal285] .nil .nil)) (.node [signal107,signal157,signal210,signal241,signal285] (.node [signal106,signal181,signal210,signal241,signal279] .nil .nil) .nil)) (.node [signal111,signal121,signal150,signal181,signal210] (.node [signal109,signal162,signal181,signal241,signal282] (.node [signal109,signal159,signal181,signal241,signal285] .nil .nil) .nil) (.node [signal111,signal121,signal162,signal181,signal198] (.node [signal111,signal121,signal162,signal169,signal210] .nil .nil) .nil))) (.node [signal121,signal141,signal150,signal181,signal210] (.node [signal112,signal133,signal150,signal169,signal210] (.node [signal112,signal121,signal162,signal181,signal198] (.node [signal112,signal121,signal162,signal169,signal210] .nil .nil) .nil) (.node [signal121,signal140,signal150,signal181,signal210] (.node [signal112,signal133,signal150,signal181,signal198] .nil .nil) .nil)) (.node [signal121,signal150,signal169,signal210,signal241] (.node [signal121,signal141,signal162,signal181,signal198] (.node [signal121,signal141,signal162,signal169,signal210] .nil .nil) .nil) (.node [signal121,signal150,signal181,signal210,signal227] (.node [signal121,signal150,signal181,signal198,signal241] .nil .nil) .nil)))))) (.node [signal133,signal150,signal169,signal210,signal278] (.node [signal121,signal162,signal181,signal210,signal265] (.node [signal121,signal162,signal172,signal210,signal241] (.node [signal121,signal162,signal169,signal210,signal227] (.node [signal121,signal153,signal181,signal210,signal241] (.node [signal121,signal150,signal181,signal210,signal278] (.node [signal121,signal150,signal181,signal210,signal271] .nil .nil) (.node [signal121,signal152,signal181,signal210,signal241] .nil .nil)) (.node [signal121,signal162,signal169,signal198,signal241] (.node [signal121,signal155,signal181,signal210,signal241] .nil .nil) .nil)) (.node [signal121,signal162,signal169,signal210,signal271] (.node [signal121,signal162,signal169,signal210,signal270] (.node [signal121,signal162,signal169,signal210,signal241] .nil .nil) .nil) (.node [signal121,signal162,signal171,signal210,signal241] (.node [signal121,signal162,signal169,signal210,signal278] .nil .nil) .nil))) (.node [signal121,signal162,signal181,signal198,signal278] (.node [signal121,signal162,signal181,signal198,signal241] (.node [signal121,signal162,signal181,signal185,signal210] (.node [signal121,signal162,signal174,signal210,signal241] .nil .nil) (.node [signal121,signal162,signal181,signal198,signal227] .nil .nil)) (.node [signal121,signal162,signal181,signal198,signal277] (.node [signal121,signal162,signal181,signal198,signal271] .nil .nil) .nil)) (.node [signal121,signal162,signal181,signal203,signal241] (.node [signal121,signal162,signal181,signal201,signal241] (.node [signal121,signal162,signal181,signal200,signal241] .nil .nil) .nil) (.node [signal121,signal162,signal181,signal210,signal253] (.node [signal121,signal162,signal181,signal210,signal214] .nil .nil) .nil)))) (.node [signal132,signal162,signal181,signal210,signal285] (.node [signal125,signal162,signal181,signal198,signal241] (.node [signal123,signal150,signal181,signal210,signal241] (.node [signal121,signal162,signal181,signal224,signal285] (.node [signal121,signal162,signal181,signal210,signal272] .nil .nil) (.node [signal121,signal162,signal195,signal210,signal285] .nil .nil)) (.node [signal125,signal162,signal169,signal210,signal241] (.node [signal124,signal150,signal181,signal210,signal241] .nil .nil) .nil)) (.node [signal128,signal136,signal210,signal241,signal285] (.node [signal127,signal162,signal169,signal210,signal241] (.node [signal126,signal150,signal181,signal210,signal241] .nil .nil) .nil) (.node [signal130,signal138,signal181,signal241,signal285] (.node [signal129,signal162,signal181,signal198,signal241] .nil .nil) .nil))) (.node [signal133,signal141,signal150,signal181,signal198] (.node [signal133,signal140,signal150,signal169,signal210] (.node [signal133,signal138,signal181,signal241,signal283] (.node [signal133,signal136,signal210,signal241,signal281] .nil .nil) .nil) (.node [signal133,signal141,signal150,signal169,signal210] (.node [signal133,signal140,signal150,signal181,signal198] .nil .nil) .nil)) (.node [signal133,signal150,signal169,signal210,signal241] (.node [signal133,signal150,signal169,signal210,signal227] (.node [signal133,signal150,signal169,signal198,signal241] .nil .nil) .nil) (.node [signal133,signal150,signal169,signal210,signal271] (.node [signal133,signal150,signal169,signal210,signal270] .nil .nil) .nil))))) (.node [signal133,signal162,signal167,signal271,signal285] (.node [signal133,signal150,signal181,signal210,signal214] (.node [signal133,signal150,signal181,signal198,signal271] (.node [signal133,signal150,signal181,signal185,signal210] (.node [signal133,signal150,signal173,signal210,signal241] (.node [signal133,signal150,signal171,signal210,signal241] .nil .nil) (.node [signal133,signal150,signal175,signal210,signal241] .nil .nil)) (.node [signal133,signal150,signal181,signal198,signal241] (.node [signal133,signal150,signal181,signal198,signal227] .nil .nil) .nil)) (.node [signal133,signal150,signal181,signal200,signal241] (.node [signal133,signal150,signal181,signal198,signal278] (.node [signal133,signal150,signal181,signal198,signal277] .nil .nil) .nil) (.node [signal133,signal150,signal181,signal204,signal241] (.node [signal133,signal150,signal181,signal202,signal241] .nil .nil) .nil))) (.node [signal133,signal154,signal181,signal198,signal241] (.node [signal133,signal150,signal181,signal224,signal285] (.node [signal133,signal150,signal181,signal210,signal265] (.node [signal133,signal150,signal181,signal210,signal248] .nil .nil) (.node [signal133,signal150,signal181,signal210,signal272] .nil .nil)) (.node [signal133,signal154,signal169,signal210,signal241] (.node [signal133,signal150,signal195,signal210,signal285] .nil .nil) .nil)) (.node [signal133,signal161,signal181,signal210,signal285] (.node [signal133,signal158,signal181,signal198,signal241] (.node [signal133,signal156,signal169,signal210,signal241] .nil .nil) .nil) (.node [signal133,signal162,signal166,signal278,signal285] (.node [signal133,signal162,signal165,signal285,signal296] .nil .nil) .nil)))) (.node [signal133,signal162,signal181,signal225,signal285] (.node [signal133,signal162,signal181,signal219,signal285] (.node [signal133,signal162,signal169,signal225,signal285] (.node [signal133,signal162,signal169,signal210,signal272] (.node [signal133,signal162,signal169,signal198,signal227] .nil .nil) (.node [signal133,signal162,signal169,signal224,signal285] .nil .nil)) (.node [signal133,signal162,signal181,signal210,signal284] (.node [signal133,signal162,signal181,signal198,signal265] .nil .nil) .nil)) (.node [signal133,signal162,signal181,signal222,signal285] (.node [signal133,signal162,signal181,signal221,signal285] (.node [signal133,signal162,signal181,signal220,signal285] .nil .nil) .nil) (.node [signal133,signal162,signal181,signal224,signal285] (.node [signal133,signal162,signal181,signal223,signal285] .nil .nil) .nil))) (.node [signal133,signal162,signal194,signal210,signal285] (.node [signal133,signal162,signal191,signal210,signal285] (.node [signal133,signal162,signal190,signal210,signal285] (.node [signal133,signal162,signal181,signal274,signal285] .nil .nil) .nil) (.node [signal133,signal162,signal193,signal210,signal285] (.node [signal133,signal162,signal192,signal210,signal285] .nil .nil) .nil)) (.node [signal133,signal162,signal196,signal198,signal285] (.node [signal133,signal162,signal195,signal210,signal285] (.node [signal133,signal162,signal195,signal198,signal285] .nil .nil) .nil) (.node [signal133,signal162,signal210,signal267,signal285] (.node [signal133,signal162,signal196,signal210,signal285] .nil .nil) .nil)))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok4 : everyKey (rowOK 3 layer3) layer4=true := by decide +kernel
theorem closed4 : Closed 4 layer4 := closed_next 3 (by decide) _ _ closed3 ok4
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer5 : BinaryTree (List W) := (.node [signal112,signal133,signal162,signal169,signal210,signal285] (.node [signal41,signal133,signal150,signal181,signal241,signal285] (.node [signal17,signal133,signal162,signal181,signal210,signal285] (.node [signal13,signal121,signal162,signal181,signal210,signal285] (.node [signal3,signal121,signal162,signal181,signal210,signal241] (.node [signal1,signal133,signal162,signal169,signal210,signal241] (.node [signal0,signal133,signal162,signal181,signal198,signal241] (.node [signal0,signal133,signal150,signal181,signal210,signal241] (.node [signal0,signal90,signal162,signal181,signal210,signal241] .nil .nil) (.node [signal0,signal133,signal162,signal169,signal210,signal241] .nil .nil)) (.node [signal1,signal121,signal162,signal181,signal210,signal241] (.node [signal1,signal75,signal133,signal181,signal210,signal241] .nil .nil) .nil)) (.node [signal2,signal121,signal162,signal181,signal210,signal241] (.node [signal2,signal60,signal133,signal162,signal210,signal241] (.node [signal1,signal133,signal162,signal181,signal198,signal241] .nil .nil) .nil) (.node [signal3,signal41,signal133,signal162,signal181,signal241] (.node [signal2,signal133,signal150,signal181,signal210,signal241] .nil .nil) .nil))) (.node [signal8,signal133,signal162,signal181,signal210,signal285] (.node [signal6,signal41,signal133,signal162,signal181,signal285] (.node [signal4,signal21,signal133,signal162,signal181,signal210] (.node [signal3,signal133,signal150,signal181,signal210,signal241] .nil .nil) (.node [signal5,signal133,signal162,signal181,signal210,signal241] .nil .nil)) (.node [signal7,signal133,signal162,signal181,signal210,signal285] (.node [signal6,signal133,signal162,signal181,signal210,signal285] .nil .nil) .nil)) (.node [signal10,signal133,signal162,signal181,signal210,signal285] (.node [signal9,signal133,signal162,signal181,signal210,signal285] (.node [signal9,signal60,signal133,signal162,signal210,signal285] .nil .nil) .nil) (.node [signal12,signal133,signal162,signal181,signal210,signal285] (.node [signal11,signal133,signal162,signal181,signal210,signal285] .nil .nil) .nil)))) (.node [signal15,signal133,signal162,signal181,signal210,signal285] (.node [signal14,signal112,signal162,signal181,signal210,signal285] (.node [signal14,signal75,signal133,signal181,signal210,signal285] (.node [signal14,signal41,signal133,signal162,signal181,signal285] (.node [signal13,signal133,signal162,signal181,signal210,signal285] .nil .nil) (.node [signal14,signal60,signal133,signal162,signal210,signal285] .nil .nil)) (.node [signal14,signal90,signal162,signal181,signal210,signal285] (.node [signal14,signal89,signal162,signal181,signal210,signal285] .nil .nil) .nil)) (.node [signal14,signal133,signal162,signal169,signal210,signal285] (.node [signal14,signal133,signal150,signal181,signal210,signal285] (.node [signal14,signal121,signal162,signal181,signal210,signal285] .nil .nil) .nil) (.node [signal14,signal133,signal162,signal181,signal210,signal285] (.node [signal14,signal133,signal162,signal181,signal198,signal285] .nil .nil) .nil))) (.node [signal17,signal90,signal162,signal181,signal210,signal285] (.node [signal17,signal60,signal133,signal162,signal210,signal285] (.node [signal16,signal133,signal162,signal181,signal210,signal285] (.node [signal16,signal133,signal150,signal181,signal210,signal285] .nil .nil) (.node [signal17,signal41,signal133,signal162,signal181,signal285] .nil .nil)) (.node [signal17,signal75,signal133,signal181,signal210,signal285] (.node [signal17,signal74,signal133,signal181,signal210,signal285] .nil .nil) .nil)) (.node [signal17,signal133,signal150,signal181,signal210,signal285] (.node [signal17,signal133,signal141,signal181,signal210,signal285] (.node [signal17,signal121,signal162,signal181,signal210,signal285] .nil .nil) .nil) (.node [signal17,signal133,signal162,signal181,signal198,signal285] (.node [signal17,signal133,signal162,signal169,signal210,signal285] .nil .nil) .nil))))) (.node [signal36,signal41,signal133,signal162,signal181,signal285] (.node [signal21,signal133,signal162,signal181,signal210,signal285] (.node [signal21,signal90,signal162,signal181,signal210,signal285] (.node [signal21,signal41,signal133,signal162,signal181,signal285] (.node [signal19,signal58,signal133,signal162,signal210,signal285] (.node [signal18,signal133,signal162,signal181,signal210,signal285] .nil .nil) (.node [signal20,signal39,signal133,signal162,signal181,signal285] .nil .nil)) (.node [signal21,signal75,signal133,signal181,signal210,signal285] (.node [signal21,signal60,signal133,signal162,signal210,signal285] .nil .nil) .nil)) (.node [signal21,signal133,signal162,signal169,signal210,signal285] (.node [signal21,signal133,signal150,signal181,signal210,signal285] (.node [signal21,signal121,signal162,signal181,signal210,signal285] .nil .nil) .nil) (.node [signal21,signal133,signal162,signal181,signal210,signal227] (.node [signal21,signal133,signal162,signal181,signal198,signal285] .nil .nil) .nil))) (.node [signal28,signal133,signal162,signal181,signal210,signal285] (.node [signal25,signal133,signal162,signal181,signal210,signal285] (.node [signal23,signal133,signal162,signal181,signal210,signal285] (.node [signal22,signal133,signal162,signal181,signal210,signal285] .nil .nil) (.node [signal24,signal133,signal162,signal181,signal210,signal285] .nil .nil)) (.node [signal27,signal133,signal162,signal181,signal210,signal285] (.node [signal26,signal133,signal162,signal181,signal210,signal285] .nil .nil) .nil)) (.node [signal32,signal133,signal162,signal181,signal210,signal285] (.node [signal30,signal133,signal162,signal181,signal210,signal285] (.node [signal29,signal133,signal162,signal181,signal210,signal285] .nil .nil) .nil) (.node [signal34,signal133,signal162,signal181,signal278,signal285] (.node [signal34,signal53,signal133,signal162,signal241,signal285] .nil .nil) .nil)))) (.node [signal39,signal133,signal162,signal181,signal210,signal285] (.node [signal39,signal90,signal162,signal181,signal210,signal285] (.node [signal39,signal41,signal133,signal162,signal181,signal285] (.node [signal37,signal133,signal162,signal181,signal210,signal285] (.node [signal36,signal133,signal162,signal181,signal210,signal285] .nil .nil) (.node [signal38,signal133,signal162,signal181,signal210,signal285] .nil .nil)) (.node [signal39,signal75,signal133,signal181,signal210,signal285] (.node [signal39,signal60,signal133,signal162,signal210,signal285] .nil .nil) .nil)) (.node [signal39,signal133,signal162,signal166,signal210,signal285] (.node [signal39,signal133,signal150,signal181,signal210,signal285] (.node [signal39,signal121,signal162,signal181,signal210,signal285] .nil .nil) .nil) (.node [signal39,signal133,signal162,signal181,signal198,signal285] (.node [signal39,signal133,signal162,signal169,signal210,signal285] .nil .nil) .nil))) (.node [signal41,signal60,signal133,signal162,signal241,signal285] (.node [signal40,signal133,signal162,signal181,signal198,signal285] (.node [signal39,signal133,signal162,signal195,signal210,signal285] (.node [signal39,signal133,signal162,signal181,signal278,signal285] .nil .nil) .nil) (.node [signal41,signal58,signal133,signal162,signal181,signal285] (.node [signal40,signal133,signal162,signal181,signal210,signal285] .nil .nil) .nil)) (.node [signal41,signal112,signal133,signal162,signal181,signal285] (.node [signal41,signal90,signal162,signal181,signal241,signal285] (.node [signal41,signal75,signal133,signal181,signal241,signal285] .nil .nil) .nil) (.node [signal41,signal133,signal141,signal162,signal181,signal285] (.node [signal41,signal121,signal162,signal181,signal241,signal285] .nil .nil) .nil)))))) (.node [signal67,signal133,signal162,signal181,signal210,signal285] (.node [signal58,signal133,signal162,signal169,signal210,signal285] (.node [signal48,signal133,signal162,signal181,signal210,signal285] (.node [signal42,signal93,signal162,signal181,signal241,signal285] (.node [signal41,signal133,signal162,signal181,signal241,signal285] (.node [signal41,signal133,signal162,signal181,signal198,signal241] (.node [signal41,signal133,signal162,signal169,signal241,signal285] .nil .nil) (.node [signal41,signal133,signal162,signal181,signal227,signal285] .nil .nil)) (.node [signal41,signal133,signal162,signal181,signal278,signal285] (.node [signal41,signal133,signal162,signal181,signal271,signal285] .nil .nil) .nil)) (.node [signal45,signal133,signal162,signal181,signal241,signal285] (.node [signal44,signal133,signal162,signal181,signal241,signal285] (.node [signal43,signal78,signal133,signal181,signal241,signal285] .nil .nil) .nil) (.node [signal47,signal133,signal162,signal181,signal241,signal285] (.node [signal46,signal133,signal162,signal181,signal241,signal285] .nil .nil) .nil))) (.node [signal58,signal60,signal133,signal162,signal210,signal285] (.node [signal55,signal133,signal162,signal181,signal210,signal285] (.node [signal53,signal133,signal162,signal210,signal271,signal285] (.node [signal49,signal133,signal162,signal181,signal241,signal285] .nil .nil) (.node [signal55,signal60,signal133,signal162,signal210,signal285] .nil .nil)) (.node [signal57,signal133,signal162,signal181,signal210,signal285] (.node [signal56,signal133,signal162,signal181,signal210,signal285] .nil .nil) .nil)) (.node [signal58,signal121,signal162,signal181,signal210,signal285] (.node [signal58,signal90,signal162,signal181,signal210,signal285] (.node [signal58,signal75,signal133,signal181,signal210,signal285] .nil .nil) .nil) (.node [signal58,signal133,signal162,signal167,signal181,signal285] (.node [signal58,signal133,signal150,signal181,signal210,signal285] .nil .nil) .nil)))) (.node [signal60,signal133,signal162,signal169,signal210,signal241] (.node [signal60,signal75,signal133,signal210,signal241,signal285] (.node [signal58,signal133,signal162,signal210,signal271,signal285] (.node [signal58,signal133,signal162,signal181,signal210,signal285] (.node [signal58,signal133,signal162,signal181,signal198,signal285] .nil .nil) (.node [signal58,signal133,signal162,signal181,signal224,signal285] .nil .nil)) (.node [signal59,signal133,signal162,signal181,signal210,signal285] (.node [signal59,signal133,signal162,signal169,signal210,signal285] .nil .nil) .nil)) (.node [signal60,signal121,signal162,signal210,signal241,signal285] (.node [signal60,signal112,signal133,signal162,signal210,signal285] (.node [signal60,signal90,signal162,signal210,signal241,signal285] .nil .nil) .nil) (.node [signal60,signal133,signal150,signal210,signal241,signal285] (.node [signal60,signal133,signal141,signal162,signal210,signal285] .nil .nil) .nil))) (.node [signal61,signal92,signal162,signal210,signal241,signal285] (.node [signal60,signal133,signal162,signal210,signal241,signal285] (.node [signal60,signal133,signal162,signal210,signal227,signal285] (.node [signal60,signal133,signal162,signal198,signal241,signal285] .nil .nil) .nil) (.node [signal60,signal133,signal162,signal210,signal278,signal285] (.node [signal60,signal133,signal162,signal210,signal271,signal285] .nil .nil) .nil)) (.node [signal64,signal133,signal162,signal210,signal241,signal285] (.node [signal63,signal133,signal162,signal210,signal241,signal285] (.node [signal62,signal77,signal133,signal210,signal241,signal285] .nil .nil) .nil) (.node [signal66,signal133,signal162,signal210,signal241,signal285] (.node [signal65,signal133,signal162,signal210,signal241,signal285] .nil .nil) .nil))))) (.node [signal90,signal141,signal162,signal181,signal210,signal285] (.node [signal75,signal133,signal181,signal210,signal249,signal285] (.node [signal75,signal133,signal146,signal181,signal210,signal285] (.node [signal75,signal112,signal133,signal181,signal210,signal285] (.node [signal72,signal133,signal162,signal181,signal210,signal285] (.node [signal68,signal133,signal162,signal210,signal241,signal285] .nil .nil) (.node [signal75,signal90,signal181,signal210,signal241,signal285] .nil .nil)) (.node [signal75,signal133,signal141,signal181,signal210,signal285] (.node [signal75,signal121,signal181,signal210,signal241,signal285] .nil .nil) .nil)) (.node [signal75,signal133,signal181,signal198,signal241,signal285] (.node [signal75,signal133,signal169,signal210,signal241,signal285] (.node [signal75,signal133,signal150,signal181,signal210,signal241] .nil .nil) .nil) (.node [signal75,signal133,signal181,signal210,signal241,signal285] (.node [signal75,signal133,signal181,signal210,signal227,signal285] .nil .nil) .nil))) (.node [signal84,signal133,signal162,signal181,signal210,signal285] (.node [signal79,signal133,signal181,signal210,signal241,signal285] (.node [signal75,signal133,signal181,signal210,signal278,signal285] (.node [signal75,signal133,signal181,signal210,signal271,signal285] .nil .nil) (.node [signal76,signal91,signal181,signal210,signal241,signal285] .nil .nil)) (.node [signal82,signal133,signal162,signal181,signal210,signal285] (.node [signal80,signal133,signal181,signal210,signal241,signal285] .nil .nil) .nil)) (.node [signal90,signal112,signal162,signal181,signal210,signal285] (.node [signal87,signal133,signal162,signal181,signal210,signal285] (.node [signal85,signal133,signal162,signal181,signal210,signal285] .nil .nil) .nil) (.node [signal90,signal121,signal162,signal181,signal210,signal241] (.node [signal90,signal117,signal162,signal181,signal210,signal285] .nil .nil) .nil)))) (.node [signal100,signal133,signal162,signal181,signal210,signal285] (.node [signal90,signal162,signal181,signal210,signal271,signal285] (.node [signal90,signal162,signal181,signal210,signal227,signal285] (.node [signal90,signal162,signal169,signal210,signal241,signal285] (.node [signal90,signal150,signal181,signal210,signal241,signal285] .nil .nil) (.node [signal90,signal162,signal181,signal198,signal241,signal285] .nil .nil)) (.node [signal90,signal162,signal181,signal210,signal254,signal285] (.node [signal90,signal162,signal181,signal210,signal241,signal285] .nil .nil) .nil)) (.node [signal95,signal162,signal181,signal210,signal241,signal285] (.node [signal94,signal162,signal181,signal210,signal241,signal285] (.node [signal90,signal162,signal181,signal210,signal278,signal285] .nil .nil) .nil) (.node [signal99,signal133,signal162,signal181,signal210,signal285] (.node [signal98,signal133,signal162,signal181,signal210,signal285] .nil .nil) .nil))) (.node [signal109,signal162,signal181,signal241,signal285,signal293] (.node [signal106,signal181,signal210,signal241,signal285,signal288] (.node [signal105,signal133,signal162,signal181,signal210,signal285] (.node [signal102,signal133,signal162,signal181,signal210,signal285] .nil .nil) .nil) (.node [signal108,signal133,signal162,signal181,signal210,signal285] (.node [signal107,signal162,signal210,signal241,signal285,signal290] .nil .nil) .nil)) (.node [signal111,signal133,signal162,signal181,signal210,signal285] (.node [signal111,signal121,signal162,signal181,signal210,signal285] (.node [signal110,signal133,signal162,signal181,signal210,signal285] .nil .nil) .nil) (.node [signal112,signal133,signal150,signal181,signal210,signal285] (.node [signal112,signal121,signal162,signal181,signal210,signal285] .nil .nil) .nil))))))) (.node [signal133,signal162,signal178,signal210,signal241,signal285] (.node [signal133,signal143,signal162,signal181,signal210,signal285] (.node [signal121,signal162,signal181,signal210,signal241,signal285] (.node [signal121,signal133,signal162,signal169,signal210,signal241] (.node [signal116,signal133,signal162,signal181,signal210,signal285] (.node [signal113,signal133,signal162,signal181,signal210,signal285] (.node [signal112,signal133,signal162,signal181,signal210,signal285] (.node [signal112,signal133,signal162,signal181,signal198,signal285] .nil .nil) (.node [signal112,signal162,signal181,signal210,signal260,signal285] .nil .nil)) (.node [signal115,signal133,signal162,signal181,signal210,signal285] (.node [signal114,signal133,signal162,signal181,signal210,signal285] .nil .nil) .nil)) (.node [signal119,signal133,signal162,signal181,signal210,signal285] (.node [signal118,signal133,signal162,signal181,signal210,signal285] (.node [signal117,signal133,signal162,signal181,signal210,signal285] .nil .nil) .nil) (.node [signal121,signal133,signal150,signal181,signal210,signal241] (.node [signal120,signal133,signal162,signal181,signal210,signal285] .nil .nil) .nil))) (.node [signal121,signal162,signal169,signal210,signal241] (.node [signal121,signal150,signal181,signal210,signal241] (.node [signal121,signal141,signal162,signal181,signal210,signal285] (.node [signal121,signal133,signal162,signal181,signal198,signal241] .nil .nil) (.node [signal121,signal150,signal162,signal181,signal210,signal241] .nil .nil)) (.node [signal121,signal162,signal169,signal181,signal210,signal241] (.node [signal121,signal150,signal181,signal210,signal241,signal285] .nil .nil) .nil)) (.node [signal121,signal162,signal181,signal198,signal241] (.node [signal121,signal162,signal181,signal198,signal210,signal241] (.node [signal121,signal162,signal169,signal210,signal241,signal285] .nil .nil) .nil) (.node [signal121,signal162,signal181,signal210,signal227,signal285] (.node [signal121,signal162,signal181,signal198,signal241,signal285] .nil .nil) .nil)))) (.node [signal131,signal162,signal181,signal210,signal241,signal285] (.node [signal125,signal162,signal181,signal210,signal241,signal285] (.node [signal122,signal162,signal181,signal210,signal241,signal285] (.node [signal121,signal162,signal181,signal210,signal271,signal285] (.node [signal121,signal162,signal181,signal210,signal241,signal286] .nil .nil) (.node [signal121,signal162,signal181,signal210,signal278,signal285] .nil .nil)) (.node [signal124,signal162,signal181,signal210,signal241,signal285] (.node [signal123,signal162,signal181,signal210,signal241,signal285] .nil .nil) .nil)) (.node [signal128,signal162,signal181,signal210,signal241,signal285] (.node [signal127,signal162,signal181,signal210,signal241,signal285] (.node [signal126,signal162,signal181,signal210,signal241,signal285] .nil .nil) .nil) (.node [signal130,signal162,signal181,signal210,signal241,signal285] (.node [signal129,signal162,signal181,signal210,signal241,signal285] .nil .nil) .nil))) (.node [signal133,signal141,signal150,signal181,signal210,signal285] (.node [signal133,signal139,signal162,signal181,signal210,signal285] (.node [signal133,signal137,signal162,signal181,signal210,signal285] (.node [signal133,signal136,signal210,signal241,signal285,signal291] .nil .nil) (.node [signal133,signal138,signal181,signal241,signal285,signal294] .nil .nil)) (.node [signal133,signal140,signal162,signal181,signal210,signal285] (.node [signal133,signal140,signal150,signal181,signal210,signal285] .nil .nil) .nil)) (.node [signal133,signal141,signal162,signal181,signal210,signal285] (.node [signal133,signal141,signal162,signal181,signal198,signal285] (.node [signal133,signal141,signal162,signal169,signal210,signal285] .nil .nil) .nil) (.node [signal133,signal142,signal162,signal181,signal210,signal285] (.node [signal133,signal141,signal181,signal210,signal263,signal285] .nil .nil) .nil))))) (.node [signal133,signal157,signal181,signal210,signal241,signal285] (.node [signal133,signal150,signal181,signal198,signal241] (.node [signal133,signal150,signal162,signal169,signal210,signal241] (.node [signal133,signal147,signal162,signal181,signal210,signal285] (.node [signal133,signal145,signal162,signal181,signal210,signal285] (.node [signal133,signal144,signal162,signal181,signal210,signal285] .nil .nil) (.node [signal133,signal146,signal162,signal181,signal210,signal285] .nil .nil)) (.node [signal133,signal149,signal162,signal181,signal210,signal285] (.node [signal133,signal148,signal162,signal181,signal210,signal285] .nil .nil) .nil)) (.node [signal133,signal150,signal169,signal210,signal241] (.node [signal133,signal150,signal169,signal181,signal210,signal241] (.node [signal133,signal150,signal162,signal181,signal198,signal241] .nil .nil) .nil) (.node [signal133,signal150,signal181,signal198,signal210,signal241] (.node [signal133,signal150,signal169,signal210,signal241,signal285] .nil .nil) .nil))) (.node [signal133,signal151,signal181,signal210,signal241,signal285] (.node [signal133,signal150,signal181,signal210,signal241,signal287] (.node [signal133,signal150,signal181,signal210,signal227,signal285] (.node [signal133,signal150,signal181,signal198,signal241,signal285] .nil .nil) (.node [signal133,signal150,signal181,signal210,signal241,signal285] .nil .nil)) (.node [signal133,signal150,signal181,signal210,signal278,signal285] (.node [signal133,signal150,signal181,signal210,signal271,signal285] .nil .nil) .nil)) (.node [signal133,signal154,signal181,signal210,signal241,signal285] (.node [signal133,signal153,signal181,signal210,signal241,signal285] (.node [signal133,signal152,signal181,signal210,signal241,signal285] .nil .nil) .nil) (.node [signal133,signal156,signal181,signal210,signal241,signal285] (.node [signal133,signal155,signal181,signal210,signal241,signal285] .nil .nil) .nil)))) (.node [signal133,signal162,signal169,signal210,signal241,signal289] (.node [signal133,signal162,signal166,signal210,signal241,signal285] (.node [signal133,signal162,signal165,signal181,signal278,signal285] (.node [signal133,signal159,signal181,signal210,signal241,signal285] (.node [signal133,signal158,signal181,signal210,signal241,signal285] .nil .nil) (.node [signal133,signal160,signal181,signal210,signal241,signal285] .nil .nil)) (.node [signal133,signal162,signal165,signal226,signal241,signal285] (.node [signal133,signal162,signal165,signal210,signal271,signal285] .nil .nil) .nil)) (.node [signal133,signal162,signal169,signal198,signal241,signal285] (.node [signal133,signal162,signal168,signal210,signal271,signal285] (.node [signal133,signal162,signal167,signal181,signal241,signal285] .nil .nil) .nil) (.node [signal133,signal162,signal169,signal210,signal241,signal285] (.node [signal133,signal162,signal169,signal210,signal227,signal285] .nil .nil) .nil))) (.node [signal133,signal162,signal172,signal210,signal241,signal285] (.node [signal133,signal162,signal169,signal210,signal278,signal285] (.node [signal133,signal162,signal169,signal210,signal271,signal285] (.node [signal133,signal162,signal169,signal210,signal270,signal285] .nil .nil) .nil) (.node [signal133,signal162,signal171,signal210,signal241,signal285] (.node [signal133,signal162,signal170,signal210,signal241,signal285] .nil .nil) .nil)) (.node [signal133,signal162,signal175,signal210,signal241,signal285] (.node [signal133,signal162,signal174,signal210,signal241,signal285] (.node [signal133,signal162,signal173,signal210,signal241,signal285] .nil .nil) .nil) (.node [signal133,signal162,signal177,signal210,signal241,signal285] (.node [signal133,signal162,signal176,signal210,signal241,signal285] .nil .nil) .nil)))))) (.node [signal133,signal162,signal181,signal210,signal241,signal282] (.node [signal133,signal162,signal181,signal209,signal241,signal285] (.node [signal133,signal162,signal181,signal198,signal271,signal285] (.node [signal133,signal162,signal181,signal189,signal210,signal285] (.node [signal133,signal162,signal181,signal186,signal210,signal285] (.node [signal133,signal162,signal180,signal210,signal241,signal285] (.node [signal133,signal162,signal179,signal210,signal241,signal285] .nil .nil) (.node [signal133,signal162,signal181,signal185,signal210,signal285] .nil .nil)) (.node [signal133,signal162,signal181,signal188,signal210,signal285] (.node [signal133,signal162,signal181,signal187,signal210,signal285] .nil .nil) .nil)) (.node [signal133,signal162,signal181,signal198,signal227,signal285] (.node [signal133,signal162,signal181,signal197,signal278,signal285] (.node [signal133,signal162,signal181,signal195,signal210,signal285] .nil .nil) .nil) (.node [signal133,signal162,signal181,signal198,signal241,signal292] (.node [signal133,signal162,signal181,signal198,signal241,signal285] .nil .nil) .nil))) (.node [signal133,signal162,signal181,signal203,signal241,signal285] (.node [signal133,signal162,signal181,signal200,signal241,signal285] (.node [signal133,signal162,signal181,signal198,signal278,signal285] (.node [signal133,signal162,signal181,signal198,signal277,signal285] .nil .nil) (.node [signal133,signal162,signal181,signal199,signal241,signal285] .nil .nil)) (.node [signal133,signal162,signal181,signal202,signal241,signal285] (.node [signal133,signal162,signal181,signal201,signal241,signal285] .nil .nil) .nil)) (.node [signal133,signal162,signal181,signal206,signal241,signal285] (.node [signal133,signal162,signal181,signal205,signal241,signal285] (.node [signal133,signal162,signal181,signal204,signal241,signal285] .nil .nil) .nil) (.node [signal133,signal162,signal181,signal208,signal241,signal285] (.node [signal133,signal162,signal181,signal207,signal241,signal285] .nil .nil) .nil)))) (.node [signal133,signal162,signal181,signal210,signal232,signal285] (.node [signal133,signal162,signal181,signal210,signal227,signal285] (.node [signal133,signal162,signal181,signal210,signal217,signal285] (.node [signal133,signal162,signal181,signal210,signal215,signal285] (.node [signal133,signal162,signal181,signal210,signal214,signal285] .nil .nil) (.node [signal133,signal162,signal181,signal210,signal216,signal285] .nil .nil)) (.node [signal133,signal162,signal181,signal210,signal224,signal285] (.node [signal133,signal162,signal181,signal210,signal218,signal285] .nil .nil) .nil)) (.node [signal133,signal162,signal181,signal210,signal229,signal285] (.node [signal133,signal162,signal181,signal210,signal228,signal285] (.node [signal133,signal162,signal181,signal210,signal227,signal295] .nil .nil) .nil) (.node [signal133,signal162,signal181,signal210,signal231,signal285] (.node [signal133,signal162,signal181,signal210,signal230,signal285] .nil .nil) .nil))) (.node [signal133,signal162,signal181,signal210,signal238,signal285] (.node [signal133,signal162,signal181,signal210,signal235,signal285] (.node [signal133,signal162,signal181,signal210,signal234,signal285] (.node [signal133,signal162,signal181,signal210,signal233,signal285] .nil .nil) .nil) (.node [signal133,signal162,signal181,signal210,signal237,signal285] (.node [signal133,signal162,signal181,signal210,signal236,signal285] .nil .nil) .nil)) (.node [signal133,signal162,signal181,signal210,signal241,signal279] (.node [signal133,signal162,signal181,signal210,signal240,signal285] (.node [signal133,signal162,signal181,signal210,signal239,signal285] .nil .nil) .nil) (.node [signal133,signal162,signal181,signal210,signal241,signal281] (.node [signal133,signal162,signal181,signal210,signal241,signal280] .nil .nil) .nil))))) (.node [signal133,signal162,signal181,signal210,signal268,signal285] (.node [signal133,signal162,signal181,signal210,signal252,signal285] (.node [signal133,signal162,signal181,signal210,signal246,signal285] (.node [signal133,signal162,signal181,signal210,signal243,signal285] (.node [signal133,signal162,signal181,signal210,signal241,signal285] (.node [signal133,signal162,signal181,signal210,signal241,signal283] .nil .nil) (.node [signal133,signal162,signal181,signal210,signal242,signal285] .nil .nil)) (.node [signal133,signal162,signal181,signal210,signal245,signal285] (.node [signal133,signal162,signal181,signal210,signal244,signal285] .nil .nil) .nil)) (.node [signal133,signal162,signal181,signal210,signal249,signal285] (.node [signal133,signal162,signal181,signal210,signal248,signal285] (.node [signal133,signal162,signal181,signal210,signal247,signal285] .nil .nil) .nil) (.node [signal133,signal162,signal181,signal210,signal251,signal285] (.node [signal133,signal162,signal181,signal210,signal250,signal285] .nil .nil) .nil))) (.node [signal133,signal162,signal181,signal210,signal259,signal285] (.node [signal133,signal162,signal181,signal210,signal256,signal285] (.node [signal133,signal162,signal181,signal210,signal254,signal285] (.node [signal133,signal162,signal181,signal210,signal253,signal285] .nil .nil) (.node [signal133,signal162,signal181,signal210,signal255,signal285] .nil .nil)) (.node [signal133,signal162,signal181,signal210,signal258,signal285] (.node [signal133,signal162,signal181,signal210,signal257,signal285] .nil .nil) .nil)) (.node [signal133,signal162,signal181,signal210,signal264,signal285] (.node [signal133,signal162,signal181,signal210,signal262,signal285] (.node [signal133,signal162,signal181,signal210,signal261,signal285] .nil .nil) .nil) (.node [signal133,signal162,signal181,signal210,signal266,signal285] (.node [signal133,signal162,signal181,signal210,signal265,signal285] .nil .nil) .nil)))) (.node [signal133,signal162,signal181,signal213,signal241,signal285] (.node [signal133,signal162,signal181,signal210,signal276,signal285] (.node [signal133,signal162,signal181,signal210,signal272,signal285] (.node [signal133,signal162,signal181,signal210,signal270,signal285] (.node [signal133,signal162,signal181,signal210,signal269,signal285] .nil .nil) (.node [signal133,signal162,signal181,signal210,signal271,signal285] .nil .nil)) (.node [signal133,signal162,signal181,signal210,signal275,signal285] (.node [signal133,signal162,signal181,signal210,signal273,signal285] .nil .nil) .nil)) (.node [signal133,signal162,signal181,signal210,signal285,signal296] (.node [signal133,signal162,signal181,signal210,signal278,signal285] (.node [signal133,signal162,signal181,signal210,signal277,signal285] .nil .nil) .nil) (.node [signal133,signal162,signal181,signal212,signal241,signal285] (.node [signal133,signal162,signal181,signal211,signal241,signal285] .nil .nil) .nil))) (.node [signal133,signal162,signal195,signal210,signal241,signal285] (.node [signal133,signal162,signal182,signal210,signal241,signal285] (.node [signal133,signal162,signal181,signal224,signal285] (.node [signal133,signal162,signal181,signal224,signal241,signal285] .nil .nil) .nil) (.node [signal133,signal162,signal184,signal210,signal241,signal285] (.node [signal133,signal162,signal183,signal210,signal241,signal285] .nil .nil) .nil)) (.node [signal133,signal164,signal181,signal210,signal241,signal285] (.node [signal133,signal163,signal181,signal210,signal241,signal285] (.node [signal133,signal162,signal195,signal210,signal285] .nil .nil) .nil) (.node [signal135,signal162,signal181,signal210,signal241,signal285] (.node [signal134,signal162,signal181,signal210,signal241,signal285] .nil .nil) .nil))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok5 : everyKey (rowOK 4 layer4) layer5=true := by decide +kernel
theorem closed5 : Closed 5 layer5 := closed_next 4 (by decide) _ _ closed4 ok5
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer6 : BinaryTree (List W) := (.node [signal106,signal133,signal162,signal181,signal210,signal241,signal285] (.node [signal43,signal133,signal162,signal181,signal210,signal241,signal285] (.node [signal19,signal133,signal162,signal181,signal210,signal241,signal285] (.node [signal4,signal133,signal162,signal181,signal210,signal241,signal285] (.node [signal2,signal133,signal162,signal181,signal210,signal241,signal285] (.node [signal1,signal133,signal162,signal181,signal210,signal241,signal285] (.node [signal0,signal133,signal162,signal181,signal210,signal241,signal285] .nil .nil) .nil) (.node [signal3,signal133,signal162,signal181,signal210,signal241,signal285] .nil .nil)) (.node [signal17,signal133,signal162,signal181,signal210,signal241,signal285] (.node [signal14,signal133,signal162,signal181,signal210,signal285] (.node [signal14,signal133,signal162,signal181,signal210,signal241,signal285] .nil .nil) .nil) (.node [signal17,signal133,signal162,signal181,signal210,signal285] .nil .nil))) (.node [signal39,signal133,signal162,signal181,signal210,signal241,signal285] (.node [signal21,signal133,signal162,signal181,signal210,signal285] (.node [signal21,signal133,signal162,signal181,signal210,signal241,signal285] (.node [signal20,signal133,signal162,signal181,signal210,signal241,signal285] .nil .nil) .nil) (.node [signal34,signal133,signal162,signal181,signal210,signal241,signal285] .nil .nil)) (.node [signal41,signal133,signal162,signal181,signal241,signal285] (.node [signal41,signal133,signal162,signal181,signal210,signal241,signal285] (.node [signal39,signal133,signal162,signal181,signal210,signal285] .nil .nil) .nil) (.node [signal42,signal133,signal162,signal181,signal210,signal241,signal285] .nil .nil)))) (.node [signal75,signal133,signal181,signal210,signal241,signal285] (.node [signal60,signal133,signal162,signal210,signal241,signal285] (.node [signal58,signal133,signal162,signal181,signal210,signal285] (.node [signal58,signal133,signal162,signal181,signal210,signal241,signal285] (.node [signal53,signal133,signal162,signal181,signal210,signal241,signal285] .nil .nil) .nil) (.node [signal60,signal133,signal162,signal181,signal210,signal241,signal285] .nil .nil)) (.node [signal74,signal133,signal162,signal181,signal210,signal241,signal285] (.node [signal62,signal133,signal162,signal181,signal210,signal241,signal285] (.node [signal61,signal133,signal162,signal181,signal210,signal241,signal285] .nil .nil) .nil) (.node [signal75,signal133,signal162,signal181,signal210,signal241,signal285] .nil .nil))) (.node [signal90,signal133,signal162,signal181,signal210,signal241,signal285] (.node [signal78,signal133,signal162,signal181,signal210,signal241,signal285] (.node [signal77,signal133,signal162,signal181,signal210,signal241,signal285] (.node [signal76,signal133,signal162,signal181,signal210,signal241,signal285] .nil .nil) .nil) (.node [signal89,signal133,signal162,signal181,signal210,signal241,signal285] .nil .nil)) (.node [signal92,signal133,signal162,signal181,signal210,signal241,signal285] (.node [signal91,signal133,signal162,signal181,signal210,signal241,signal285] (.node [signal90,signal162,signal181,signal210,signal241,signal285] .nil .nil) .nil) (.node [signal93,signal133,signal162,signal181,signal210,signal241,signal285] .nil .nil))))) (.node [signal133,signal162,signal181,signal210,signal226,signal241,signal285] (.node [signal133,signal141,signal162,signal181,signal210,signal285] (.node [signal121,signal133,signal162,signal181,signal210,signal241,signal285] (.node [signal112,signal133,signal162,signal181,signal210,signal241,signal285] (.node [signal109,signal133,signal162,signal181,signal210,signal241,signal285] (.node [signal107,signal133,signal162,signal181,signal210,signal241,signal285] .nil .nil) .nil) (.node [signal112,signal133,signal162,signal181,signal210,signal285] .nil .nil)) (.node [signal133,signal138,signal162,signal181,signal210,signal241,signal285] (.node [signal133,signal136,signal162,signal181,signal210,signal241,signal285] (.node [signal121,signal162,signal181,signal210,signal241,signal285] .nil .nil) .nil) (.node [signal133,signal141,signal162,signal181,signal210,signal241,signal285] .nil .nil))) (.node [signal133,signal162,signal169,signal181,signal210,signal241,signal285] (.node [signal133,signal162,signal165,signal181,signal210,signal241,signal285] (.node [signal133,signal150,signal181,signal210,signal241,signal285] (.node [signal133,signal150,signal162,signal181,signal210,signal241,signal285] .nil .nil) .nil) (.node [signal133,signal162,signal168,signal181,signal210,signal241,signal285] .nil .nil)) (.node [signal133,signal162,signal181,signal198,signal210,signal241,signal285] (.node [signal133,signal162,signal181,signal197,signal210,signal241,signal285] (.node [signal133,signal162,signal169,signal210,signal241,signal285] .nil .nil) .nil) (.node [signal133,signal162,signal181,signal198,signal241,signal285] .nil .nil)))) (.node [signal133,signal162,signal181,signal210,signal241,signal285,signal289] (.node [signal133,signal162,signal181,signal210,signal241,signal271,signal285] (.node [signal133,signal162,signal181,signal210,signal241,signal260,signal285] (.node [signal133,signal162,signal181,signal210,signal227,signal285] (.node [signal133,signal162,signal181,signal210,signal227,signal241,signal285] .nil .nil) .nil) (.node [signal133,signal162,signal181,signal210,signal241,signal263,signal285] .nil .nil)) (.node [signal133,signal162,signal181,signal210,signal241,signal285,signal287] (.node [signal133,signal162,signal181,signal210,signal241,signal285,signal286] (.node [signal133,signal162,signal181,signal210,signal241,signal278,signal285] .nil .nil) .nil) (.node [signal133,signal162,signal181,signal210,signal241,signal285,signal288] .nil .nil))) (.node [signal133,signal162,signal181,signal210,signal241,signal285,signal294] (.node [signal133,signal162,signal181,signal210,signal241,signal285,signal292] (.node [signal133,signal162,signal181,signal210,signal241,signal285,signal291] (.node [signal133,signal162,signal181,signal210,signal241,signal285,signal290] .nil .nil) .nil) (.node [signal133,signal162,signal181,signal210,signal241,signal285,signal293] .nil .nil)) (.node [signal133,signal162,signal181,signal210,signal271,signal285] (.node [signal133,signal162,signal181,signal210,signal241,signal285,signal295] .nil .nil) (.node [signal133,signal162,signal181,signal210,signal278,signal285] .nil .nil))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok6 : everyKey (rowOK 5 layer5) layer6=true := by decide +kernel
theorem closed6 : Closed 6 layer6 := closed_next 5 (by decide) _ _ closed5 ok6
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer7 : BinaryTree (List W) := (.node [signal133,signal162,signal181,signal210,signal241,signal285] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok7 : everyKey (rowOK 6 layer6) layer7=true := by decide +kernel
theorem closed7 : Closed 7 layer7 := closed_next 6 (by decide) _ _ closed6 ok7
def table : ℕ := 2826993792 * 2 ^ 32 + 2826993664
theorem row : ∀j : Fin 72, Nat.testBit table (∑i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i:ℕ) else 0)=goal[j.val] := by decide +kernel
theorem reject : ∀z, z=goal ∨ z = ~~~goal → ¬build basicOps z 7 ins.toFinset := no_build 7 layer7 ins (by decide) (by decide) closed7 (by decide +kernel)
open PEqualNP.CircuitLowerBounds
def monoGates : List Gate := [⟨.or,[2,1]⟩,⟨.and,[0,6]⟩,⟨.and,[2,1]⟩,⟨.or,[4,5]⟩,⟨.or,[4,8]⟩,⟨.and,[7,10]⟩,⟨.and,[8,9]⟩,⟨.or,[3,12]⟩,⟨.and,[13,11]⟩]
theorem upper : ∃(gs : List Gate) (o : ℕ), (∀g∈gs,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2) ∧ gs.length=9 ∧ ∀x : Fin 6 → Bool,Circuit.eval ⟨gs,o⟩ (List.ofFn x)=Nat.testBit table (∑i : Fin 6,if x i then 2^(i:ℕ) else 0) := ⟨monoGates,14,by simp [monoGates],rfl,by decide +kernel⟩
end PEqualNP.Outside.L_meta_15091

open PEqualNP.Outside.L_meta_15091 in
theorem PEqualNP.Outside.L_meta_15091 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (2826993792 * 2 ^ 32 + 2826993664) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (2826993792 * 2 ^ 32 + 2826993664) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro s h
  obtain ⟨C, hfan, hsize, hev⟩ := h
  obtain ⟨gates, o⟩ := C
  have hleg : ∀ g ∈ gates, legal g := by
    intro g hg
    obtain ⟨hop, cap⟩ := hfan g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    exact ⟨hop, cap⟩
  obtain ⟨ds, p, mono, len, ev⟩ := replace table 9 ins (by decide) row rfl reject upper gates o hleg hev
  refine ⟨⟨ds, p⟩, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨hop, cap⟩ := mono g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact ⟨hop, cap⟩
  · exact le_trans len hsize
  · exact ev
