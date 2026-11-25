import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_13543_aux

-- SPDX-License-Identifier: Apache-2.0
-- The finite search checker and circuit semantics adapt L_meta_8639
-- by tacyon52 in open-goat/pequalnp-proofs pull request 12794.
-- The sampled rows and search states below are for this six-input function.

-- Adapted from Sam Lentz's L-meta-1423 (PR 3033), Apache-2.0.
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

-- The upper and lower halves represent opposite target labels on 54 pairs of assignments.
abbrev W := BitVec 108
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 54 := ((x >>> 54) ^^^ x).setWidth 54
def cuts (ws : List W) : BitVec 54 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 54) ++ (0 : BitVec 54)
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

def differs (i : Fin 54) (w : W) : Prop :=
  w.getLsbD (54+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 54) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 54+i.val < 108 := by omega
  have hi' : i.val < 108 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 54) :
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
  change (cuts ws)[j] = (BitVec.allOnes 54)[j]
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
  · change reachable av (BitVec.allOnes 108 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 108)
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

private def bit (k : Fin 108) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 108) :
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

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 108) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#108)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
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
    (row : ∀ j : Fin 108, Nat.testBit T (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
    (width : ins.length = 6) (rejection : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z n ins.toFinset)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 6, if x i then 2^(i : ℕ) else 0)) : n < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ ins, holds ins.toFinset u := fun u hu =>
    .inr (.inr ⟨u,List.mem_toFinset.mpr hu,.inl rfl⟩)
  have evaluate (k : Fin 108) :
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

def v0 : W := 0x2b64d97c0000001d9003f
def v1 : W := 0x51f9b33800000001eedc6
def v2 : W := 0x63a9c3680000019e0f1f8
def v3 : W := 0x6beddb7c0000019f9f1ff
def v4 : W := 0x73f9f3780000019fefdfe
def v5 : W := 0x7a55f854000001e00fe00
def v6 : W := 0x7bfd2200000001fff0000
def v7 : W := 0x7bfde368000001ffff1f8
def v8 : W := 0x7bfdfb7c0000001dfedff
def v9 : W := 0x7bfdfb7c000001fe0fff8
def v10 : W := 0x4dd8000d9fc000036000003f
def v11 : W := 0x92200020400000e08000edc0
def v12 : W := 0x9ae00029538000e38000edc6
def v13 : W := 0xd368002c5e80030c0000f1f8
def v14 : W := 0xdbe8002d5f8003ef8000fdfe
def v15 : W := 0xdc90002d854003f00000fe00
def v16 : W := 0xdef0002dd7c003f38000ffc6
def v17 : W := 0xdff80020480003ffe0000000
def v18 : W := 0xdff800295b8003ffe000edc6
def v19 : W := 0xdff8002ddfc000e3e000edff
def v20 : W := 0xdff8002ddfc003fc0000fff8
def v21 : W := 0xdfffbff2680003ffffff0000
def v22 : W := 0x3008c016091380c00300180006
def v23 : W := 0x309ae016295380c0e38018edc6
def v24 : W := 0x51014852001a80cc0361d9003f
def v25 : W := 0x9402601a807280f003801e01c6
def v26 : W := 0xd500005a802003fc0001ff0000
def v27 : W := 0xd501485a803a80fc0361df003f
def v28 : W := 0xd501485a803a83fc0361ff003f
def v29 : W := 0xd5036840004803fc0fe0000000
def v30 : W := 0xd503685a807a80fc03e1df01ff
def v31 : W := 0xd503685a807a83000c01e001f8
def v32 : W := 0xd5036fe55fcd43fc0ffe00fe00
def v33 : W := 0xd5d3685aac7e83030c01e0f1f8
def v34 : W := 0xd5dc905aada543fff001fffe00
def v35 : W := 0xd5dff840204803ffffe0000000
def v36 : W := 0x1220c9084418140cc0360190007
def v37 : W := 0x228288105030100f0e3801e0c06
def v38 : W := 0x32a20018542000cfc00061f0000
def v39 : W := 0x32a2007bfd2200cfc001fff0000
def v40 : W := 0x32a2c900000000cfcf3e0000000
def v41 : W := 0x32a2c910503010cfcf3e01e0c06
def v42 : W := 0x32a2c9185438140fce3e01f0c07
def v43 : W := 0x32a2c918543814c00f006000e00
def v44 : W := 0x32a2c963a9c368cfcf3f9e0f1f8
def v45 : W := 0x32a2c97a55f854c00f01e00fe00
def v46 : W := 0x32af369856e5e8cff0c061ff1f8
def v47 : W := 0x3ff2ff9dfc3fbcf00fc07e00ff8
def v48 : W := 0x441410a60040c33030c19e01038
def v49 : W := 0x451414a720c1e80000001c00038
def v50 : W := 0x5024412a044847c03101e001200
def v51 : W := 0x5224c92a44d8540000000000000
def v52 : W := 0x5430002e040003f0c001fe10000
def v53 : W := 0x543410ae0440c3f0f0c1fe11038
def v54 : W := 0x54345184000083f0f1c60000000
def v55 : W := 0x543451ae0448c400c0061c10039
def v56 : W := 0x543451ae0448c7f031c1fe01238
def v57 : W := 0x543451d5f9b3bbf0f1c601eedc6
def v58 : W := 0x5434ddae04d9fc00c0361c1003f
def v59 : W := 0x5439ae2e06953bf0ce39fe1edc6
def v60 : W := 0x543dff84020483f0fffe0000000
def v61 : W := 0x5730002f6400000cc0001d90000
def v62 : W := 0x5734dd840000800cc0360000000
def v63 : W := 0x5734ddaf64d9fc0000001c00038
def v64 : W := 0x5734ddaf64d9fc0cc0361d9003f
def v65 : W := 0x573dff840204800cfffe0000000
def v66 : W := 0x573dffaf66ddfc0cce3e1d9edff
def v67 : W := 0x5964672bac4f6fcf3139e1e13c6
def v68 : W := 0x669698b65070d33f3ef99fe1c3e
def v69 : W := 0x72a6c93a547857c03f01e001e00
def v70 : W := 0x72a6c93a54f854c00f006000e00
def v71 : W := 0x884922408b06033030c1820f1c0
def v72 : W := 0x89492641ab8728000000000e1c0
def v73 : W := 0x8d5936c5ab07ab3030c19e0f1f8
def v74 : W := 0x8d5936c5ab87a83000c01e0e1f8
def v75 : W := 0x9a69eb48cf1e173cf0f7839f1c7
def v76 : W := 0xa08b0050132003c03f01e00fe00
def v77 : W := 0xa28b885053b010000e00000ec00
def v78 : W := 0xa59b14d53321abccff37fd9fe3f
def v79 : W := 0xa8c200509922000300000060000
def v80 : W := 0xa8c20050992203f30001e260000
def v81 : W := 0xa8c2007bfd2203f30001fff0000
def v82 : W := 0xa8c6ddd099fbfff30037e26003f
def v83 : W := 0xa8cb2200020403f33fc80000000
def v84 : W := 0xa8cb222b66dd7ff33fc81d9003f
def v85 : W := 0xa8cb22509b2600030e08006edc0
def v86 : W := 0xa8cb22509b2603f03fc1e20ffc0
def v87 : W := 0xa8cb2251fbb738030e0801eedc6
def v88 : W := 0xa9cb2651bb27280f0e3801eedc6
def v89 : W := 0xa9cb2651bba728030e08006edc0
def v90 : W := 0xabc20051f922000f000001e0000
def v91 : W := 0xabc20051f92203ff0001e3e0000
def v92 : W := 0xabc2007bfd22000f0001fff0000
def v93 : W := 0xabc28c51f9b3380f003001e0006
def v94 : W := 0xabcb2651fba7280f000001ee1c0
def v95 : W := 0xabcbae000204000f0e380000000
def v96 : W := 0xabcbae51fbb738000e00000edc0
def v97 : W := 0xabcbae51fbb7380f0e3801eedc6
def v98 : W := 0xadd20055b92203ffc001fff0000
def v99 : W := 0xaddb3684020483fffffe0000000
def v100 : W := 0xafd20055f922003fc0001ff0000
def v101 : W := 0xafdbbe840204803fcefe0000000
def v102 : W := 0xbae20058dd2203ffc001e3f0000
def v103 : W := 0xbbe20059fd2200cfc00061f0000
def v104 : W := 0xbbebef59ffbf3c0fce3e01fedc7
def v105 : W := 0xc00d006203c043003001800f000
def v106 : W := 0xcd500067a902033000019e00000
def v107 : W := 0xcd5d36840204833030c00000000
def v108 : W := 0xcd5d36840204833ff0fe0000000
def v109 : W := 0xcd5d3685aa07ab3030c01e001f8
def v110 : W := 0xcd5d36c5ab87ab3030c0000e1c0
def v111 : W := 0xcd5d36e7abc7e80000001c0e1f8
def v112 : W := 0xcd5d36e7abc7eb3030c19e0f1f8
def v113 : W := 0xcd5d36ffffffff3030c1fe0fff8
def v114 : W := 0xcd5dff84020483303ffe0000000
def v115 : W := 0xdd7d7784020483f0f1c60000000
def v116 : W := 0xdd7d77efafcfeff031c1fe0f3f8
def v117 : W := 0xdf7dff840204833cf0f60000000
def v118 : W := 0xdf7dffefefdfff3030c19e0f1f8
def v119 : W := 0xdf7dffefefdfff3cf0f79f9f1ff
def v120 : W := 0xedd20077b92203f30001fe60000
def v121 : W := 0xeddf3684020483f33fc80000000
def v122 : W := 0xeddf36d49b2683f330c1e260000
def v123 : W := 0xefd20077f922033f00019fe0000
def v124 : W := 0xefdf36d5fb26833f30c001e0000
def v125 : W := 0xefdfbe840204833f3ef80000000
def v126 : W := 0xefdfbef7fbf7fb3f3ef99fefdfe
def v127 : W := 0xf2a2007a552003c00001e000000
def v128 : W := 0xf2a2007bfd2203c00001fff0000
def v129 : W := 0xf2a6c97a55f8540000000000000
def v130 : W := 0xf2a6c97a55f857c00001e000000
def v131 : W := 0xf2afc900020003c03f000000000
def v132 : W := 0xf2afc97a57f854000e00000ec00
def v133 : W := 0xf2afc97a57f857c03f01e00fe00
def v134 : W := 0xf7bfddff77f9ffccff37fd9fe3f
def v135 : W := 0xfae2007add2203f30001e260000
def v136 : W := 0xfaefeb7adffe57f03fc1e20ffc0
def v137 : W := 0xfbe2007bfd2203cf0001e1e0000
def v138 : W := 0xfbefef7bffff7c0f0e3801eedc6
def v139 : W := 0xfbefef7bffff7fc03f01e00ffc0
def v140 : W := 0xfbefef7bffff7fcf3f39e1effc6
def v141 : W := 0xfcf2007e9d2203f3c001fe70000
def v142 : W := 0xfcff7384020483f3ffce0000000
def v143 : W := 0xfcff73fe9f6ec403ce0e1c7edf9
def v144 : W := 0xfff20004000003ffc0000000000
def v145 : W := 0xfff20054992203ffc001e260000
def v146 : W := 0xfff20055f92203ffc00001e0000
def v147 : W := 0xfff2007ffd22000fc0001df0000
def v148 : W := 0xfff2007ffd2203f00001fe00000
def v149 : W := 0xfff2007ffd2203ffc001fff0000
def v150 : W := 0xfff2007ffdfb7fffc001fff003f
def v151 : W := 0xfff214fffd23abffc037fff003f
def v152 : W := 0xfff236fffd2683ffc0fffff0000
def v153 : W := 0xfff28c7ffdb33bffc031fff0006
def v154 : W := 0xfff2c97ffd3a17ffc037fff0007
def v155 : W := 0xfff610fffd62c3fff0c1fff1038
def v156 : W := 0xfff614fffde3ebffc001fff0038
def v157 : W := 0xfff6417ffd6a47fff101fff1200
def v158 : W := 0xfff651fffd2283fff1c7fff0000
def v159 : W := 0xfff651fffd6ac7ffc007fff0039
def v160 : W := 0xfff6c97ffdfa57ffc001fff0000
def v161 : W := 0xfff6ddfffd2283ffc037fff0000
def v162 : W := 0xfff6ddfffdfbfc0fc0361df003f
def v163 : W := 0xfff6ddfffdfbffffc037fff003f
def v164 : W := 0xfffbae7fffb73bffce39fffedc6
def v165 : W := 0xffff3684020483fff0c00000000
def v166 : W := 0xffff36ffff2683fff0c1fff0000
def v167 : W := 0xffff36ffffe7ebf030c1fe0f1f8
def v168 : W := 0xffff36ffffe7ebfff0c1ffff1f8
def v169 : W := 0xffffc97ffffa57ffff01ffffe00
def v170 : W := 0xffffff840204800fce3e0000000
def v171 : W := 0xffffff84020483f03fc00000000
def v172 : W := 0xffffff84020483fffffe0000000
def v173 : W := 0xffffff856295bbfffffe0180006
def v174 : W := 0xffffff8c461c97fffffe0190007
def v175 : W := 0xffffff94523493fffffe01e0c06
def v176 : W := 0xffffff9c562483fffffe61f0000
def v177 : W := 0xffffff9c563c97fffffe6000e00
def v178 : W := 0xffffffae064cc7ffffffe001200
def v179 : W := 0xffffffae46dcd7fffffe0000000
def v180 : W := 0xffffffaf66ddfffffffe1d9003f
def v181 : W := 0xffffffd49b2683ffffffe260000
def v182 : W := 0xffffffd5fb2683fffffe01e0000
def v183 : W := 0xffffffd5fbb7b80fce3e01eedc6
def v184 : W := 0xffffffd5fbb7bbfffffe01eedc6
def v185 : W := 0xffffffe7abc7ebffffff9e0f1f8
def v186 : W := 0xfffffffe572483ffffffe000000
def v187 : W := 0xfffffffe57fcd7f03fc1e00fe00
def v188 : W := 0xfffffffe57fcd7ffffffe00fe00
def v189 : W := 0xffffffffff2683fffffffff0000
def v190 : W := 0xfffffffffffffc0fce3e1dfedff
def v191 : W := 0xfffffffffffffff03fc1fe0fff8

def ins : List W := [v64, v97, v112, v133, v149, v172]
theorem sampled : ∀ j : Fin 108, Nat.testBit 0xeee0eae0eec0aa80 (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
def level0 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level0_ok : everyKey (fun q => !doneTest q) level0 = true := by decide +kernel
theorem closed0 : Closed 0 level0 := closed_nil level0 level0_ok
def level1 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level1_ok : everyKey (rowOK 0 level0) level1 = true := by decide +kernel
theorem closed1 : Closed 1 level1 := closed_next 0 (by decide) level1 level0 closed0 level1_ok
def level2 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level2_ok : everyKey (rowOK 1 level1) level2 = true := by decide +kernel
theorem closed2 : Closed 2 level2 := closed_next 1 (by decide) level2 level1 closed1 level2_ok
def level3 : BinaryTree (List W) := (.node [v72, v107, v133, v162] (.node [v64, v72, v124, v133] .nil .nil) .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level3_ok : everyKey (rowOK 2 level2) level3 = true := by decide +kernel
theorem closed3 : Closed 3 level3 := closed_next 2 (by decide) level3 level2 closed2 level3_ok
def level4lll : BinaryTree (List W) := (.node [v21, v64, v97, v112, v133] (.node [v2, v97, v112, v133, v162] .nil .nil) (.node [v27, v97, v112, v162, v172] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lll_ok : everyKey (rowOK 3 level3) level4lll = true := by decide +kernel
def level4llr : BinaryTree (List W) := (.node [v44, v64, v97, v133, v149] (.node [v34, v64, v97, v112, v172] .nil .nil) (.node [v46, v64, v97, v133, v172] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llr_ok : everyKey (rowOK 3 level3) level4llr = true := by decide +kernel
def level4ll : BinaryTree (List W) := .node [v32, v64, v97, v112, v149] level4lll level4llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4ll_ok : everyKey (rowOK 3 level3) level4ll = true := by
  change (_ && everyKey (rowOK 3 level3) level4lll && everyKey (rowOK 3 level3) level4llr) = true
  rw [level4lll_ok, level4llr_ok]
  decide +kernel
def level4lrl : BinaryTree (List W) := (.node [v57, v64, v112, v133, v149] (.node [v48, v112, v133, v162, v172] .nil .nil) (.node [v59, v64, v112, v133, v172] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrl_ok : everyKey (rowOK 3 level3) level4lrl = true := by decide +kernel
def level4lrr : BinaryTree (List W) := (.node [v64, v68, v133, v149, v172] (.node [v64, v67, v112, v149, v172] .nil .nil) (.node [v64, v72, v90, v107, v133] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrr_ok : everyKey (rowOK 3 level3) level4lrr = true := by decide +kernel
def level4lr : BinaryTree (List W) := .node [v60, v97, v112, v133, v162] level4lrl level4lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lr_ok : everyKey (rowOK 3 level3) level4lr = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrl && everyKey (rowOK 3 level3) level4lrr) = true
  rw [level4lrl_ok, level4lrr_ok]
  decide +kernel
def level4l : BinaryTree (List W) := .node [v47, v64, v97, v149, v172] level4ll level4lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4l_ok : everyKey (rowOK 3 level3) level4l = true := by
  change (_ && everyKey (rowOK 3 level3) level4ll && everyKey (rowOK 3 level3) level4lr) = true
  rw [level4ll_ok, level4lr_ok]
  decide +kernel
def level4rll : BinaryTree (List W) := (.node [v64, v97, v112, v122, v133] (.node [v64, v97, v107, v139, v149] .nil .nil) (.node [v64, v97, v112, v124, v133] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rll_ok : everyKey (rowOK 3 level3) level4rll = true := by decide +kernel
def level4rlr : BinaryTree (List W) := (.node [v75, v97, v133, v149, v172] (.node [v72, v112, v133, v162, v172] .nil .nil) (.node [v78, v97, v112, v149, v172] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlr_ok : everyKey (rowOK 3 level3) level4rlr = true := by decide +kernel
def level4rl : BinaryTree (List W) := .node [v64, v97, v112, v166, v187] level4rll level4rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rl_ok : everyKey (rowOK 3 level3) level4rl = true := by
  change (_ && everyKey (rowOK 3 level3) level4rll && everyKey (rowOK 3 level3) level4rlr) = true
  rw [level4rll_ok, level4rlr_ok]
  decide +kernel
def level4rrl : BinaryTree (List W) := (.node [v93, v112, v133, v172, v190] (.node [v84, v97, v112, v133, v149] .nil .nil) (.node [v97, v107, v112, v133, v162] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrl_ok : everyKey (rowOK 3 level3) level4rrl = true := by decide +kernel
def level4rrr : BinaryTree (List W) := (.node [v97, v112, v133, v162, v182] (.node [v97, v112, v133, v162, v172] .nil .nil) (.node [v112, v133, v143, v149, v172] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrr_ok : everyKey (rowOK 3 level3) level4rrr = true := by decide +kernel
def level4rr : BinaryTree (List W) := .node [v97, v112, v129, v162, v172] level4rrl level4rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rr_ok : everyKey (rowOK 3 level3) level4rr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrl && everyKey (rowOK 3 level3) level4rrr) = true
  rw [level4rrl_ok, level4rrr_ok]
  decide +kernel
def level4r : BinaryTree (List W) := .node [v82, v97, v112, v133, v172] level4rl level4rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4r_ok : everyKey (rowOK 3 level3) level4r = true := by
  change (_ && everyKey (rowOK 3 level3) level4rl && everyKey (rowOK 3 level3) level4rr) = true
  rw [level4rl_ok, level4rr_ok]
  decide +kernel
def level4 : BinaryTree (List W) := .node [v64, v96, v107, v133, v149] level4l level4r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4_ok : everyKey (rowOK 3 level3) level4 = true := by
  change (_ && everyKey (rowOK 3 level3) level4l && everyKey (rowOK 3 level3) level4r) = true
  rw [level4l_ok, level4r_ok]
  decide +kernel
theorem closed4 : Closed 4 level4 := closed_next 3 (by decide) level4 level3 closed3 level4_ok
def level5lllll : BinaryTree (List W) := (.node [v2, v12, v64, v97, v112, v133] (.node [v1, v54, v64, v112, v133, v149] (.node [v0, v83, v97, v112, v133, v149] .nil .nil) .nil) (.node [v2, v64, v80, v97, v112, v133] (.node [v2, v40, v64, v97, v133, v149] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllll_ok : everyKey (rowOK 4 level4) level5lllll = true := by decide +kernel
def level5llllr : BinaryTree (List W) := (.node [v2, v64, v97, v112, v133, v163] (.node [v2, v64, v97, v112, v133, v149] (.node [v2, v64, v97, v107, v133, v149] .nil .nil) .nil) (.node [v4, v64, v97, v112, v133, v149] (.node [v3, v64, v97, v112, v133, v149] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llllr_ok : everyKey (rowOK 4 level4) level5llllr = true := by decide +kernel
def level5llll : BinaryTree (List W) := .node [v2, v64, v90, v97, v112, v133] level5lllll level5llllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llll_ok : everyKey (rowOK 4 level4) level5llll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lllll && everyKey (rowOK 4 level4) level5llllr) = true
  rw [level5lllll_ok, level5llllr_ok]
  decide +kernel
def level5lllrl : BinaryTree (List W) := (.node [v8, v64, v97, v112, v133, v149] (.node [v7, v64, v97, v112, v133, v149] (.node [v6, v17, v64, v97, v112, v133] .nil .nil) .nil) (.node [v10, v80, v97, v112, v133, v172] (.node [v9, v64, v97, v112, v133, v149] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrl_ok : everyKey (rowOK 4 level4) level5lllrl = true := by decide +kernel
def level5lllrr : BinaryTree (List W) := (.node [v12, v64, v97, v107, v112, v133] (.node [v12, v64, v90, v112, v133, v172] (.node [v12, v52, v64, v112, v133, v172] .nil .nil) .nil) (.node [v12, v64, v97, v112, v133, v172] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrr_ok : everyKey (rowOK 4 level4) level5lllrr = true := by decide +kernel
def level5lllr : BinaryTree (List W) := .node [v11, v64, v97, v112, v133, v172] level5lllrl level5lllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllr_ok : everyKey (rowOK 4 level4) level5lllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lllrl && everyKey (rowOK 4 level4) level5lllrr) = true
  rw [level5lllrl_ok, level5lllrr_ok]
  decide +kernel
def level5lll : BinaryTree (List W) := .node [v5, v29, v64, v97, v112, v149] level5llll level5lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lll_ok : everyKey (rowOK 4 level4) level5lll = true := by
  change (_ && everyKey (rowOK 4 level4) level5llll && everyKey (rowOK 4 level4) level5lllr) = true
  rw [level5llll_ok, level5lllr_ok]
  decide +kernel
def level5llrll : BinaryTree (List W) := (.node [v16, v64, v97, v112, v133, v172] (.node [v15, v26, v64, v97, v112, v172] (.node [v14, v64, v97, v112, v133, v172] .nil .nil) .nil) (.node [v19, v64, v97, v112, v133, v172] (.node [v18, v64, v97, v112, v133, v172] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrll_ok : everyKey (rowOK 4 level4) level5llrll = true := by decide +kernel
def level5llrlr : BinaryTree (List W) := (.node [v24, v76, v97, v112, v149, v172] (.node [v23, v64, v97, v112, v133, v172] (.node [v22, v112, v133, v149, v172, v190] .nil .nil) .nil) (.node [v25, v50, v64, v112, v149, v172] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrlr_ok : everyKey (rowOK 4 level4) level5llrlr = true := by decide +kernel
def level5llrl : BinaryTree (List W) := .node [v20, v64, v97, v112, v133, v172] level5llrll level5llrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrl_ok : everyKey (rowOK 4 level4) level5llrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrll && everyKey (rowOK 4 level4) level5llrlr) = true
  rw [level5llrll_ok, level5llrlr_ok]
  decide +kernel
def level5llrrl : BinaryTree (List W) := (.node [v31, v43, v64, v97, v149, v172] (.node [v30, v64, v97, v112, v149, v172] (.node [v28, v64, v97, v112, v163, v172] .nil .nil) .nil) (.node [v33, v64, v97, v133, v149, v172] (.node [v31, v64, v97, v107, v133, v149] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrl_ok : everyKey (rowOK 4 level4) level5llrrl = true := by decide +kernel
def level5llrrr : BinaryTree (List W) := (.node [v37, v64, v97, v107, v133, v149] (.node [v37, v48, v64, v133, v149, v172] (.node [v36, v71, v97, v133, v149, v172] .nil .nil) .nil) (.node [v39, v64, v97, v107, v112, v133] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrr_ok : everyKey (rowOK 4 level4) level5llrrr = true := by decide +kernel
def level5llrr : BinaryTree (List W) := .node [v35, v64, v97, v112, v133, v149] level5llrrl level5llrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrr_ok : everyKey (rowOK 4 level4) level5llrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrrl && everyKey (rowOK 4 level4) level5llrrr) = true
  rw [level5llrrl_ok, level5llrrr_ok]
  decide +kernel
def level5llr : BinaryTree (List W) := .node [v28, v64, v97, v112, v149, v172] level5llrl level5llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llr_ok : everyKey (rowOK 4 level4) level5llr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrl && everyKey (rowOK 4 level4) level5llrr) = true
  rw [level5llrl_ok, level5llrr_ok]
  decide +kernel
def level5ll : BinaryTree (List W) := .node [v13, v38, v64, v97, v133, v172] level5lll level5llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5ll_ok : everyKey (rowOK 4 level4) level5ll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lll && everyKey (rowOK 4 level4) level5llr) = true
  rw [level5lll_ok, level5llr_ok]
  decide +kernel
def level5lrlll : BinaryTree (List W) := (.node [v45, v64, v97, v107, v112, v149] (.node [v42, v64, v97, v133, v149, v172] (.node [v41, v64, v97, v133, v149, v172] .nil .nil) .nil) (.node [v48, v64, v90, v112, v133, v172] (.node [v45, v64, v97, v112, v149, v172] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlll_ok : everyKey (rowOK 4 level4) level5lrlll = true := by decide +kernel
def level5lrllr : BinaryTree (List W) := (.node [v55, v85, v112, v133, v149, v172] (.node [v53, v64, v112, v133, v149, v172] (.node [v51, v97, v112, v134, v149, v172] .nil .nil) .nil) (.node [v55, v97, v112, v133, v163, v172] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrllr_ok : everyKey (rowOK 4 level4) level5lrllr = true := by decide +kernel
def level5lrll : BinaryTree (List W) := .node [v49, v97, v119, v133, v149, v172] level5lrlll level5lrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrll_ok : everyKey (rowOK 4 level4) level5lrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrlll && everyKey (rowOK 4 level4) level5lrllr) = true
  rw [level5lrlll_ok, level5lrllr_ok]
  decide +kernel
def level5lrlrl : BinaryTree (List W) := (.node [v60, v64, v90, v97, v112, v133] (.node [v58, v97, v112, v133, v149, v172] (.node [v58, v90, v97, v112, v133, v172] .nil .nil) .nil) (.node [v61, v97, v112, v133, v163, v172] (.node [v60, v64, v97, v112, v133, v149] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrl_ok : everyKey (rowOK 4 level4) level5lrlrl = true := by decide +kernel
def level5lrlrr : BinaryTree (List W) := (.node [v64, v65, v97, v112, v133, v149] (.node [v64, v65, v80, v97, v112, v133] (.node [v63, v97, v112, v133, v149, v172] .nil .nil) .nil) (.node [v64, v66, v97, v112, v133, v172] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrr_ok : everyKey (rowOK 4 level4) level5lrlrr = true := by decide +kernel
def level5lrlr : BinaryTree (List W) := .node [v62, v97, v112, v133, v149, v180] level5lrlrl level5lrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlr_ok : everyKey (rowOK 4 level4) level5lrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrlrl && everyKey (rowOK 4 level4) level5lrlrr) = true
  rw [level5lrlrl_ok, level5lrlrr_ok]
  decide +kernel
def level5lrl : BinaryTree (List W) := .node [v56, v64, v112, v133, v149, v172] level5lrll level5lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrl_ok : everyKey (rowOK 4 level4) level5lrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrll && everyKey (rowOK 4 level4) level5lrlr) = true
  rw [level5lrll_ok, level5lrlr_ok]
  decide +kernel
def level5lrrll : BinaryTree (List W) := (.node [v64, v72, v97, v107, v133, v149] (.node [v64, v72, v90, v112, v133, v172] (.node [v64, v70, v97, v112, v149, v172] .nil .nil) .nil) (.node [v64, v73, v97, v133, v149, v172] (.node [v64, v72, v126, v133, v149, v172] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrll_ok : everyKey (rowOK 4 level4) level5lrrll = true := by decide +kernel
def level5lrrlr : BinaryTree (List W) := (.node [v64, v80, v97, v107, v112, v133] (.node [v64, v79, v97, v112, v133, v172] (.node [v64, v77, v112, v140, v149, v172] .nil .nil) .nil) (.node [v64, v80, v97, v112, v133, v172] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrlr_ok : everyKey (rowOK 4 level4) level5lrrlr = true := by decide +kernel
def level5lrrl : BinaryTree (List W) := .node [v64, v74, v97, v133, v149, v172] level5lrrll level5lrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrl_ok : everyKey (rowOK 4 level4) level5lrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrll && everyKey (rowOK 4 level4) level5lrrlr) = true
  rw [level5lrrll_ok, level5lrrlr_ok]
  decide +kernel
def level5lrrrl : BinaryTree (List W) := (.node [v64, v88, v112, v133, v149, v172] (.node [v64, v87, v112, v133, v149, v172] (.node [v64, v81, v97, v112, v133, v172] .nil .nil) .nil) (.node [v64, v90, v97, v107, v112, v133] (.node [v64, v89, v112, v133, v149, v172] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrl_ok : everyKey (rowOK 4 level4) level5lrrrl = true := by decide +kernel
def level5lrrrr : BinaryTree (List W) := (.node [v64, v91, v97, v112, v133, v172] (.node [v64, v90, v112, v133, v164, v172] (.node [v64, v90, v97, v112, v133, v182] .nil .nil) .nil) (.node [v64, v92, v97, v112, v133, v172] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrr_ok : everyKey (rowOK 4 level4) level5lrrrr = true := by decide +kernel
def level5lrrr : BinaryTree (List W) := .node [v64, v90, v97, v112, v133, v172] level5lrrrl level5lrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrr_ok : everyKey (rowOK 4 level4) level5lrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrrl && everyKey (rowOK 4 level4) level5lrrrr) = true
  rw [level5lrrrl_ok, level5lrrrr_ok]
  decide +kernel
def level5lrr : BinaryTree (List W) := .node [v64, v80, v97, v112, v133, v181] level5lrrl level5lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrr_ok : everyKey (rowOK 4 level4) level5lrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrl && everyKey (rowOK 4 level4) level5lrrr) = true
  rw [level5lrrl_ok, level5lrrr_ok]
  decide +kernel
def level5lr : BinaryTree (List W) := .node [v64, v69, v97, v112, v149, v172] level5lrl level5lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lr_ok : everyKey (rowOK 4 level4) level5lr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrl && everyKey (rowOK 4 level4) level5lrr) = true
  rw [level5lrl_ok, level5lrr_ok]
  decide +kernel
def level5l : BinaryTree (List W) := .node [v39, v64, v97, v112, v133, v172] level5ll level5lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5l_ok : everyKey (rowOK 4 level4) level5l = true := by
  change (_ && everyKey (rowOK 4 level4) level5ll && everyKey (rowOK 4 level4) level5lr) = true
  rw [level5ll_ok, level5lr_ok]
  decide +kernel
def level5rllll : BinaryTree (List W) := (.node [v64, v96, v112, v133, v149, v172] (.node [v64, v95, v112, v133, v149, v184] (.node [v64, v94, v112, v133, v149, v172] .nil .nil) .nil) (.node [v64, v97, v99, v112, v133, v149] (.node [v64, v97, v98, v112, v133, v172] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllll_ok : everyKey (rowOK 4 level4) level5rllll = true := by decide +kernel
def level5rlllr : BinaryTree (List W) := (.node [v64, v97, v103, v112, v133, v172] (.node [v64, v97, v102, v112, v133, v172] (.node [v64, v97, v101, v112, v133, v149] .nil .nil) .nil) (.node [v64, v97, v106, v133, v168, v172] (.node [v64, v97, v105, v149, v172, v191] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlllr_ok : everyKey (rowOK 4 level4) level5rlllr = true := by decide +kernel
def level5rlll : BinaryTree (List W) := .node [v64, v97, v100, v112, v133, v172] level5rllll level5rlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlll_ok : everyKey (rowOK 4 level4) level5rlll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rllll && everyKey (rowOK 4 level4) level5rlllr) = true
  rw [level5rllll_ok, level5rlllr_ok]
  decide +kernel
def level5rllrl : BinaryTree (List W) := (.node [v64, v97, v107, v112, v149, v187] (.node [v64, v97, v107, v112, v133, v166] (.node [v64, v97, v107, v112, v133, v163] .nil .nil) .nil) (.node [v64, v97, v107, v133, v149, v191] (.node [v64, v97, v107, v133, v149, v185] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrl_ok : everyKey (rowOK 4 level4) level5rllrl = true := by decide +kernel
def level5rllrr : BinaryTree (List W) := (.node [v64, v97, v111, v133, v149, v172] (.node [v64, v97, v110, v133, v149, v172] (.node [v64, v97, v109, v133, v149, v172] .nil .nil) .nil) (.node [v64, v97, v112, v114, v133, v149] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrr_ok : everyKey (rowOK 4 level4) level5rllrr = true := by decide +kernel
def level5rllr : BinaryTree (List W) := .node [v64, v97, v108, v112, v133, v149] level5rllrl level5rllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllr_ok : everyKey (rowOK 4 level4) level5rllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rllrl && everyKey (rowOK 4 level4) level5rllrr) = true
  rw [level5rllrl_ok, level5rllrr_ok]
  decide +kernel
def level5rll : BinaryTree (List W) := .node [v64, v97, v107, v112, v133, v149] level5rlll level5rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rll_ok : everyKey (rowOK 4 level4) level5rll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlll && everyKey (rowOK 4 level4) level5rllr) = true
  rw [level5rlll_ok, level5rllr_ok]
  decide +kernel
def level5rlrll : BinaryTree (List W) := (.node [v64, v97, v112, v121, v133, v149] (.node [v64, v97, v112, v120, v133, v172] (.node [v64, v97, v112, v117, v133, v149] .nil .nil) .nil) (.node [v64, v97, v112, v125, v133, v149] (.node [v64, v97, v112, v123, v133, v172] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrll_ok : everyKey (rowOK 4 level4) level5rlrll = true := by decide +kernel
def level5rlrlr : BinaryTree (List W) := (.node [v64, v97, v112, v130, v163, v172] (.node [v64, v97, v112, v130, v149, v172] (.node [v64, v97, v112, v128, v133, v172] .nil .nil) .nil) (.node [v64, v97, v112, v131, v149, v188] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrlr_ok : everyKey (rowOK 4 level4) level5rlrlr = true := by decide +kernel
def level5rlrl : BinaryTree (List W) := .node [v64, v97, v112, v127, v169, v172] level5rlrll level5rlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrl_ok : everyKey (rowOK 4 level4) level5rlrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrll && everyKey (rowOK 4 level4) level5rlrlr) = true
  rw [level5rlrll_ok, level5rlrlr_ok]
  decide +kernel
def level5rlrrl : BinaryTree (List W) := (.node [v64, v97, v112, v133, v141, v172] (.node [v64, v97, v112, v133, v137, v172] (.node [v64, v97, v112, v133, v135, v172] .nil .nil) .nil) (.node [v64, v97, v112, v133, v144, v189] (.node [v64, v97, v112, v133, v142, v149] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrl_ok : everyKey (rowOK 4 level4) level5rlrrl = true := by decide +kernel
def level5rlrrr : BinaryTree (List W) := (.node [v64, v97, v112, v133, v148, v172] (.node [v64, v97, v112, v133, v147, v172] (.node [v64, v97, v112, v133, v146, v172] .nil .nil) .nil) (.node [v64, v97, v112, v133, v149, v165] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrr_ok : everyKey (rowOK 4 level4) level5rlrrr = true := by decide +kernel
def level5rlrr : BinaryTree (List W) := .node [v64, v97, v112, v133, v145, v172] level5rlrrl level5rlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrr_ok : everyKey (rowOK 4 level4) level5rlrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrrl && everyKey (rowOK 4 level4) level5rlrrr) = true
  rw [level5rlrrl_ok, level5rlrrr_ok]
  decide +kernel
def level5rlr : BinaryTree (List W) := .node [v64, v97, v112, v132, v149, v172] level5rlrl level5rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlr_ok : everyKey (rowOK 4 level4) level5rlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrl && everyKey (rowOK 4 level4) level5rlrr) = true
  rw [level5rlrl_ok, level5rlrr_ok]
  decide +kernel
def level5rl : BinaryTree (List W) := .node [v64, v97, v112, v115, v133, v149] level5rll level5rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rl_ok : everyKey (rowOK 4 level4) level5rl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rll && everyKey (rowOK 4 level4) level5rlr) = true
  rw [level5rll_ok, level5rlr_ok]
  decide +kernel
def level5rrlll : BinaryTree (List W) := (.node [v64, v97, v112, v133, v149, v173] (.node [v64, v97, v112, v133, v149, v172] (.node [v64, v97, v112, v133, v149, v171] .nil .nil) .nil) (.node [v64, v97, v112, v133, v149, v175] (.node [v64, v97, v112, v133, v149, v174] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlll_ok : everyKey (rowOK 4 level4) level5rrlll = true := by decide +kernel
def level5rrllr : BinaryTree (List W) := (.node [v64, v97, v112, v133, v149, v179] (.node [v64, v97, v112, v133, v149, v178] (.node [v64, v97, v112, v133, v149, v177] .nil .nil) .nil) (.node [v64, v97, v112, v133, v149, v181] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrllr_ok : everyKey (rowOK 4 level4) level5rrllr = true := by decide +kernel
def level5rrll : BinaryTree (List W) := .node [v64, v97, v112, v133, v149, v176] level5rrlll level5rrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrll_ok : everyKey (rowOK 4 level4) level5rrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrlll && everyKey (rowOK 4 level4) level5rrllr) = true
  rw [level5rrlll_ok, level5rrllr_ok]
  decide +kernel
def level5rrlrl : BinaryTree (List W) := (.node [v64, v97, v112, v133, v151, v172] (.node [v64, v97, v112, v133, v150, v172] (.node [v64, v97, v112, v133, v149, v186] .nil .nil) .nil) (.node [v64, v97, v112, v133, v153, v172] (.node [v64, v97, v112, v133, v152, v172] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrl_ok : everyKey (rowOK 4 level4) level5rrlrl = true := by decide +kernel
def level5rrlrr : BinaryTree (List W) := (.node [v64, v97, v112, v133, v157, v172] (.node [v64, v97, v112, v133, v156, v172] (.node [v64, v97, v112, v133, v155, v172] .nil .nil) .nil) (.node [v64, v97, v112, v133, v158, v172] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrr_ok : everyKey (rowOK 4 level4) level5rrlrr = true := by decide +kernel
def level5rrlr : BinaryTree (List W) := .node [v64, v97, v112, v133, v154, v172] level5rrlrl level5rrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlr_ok : everyKey (rowOK 4 level4) level5rrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrlrl && everyKey (rowOK 4 level4) level5rrlrr) = true
  rw [level5rrlrl_ok, level5rrlrr_ok]
  decide +kernel
def level5rrl : BinaryTree (List W) := .node [v64, v97, v112, v133, v149, v182] level5rrll level5rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrl_ok : everyKey (rowOK 4 level4) level5rrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrll && everyKey (rowOK 4 level4) level5rrlr) = true
  rw [level5rrll_ok, level5rrlr_ok]
  decide +kernel
def level5rrrll : BinaryTree (List W) := (.node [v64, v97, v112, v133, v162, v172] (.node [v64, v97, v112, v133, v161, v172] (.node [v64, v97, v112, v133, v160, v172] .nil .nil) .nil) (.node [v64, v97, v112, v133, v166, v172] (.node [v64, v97, v112, v133, v163, v172] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrll_ok : everyKey (rowOK 4 level4) level5rrrll = true := by decide +kernel
def level5rrrlr : BinaryTree (List W) := (.node [v64, v97, v113, v133, v149, v172] (.node [v64, v97, v112, v149, v172, v187] (.node [v64, v97, v112, v139, v149, v172] .nil .nil) .nil) (.node [v64, v97, v116, v133, v149, v172] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrlr_ok : everyKey (rowOK 4 level4) level5rrrlr = true := by decide +kernel
def level5rrrl : BinaryTree (List W) := .node [v64, v97, v112, v136, v149, v172] level5rrrll level5rrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrl_ok : everyKey (rowOK 4 level4) level5rrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrll && everyKey (rowOK 4 level4) level5rrrlr) = true
  rw [level5rrrll_ok, level5rrrlr_ok]
  decide +kernel
def level5rrrrl : BinaryTree (List W) := (.node [v64, v112, v133, v138, v149, v172] (.node [v64, v104, v112, v133, v149, v172] (.node [v64, v97, v133, v149, v167, v172] .nil .nil) .nil) (.node [v80, v97, v112, v133, v163, v172] (.node [v64, v112, v133, v149, v172, v183] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrl_ok : everyKey (rowOK 4 level4) level5rrrrl = true := by decide +kernel
def level5rrrrr : BinaryTree (List W) := (.node [v97, v112, v133, v162, v172] (.node [v97, v112, v133, v149, v162, v172] (.node [v90, v97, v112, v133, v162, v172] .nil .nil) .nil) (.node [v97, v112, v133, v163, v172, v190] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrr_ok : everyKey (rowOK 4 level4) level5rrrrr = true := by decide +kernel
def level5rrrr : BinaryTree (List W) := .node [v86, v97, v112, v133, v149, v172] level5rrrrl level5rrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrr_ok : everyKey (rowOK 4 level4) level5rrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrrl && everyKey (rowOK 4 level4) level5rrrrr) = true
  rw [level5rrrrl_ok, level5rrrrr_ok]
  decide +kernel
def level5rrr : BinaryTree (List W) := .node [v64, v97, v118, v133, v149, v172] level5rrrl level5rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrr_ok : everyKey (rowOK 4 level4) level5rrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrl && everyKey (rowOK 4 level4) level5rrrr) = true
  rw [level5rrrl_ok, level5rrrr_ok]
  decide +kernel
def level5rr : BinaryTree (List W) := .node [v64, v97, v112, v133, v159, v172] level5rrl level5rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rr_ok : everyKey (rowOK 4 level4) level5rr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrl && everyKey (rowOK 4 level4) level5rrr) = true
  rw [level5rrl_ok, level5rrr_ok]
  decide +kernel
def level5r : BinaryTree (List W) := .node [v64, v97, v112, v133, v149, v170] level5rl level5rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5r_ok : everyKey (rowOK 4 level4) level5r = true := by
  change (_ && everyKey (rowOK 4 level4) level5rl && everyKey (rowOK 4 level4) level5rr) = true
  rw [level5rl_ok, level5rr_ok]
  decide +kernel
def level5 : BinaryTree (List W) := .node [v64, v93, v97, v112, v133, v172] level5l level5r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5_ok : everyKey (rowOK 4 level4) level5 = true := by
  change (_ && everyKey (rowOK 4 level4) level5l && everyKey (rowOK 4 level4) level5r) = true
  rw [level5l_ok, level5r_ok]
  decide +kernel
theorem closed5 : Closed 5 level5 := closed_next 4 (by decide) level5 level4 closed4 level5_ok
def level6llll : BinaryTree (List W) := (.node [v2, v64, v97, v112, v133, v149] (.node [v1, v64, v97, v112, v133, v149, v172] (.node [v0, v64, v97, v112, v133, v149, v172] .nil .nil) .nil) (.node [v2, v64, v97, v112, v133, v149, v172] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llll_ok : everyKey (rowOK 5 level5) level6llll = true := by decide +kernel
def level6lllr : BinaryTree (List W) := (.node [v10, v64, v97, v112, v133, v149, v172] (.node [v6, v64, v97, v112, v133, v149, v172] .nil .nil) (.node [v12, v64, v97, v112, v133, v149, v172] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllr_ok : everyKey (rowOK 5 level5) level6lllr = true := by decide +kernel
def level6lll : BinaryTree (List W) := .node [v5, v64, v97, v112, v133, v149, v172] level6llll level6lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lll_ok : everyKey (rowOK 5 level5) level6lll = true := by
  change (_ && everyKey (rowOK 5 level5) level6llll && everyKey (rowOK 5 level5) level6lllr) = true
  rw [level6llll_ok, level6lllr_ok]
  decide +kernel
def level6llrl : BinaryTree (List W) := (.node [v15, v64, v97, v112, v133, v149, v172] (.node [v13, v64, v97, v112, v133, v149, v172] .nil .nil) (.node [v17, v64, v97, v112, v133, v149, v172] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrl_ok : everyKey (rowOK 5 level5) level6llrl = true := by decide +kernel
def level6llrr : BinaryTree (List W) := (.node [v25, v64, v97, v112, v133, v149, v172] (.node [v24, v64, v97, v112, v133, v149, v172] .nil .nil) (.node [v26, v64, v97, v112, v133, v149, v172] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrr_ok : everyKey (rowOK 5 level5) level6llrr = true := by decide +kernel
def level6llr : BinaryTree (List W) := .node [v22, v64, v97, v112, v133, v149, v172] level6llrl level6llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llr_ok : everyKey (rowOK 5 level5) level6llr = true := by
  change (_ && everyKey (rowOK 5 level5) level6llrl && everyKey (rowOK 5 level5) level6llrr) = true
  rw [level6llrl_ok, level6llrr_ok]
  decide +kernel
def level6ll : BinaryTree (List W) := .node [v12, v64, v97, v112, v133, v172] level6lll level6llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6ll_ok : everyKey (rowOK 5 level5) level6ll = true := by
  change (_ && everyKey (rowOK 5 level5) level6lll && everyKey (rowOK 5 level5) level6llr) = true
  rw [level6lll_ok, level6llr_ok]
  decide +kernel
def level6lrll : BinaryTree (List W) := (.node [v37, v64, v97, v112, v133, v149, v172] (.node [v36, v64, v97, v112, v133, v149, v172] (.node [v31, v64, v97, v112, v133, v149, v172] .nil .nil) .nil) (.node [v38, v64, v97, v112, v133, v149, v172] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrll_ok : everyKey (rowOK 5 level5) level6lrll = true := by decide +kernel
def level6lrlr : BinaryTree (List W) := (.node [v48, v64, v97, v112, v133, v149, v172] (.node [v43, v64, v97, v112, v133, v149, v172] .nil .nil) (.node [v49, v64, v97, v112, v133, v149, v172] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlr_ok : everyKey (rowOK 5 level5) level6lrlr = true := by decide +kernel
def level6lrl : BinaryTree (List W) := .node [v40, v64, v97, v112, v133, v149, v172] level6lrll level6lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrl_ok : everyKey (rowOK 5 level5) level6lrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrll && everyKey (rowOK 5 level5) level6lrlr) = true
  rw [level6lrll_ok, level6lrlr_ok]
  decide +kernel
def level6lrrl : BinaryTree (List W) := (.node [v52, v64, v97, v112, v133, v149, v172] (.node [v51, v64, v97, v112, v133, v149, v172] .nil .nil) (.node [v54, v64, v97, v112, v133, v149, v172] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrl_ok : everyKey (rowOK 5 level5) level6lrrl = true := by decide +kernel
def level6lrrr : BinaryTree (List W) := (.node [v62, v64, v97, v112, v133, v149, v172] (.node [v61, v64, v97, v112, v133, v149, v172] .nil .nil) (.node [v64, v71, v97, v112, v133, v149, v172] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrr_ok : everyKey (rowOK 5 level5) level6lrrr = true := by decide +kernel
def level6lrr : BinaryTree (List W) := .node [v55, v64, v97, v112, v133, v149, v172] level6lrrl level6lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrr_ok : everyKey (rowOK 5 level5) level6lrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrrl && everyKey (rowOK 5 level5) level6lrrr) = true
  rw [level6lrrl_ok, level6lrrr_ok]
  decide +kernel
def level6lr : BinaryTree (List W) := .node [v50, v64, v97, v112, v133, v149, v172] level6lrl level6lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lr_ok : everyKey (rowOK 5 level5) level6lr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrl && everyKey (rowOK 5 level5) level6lrr) = true
  rw [level6lrl_ok, level6lrr_ok]
  decide +kernel
def level6l : BinaryTree (List W) := .node [v29, v64, v97, v112, v133, v149, v172] level6ll level6lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6l_ok : everyKey (rowOK 5 level5) level6l = true := by
  change (_ && everyKey (rowOK 5 level5) level6ll && everyKey (rowOK 5 level5) level6lr) = true
  rw [level6ll_ok, level6lr_ok]
  decide +kernel
def level6rlll : BinaryTree (List W) := (.node [v64, v80, v97, v112, v133, v149, v172] (.node [v64, v77, v97, v112, v133, v149, v172] (.node [v64, v76, v97, v112, v133, v149, v172] .nil .nil) .nil) (.node [v64, v80, v97, v112, v133, v172] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlll_ok : everyKey (rowOK 5 level5) level6rlll = true := by decide +kernel
def level6rllr : BinaryTree (List W) := (.node [v64, v90, v97, v112, v133, v149, v172] (.node [v64, v85, v97, v112, v133, v149, v172] .nil .nil) (.node [v64, v90, v97, v112, v133, v172] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllr_ok : everyKey (rowOK 5 level5) level6rllr = true := by decide +kernel
def level6rll : BinaryTree (List W) := .node [v64, v83, v97, v112, v133, v149, v172] level6rlll level6rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rll_ok : everyKey (rowOK 5 level5) level6rll = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlll && everyKey (rowOK 5 level5) level6rllr) = true
  rw [level6rlll_ok, level6rllr_ok]
  decide +kernel
def level6rlrl : BinaryTree (List W) := (.node [v64, v97, v106, v112, v133, v149, v172] (.node [v64, v97, v105, v112, v133, v149, v172] .nil .nil) (.node [v64, v97, v107, v112, v133, v149] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrl_ok : everyKey (rowOK 5 level5) level6rlrl = true := by decide +kernel
def level6rlrr : BinaryTree (List W) := (.node [v64, v97, v112, v126, v133, v149, v172] (.node [v64, v97, v112, v119, v133, v149, v172] .nil .nil) (.node [v64, v97, v112, v127, v133, v149, v172] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrr_ok : everyKey (rowOK 5 level5) level6rlrr = true := by decide +kernel
def level6rlr : BinaryTree (List W) := .node [v64, v97, v107, v112, v133, v149, v172] level6rlrl level6rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlr_ok : everyKey (rowOK 5 level5) level6rlr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlrl && everyKey (rowOK 5 level5) level6rlrr) = true
  rw [level6rlrl_ok, level6rlrr_ok]
  decide +kernel
def level6rl : BinaryTree (List W) := .node [v64, v95, v97, v112, v133, v149, v172] level6rll level6rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rl_ok : everyKey (rowOK 5 level5) level6rl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rll && everyKey (rowOK 5 level5) level6rlr) = true
  rw [level6rll_ok, level6rlr_ok]
  decide +kernel
def level6rrll : BinaryTree (List W) := (.node [v64, v97, v112, v133, v140, v149, v172] (.node [v64, v97, v112, v133, v134, v149, v172] .nil .nil) (.node [v64, v97, v112, v133, v144, v149, v172] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrll_ok : everyKey (rowOK 5 level5) level6rrll = true := by decide +kernel
def level6rrlr : BinaryTree (List W) := (.node [v64, v97, v112, v133, v149, v168, v172] (.node [v64, v97, v112, v133, v149, v164, v172] .nil .nil) (.node [v64, v97, v112, v133, v149, v169, v172] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlr_ok : everyKey (rowOK 5 level5) level6rrlr = true := by decide +kernel
def level6rrl : BinaryTree (List W) := .node [v64, v97, v112, v133, v149, v163, v172] level6rrll level6rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrl_ok : everyKey (rowOK 5 level5) level6rrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrll && everyKey (rowOK 5 level5) level6rrlr) = true
  rw [level6rrll_ok, level6rrlr_ok]
  decide +kernel
def level6rrrl : BinaryTree (List W) := (.node [v64, v97, v112, v133, v149, v172, v185] (.node [v64, v97, v112, v133, v149, v172, v184] .nil .nil) (.node [v64, v97, v112, v133, v149, v172, v188] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrl_ok : everyKey (rowOK 5 level5) level6rrrl = true := by decide +kernel
def level6rrrr : BinaryTree (List W) := (.node [v64, v97, v112, v133, v149, v172, v191] (.node [v64, v97, v112, v133, v149, v172, v190] .nil .nil) (.node [v64, v97, v112, v133, v163, v172] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrr_ok : everyKey (rowOK 5 level5) level6rrrr = true := by decide +kernel
def level6rrr : BinaryTree (List W) := .node [v64, v97, v112, v133, v149, v172, v189] level6rrrl level6rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrr_ok : everyKey (rowOK 5 level5) level6rrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrrl && everyKey (rowOK 5 level5) level6rrrr) = true
  rw [level6rrrl_ok, level6rrrr_ok]
  decide +kernel
def level6rr : BinaryTree (List W) := .node [v64, v97, v112, v133, v149, v172, v180] level6rrl level6rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rr_ok : everyKey (rowOK 5 level5) level6rr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrl && everyKey (rowOK 5 level5) level6rrr) = true
  rw [level6rrl_ok, level6rrr_ok]
  decide +kernel
def level6r : BinaryTree (List W) := .node [v64, v97, v112, v131, v133, v149, v172] level6rl level6rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6r_ok : everyKey (rowOK 5 level5) level6r = true := by
  change (_ && everyKey (rowOK 5 level5) level6rl && everyKey (rowOK 5 level5) level6rr) = true
  rw [level6rl_ok, level6rr_ok]
  decide +kernel
def level6 : BinaryTree (List W) := .node [v64, v72, v97, v112, v133, v149, v172] level6l level6r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6_ok : everyKey (rowOK 5 level5) level6 = true := by
  change (_ && everyKey (rowOK 5 level5) level6l && everyKey (rowOK 5 level5) level6r) = true
  rw [level6l_ok, level6r_ok]
  decide +kernel
theorem closed6 : Closed 6 level6 := closed_next 5 (by decide) level6 level5 closed5 level6_ok
def level7 : BinaryTree (List W) := (.node [v64, v97, v112, v133, v149, v172] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7_ok : everyKey (rowOK 6 level6) level7 = true := by decide +kernel
theorem closed7 : Closed 7 level7 := closed_next 6 (by decide) level7 level6 closed6 level7_ok

theorem lower : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z 7 ins.toFinset :=
  @no_build 7 level7 ins (by decide +kernel) (by decide) closed7 (by decide +kernel)

open PEqualNP.MetaComplexity

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit 0xeee0eae0eec0aa80 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem binary_lower (C : Circuit) (hlegal : FanInTwo C)
    (h : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x) :
    8 ≤ binaryCost C.gates := by
  exact Nat.succ_le_of_lt (bound_from_search 0xeee0eae0eec0aa80 7 ins (by decide +kernel)
    sampled rfl lower C.gates C.output hlegal h)

theorem gate_lower (s : ℕ) (h : HasCircuitSize 6 target s) : 8 ≤ s := by
  obtain ⟨C, hlegal, hsize, hcomp⟩ := h
  have hbinary : binaryCost C.gates ≤ C.size := List.length_filter_le _ _
  exact (binary_lower C hlegal hcomp).trans (hbinary.trans hsize)

def witness : Circuit :=
  ⟨[⟨.and, [2, 5]⟩, ⟨.or, [6, 1]⟩, ⟨.or, [6, 4]⟩, ⟨.and, [7, 2]⟩,
    ⟨.and, [8, 1]⟩, ⟨.or, [9, 3]⟩, ⟨.or, [10, 0]⟩, ⟨.and, [12, 11]⟩], 13⟩

theorem witness_mono : Monotone2 witness := by simp [Monotone2, witness]

theorem witness_size : witness.size = 8 := rfl

set_option maxRecDepth 100000 in
theorem witness_correct : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = target x := by
  decide +kernel

end PEqualNP.Outside.L_meta_13543_aux

open PEqualNP.Outside.L_meta_13543_aux in
theorem PEqualNP.Outside.L_meta_13543 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4007717600 * 2 ^ 32 + 4005603968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4007717600 * 2 ^ 32 + 4005603968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  have code : 4007717600 * 2 ^ 32 + 4005603968 = 0xeee0eae0eec0aa80 := by decide
  simp only [code] at h ⊢
  exact ⟨witness, witness_mono, witness_size.le.trans (gate_lower s h), witness_correct⟩
