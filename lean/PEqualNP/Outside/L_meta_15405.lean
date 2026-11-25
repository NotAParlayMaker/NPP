import PEqualNP.Defs

-- The live-wire search and circuit compiler are adapted from tacyon52 in L-meta-8639, pull request 12794 under Apache-2.0.
namespace PEqualNP.Outside.L_meta_15405_aux

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

-- The upper and lower halves represent opposite target labels on 52 pairs of assignments.
abbrev W := BitVec 104
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 52 := ((x >>> 52) ^^^ x).setWidth 52
def cuts (ws : List W) : BitVec 52 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 52) ++ (0 : BitVec 52)
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

def differs (i : Fin 52) (w : W) : Prop :=
  w.getLsbD (52+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 52) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 52+i.val < 104 := by omega
  have hi' : i.val < 104 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 52) :
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
  change (cuts ws)[j] = (BitVec.allOnes 52)[j]
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
  · change reachable av (BitVec.allOnes 104 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 104)
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

private def bit (k : Fin 104) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 104) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 104) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#104)[k.val] = false; simp
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
    (row : ∀ j : Fin 104, Nat.testBit T (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
    (width : ins.length = 6) (rejection : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z n ins.toFinset)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 6, if x i then 2^(i : ℕ) else 0)) : n < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ ins, holds ins.toFinset u := fun u hu =>
    .inr (.inr ⟨u,List.mem_toFinset.mpr hu,.inl rfl⟩)
  have evaluate (k : Fin 104) :
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
    (row : ∀ j : Fin 104, Nat.testBit T (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
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

def v0 : W := 0x2cfcfdf000000006c3cf
def v1 : W := 0x51010000000001b93830
def v2 : W := 0x51010000000006383c30
def v3 : W := 0x51a19150000000383830
def v4 : W := 0x59b5b170000001b93b33
def v5 : W := 0x71e1d5d00000063e3c3c
def v6 : W := 0x79f5f5f0000007bf3f3f
def v7 : W := 0x7d49fc80000007c03fc0
def v8 : W := 0x7de9fdd0000007fe3ffc
def v9 : W := 0x7dfd2820000007ffc000
def v10 : W := 0x7dfdb970000007fffb33
def v11 : W := 0x7dfdfdf0000001bffbff
def v12 : W := 0x7dfdfdf00000063effff
def v13 : W := 0x7dfdfdf0000007f93ff3
def v14 : W := 0x7dfdfdf0000007fffc3c
def v15 : W := 0x5390000d5d00037b00003cf
def v16 : W := 0x98d80029350003838003b33
def v17 : W := 0xdb00002d48000fe00003fc0
def v18 : W := 0xdb90002d5d000ffb0003fcf
def v19 : W := 0xdbd8002020000fff8000000
def v20 : W := 0xdbd8002d7d0003fb8003bff
def v21 : W := 0xdbd8002d7d000c1c0003c3c
def v22 : W := 0xdbd8002d7d000f7f0003fff
def v23 : W := 0xdbd8002d7d000fe38003ff3
def v24 : W := 0xdbdfdff2a2000ffffffc000
def v25 : W := 0x2500b00b401706301b006c00f
def v26 : W := 0x3800d82a003507001c03e003c
def v27 : W := 0x3d00202b400207f00003fc000
def v28 : W := 0x3d00b02b401707f01b03fc00f
def v29 : W := 0x3d00f820002007f01f8000000
def v30 : W := 0x3d00f82b403700c0038390033
def v31 : W := 0x3d00f82b403706f01b83fc03f
def v32 : W := 0x3d00f82b403707301f03ec03f
def v33 : W := 0x3d00f82b403707f01c03fc03c
def v34 : W := 0x3d00fff49fe807f01ffc03fc0
def v35 : W := 0x3ddb202b6d4a07ffe003fffc0
def v36 : W := 0x3ddbf820202007ffff8000000
def v37 : W := 0x105202081420230c3839810303
def v38 : W := 0x10520259b5b1730c3839b93b33
def v39 : W := 0x12530b08b4b170003030000303
def v40 : W := 0x12530b59b5b170003031b93b33
def v41 : W := 0x1822400c082803803e01c003c0
def v42 : W := 0x187242000000038f3e38000000
def v43 : W := 0x1872420c1c282003363000c3c3
def v44 : W := 0x1872420c1c28230f3e3981c3c3
def v45 : W := 0x1872420c1c28238c3e39c103c3
def v46 : W := 0x1872420c1c28238f0001c1c000
def v47 : W := 0x18724271e1d5d38f3e3e3e3c3c
def v48 : W := 0x1872427dfd28238f0007ffc000
def v49 : W := 0x187fff8c1efff38fc1c1c1fc3c
def v50 : W := 0x1ba24d8ea82b53f03fc1fe03fc
def v51 : W := 0x4404302040448c70c1c606040c
def v52 : W := 0x44043071e1d5dc70c1c63e3c3c
def v53 : W := 0x46053920e0d5d060018006000c
def v54 : W := 0x46053971e1d5d06001863e3c3c
def v55 : W := 0x4c20402448080cf3000646c000
def v56 : W := 0x4c24700000000cf3c7c0000000
def v57 : W := 0x4c247024484c8063078006c0cc
def v58 : W := 0x4c247024484c8c73c7c606c4cc
def v59 : W := 0x4c247024484c8c80c6064004c0
def v60 : W := 0x4c247024484c8cf3c1c646c40c
def v61 : W := 0x4c247059b5b17cf3c7c1b93b33
def v62 : W := 0x4c24707d49fc8c80c607c03fc0
def v63 : W := 0x4c29cda44a9b5cf3383e46fb33
def v64 : W := 0x4ff47fa6fc4ffc8cc63e7904f3
def v65 : W := 0x545632285464af7cf9ff87070f
def v66 : W := 0x5c27702c48fc800036000003c0
def v67 : W := 0x5c27707d49fc80003607c03fc0
def v68 : W := 0x5e72422cfc282063000006c000
def v69 : W := 0x5e72427dfd2820630007ffc000
def v70 : W := 0x5e777b000000006337b0000000
def v71 : W := 0x5e777b2cfcfdf00036300003c3
def v72 : W := 0x5e777b2cfcfdf063018006c00c
def v73 : W := 0x5e777b2cfcfdf06337b006c3cf
def v74 : W := 0x5e777b7dfdfdf06337b1bffbff
def v75 : W := 0x5e777b7dfdfdf06337b63effff
def v76 : W := 0xa008805103000f80c807c03c00
def v77 : W := 0xa180005301000f9c0007f90000
def v78 : W := 0xa185395301d5df9c37b7f903cf
def v79 : W := 0xa18884820202030c0808000000
def v80 : W := 0xa188848202020c10c040000000
def v81 : W := 0xa188848202020f9cc848000000
def v82 : W := 0xa18884aefeffff9cc84806c3cf
def v83 : W := 0xa18884d30302030c0809b93830
def v84 : W := 0xa18884d303020c10c046383c30
def v85 : W := 0xa18884d303020f8cc80ff93c30
def v86 : W := 0xa18884d303020f9cc047f93c30
def v87 : W := 0xa18dbd8202020f9cfff8000000
def v88 : W := 0xa18dbdd303d7dc10c1c6383c3c
def v89 : W := 0xa2588b51b7017fe3c9b7c6fc0f
def v90 : W := 0xa3898d82020200000000000000
def v91 : W := 0xa3898dd3a39350000000383830
def v92 : W := 0xa38dbdd3a3d7d000c1c0383c3c
def v93 : W := 0xa3d88f8202020fffc9f8000000
def v94 : W := 0xa3d88fd3b703730c0839b93833
def v95 : W := 0xa3d98fd3b793700c0038393833
def v96 : W := 0xb00b805903b003003801803b00
def v97 : W := 0xb3d2025bb520230c0001b90000
def v98 : W := 0xb3db8f820202030c3838000000
def v99 : W := 0xb3db8f820202037f39f8000000
def v100 : W := 0xb3db8f8202020f9cf878000000
def v101 : W := 0xb3db8f8a1622230c3839810303
def v102 : W := 0xb3db8f8ab6b3730c3838000303
def v103 : W := 0xb3db8fdbb7b370003030383b33
def v104 : W := 0xb3db8fdbb7b3730c0001b93830
def v105 : W := 0xb3db8fdbb7b3730c3839b93b33
def v106 : W := 0xb3dfbf820202030cfff8000000
def v107 : W := 0xb9f2425f1d282f9f0007f9c000
def v108 : W := 0xb9fac68202020f9ffe78000000
def v109 : W := 0xb9fac6df1f2a2c13f67638fff3
def v110 : W := 0xbbf2425fbd28238f0001f9c000
def v111 : W := 0xbbfbcf820202038f3e38000000
def v112 : W := 0xbbfbcfdfbfbb738c3e39f93bf3
def v113 : W := 0xe40db07143d48c00c006003c00
def v114 : W := 0xe7800073e1000c7000063e0000
def v115 : W := 0xe78dbd8202020c70c1c0000000
def v116 : W := 0xe78dbd8202020c70fff8000000
def v117 : W := 0xe78dbd8202020ffcc9c8000000
def v118 : W := 0xe78dbda242468c70c1c606040c
def v119 : W := 0xe78dbda2e2d7dc70c1c006000c
def v120 : W := 0xe78dbdf3e3d7d06001803e383c
def v121 : W := 0xe78dbdf3e3d7dc00c006383c30
def v122 : W := 0xe78dbdf3e3d7dc70c1c63e3c3c
def v123 : W := 0xe7ddbf8202020c7fc1f8000000
def v124 : W := 0xec2cf0754b4c8f80ce07c03cc0
def v125 : W := 0xec2df0754bdc8c80c606403cc0
def v126 : W := 0xedacf48202020fffcfc8000000
def v127 : W := 0xedacf4f74b4e836f0f89bff8fc
def v128 : W := 0xefadfd8202020cf3c7c0000000
def v129 : W := 0xefadfdf7ebdfdcf3c1c67efc3c
def v130 : W := 0xf7dfbf8202020f7cf9f8000000
def v131 : W := 0xf7dfbffbf7f7ff7cf9ffbf3f3f
def v132 : W := 0xfc22407d49280f800007c00000
def v133 : W := 0xfc26707d496c8f80c607c004c0
def v134 : W := 0xfc27707d49fc8f803607c003c0
def v135 : W := 0xfc2ff00002000f80fe00000000
def v136 : W := 0xfc2ff07d4bfc83003e01803bc0
def v137 : W := 0xfc2ff07d4bfc8c00f606003fc0
def v138 : W := 0xfc2ff07d4bfc8f80c007c03c00
def v139 : W := 0xfc2ff07d4bfc8f80fe07c03fc0
def v140 : W := 0xfc2ffdfd4bffdf80fe3fc03ff3
def v141 : W := 0xfc72427d5d282f8f0007c1c000
def v142 : W := 0xfc7ff27d5ffcaf8cfe3fc13fc3
def v143 : W := 0xfdaff48202020f9cfe48000000
def v144 : W := 0xfdaff4ff4bfe8f9cfe4fc03fc0
def v145 : W := 0xfe72427dfd282fe30007c6c000
def v146 : W := 0xfe7ffb7dfffdff80fe37c03fc3
def v147 : W := 0xfe7ffb7dfffdffe3ffb7c6ffcf
def v148 : W := 0xffaffd8202020ff0ffc0000000
def v149 : W := 0xffaffdffebffdff0ffc7fe3ffc
def v150 : W := 0xfff2420200000fff0000000000
def v151 : W := 0xfff2427ffd28236f0001bfc000
def v152 : W := 0xfff2427ffd282c7300063ec000
def v153 : W := 0xfff2427ffd282f8c0007f90000
def v154 : W := 0xfff2427ffd282fff0007ffc000
def v155 : W := 0xfff24ffffd2b7fff01c7ffc03c
def v156 : W := 0xfff6727ffd6cafffc1c7ffc40c
def v157 : W := 0xfff77b7ffdfdffff0187ffc00c
def v158 : W := 0xfff77b7ffdfdffff37b7ffc3cf
def v159 : W := 0xfffac68202020fffc848000000
def v160 : W := 0xfffac6ffff2a2fffc84fffc000
def v161 : W := 0xfffbcf8202020fff3838000000
def v162 : W := 0xfffbcfffffbb7fff383ffffb33
def v163 : W := 0xfffff27ffffcaffffe07ffffc0
def v164 : W := 0xffffff820202036f3fb8000000
def v165 : W := 0xffffff8202020c73f7f0000000
def v166 : W := 0xffffff8202020f8cfe38000000
def v167 : W := 0xffffff8202020fffc1c0000000
def v168 : W := 0xffffff8202020ffffff8000000
def v169 : W := 0xffffff8202d7dffffff80003cf
def v170 : W := 0xffffff82b6037ffffff806c00f
def v171 : W := 0xffffff8a16222ffffff9810303
def v172 : W := 0xffffff8ab6b37ffffff8000303
def v173 : W := 0xffffff8e0a2a0ffffff9c003c0
def v174 : W := 0xffffff8e1e2a2ffffff800c3c3
def v175 : W := 0xffffff8e1e2a2ffffff9c1c000
def v176 : W := 0xffffffa242468ffffffe06040c
def v177 : W := 0xffffffa2e2d7dffffff806000c
def v178 : W := 0xffffffa64a0a0ffffffe46c000
def v179 : W := 0xffffffa64a4e8ffffff806c0cc
def v180 : W := 0xffffffa64a4e8ffffffe4004c0
def v181 : W := 0xffffffae4afe8ffffff80003c0
def v182 : W := 0xffffffaefe2a2ffffff806c000
def v183 : W := 0xffffffaefefff06337b006c3cf
def v184 : W := 0xffffffaefefff36f3fb806c3cf
def v185 : W := 0xffffffaefefffc73f7f006c3cf
def v186 : W := 0xffffffaefefffffffff806c3cf
def v187 : W := 0xffffffdbb7b37ffffff9b93b33
def v188 : W := 0xfffffff3e3d7dffffffe3e3c3c
def v189 : W := 0xffffffff4b2a0fffffffc00000
def v190 : W := 0xffffffff4bfe8f8cfe3fc03fc0
def v191 : W := 0xffffffff4bfe8fffffffc03fc0
def v192 : W := 0xffffffffff2a2fffc1c7ffc000
def v193 : W := 0xffffffffff2a2fffffffffc000
def v194 : W := 0xfffffffffffff30c3e39b93bf3
def v195 : W := 0xfffffffffffff36f3fb9bffbff
def v196 : W := 0xfffffffffffffc73c1c63efc3c
def v197 : W := 0xfffffffffffffc73f7f63effff
def v198 : W := 0xffffffffffffff8cfe3ff93ff3
def v199 : W := 0xffffffffffffffffc1c7fffc3c

def ins : List W := [v73, v105, v122, v139, v154, v168]
theorem sampled : ∀ j : Fin 104, Nat.testBit 0xeac8e0c0ea88a080 (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
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
def level3 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level3_ok : everyKey (rowOK 2 level2) level3 = true := by decide +kernel
theorem closed3 : Closed 3 level3 := closed_next 2 (by decide) level3 level2 closed2 level3_ok
def level4 : BinaryTree (List W) := (.node [v64, v73, v122, v154, v168] (.node [v49, v73, v105, v139, v168] (.node [v35, v73, v105, v122, v168] (.node [v34, v73, v105, v122, v154] (.node [v24, v73, v105, v122, v139] .nil .nil) .nil) (.node [v47, v73, v105, v139, v154] .nil .nil)) (.node [v61, v73, v122, v139, v154] (.node [v50, v73, v105, v154, v168] .nil .nil) (.node [v63, v73, v122, v139, v168] .nil .nil))) (.node [v89, v105, v122, v154, v168] (.node [v78, v105, v122, v139, v168] (.node [v73, v105, v122, v144, v160] (.node [v65, v73, v139, v154, v168] .nil .nil) .nil) (.node [v82, v105, v122, v139, v154] .nil .nil)) (.node [v105, v122, v139, v154, v183] (.node [v105, v109, v139, v154, v168] .nil .nil) (.node [v122, v127, v139, v154, v168] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4_ok : everyKey (rowOK 3 level3) level4 = true := by decide +kernel
theorem closed4 : Closed 4 level4 := closed_next 3 (by decide) level4 level3 closed3 level4_ok
def level5ll : BinaryTree (List W) := (.node [v16, v55, v73, v122, v139, v168] (.node [v6, v73, v105, v122, v139, v154] (.node [v4, v73, v98, v122, v139, v154] (.node [v2, v73, v105, v122, v139, v154] (.node [v1, v73, v105, v122, v139, v154] (.node [v0, v81, v105, v122, v139, v154] .nil .nil) .nil) (.node [v4, v56, v73, v122, v139, v154] (.node [v3, v73, v105, v122, v139, v154] .nil .nil) .nil)) (.node [v5, v73, v105, v115, v139, v154] (.node [v5, v42, v73, v105, v139, v154] (.node [v4, v73, v105, v122, v139, v154] .nil .nil) .nil) (.node [v5, v73, v105, v122, v139, v154] .nil .nil))) (.node [v11, v73, v105, v122, v139, v154] (.node [v9, v19, v73, v105, v122, v139] (.node [v8, v73, v105, v122, v139, v154] (.node [v7, v29, v73, v105, v122, v154] .nil .nil) .nil) (.node [v10, v73, v105, v122, v139, v154] .nil .nil)) (.node [v14, v73, v105, v122, v139, v154] (.node [v13, v73, v105, v122, v139, v154] (.node [v12, v73, v105, v122, v139, v154] .nil .nil) .nil) (.node [v15, v77, v105, v122, v139, v168] .nil .nil)))) (.node [v31, v73, v105, v122, v154, v168] (.node [v23, v73, v105, v122, v139, v168] (.node [v20, v73, v105, v122, v139, v168] (.node [v18, v73, v105, v122, v139, v168] (.node [v17, v27, v73, v105, v122, v168] .nil .nil) .nil) (.node [v22, v73, v105, v122, v139, v168] (.node [v21, v46, v73, v105, v139, v168] .nil .nil) .nil)) (.node [v28, v73, v105, v122, v154, v168] (.node [v26, v41, v73, v105, v154, v168] (.node [v25, v76, v105, v122, v154, v168] .nil .nil) .nil) (.node [v30, v59, v73, v122, v154, v168] .nil .nil))) (.node [v38, v73, v105, v122, v139, v154] (.node [v36, v73, v105, v122, v139, v154] (.node [v33, v73, v105, v122, v154, v168] (.node [v32, v73, v105, v122, v154, v168] .nil .nil) .nil) (.node [v37, v51, v73, v139, v154, v168] .nil .nil)) (.node [v43, v84, v105, v139, v154, v168] (.node [v40, v73, v105, v122, v139, v154] (.node [v39, v122, v139, v154, v168, v195] .nil .nil) .nil) (.node [v44, v73, v105, v139, v154, v168] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5ll_ok : everyKey (rowOK 4 level4) level5ll = true := by decide +kernel
def level5lr : BinaryTree (List W) := (.node [v73, v75, v105, v122, v139, v154] (.node [v66, v105, v122, v147, v154, v168] (.node [v57, v83, v122, v139, v154, v168] (.node [v52, v73, v105, v122, v139, v154] (.node [v48, v73, v105, v122, v139, v168] (.node [v48, v73, v105, v115, v122, v139] .nil .nil) .nil) (.node [v54, v73, v105, v122, v139, v154] (.node [v53, v105, v139, v154, v168, v197] .nil .nil) .nil)) (.node [v62, v73, v98, v105, v122, v154] (.node [v60, v73, v122, v139, v154, v168] (.node [v58, v73, v122, v139, v154, v168] .nil .nil) .nil) (.node [v62, v73, v105, v122, v154, v168] .nil .nil))) (.node [v69, v73, v105, v122, v139, v168] (.node [v68, v105, v122, v139, v158, v168] (.node [v67, v73, v105, v122, v154, v168] (.node [v67, v73, v81, v105, v122, v154] .nil .nil) .nil) (.node [v69, v73, v81, v105, v122, v139] .nil .nil)) (.node [v72, v105, v122, v139, v154, v168] (.node [v71, v105, v122, v139, v154, v168] (.node [v70, v105, v122, v139, v154, v186] .nil .nil) .nil) (.node [v73, v74, v105, v122, v139, v154] .nil .nil)))) (.node [v73, v93, v105, v122, v139, v154] (.node [v73, v87, v105, v122, v139, v154] (.node [v73, v81, v105, v122, v139, v154] (.node [v73, v80, v105, v122, v139, v154] (.node [v73, v79, v105, v122, v139, v154] .nil .nil) .nil) (.node [v73, v81, v105, v122, v144, v154] (.node [v73, v81, v105, v122, v139, v160] .nil .nil) .nil)) (.node [v73, v91, v131, v139, v154, v168] (.node [v73, v90, v105, v122, v139, v154] (.node [v73, v88, v105, v139, v154, v168] .nil .nil) .nil) (.node [v73, v92, v105, v139, v154, v168] .nil .nil))) (.node [v73, v98, v105, v122, v139, v154] (.node [v73, v96, v122, v154, v168, v198] (.node [v73, v95, v122, v139, v154, v168] (.node [v73, v94, v122, v139, v154, v168] .nil .nil) .nil) (.node [v73, v97, v122, v139, v162, v168] .nil .nil)) (.node [v73, v99, v105, v122, v139, v154] (.node [v73, v98, v122, v139, v154, v187] (.node [v73, v98, v105, v122, v154, v190] .nil .nil) .nil) (.node [v73, v100, v105, v122, v139, v154] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lr_ok : everyKey (rowOK 4 level4) level5lr = true := by decide +kernel
def level5l : BinaryTree (List W) := .node [v45, v73, v105, v139, v154, v168] level5ll level5lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5l_ok : everyKey (rowOK 4 level4) level5l = true := by
  change (_ && everyKey (rowOK 4 level4) level5ll && everyKey (rowOK 4 level4) level5lr) = true
  rw [level5ll_ok, level5lr_ok]
  decide +kernel
def level5rl : BinaryTree (List W) := (.node [v73, v105, v122, v124, v154, v168] (.node [v73, v105, v115, v122, v139, v154] (.node [v73, v105, v108, v122, v139, v154] (.node [v73, v104, v122, v139, v154, v168] (.node [v73, v103, v122, v139, v154, v168] (.node [v73, v102, v105, v122, v139, v154] .nil .nil) .nil) (.node [v73, v105, v107, v122, v139, v168] (.node [v73, v105, v106, v122, v139, v154] .nil .nil) .nil)) (.node [v73, v105, v113, v149, v154, v168] (.node [v73, v105, v111, v122, v139, v154] (.node [v73, v105, v110, v122, v139, v168] .nil .nil) .nil) (.node [v73, v105, v114, v139, v168, v199] .nil .nil))) (.node [v73, v105, v118, v122, v139, v154] (.node [v73, v105, v116, v122, v139, v154] (.node [v73, v105, v115, v139, v154, v188] (.node [v73, v105, v115, v122, v139, v192] .nil .nil) .nil) (.node [v73, v105, v117, v122, v139, v154] .nil .nil)) (.node [v73, v105, v121, v139, v154, v168] (.node [v73, v105, v120, v139, v154, v168] (.node [v73, v105, v119, v122, v139, v154] .nil .nil) .nil) (.node [v73, v105, v122, v123, v139, v154] .nil .nil)))) (.node [v73, v105, v122, v138, v154, v168] (.node [v73, v105, v122, v133, v154, v168] (.node [v73, v105, v122, v128, v139, v154] (.node [v73, v105, v122, v126, v139, v154] (.node [v73, v105, v122, v125, v154, v168] .nil .nil) .nil) (.node [v73, v105, v122, v132, v163, v168] (.node [v73, v105, v122, v130, v139, v154] .nil .nil) .nil)) (.node [v73, v105, v122, v136, v154, v168] (.node [v73, v105, v122, v135, v154, v191] (.node [v73, v105, v122, v134, v154, v168] .nil .nil) .nil) (.node [v73, v105, v122, v137, v154, v168] .nil .nil))) (.node [v73, v105, v122, v139, v150, v193] (.node [v73, v105, v122, v139, v145, v168] (.node [v73, v105, v122, v139, v143, v154] (.node [v73, v105, v122, v139, v141, v168] .nil .nil) .nil) (.node [v73, v105, v122, v139, v148, v154] .nil .nil)) (.node [v73, v105, v122, v139, v153, v168] (.node [v73, v105, v122, v139, v152, v168] (.node [v73, v105, v122, v139, v151, v168] .nil .nil) .nil) (.node [v73, v105, v122, v139, v154, v159] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rl_ok : everyKey (rowOK 4 level4) level5rl = true := by decide +kernel
def level5rr : BinaryTree (List W) := (.node [v73, v105, v122, v139, v154, v185] (.node [v73, v105, v122, v139, v154, v174] (.node [v73, v105, v122, v139, v154, v169] (.node [v73, v105, v122, v139, v154, v166] (.node [v73, v105, v122, v139, v154, v165] (.node [v73, v105, v122, v139, v154, v164] .nil .nil) .nil) (.node [v73, v105, v122, v139, v154, v168] (.node [v73, v105, v122, v139, v154, v167] .nil .nil) .nil)) (.node [v73, v105, v122, v139, v154, v172] (.node [v73, v105, v122, v139, v154, v171] (.node [v73, v105, v122, v139, v154, v170] .nil .nil) .nil) (.node [v73, v105, v122, v139, v154, v173] .nil .nil))) (.node [v73, v105, v122, v139, v154, v179] (.node [v73, v105, v122, v139, v154, v177] (.node [v73, v105, v122, v139, v154, v176] (.node [v73, v105, v122, v139, v154, v175] .nil .nil) .nil) (.node [v73, v105, v122, v139, v154, v178] .nil .nil)) (.node [v73, v105, v122, v139, v154, v182] (.node [v73, v105, v122, v139, v154, v181] (.node [v73, v105, v122, v139, v154, v180] .nil .nil) .nil) (.node [v73, v105, v122, v139, v154, v184] .nil .nil)))) (.node [v73, v105, v122, v144, v154, v168] (.node [v73, v105, v122, v139, v157, v168] (.node [v73, v105, v122, v139, v155, v168] (.node [v73, v105, v122, v139, v154, v189] (.node [v73, v105, v122, v139, v154, v186] .nil .nil) .nil) (.node [v73, v105, v122, v139, v156, v168] .nil .nil)) (.node [v73, v105, v122, v140, v154, v168] (.node [v73, v105, v122, v139, v168, v192] (.node [v73, v105, v122, v139, v160, v168] .nil .nil) .nil) (.node [v73, v105, v122, v142, v154, v168] .nil .nil))) (.node [v73, v112, v122, v139, v154, v168] (.node [v73, v105, v129, v139, v154, v168] (.node [v73, v105, v122, v154, v168, v190] (.node [v73, v105, v122, v146, v154, v168] .nil .nil) .nil) (.node [v73, v105, v139, v154, v168, v196] .nil .nil)) (.node [v85, v105, v122, v139, v154, v168] (.node [v81, v105, v122, v139, v154, v186] (.node [v73, v122, v139, v154, v168, v194] .nil .nil) .nil) (.node [v86, v105, v122, v139, v154, v168] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rr_ok : everyKey (rowOK 4 level4) level5rr = true := by decide +kernel
def level5r : BinaryTree (List W) := .node [v73, v105, v122, v139, v154, v161] level5rl level5rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5r_ok : everyKey (rowOK 4 level4) level5r = true := by
  change (_ && everyKey (rowOK 4 level4) level5rl && everyKey (rowOK 4 level4) level5rr) = true
  rw [level5rl_ok, level5rr_ok]
  decide +kernel
def level5 : BinaryTree (List W) := .node [v73, v101, v105, v122, v139, v154] level5l level5r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5_ok : everyKey (rowOK 4 level4) level5 = true := by
  change (_ && everyKey (rowOK 4 level4) level5l && everyKey (rowOK 4 level4) level5r) = true
  rw [level5l_ok, level5r_ok]
  decide +kernel
theorem closed5 : Closed 5 level5 := closed_next 4 (by decide) level5 level4 closed4 level5_ok
def level6l : BinaryTree (List W) := (.node [v30, v73, v105, v122, v139, v154, v168] (.node [v16, v73, v105, v122, v139, v154, v168] (.node [v5, v73, v105, v122, v139, v154, v168] (.node [v4, v73, v105, v122, v139, v154, v168] (.node [v4, v73, v105, v122, v139, v154] (.node [v0, v73, v105, v122, v139, v154, v168] .nil .nil) .nil) (.node [v5, v73, v105, v122, v139, v154] .nil .nil)) (.node [v9, v73, v105, v122, v139, v154, v168] (.node [v7, v73, v105, v122, v139, v154, v168] .nil .nil) (.node [v15, v73, v105, v122, v139, v154, v168] .nil .nil))) (.node [v25, v73, v105, v122, v139, v154, v168] (.node [v19, v73, v105, v122, v139, v154, v168] (.node [v17, v73, v105, v122, v139, v154, v168] .nil .nil) (.node [v21, v73, v105, v122, v139, v154, v168] .nil .nil)) (.node [v27, v73, v105, v122, v139, v154, v168] (.node [v26, v73, v105, v122, v139, v154, v168] .nil .nil) (.node [v29, v73, v105, v122, v139, v154, v168] .nil .nil)))) (.node [v55, v73, v105, v122, v139, v154, v168] (.node [v43, v73, v105, v122, v139, v154, v168] (.node [v41, v73, v105, v122, v139, v154, v168] (.node [v39, v73, v105, v122, v139, v154, v168] (.node [v37, v73, v105, v122, v139, v154, v168] .nil .nil) .nil) (.node [v42, v73, v105, v122, v139, v154, v168] .nil .nil)) (.node [v51, v73, v105, v122, v139, v154, v168] (.node [v46, v73, v105, v122, v139, v154, v168] .nil .nil) (.node [v53, v73, v105, v122, v139, v154, v168] .nil .nil))) (.node [v66, v73, v105, v122, v139, v154, v168] (.node [v57, v73, v105, v122, v139, v154, v168] (.node [v56, v73, v105, v122, v139, v154, v168] .nil .nil) (.node [v59, v73, v105, v122, v139, v154, v168] .nil .nil)) (.node [v70, v73, v105, v122, v139, v154, v168] (.node [v68, v73, v105, v122, v139, v154, v168] .nil .nil) (.node [v73, v76, v105, v122, v139, v154, v168] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6l_ok : everyKey (rowOK 5 level5) level6l = true := by decide +kernel
def level6r : BinaryTree (List W) := (.node [v73, v105, v122, v139, v147, v154, v168] (.node [v73, v98, v105, v122, v139, v154, v168] (.node [v73, v91, v105, v122, v139, v154, v168] (.node [v73, v83, v105, v122, v139, v154, v168] (.node [v73, v81, v105, v122, v139, v154, v168] (.node [v73, v81, v105, v122, v139, v154] .nil .nil) .nil) (.node [v73, v84, v105, v122, v139, v154, v168] .nil .nil)) (.node [v73, v97, v105, v122, v139, v154, v168] (.node [v73, v96, v105, v122, v139, v154, v168] .nil .nil) (.node [v73, v98, v105, v122, v139, v154] .nil .nil))) (.node [v73, v105, v115, v122, v139, v154, v168] (.node [v73, v105, v114, v122, v139, v154, v168] (.node [v73, v105, v113, v122, v139, v154, v168] .nil .nil) (.node [v73, v105, v115, v122, v139, v154] .nil .nil)) (.node [v73, v105, v122, v132, v139, v154, v168] (.node [v73, v105, v122, v131, v139, v154, v168] .nil .nil) (.node [v73, v105, v122, v135, v139, v154, v168] .nil .nil)))) (.node [v73, v105, v122, v139, v154, v168, v188] (.node [v73, v105, v122, v139, v154, v162, v168] (.node [v73, v105, v122, v139, v150, v154, v168] (.node [v73, v105, v122, v139, v149, v154, v168] .nil .nil) (.node [v73, v105, v122, v139, v154, v158, v168] .nil .nil)) (.node [v73, v105, v122, v139, v154, v168, v186] (.node [v73, v105, v122, v139, v154, v163, v168] .nil .nil) (.node [v73, v105, v122, v139, v154, v168, v187] .nil .nil))) (.node [v73, v105, v122, v139, v154, v168, v197] (.node [v73, v105, v122, v139, v154, v168, v193] (.node [v73, v105, v122, v139, v154, v168, v191] .nil .nil) (.node [v73, v105, v122, v139, v154, v168, v195] .nil .nil)) (.node [v73, v105, v122, v139, v154, v168, v199] (.node [v73, v105, v122, v139, v154, v168, v198] .nil .nil) (.node [v73, v105, v122, v139, v154, v186] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6r_ok : everyKey (rowOK 5 level5) level6r = true := by decide +kernel
def level6 : BinaryTree (List W) := .node [v73, v77, v105, v122, v139, v154, v168] level6l level6r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6_ok : everyKey (rowOK 5 level5) level6 = true := by
  change (_ && everyKey (rowOK 5 level5) level6l && everyKey (rowOK 5 level5) level6r) = true
  rw [level6l_ok, level6r_ok]
  decide +kernel
theorem closed6 : Closed 6 level6 := closed_next 5 (by decide) level6 level5 closed5 level6_ok
def level7 : BinaryTree (List W) := (.node [v73, v105, v122, v139, v154, v168] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7_ok : everyKey (rowOK 6 level6) level7 = true := by decide +kernel
theorem closed7 : Closed 7 level7 := closed_next 6 (by decide) level7 level6 closed6 level7_ok

theorem lower : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z 7 ins.toFinset :=
  @no_build 7 level7 ins (by decide +kernel) (by decide) closed7 (by decide +kernel)
def witness : List Gate := [⟨.or,[2,4]⟩, ⟨.and,[0,6]⟩, ⟨.and,[1,2]⟩, ⟨.or,[1,3]⟩, ⟨.and,[3,4]⟩, ⟨.or,[5,10]⟩, ⟨.and,[7,9]⟩, ⟨.and,[8,11]⟩, ⟨.or,[12,13]⟩]
theorem upper : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 9 ∧ ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xeac8e0c0ea88a080 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact ⟨witness,14,by simp [witness],rfl,by decide +kernel⟩
end PEqualNP.Outside.L_meta_15405_aux

open PEqualNP.Outside.L_meta_15405_aux in
theorem PEqualNP.Outside.L_meta_15405 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3939033280 * 2 ^ 32 + 3934822528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3939033280 * 2 ^ 32 + 3934822528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  have code : 3939033280 * 2 ^ 32 + 3934822528 = 0xeac8e0c0ea88a080 := by decide
  simp only [code] at h ⊢
  obtain ⟨C,legal,size,computes⟩ := h
  obtain ⟨gs,o,mono,bound,ev⟩ := replace 0xeac8e0c0ea88a080 9 ins (by decide +kernel) sampled rfl lower upper C.gates C.output legal computes
  exact ⟨⟨gs,o⟩,mono,bound.trans size,ev⟩
