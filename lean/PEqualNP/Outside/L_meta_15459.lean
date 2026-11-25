import PEqualNP.Defs

-- The live-wire search and circuit compiler are adapted from tacyon52 in L-meta-8639, pull request 12794 under Apache-2.0.
namespace PEqualNP.Outside.L_meta_15459_aux

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

def v0 : W := 0x0
def v1 : W := 0x3183061830c04
def v2 : W := 0x3803001800c00
def v3 : W := 0x3980001830000
def v4 : W := 0x3983060000000
def v5 : W := 0xc60c1860c3008
def v6 : W := 0xc80c006003000
def v7 : W := 0xce000060c0000
def v8 : W := 0xce0c180000000
def v9 : W := 0x100000000000000
def v10 : W := 0x171f0000000000303
def v11 : W := 0x2d350000000000cf4
def v12 : W := 0x3a3a00000000030f8
def v13 : W := 0x3f200000000003f00
def v14 : W := 0x5c01f000000000c003
def v15 : W := 0xb405500000000300f4
def v16 : W := 0xe805a00000000c00f8
def v17 : W := 0xfc04000000000fc000
def v18 : W := 0x9005000000001f00f00
def v19 : W := 0x9140000000001f3c000
def v20 : W := 0x914505000000070c303
def v21 : W := 0x9145050000001830c04
def v22 : W := 0x9145150000000000000
def v23 : W := 0x917a3a0000001f3f0f8
def v24 : W := 0x9e855a0000001fc0ff8
def v25 : W := 0x22012000000006703300
def v26 : W := 0x224800000000067cc000
def v27 : W := 0x224920a000000070c303
def v28 : W := 0x224920a00000060c3008
def v29 : W := 0x224921a0000000000000
def v30 : W := 0x224ad3500000067cccf4
def v31 : W := 0x22b525500000067333f4
def v32 : W := 0x2b017000000000700300
def v33 : W := 0x2b5c000000000070c000
def v34 : W := 0x2b5d71f000000070c303
def v35 : W := 0x2b5ff3f000000070cff7
def v36 : W := 0x2b5ff3f000000070f3fb
def v37 : W := 0x2bfd75f000000073c3f7
def v38 : W := 0x2bfd75f00000007cc3fb
def v39 : W := 0x50028200000007803c00
def v40 : W := 0x50a004000000078f0000
def v41 : W := 0x50a28600000001830cf4
def v42 : W := 0x50a286000000060c30f8
def v43 : W := 0x50a287000000000000f0
def v44 : W := 0x5902d200000001800c00
def v45 : W := 0x59b40400000001830000
def v46 : W := 0x59b6d6500000067cf3fb
def v47 : W := 0x59b6d750000001830cf4
def v48 : W := 0x59b6d750000001f30ff4
def v49 : W := 0x59b6d750000001f3ccf4
def v50 : W := 0x59b6d750000001f3cff7
def v51 : W := 0x7203a200000006003000
def v52 : W := 0x72e804000000060c0000
def v53 : W := 0x72eba6a0000001f3cff7
def v54 : W := 0x72eba7a00000060c30f8
def v55 : W := 0x72eba7a00000067c33f8
def v56 : W := 0x72eba7a00000067cf0f8
def v57 : W := 0x72eba7a00000067cf3fb
def v58 : W := 0x7b000000000007f00000
def v59 : W := 0x7b03f200000007f03f00
def v60 : W := 0x7b03f350000007f03ff4
def v61 : W := 0x7b03f3a0000007f03ff8
def v62 : W := 0x7b5ff3f0000007f0ff03
def v63 : W := 0x7ba3f600000007f33ff4
def v64 : W := 0x7ba3f600000007fc3ff8
def v65 : W := 0x7ba3f700000007f03ff0
def v66 : W := 0x7bb6d750000007f30cf4
def v67 : W := 0x7bb7f750000001f30ff4
def v68 : W := 0x7bb7f750000007f33ff4
def v69 : W := 0x7beba7a0000007fc30f8
def v70 : W := 0x7bebf7a00000067c33f8
def v71 : W := 0x7bebf7a0000007fc3ff8
def v72 : W := 0x7bfc0400000007ffc000
def v73 : W := 0x7bfc0550000007ffc0f4
def v74 : W := 0x7bfc05a0000007ffc0f8
def v75 : W := 0x7bfd75f0000007ffc303
def v76 : W := 0x7bfe8600000007ffccf4
def v77 : W := 0x7bfe8600000007fff0f8
def v78 : W := 0x7bfe8700000007ffc0f0
def v79 : W := 0x7bfed750000001f3ccf4
def v80 : W := 0x7bfed750000007ffccf4
def v81 : W := 0x7bffa7a00000067cf0f8
def v82 : W := 0x7bffa7a0000007fff0f8
def v83 : W := 0x7bfff600000007ffff00
def v84 : W := 0x7bfff750000007fffff4
def v85 : W := 0x7bfff7a0000007fffff8
def v86 : W := 0x7bfff7f000000070c3f3
def v87 : W := 0x7bfff7f0000001f3cff7
def v88 : W := 0x7bfff7f00000067cf3fb
def v89 : W := 0x7bfff7f00000078f3cfc
def v90 : W := 0x7bfff7f0000007f3fff7
def v91 : W := 0x7bfff7f0000007fcfffb
def v92 : W := 0x7bfff7f0000007ff3ffc
def v93 : W := 0x7bfff7f0000007ffcff7
def v94 : W := 0x7bfff7f0000007fff3fb
def v95 : W := 0x7bfff7f0000007fffcfc
def v96 : W := 0x7bfff7f0000007ffffff
def v97 : W := 0xb800001f0000018000003
def v98 : W := 0x16800009500000600000f4
def v99 : W := 0x1d000009a00001800000f8
def v100 : W := 0x1f800008000001f8000000
def v101 : W := 0x12000005000003e00000f00
def v102 : W := 0x12280000000003e78000000
def v103 : W := 0x12280005050000e18000303
def v104 : W := 0x12280005050003060000c04
def v105 : W := 0x12280005150000000000000
def v106 : W := 0x1228003a3a0003e780030f8
def v107 : W := 0x13d000059a0003f80000ff8
def v108 : W := 0x4400001200000ce00003300
def v109 : W := 0x4490000000000cf98000000
def v110 : W := 0x449000120a0000e18000303
def v111 : W := 0x449000120a000c180003008
def v112 : W := 0x449000121a0000000000000
def v113 : W := 0x4490002d35000cf98000cf4
def v114 : W := 0x4568001295000ce600033f4
def v115 : W := 0x56000017000000e00000300
def v116 : W := 0x56b80000000000e18000000
def v117 : W := 0x56b800171f0000e18000303
def v118 : W := 0x56b8003f3f0000e18000ff7
def v119 : W := 0x56b8003f3f0000e180033fb
def v120 : W := 0x56bab5d71f0000e1870c303
def v121 : W := 0x56bfbfd75f0000e1fffc303
def v122 : W := 0x57f800179f0000e780003f7
def v123 : W := 0x57f800179f0000f980003fb
def v124 : W := 0xa000002820000f000003c00
def v125 : W := 0xa140000080000f1e0000000
def v126 : W := 0xa1400028a00003060000cf4
def v127 : W := 0xa1400028a0000c1800030f8
def v128 : W := 0xa1400028b000000000000f0
def v129 : W := 0xb200002d200003000000c00
def v130 : W := 0xb3680000800003060000000
def v131 : W := 0xb368002da5000cf980033fb
def v132 : W := 0xb368002db50003060000cf4
def v133 : W := 0xb368002db50003e60000ff4
def v134 : W := 0xb368002db50003e78000cf4
def v135 : W := 0xb368002db50003e78000ff7
def v136 : W := 0xb36d9b6df50003061830cf4
def v137 : W := 0xe400003a20000c000003000
def v138 : W := 0xe5d0000080000c180000000
def v139 : W := 0xe5d0003aaa0003e78000ff7
def v140 : W := 0xe5d0003aba000c1800030f8
def v141 : W := 0xe5d0003aba000cf800033f8
def v142 : W := 0xe5d0003aba000cf980030f8
def v143 : W := 0xe5d0003aba000cf980033fb
def v144 : W := 0xe5d72ebafa000c1860c30f8
def v145 : W := 0xf600000000000fe00000000
def v146 : W := 0xf600003f20000fe00003f00
def v147 : W := 0xf600003f35000fe00003ff4
def v148 : W := 0xf600003f3a000fe00003ff8
def v149 : W := 0xf607b03f20000fe07f03f00
def v150 : W := 0xf607bfff60000fe07ffff00
def v151 : W := 0xf6b8003f3f000fe18003f03
def v152 : W := 0xf740003fa0000fe60003ff4
def v153 : W := 0xf740003fa0000ff80003ff8
def v154 : W := 0xf740003fb0000fe00003ff0
def v155 : W := 0xf768002db5000fe60000cf4
def v156 : W := 0xf768003fb50003e60000ff4
def v157 : W := 0xf768003fb5000fe60003ff4
def v158 : W := 0xf7d0003aba000ff800030f8
def v159 : W := 0xf7d0003fba000cf800033f8
def v160 : W := 0xf7d0003fba000ff80003ff8
def v161 : W := 0xf7f8000080000fff8000000
def v162 : W := 0xf7f8000095000fff80000f4
def v163 : W := 0xf7f800009a000fff80000f8
def v164 : W := 0xf7f800179f000fff8000303
def v165 : W := 0xf7f80028a0000fff8000cf4
def v166 : W := 0xf7f80028a0000fff80030f8
def v167 : W := 0xf7f80028b0000fff80000f0
def v168 : W := 0xf7f8002db50003e78000cf4
def v169 : W := 0xf7f8002db5000fff8000cf4
def v170 : W := 0xf7f8003aba000cf980030f8
def v171 : W := 0xf7f8003aba000fff80030f8
def v172 : W := 0xf7f8003fa0000fff8003f00
def v173 : W := 0xf7f8003fb5000fff8003ff4
def v174 : W := 0xf7f8003fba000fff8003ff8
def v175 : W := 0xf7f8003fbf0000e180003f3
def v176 : W := 0xf7f8003fbf0003e78000ff7
def v177 : W := 0xf7f8003fbf000cf980033fb
def v178 : W := 0xf7f8003fbf000f1e0003cfc
def v179 : W := 0xf7f8003fbf000fe78003ff7
def v180 : W := 0xf7f8003fbf000ff98003ffb
def v181 : W := 0xf7f8003fbf000ffe0003ffc
def v182 : W := 0xf7f8003fbf000fff8000ff7
def v183 : W := 0xf7f8003fbf000fff80033fb
def v184 : W := 0xf7f8003fbf000fff8003cfc
def v185 : W := 0xf7f8003fbf000fff8003fff
def v186 : W := 0xf7fab5d79f000fff870c303
def v187 : W := 0xf7ffb03fa0000fffff03f00
def v188 : W := 0xf7ffbfc0c0000ffffffc000
def v189 : W := 0xf7ffbfd7df000ffffffc303
def v190 : W := 0xf7ffbfffe0000ffffffff00
def v191 : W := 0x9000001400001f000003c000
def v192 : W := 0x9002800000001f0078000000
def v193 : W := 0x90028014005007001800c003
def v194 : W := 0x900280140050180060030004
def v195 : W := 0x900280140150000000000000
def v196 : W := 0x900280e805a01f00780c00f8
def v197 : W := 0x901d001409a01f018003c0f8
def v198 : W := 0x22000004800006700000cc000
def v199 : W := 0x2200900000000670198000000
def v200 : W := 0x22009004800a007001800c003
def v201 : W := 0x22009004800a06001800c0008
def v202 : W := 0x22009004801a0000000000000
def v203 : W := 0x2200900b405506701980300f4
def v204 : W := 0x22016804809506700600cc0f4
def v205 : W := 0x2b000005c000007000000c000
def v206 : W := 0x2b00b80000000070018000000
def v207 : W := 0x2b00b805c01f007001800c003
def v208 : W := 0x2b00b80fc05f007001803c0f7
def v209 : W := 0x2b00b80fc05f00700180cc0fb
def v210 : W := 0x2b00bab5d71f007001870c303
def v211 : W := 0x2b00bfb5ff3f007001ff0ff03
def v212 : W := 0x2b01f805c09f007007800c0f7
def v213 : W := 0x2b01f805c09f007019800c0fb
def v214 : W := 0x2b56b805d71f0070e1800c303
def v215 : W := 0x2bf6b805ff3f007fe1800ff03
def v216 : W := 0x5000000a004007800000f0000
def v217 : W := 0x50014000008007801e0000000
def v218 : W := 0x5001400a00c001800600300f4
def v219 : W := 0x5001400a00c006001800c00f8
def v220 : W := 0x5001400a00d000000000000f0
def v221 : W := 0x5900000b40400180000030000
def v222 : W := 0x5901680000800180060000000
def v223 : W := 0x5901680b40c506701980cc0fb
def v224 : W := 0x5901680b40d501800600300f4
def v225 : W := 0x5901680b40d501f006003c0f4
def v226 : W := 0x5901680b40d501f00780300f4
def v227 : W := 0x5901680b40d501f007803c0f7
def v228 : W := 0x59016d9b6df50180061830cf4
def v229 : W := 0x59b3680b6df50183060030cf4
def v230 : W := 0x7200000e804006000000c0000
def v231 : W := 0x7201d00000800600180000000
def v232 : W := 0x7201d00e80ca01f007803c0f7
def v233 : W := 0x7201d00e80da06001800c00f8
def v234 : W := 0x7201d00e80da06701800cc0f8
def v235 : W := 0x7201d00e80da06701980c00f8
def v236 : W := 0x7201d00e80da06701980cc0fb
def v237 : W := 0x7201d72ebafa06001860c30f8
def v238 : W := 0x72e5d00ebafa060c1800c30f8
def v239 : W := 0x7b000000000007f0000000000
def v240 : W := 0x7b00000fc04007f00000fc000
def v241 : W := 0x7b00000fc05507f00000fc0f4
def v242 : W := 0x7b00000fc05a07f00000fc0f8
def v243 : W := 0x7b0007bfc04007f0007ffc000
def v244 : W := 0x7b0007bfff6007f0007ffff00
def v245 : W := 0x7b00b80fc05f07f00180fc003
def v246 : W := 0x7b01400fc0c007f00600fc0f4
def v247 : W := 0x7b01400fc0c007f01800fc0f8
def v248 : W := 0x7b01400fc0d007f00000fc0f0
def v249 : W := 0x7b01680b40d507f00600300f4
def v250 : W := 0x7b01680fc0d501f006003c0f4
def v251 : W := 0x7b01680fc0d507f00600fc0f4
def v252 : W := 0x7b01d00e80da07f01800c00f8
def v253 : W := 0x7b01d00fc0da06701800cc0f8
def v254 : W := 0x7b01d00fc0da07f01800fc0f8
def v255 : W := 0x7b01f800008007f01f8000000
def v256 : W := 0x7b01f800009507f01f80000f4
def v257 : W := 0x7b01f800009a07f01f80000f8
def v258 : W := 0x7b01f805c09f07f01f800c003
def v259 : W := 0x7b01f80a00c007f01f80300f4
def v260 : W := 0x7b01f80a00c007f01f80c00f8
def v261 : W := 0x7b01f80a00d007f01f80000f0
def v262 : W := 0x7b01f80b40d501f00780300f4
def v263 : W := 0x7b01f80b40d507f01f80300f4
def v264 : W := 0x7b01f80e80da06701980c00f8
def v265 : W := 0x7b01f80e80da07f01f80c00f8
def v266 : W := 0x7b01f80fc0c007f01f80fc000
def v267 : W := 0x7b01f80fc0d507f01f80fc0f4
def v268 : W := 0x7b01f80fc0da07f01f80fc0f8
def v269 : W := 0x7b01f80fc0df007001800c0f3
def v270 : W := 0x7b01f80fc0df01f007803c0f7
def v271 : W := 0x7b01f80fc0df06701980cc0fb
def v272 : W := 0x7b01f80fc0df07801e00f00fc
def v273 : W := 0x7b01f80fc0df07f00780fc0f7
def v274 : W := 0x7b01f80fc0df07f01980fc0fb
def v275 : W := 0x7b01f80fc0df07f01e00fc0fc
def v276 : W := 0x7b01f80fc0df07f01f803c0f7
def v277 : W := 0x7b01f80fc0df07f01f80cc0fb
def v278 : W := 0x7b01f80fc0df07f01f80f00fc
def v279 : W := 0x7b01f80fc0df07f01f80fc0ff
def v280 : W := 0x7b01fab5d79f07f01f870c303
def v281 : W := 0x7b01ffb03fa007f01fff03f00
def v282 : W := 0x7b01ffb5ffbf07f01fff0ff03
def v283 : W := 0x7b01ffbfc0c007f01ffffc000
def v284 : W := 0x7b01ffbfffe007f01ffffff00
def v285 : W := 0x7b56b80fd75f07f0e180fc303
def v286 : W := 0x7bf6000fff6007ffe000fff00
def v287 : W := 0x7bf607bfff6007ffe07ffff00
def v288 : W := 0x7bf6b80fff7f07ffe180fff03
def v289 : W := 0x7bf7f800008007ffff8000000
def v290 : W := 0x7bf7f8003fa007ffff8003f00
def v291 : W := 0x7bf7f80fc0c007ffff80fc000
def v292 : W := 0x7bf7f80fffe007ffff80fff00
def v293 : W := 0x7bf7ffb03fa007ffffff03f00
def v294 : W := 0x7bf7ffbfc0c007fffffffc000
def v295 : W := 0x7bf7ffbfffe007fffffffff00
def v296 : W := 0x8408004000000070e1870c303
def v297 : W := 0x8408004000000800e00700300
def v298 : W := 0x840800400000087000070c000
def v299 : W := 0x8408004000000870e18000000
def v300 : W := 0x84080040000031f3e79f3cf07
def v301 : W := 0x840800400000c67cf9e7cf30b
def v302 : W := 0x840807f03f200800e07f03f00
def v303 : W := 0x840807ffc0400870007ffc000
def v304 : W := 0x84fe00403f20080fe00703f00
def v305 : W := 0x84fff8400080087fff8000000
def v306 : W := 0xff08004fc0400ff00007fc000
def v307 : W := 0xff09f84000800ff0ff8000000
def v308 : W := 0x10012009005000000000000000
def v309 : W := 0x10012009005003003001800c00
def v310 : W := 0x10900009140000000000000000
def v311 : W := 0x10900009140003180001830000
def v312 : W := 0x10912280000000000000000000
def v313 : W := 0x10912280000003183060000000
def v314 : W := 0x10912289145050000000000000
def v315 : W := 0x10912289145053183061830c04
def v316 : W := 0x10912289145150000000000000
def v317 : W := 0x10912289145153183061830c04
def v318 : W := 0x109122ab5d71f000000070c303
def v319 : W := 0x109122d9b6d750000001830cf4
def v320 : W := 0x109122d9b6d753183061830cf4
def v321 : W := 0x10956b891571f0000e18000303
def v322 : W := 0x109b368916db50003060000cf4
def v323 : W := 0x109b368916db53183061830cf4
def v324 : W := 0x12b12b895c51f007001800c003
def v325 : W := 0x15913689b45d501800600300f4
def v326 : W := 0x15913689b45d53183061830cf4
def v327 : W := 0x1840800d000003800001f00000
def v328 : W := 0x1840807f03f203800007f03f00
def v329 : W := 0x1840807ffc0403800007ffc000
def v330 : W := 0x1841a004000003803e00000000
def v331 : W := 0x1841a00d005000000e00700300
def v332 : W := 0x1841a00d005003803e01f00f00
def v333 : W := 0x1841a00d03f203803e01f03f00
def v334 : W := 0x1841a05d02d203803e01f00f00
def v335 : W := 0x1841a05d02d203803e07f03f00
def v336 : W := 0x1841a07603a203803e06003000
def v337 : W := 0x1841a07f03f200000e07f03f00
def v338 : W := 0x1841a07f03f203803e07f03f00
def v339 : W := 0x184ba00d02d203803e01f00f00
def v340 : W := 0x184ba00d02d20380fe01f03f00
def v341 : W := 0x184ec00d03a20380c001f03000
def v342 : W := 0x184fe00403f20380fe00003f00
def v343 : W := 0x184fe00d03f20000fe00703f00
def v344 : W := 0x184fe00d03f20380fe01f03f00
def v345 : W := 0x184fe07f03f20380fe07f03f00
def v346 : W := 0x184fff8400080380fff8000000
def v347 : W := 0x18d080040000039f0000000000
def v348 : W := 0x18d0800d14000007000070c000
def v349 : W := 0x18d0800d1400039f0001f3c000
def v350 : W := 0x18d0800dfc04039f0001ffc000
def v351 : W := 0x18d0805db404039f0001f3c000
def v352 : W := 0x18d0805db404039f0007ffc000
def v353 : W := 0x18d08076e804039f00060c0000
def v354 : W := 0x18d0807ffc0400070007ffc000
def v355 : W := 0x18d0807ffc04039f0007ffc000
def v356 : W := 0x18d1a00d1450039f3e01f3cf00
def v357 : W := 0x18d1a284000000070e18000000
def v358 : W := 0x18d1a2840000039f3e78000000
def v359 : W := 0x18d1a28d0050039f3e79f00f00
def v360 : W := 0x18d1a28d1400039f3e79f3c000
def v361 : W := 0x18d1a28d145050070e1870c303
def v362 : W := 0x18d1a28d1450531f3e79f3cf07
def v363 : W := 0x18d1a28d145053873e19f0cf03
def v364 : W := 0x18d1a28d145053983e61f30f04
def v365 : W := 0x18d1a28d1450539f0e19f3c303
def v366 : W := 0x18d1a28d1450539f3061f3cc04
def v367 : W := 0x18d1a28d1450539f3e7870c303
def v368 : W := 0x18d1a28d1450539f3e79830c04
def v369 : W := 0x18d1a28d1450539f3e79f3cf07
def v370 : W := 0x18d1a28d145150070e1870c303
def v371 : W := 0x18d1a2af5d71f0070e1870c303
def v372 : W := 0x18d1a2ddb6d7539f3e79830cf4
def v373 : W := 0x18d1a2f6eba7a39f3e7e0c30f8
def v374 : W := 0x18d1bf840008039f3ff8000000
def v375 : W := 0x18d5eb8d1571f0070e1870c303
def v376 : W := 0x18dbb6840008039f3e78000000
def v377 : W := 0x18dbb6840008039ffff8000000
def v378 : W := 0x18dbb68d16db539f3061f3ccf4
def v379 : W := 0x18dedd040008039fc180000000
def v380 : W := 0x18dedd0d17aba39fc181f3f0f8
def v381 : W := 0x18dfff8400080007fff8000000
def v382 : W := 0x18dfff840008039ffff8000000
def v383 : W := 0x1af1ab8d5c51f0070e1870c303
def v384 : W := 0x1dd0800db404039f0001f3c000
def v385 : W := 0x1dd0800db40403ff0001ffc000
def v386 : W := 0x1dd1b6840008039f3e78000000
def v387 : W := 0x1dd1b684000803ff3ff8000000
def v388 : W := 0x1dd1b68db45d53983e61f30ff4
def v389 : W := 0x1f60800de80403e00001fc0000
def v390 : W := 0x1f61bd04000803e03f80000000
def v391 : W := 0x1f61bd0de85da3e03f81fc0ff8
def v392 : W := 0x1ff08004fc0403ff00000fc000
def v393 : W := 0x1ff0800dfc04007f00007fc000
def v394 : W := 0x1ff0800dfc0403ff0001ffc000
def v395 : W := 0x1ff0807ffc0403ff0007ffc000
def v396 : W := 0x1ff09f84000803ff01f8000000
def v397 : W := 0x1ff1bf840008007f0ff8000000
def v398 : W := 0x1ff1bf84000803ff3ff8000000
def v399 : W := 0x1fffff84000803fffff8000000
def v400 : W := 0x40044022012000000000000000
def v401 : W := 0x4004402201200c00c006003000
def v402 : W := 0x42200022480000000000000000
def v403 : W := 0x4220002248000c6000060c0000
def v404 : W := 0x42244900000000000000000000
def v405 : W := 0x4224490000000c60c180000000
def v406 : W := 0x422449224920a0000000000000
def v407 : W := 0x422449224920ac60c1860c3008
def v408 : W := 0x422449224921a0000000000000
def v409 : W := 0x422449224921ac60c1860c3008
def v410 : W := 0x4224492b5d71f000000070c303
def v411 : W := 0x42244972eba7a00000060c30f8
def v412 : W := 0x42244972eba7ac60c1860c30f8
def v413 : W := 0x42256ba24971f0000e18000303
def v414 : W := 0x422e5d224baba000c1800030f8
def v415 : W := 0x422e5d224babac60c1860c30f8
def v416 : W := 0x42b44ba25d21f007001800c003
def v417 : W := 0x47245d22e92da06001800c00f8
def v418 : W := 0x47245d22e92dac60c1860c30f8
def v419 : W := 0x4840802600000c800006700000
def v420 : W := 0x4840807f03f20c800007f03f00
def v421 : W := 0x4840807ffc040c800007ffc000
def v422 : W := 0x4844c00400000c80ce00000000
def v423 : W := 0x4844c026012000000e00700300
def v424 : W := 0x4844c02601200c80ce06703300
def v425 : W := 0x4844c02603f20c80ce06703f00
def v426 : W := 0x4844c05d02d20c80ce01800c00
def v427 : W := 0x4844c07603a20c80ce06703300
def v428 : W := 0x4844c07603a20c80ce07f03f00
def v429 : W := 0x4844c07f03f200000e07f03f00
def v430 : W := 0x4844c07f03f20c80ce07f03f00
def v431 : W := 0x484ba02602d20c803006700c00
def v432 : W := 0x484ec02603a20c80ce06703300
def v433 : W := 0x484ec02603a20c80fe06703f00
def v434 : W := 0x484fe00403f20c80fe00003f00
def v435 : W := 0x484fe02603f20000fe00703f00
def v436 : W := 0x484fe02603f20c80fe06703f00
def v437 : W := 0x484fe07f03f20c80fe07f03f00
def v438 : W := 0x484fff8400080c80fff8000000
def v439 : W := 0x4a60800400000ce70000000000
def v440 : W := 0x4a60802648000007000070c000
def v441 : W := 0x4a60802648000ce700067cc000
def v442 : W := 0x4a608026fc040ce700067fc000
def v443 : W := 0x4a60805db4040ce70001830000
def v444 : W := 0x4a608076e8040ce700067cc000
def v445 : W := 0x4a608076e8040ce70007ffc000
def v446 : W := 0x4a60807ffc0400070007ffc000
def v447 : W := 0x4a60807ffc040ce70007ffc000
def v448 : W := 0x4a64c02649200ce7ce067cf300
def v449 : W := 0x4a64c904000000070e18000000
def v450 : W := 0x4a64c90400000ce7cf98000000
def v451 : W := 0x4a64c92601200ce7cf9e703300
def v452 : W := 0x4a64c92648000ce7cf9e7cc000
def v453 : W := 0x4a64c9264920a0070e1870c303
def v454 : W := 0x4a64c9264920ac67cf9e7cf30b
def v455 : W := 0x4a64c9264920ac87ce1e70f303
def v456 : W := 0x4a64c9264920ace0cf867c3308
def v457 : W := 0x4a64c9264920ace70e1e7cc303
def v458 : W := 0x4a64c9264920ace7c1867cf008
def v459 : W := 0x4a64c9264920ace7cf9870c303
def v460 : W := 0x4a64c9264920ace7cf9e0c3008
def v461 : W := 0x4a64c9264920ace7cf9e7cf30b
def v462 : W := 0x4a64c9264921a0070e1870c303
def v463 : W := 0x4a64c92f5d71f0070e1870c303
def v464 : W := 0x4a64c95db6d75ce7cf99830cf4
def v465 : W := 0x4a64c976eba7ace7cf9e0c30f8
def v466 : W := 0x4a64df8400080ce7cff8000000
def v467 : W := 0x4a65eba64971f0070e1870c303
def v468 : W := 0x4a6bb68400080ce73060000000
def v469 : W := 0x4a6bb6a64adb5ce730667cccf4
def v470 : W := 0x4a6edd0400080ce7cf98000000
def v471 : W := 0x4a6edd0400080ce7fff8000000
def v472 : W := 0x4a6edd264babace7c1867cf0f8
def v473 : W := 0x4a6fff8400080007fff8000000
def v474 : W := 0x4a6fff8400080ce7fff8000000
def v475 : W := 0x4af4cba65d21f0070e1870c303
def v476 : W := 0x4dd08026b4040c980006730000
def v477 : W := 0x4dd4d68400080c98ce60000000
def v478 : W := 0x4dd4d6a6b52d5c98ce667333f4
def v479 : W := 0x4f608026e8040ce700067cc000
def v480 : W := 0x4f608026e8040cff00067fc000
def v481 : W := 0x4f64dd0400080ce7cf98000000
def v482 : W := 0x4f64dd0400080cffcff8000000
def v483 : W := 0x4f64dd26e92dace0cf867c33f8
def v484 : W := 0x4ff08004fc040cff00000fc000
def v485 : W := 0x4ff08026fc04007f00007fc000
def v486 : W := 0x4ff08026fc040cff00067fc000
def v487 : W := 0x4ff0807ffc040cff0007ffc000
def v488 : W := 0x4ff09f8400080cff01f8000000
def v489 : W := 0x4ff4df840008007f0ff8000000
def v490 : W := 0x4ff4df8400080cffcff8000000
def v491 : W := 0x4fffff8400080cfffff8000000
def v492 : W := 0x52b56bab5d70ff78f1e78f3c0c
def v493 : W := 0x52b56bab5d71f0000000000000
def v494 : W := 0x52b56bab5d71f3183061830c04
def v495 : W := 0x52b56bab5d71fc60c1860c3008
def v496 : W := 0x52b56bab5d71ff78f1e78f3c0c
def v497 : W := 0x5840802f000000000000700000
def v498 : W := 0x5840807f03f200000007f03f00
def v499 : W := 0x5840807ffc0400000007ffc000
def v500 : W := 0x5845e004000000000e00000000
def v501 : W := 0x5845e02f017000000e00700300
def v502 : W := 0x5845e02f017003803e01f00f00
def v503 : W := 0x5845e02f01700c80ce06703300
def v504 : W := 0x5845e02f01700f80fe07f03f00
def v505 : W := 0x5845e02f03f200000e00703f00
def v506 : W := 0x5845e02f5d71f0000e0070c303
def v507 : W := 0x5845e054028200000e07803c00
def v508 : W := 0x5845e07f03f200000e01f00f00
def v509 : W := 0x5845e07f03f200000e06703300
def v510 : W := 0x5845e07f03f200000e07f03f00
def v511 : W := 0x5845e07f03f203803e07f03f00
def v512 : W := 0x5845e07f03f20c80ce07f03f00
def v513 : W := 0x5845e07f03f20f80fe07f03f00
def v514 : W := 0x5845ebaf0171f0000e18700303
def v515 : W := 0x584a802f02820000f000703c00
def v516 : W := 0x584fe00403f20000fe00003f00
def v517 : W := 0x584fe02f03f200003e00700f00
def v518 : W := 0x584fe02f03f20000ce00703300
def v519 : W := 0x584fe02f03f20000fe00703f00
def v520 : W := 0x584fe02f03f20380fe01f03f00
def v521 : W := 0x584fe02f03f20c80fe06703f00
def v522 : W := 0x584fe02f03f20f80fe07f03f00
def v523 : W := 0x584fe07f03f20000fe07f03f00
def v524 : W := 0x584fff8400080000fff8000000
def v525 : W := 0x58d5e2af157050070e1870c303
def v526 : W := 0x58d5e2af157150000e00700300
def v527 : W := 0x5a65e92f4970a0070e1870c303
def v528 : W := 0x5a65e92f4971a0000e00700300
def v529 : W := 0x5af08004000000070000000000
def v530 : W := 0x5af0802f5c000007000070c000
def v531 : W := 0x5af0802f5c00039f0001f3c000
def v532 : W := 0x5af0802f5c000ce700067cc000
def v533 : W := 0x5af0802f5c000fff0007ffc000
def v534 : W := 0x5af0802f5d71f007000070c303
def v535 : W := 0x5af0802ffc04000700007fc000
def v536 : W := 0x5af08054a004000700078f0000
def v537 : W := 0x5af0807ffc0400070001f3c000
def v538 : W := 0x5af0807ffc04000700067cc000
def v539 : W := 0x5af0807ffc0400070007ffc000
def v540 : W := 0x5af0807ffc04039f0007ffc000
def v541 : W := 0x5af0807ffc040ce70007ffc000
def v542 : W := 0x5af0807ffc040fff0007ffc000
def v543 : W := 0x5af08baf5c01f007001870c003
def v544 : W := 0x5af1a2af5c5050070e1870c303
def v545 : W := 0x5af1a2af5c515007000070c000
def v546 : W := 0x5af4c92f5d20a0070e1870c303
def v547 : W := 0x5af4c92f5d21a007000070c000
def v548 : W := 0x5af5e02f5d7000070e0070c300
def v549 : W := 0x5af5eb84000000070e18000000
def v550 : W := 0x5af5eb840000039f3e78000000
def v551 : W := 0x5af5eb8400000ce7cf98000000
def v552 : W := 0x5af5eb8400000ffffff8000000
def v553 : W := 0x5af5eb840171f0070e18000303
def v554 : W := 0x5af5eb845c01f0070e1800c003
def v555 : W := 0x5af5eb8d145050070e1870c303
def v556 : W := 0x5af5eb8d145150070e18000000
def v557 : W := 0x5af5eba64920a0070e1870c303
def v558 : W := 0x5af5eba64921a0070e18000000
def v559 : W := 0x5af5ebaf017000070e18700300
def v560 : W := 0x5af5ebaf5c0000070e1870c000
def v561 : W := 0x5af5ebaf5d70f0070e1870c303
def v562 : W := 0x5af5ebaf5d71f0000e00700300
def v563 : W := 0x5af5ebaf5d71f007000070c000
def v564 : W := 0x5af5ebaf5d71f0070e18000000
def v565 : W := 0x5af5ebaf5d71f0070e1870c303
def v566 : W := 0x5af5ebaf5d71f31f3e79f3cf07
def v567 : W := 0x5af5ebaf5d71f3873e19f0cf03
def v568 : W := 0x5af5ebaf5d71f39f0e19f3c303
def v569 : W := 0x5af5ebaf5d71f39f3e7870c303
def v570 : W := 0x5af5ebaf5d71fc67cf9e7cf30b
def v571 : W := 0x5af5ebaf5d71fc87ce1e70f303
def v572 : W := 0x5af5ebaf5d71fce70e1e7cc303
def v573 : W := 0x5af5ebaf5d71fce7cf9870c303
def v574 : W := 0x5af5ebddb6d750070e19830cf4
def v575 : W := 0x5af5ebf6eba7a0070e1e0c30f8
def v576 : W := 0x5af5ebff5ff3f0070e1ff0ff03
def v577 : W := 0x5af5ebfffd75f0070e1fffc303
def v578 : W := 0x5af5ebfffff7f0070e19f3cff7
def v579 : W := 0x5af5ebfffff7f0070e1e7cf3fb
def v580 : W := 0x5af5ff84000800070ff8000000
def v581 : W := 0x5afa940400080007f1e0000000
def v582 : W := 0x5afbb6af5edb5007306070ccf4
def v583 : W := 0x5afedd2f5faba007c18070f0f8
def v584 : W := 0x5affebaf5ff3f007fe1870ff03
def v585 : W := 0x5affff84000800073e78000000
def v586 : W := 0x5affff8400080007cf98000000
def v587 : W := 0x5affff8400080007fff8000000
def v588 : W := 0x5affff840008039ffff8000000
def v589 : W := 0x5affff8400080ce7fff8000000
def v590 : W := 0x5affff8400080ffffff8000000
def v591 : W := 0x5affffaf5d79f007fff870c303
def v592 : W := 0x5affffaf5ffbf0073e7870cff7
def v593 : W := 0x5affffaf5ffbf007cf9870f3fb
def v594 : W := 0x5d40802fa004007800007f0000
def v595 : W := 0x5d45f404000800780fe0000000
def v596 : W := 0x5dd5f6afb57d50180e607303f4
def v597 : W := 0x5f65fd2fe97da0600f807c03f8
def v598 : W := 0x5ff08004fc04007f00000fc000
def v599 : W := 0x5ff0802ffc04001f000073c000
def v600 : W := 0x5ff0802ffc04006700007cc000
def v601 : W := 0x5ff0802ffc04007f00007fc000
def v602 : W := 0x5ff0802ffc0403ff0001ffc000
def v603 : W := 0x5ff0802ffc040cff00067fc000
def v604 : W := 0x5ff0802ffc040fff0007ffc000
def v605 : W := 0x5ff0807ffc04007f0007ffc000
def v606 : W := 0x5ff09f840008007f01f8000000
def v607 : W := 0x5ff5ebaffd75f07f0e187fc303
def v608 : W := 0x5ff5ff840008001f0e78000000
def v609 : W := 0x5ff5ff84000800670f98000000
def v610 : W := 0x5ff5ff840008007f0ff8000000
def v611 : W := 0x5ff5ff84000803ff3ff8000000
def v612 : W := 0x5ff5ff8400080cffcff8000000
def v613 : W := 0x5ff5ff8400080ffffff8000000
def v614 : W := 0x5ff5ffaf5d79f07f0ff870c303
def v615 : W := 0x5ff5ffaffd7df01f0e7873c3f7
def v616 : W := 0x5ff5ffaffd7df0670f987cc3fb
def v617 : W := 0x5fffff840008007ffff8000000
def v618 : W := 0xa000005000000f800007800000
def v619 : W := 0xa00a000000000f80f000000000
def v620 : W := 0xa00a0050028200000000000000
def v621 : W := 0xa00a0050028203003001800c00
def v622 : W := 0xa00a005002820c00c006003000
def v623 : W := 0xa00a005002820f80f007803c00
def v624 : W := 0xa00a007b03f20f80f007f03f00
def v625 : W := 0xa00f605003f20f80fe07803f00
def v626 : W := 0xa2ba0bd05e83ff87f01f80fc03
def v627 : W := 0xa500000000000ff80000000000
def v628 : W := 0xa5000050a00400000000000000
def v629 : W := 0xa5000050a00403180001830000
def v630 : W := 0xa5000050a0040c6000060c0000
def v631 : W := 0xa5000050a0040ff800078f0000
def v632 : W := 0xa500007bfc040ff80007ffc000
def v633 : W := 0xa5056bd0a175fff80e1f8f0303
def v634 : W := 0xa50a0050a2860ff8f0078f3c00
def v635 : W := 0xa50a1400000800000000000000
def v636 : W := 0xa50a1400000803183060000000
def v637 : W := 0xa50a140000080c60c180000000
def v638 : W := 0xa50a140000080ff8f1e0000000
def v639 : W := 0xa50a142b5d79fff8f1e070c303
def v640 : W := 0xa50a1450028a0ff8f1e7803c00
def v641 : W := 0xa50a1450a00c0ff8f1e78f0000
def v642 : W := 0xa50a1450a28e000000000000f0
def v643 : W := 0xa50a1450a28e03183061830cf4
def v644 : W := 0xa50a1450a28e0c60c1860c30f8
def v645 : W := 0xa50a1450a28e0f78f1e78f3cfc
def v646 : W := 0xa50a1450a28e0f98f067833cf4
def v647 : W := 0xa50a1450a28e0fe0f1878c3cf8
def v648 : W := 0xa50a1450a28e0ff830678f0cf4
def v649 : W := 0xa50a1450a28e0ff8c1878f30f8
def v650 : W := 0xa50a1450a28e0ff8f1e1830cf4
def v651 : W := 0xa50a1450a28e0ff8f1e60c30f8
def v652 : W := 0xa50a1450a28e0ff8f1e78f3cfc
def v653 : W := 0xa50a1450a28f000000000000f0
def v654 : W := 0xa50a1450a28f03183061830cf4
def v655 : W := 0xa50a1450a28f0c60c1860c30f8
def v656 : W := 0xa50a1459b6df50000001830cf4
def v657 : W := 0xa50a1459b6df53183061830cf4
def v658 : W := 0xa50a1472ebafa00000060c30f8
def v659 : W := 0xa50a1472ebafac60c1860c30f8
def v660 : W := 0xa50a147b03fa0ff8f1e7f03f00
def v661 : W := 0xa50a147bfc0c0ff8f1e7ffc000
def v662 : W := 0xa50b36d0a2df50003060000cf4
def v663 : W := 0xa50b36d0a2df53183061830cf4
def v664 : W := 0xa50e5d50a3afa000c1800030f8
def v665 : W := 0xa50e5d50a3afac60c1860c30f8
def v666 : W := 0xa50f6050a3f60ff8fe078f3f00
def v667 : W := 0xa50f7f8000080ff8fff8000000
def v668 : W := 0xa50f7fd0a00c0ff8ffff8f0000
def v669 : W := 0xa50f7ffbfc0c0ff8ffffffc000
def v670 : W := 0xa59a16d0b68f501800600300f4
def v671 : W := 0xa59a16d0b68f53183061830cf4
def v672 : W := 0xa72a1d50ea8fa06001800c00f8
def v673 : W := 0xa72a1d50ea8fac60c1860c30f8
def v674 : W := 0xa7b00050fc040fff00078fc000
def v675 : W := 0xa7ba0050fe860ffff0078ffc00
def v676 : W := 0xa7ba1f8000080ffff1f8000000
def v677 : W := 0xa7ba1fd0028a0ffff1ff803c00
def v678 : W := 0xa7ba1ffb03fa0ffff1fff03f00
def v679 : W := 0xa7bf6050fff60ffffe078fff00
def v680 : W := 0xa84a8054028200800e00700300
def v681 : W := 0xa84a805402820f80fe07f03f00
def v682 : W := 0xad408054a0040087000070c000
def v683 : W := 0xad408054a0040fff0007ffc000
def v684 : W := 0xad4a9404000800870e18000000
def v685 : W := 0xad4a940400080ffffff8000000
def v686 : W := 0xad4a9454a28f00070e1870c3f3
def v687 : W := 0xb0000059000003000001800000
def v688 : W := 0xb00b2000000003003000000000
def v689 : W := 0xb00b205902d203003001800c00
def v690 : W := 0xb00b205902d20f80f007803c00
def v691 : W := 0xb00b2059b6d753003001830cf4
def v692 : W := 0xb00b207b03f203003007f03f00
def v693 : W := 0xb00b36d902db53003061800cf4
def v694 : W := 0xb00f605903f20300fe01803f00
def v695 : W := 0xb09b22d916d253183061830c04
def v696 : W := 0xb09b22d916d353003001800c00
def v697 : W := 0xb2bb2bd95ed3f307301980cc03
def v698 : W := 0xb50b3459a2de03183061830cf4
def v699 : W := 0xb50b3459a2df03003001800cf0
def v700 : W := 0xb5900000000003180000000000
def v701 : W := 0xb5900059b40403180001830000
def v702 : W := 0xb5900059b4040ff800078f0000
def v703 : W := 0xb5900059b6d753180001830cf4
def v704 : W := 0xb590007bfc0403180007ffc000
def v705 : W := 0xb59016d9b40d531800618300f4
def v706 : W := 0xb59122d9b45453183061830c04
def v707 : W := 0xb59122d9b45553180001830000
def v708 : W := 0xb5956bd9b575f3180e19830303
def v709 : W := 0xb59a1459b68e03183061830cf4
def v710 : W := 0xb59a1459b68f031800018300f0
def v711 : W := 0xb59b2059b6d603183001830c00
def v712 : W := 0xb59b3680000803183060000000
def v713 : W := 0xb59b368000080ff8f1e0000000
def v714 : W := 0xb59b368002db53183060000cf4
def v715 : W := 0xb59b3680b40d531830600300f4
def v716 : W := 0xb59b3689145853183061830c04
def v717 : W := 0xb59b3689145953183060000000
def v718 : W := 0xb59b36ab5d79f318306070c303
def v719 : W := 0xb59b36d0a28e03183061830cf4
def v720 : W := 0xb59b36d0a28f031830600000f0
def v721 : W := 0xb59b36d902da03183061800c00
def v722 : W := 0xb59b36d9b40c03183061830000
def v723 : W := 0xb59b36d9b6de500000000000f0
def v724 : W := 0xb59b36d9b6de53183061830cf4
def v725 : W := 0xb59b36d9b6df500000000000f0
def v726 : W := 0xb59b36d9b6df50000001830cf4
def v727 : W := 0xb59b36d9b6df50003060000cf4
def v728 : W := 0xb59b36d9b6df501800600300f4
def v729 : W := 0xb59b36d9b6df53003001800cf0
def v730 : W := 0xb59b36d9b6df531800018300f0
def v731 : W := 0xb59b36d9b6df531830600000f0
def v732 : W := 0xb59b36d9b6df53183061830cf4
def v733 : W := 0xb59b36d9b6df53983061830cf4
def v734 : W := 0xb59b36d9b6df5f78f1e78f3cfc
def v735 : W := 0xb59b36d9b6df5f98f067833cf4
def v736 : W := 0xb59b36d9b6df5ff830678f0cf4
def v737 : W := 0xb59b36d9b6df5ff8f1e1830cf4
def v738 : W := 0xb59b36fb03fa03183067f03f00
def v739 : W := 0xb59b36fbb7ff53183067f33ff4
def v740 : W := 0xb59b36fbfc0c03183067ffc000
def v741 : W := 0xb59b36fbfedf53183067ffccf4
def v742 : W := 0xb59b36fbfffff3183061830cf4
def v743 : W := 0xb59b36fbfffff3183061f3cff7
def v744 : W := 0xb59b36fbfffff31830678f3cfc
def v745 : W := 0xb59f6059b7f60318fe01833f00
def v746 : W := 0xb59f76d9b7ff5318fe61833ff4
def v747 : W := 0xb59f7f8000080318fff8000000
def v748 : W := 0xb59f7fd9b40c0318fff9830000
def v749 : W := 0xb59f7fd9b6df5318fff9830cf4
def v750 : W := 0xb59f7fd9b7fff3183061830cf4
def v751 : W := 0xb59f7fd9b7fff3183e79830ff7
def v752 : W := 0xb59f7fd9b7fff318f1e1833cfc
def v753 : W := 0xb59f7ffbfc0c0318ffffffc000
def v754 : W := 0xb7b00059fc04037f00018fc000
def v755 : W := 0xb7bb2059fed6037f30018fcc00
def v756 : W := 0xb7bb36d9fedf537f30618fccf4
def v757 : W := 0xb7bb3f800008037f31f8000000
def v758 : W := 0xb7bb3fd902da037f31f9800c00
def v759 : W := 0xb7bb3fd9b6df537f31f9830cf4
def v760 : W := 0xb7bb3fd9fedff3183061830cf4
def v761 : W := 0xb7bb3fd9fedff31f307983ccf7
def v762 : W := 0xb7bb3fd9fedff37831e18f0cfc
def v763 : W := 0xb7bb3ffb03fa037f31fff03f00
def v764 : W := 0xb7bf6059fff6037ffe018fff00
def v765 : W := 0xb84a805d02820f80f007f03c00
def v766 : W := 0xb84ba05402820f80fe07803c00
def v767 : W := 0xb84ba05d02d203003e01f00f00
def v768 : W := 0xb84ba05d02d203803001f00c00
def v769 : W := 0xb84ba05d02d203803e01800c00
def v770 : W := 0xb84ba05d02d203803e01f00f00
def v771 : W := 0xb84ba05d02d20c00ce06703300
def v772 : W := 0xb84ba05d02d20f80fe07f03f00
def v773 : W := 0xb84ba07f03f203803e07f03f00
def v774 : W := 0xb84ba07f03f20f80fe07f03f00
def v775 : W := 0xb84fe05d03f20380fe01f03f00
def v776 : W := 0xb84fe05d03f20f80fe07f03f00
def v777 : W := 0xbd40805da0040ff80007ff0000
def v778 : W := 0xbd4bb40400080ff8ffe0000000
def v779 : W := 0xbdd08054a0040fff00078f0000
def v780 : W := 0xbdd0805db404031f0001f3c000
def v781 : W := 0xbdd0805db40403980001f30000
def v782 : W := 0xbdd0805db404039f0001830000
def v783 : W := 0xbdd0805db404039f0001f3c000
def v784 : W := 0xbdd0805db4040c6700067cc000
def v785 : W := 0xbdd0805db4040fff0007ffc000
def v786 : W := 0xbdd0807ffc04039f0007ffc000
def v787 : W := 0xbdd0807ffc040fff0007ffc000
def v788 : W := 0xbdda940400080ffff1e0000000
def v789 : W := 0xbddbb6840008031f3e78000000
def v790 : W := 0xbddbb684000803983e60000000
def v791 : W := 0xbddbb6840008039f3060000000
def v792 : W := 0xbddbb6840008039f3e78000000
def v793 : W := 0xbddbb68400080c67cf98000000
def v794 : W := 0xbddbb68400080ffffff8000000
def v795 : W := 0xbddbb6ddb6de5c67cf9e7cf3fb
def v796 : W := 0xbddbb6ddb6df50070e1870c3f3
def v797 : W := 0xbddbb6ddb6df531f3e79f3cff7
def v798 : W := 0xbddbb6ddb6df53983e61f30ff4
def v799 : W := 0xbddbb6ddb6df539f3061f3ccf4
def v800 : W := 0xbddbb6ddb6df539f3e79830cf4
def v801 : W := 0xbddfff840008039ffff8000000
def v802 : W := 0xbddfff8400080ffffff8000000
def v803 : W := 0xbff0805dfc0403ff0001ffc000
def v804 : W := 0xbff0805dfc040fff0007ffc000
def v805 : W := 0xbffbbf84000803ff3ff8000000
def v806 : W := 0xbffbbf8400080ffffff8000000
def v807 : W := 0xe000007200000c000006000000
def v808 : W := 0xe00e400000000c00c000000000
def v809 : W := 0xe00e407203a20c00c006003000
def v810 : W := 0xe00e407203a20f80f007803c00
def v811 : W := 0xe00e4072eba7ac00c0060c30f8
def v812 : W := 0xe00e407b03f20c00c007f03f00
def v813 : W := 0xe00e5d7203abac00c1860030f8
def v814 : W := 0xe00f607203f20c00fe06003f00
def v815 : W := 0xe22e49724ba2ac60c1860c3008
def v816 : W := 0xe22e49724ba3ac00c006003000
def v817 : W := 0xe2be4bf25fa3fc07c01e00f003
def v818 : W := 0xe50e5472a3ae0c60c1860c30f8
def v819 : W := 0xe50e5472a3af0c00c0060030f0
def v820 : W := 0xe720000000000c600000000000
def v821 : W := 0xe7200072e8040c6000060c0000
def v822 : W := 0xe7200072e8040ff800078f0000
def v823 : W := 0xe7200072eba7ac6000060c30f8
def v824 : W := 0xe720007bfc040c600007ffc000
def v825 : W := 0xe7201d72e80dac6001860c00f8
def v826 : W := 0xe7244972e924ac60c1860c3008
def v827 : W := 0xe7244972e925ac6000060c0000
def v828 : W := 0xe7256bf2e975fc600e1e0c0303
def v829 : W := 0xe72a1472ea8e0c60c1860c30f8
def v830 : W := 0xe72a1472ea8f0c6000060c00f0
def v831 : W := 0xe72e4072eba60c60c0060c3000
def v832 : W := 0xe72e5d0000080c60c180000000
def v833 : W := 0xe72e5d0000080ff8f1e0000000
def v834 : W := 0xe72e5d0003abac60c1800030f8
def v835 : W := 0xe72e5d00e80dac60c1800c00f8
def v836 : W := 0xe72e5d224928ac60c1860c3008
def v837 : W := 0xe72e5d224929ac60c180000000
def v838 : W := 0xe72e5d2b5d79fc60c18070c303
def v839 : W := 0xe72e5d50a28e0c60c1860c30f8
def v840 : W := 0xe72e5d50a28f0c60c1800000f0
def v841 : W := 0xe72e5d7203aa0c60c186003000
def v842 : W := 0xe72e5d72e80c0c60c1860c0000
def v843 : W := 0xe72e5d72ebaea00000000000f0
def v844 : W := 0xe72e5d72ebaeac60c1860c30f8
def v845 : W := 0xe72e5d72ebafa00000000000f0
def v846 : W := 0xe72e5d72ebafa00000060c30f8
def v847 : W := 0xe72e5d72ebafa000c1800030f8
def v848 : W := 0xe72e5d72ebafa06001800c00f8
def v849 : W := 0xe72e5d72ebafac00c0060030f0
def v850 : W := 0xe72e5d72ebafac6000060c00f0
def v851 : W := 0xe72e5d72ebafac60c1800000f0
def v852 : W := 0xe72e5d72ebafac60c1860c30f8
def v853 : W := 0xe72e5d72ebaface0c1860c30f8
def v854 : W := 0xe72e5d72ebafaf78f1e78f3cfc
def v855 : W := 0xe72e5d72ebafafe0f1878c3cf8
def v856 : W := 0xe72e5d72ebafaff8c1878f30f8
def v857 : W := 0xe72e5d72ebafaff8f1e60c30f8
def v858 : W := 0xe72e5d7b03fa0c60c187f03f00
def v859 : W := 0xe72e5d7bebffac60c187fc3ff8
def v860 : W := 0xe72e5d7bfc0c0c60c187ffc000
def v861 : W := 0xe72e5d7bffafac60c187fff0f8
def v862 : W := 0xe72e5d7bfffffc60c1860c30f8
def v863 : W := 0xe72e5d7bfffffc60c1867cf3fb
def v864 : W := 0xe72e5d7bfffffc60c1878f3cfc
def v865 : W := 0xe72f6072ebf60c60fe060c3f00
def v866 : W := 0xe72f7d72ebffac60ff860c3ff8
def v867 : W := 0xe72f7f8000080c60fff8000000
def v868 : W := 0xe72f7ff2e80c0c60fffe0c0000
def v869 : W := 0xe72f7ff2ebafac60fffe0c30f8
def v870 : W := 0xe72f7ff2ebfffc60c1860c30f8
def v871 : W := 0xe72f7ff2ebfffc60cf9e0c33fb
def v872 : W := 0xe72f7ff2ebfffc60f1e60c3cfc
def v873 : W := 0xe72f7ffbfc0c0c60ffffffc000
def v874 : W := 0xe7b00072fc040c7f00060fc000
def v875 : W := 0xe7be4072ffa60c7fc0060ff000
def v876 : W := 0xe7be5d72ffafac7fc1860ff0f8
def v877 : W := 0xe7be5f8000080c7fc1f8000000
def v878 : W := 0xe7be5ff203aa0c7fc1fe003000
def v879 : W := 0xe7be5ff2ebafac7fc1fe0c30f8
def v880 : W := 0xe7be5ff2ffaffc60c1860c30f8
def v881 : W := 0xe7be5ff2ffaffc67c19e0cf0fb
def v882 : W := 0xe7be5ff2ffaffc78c1e60f30fc
def v883 : W := 0xe7be5ffb03fa0c7fc1fff03f00
def v884 : W := 0xe7bf6072fff60c7ffe060fff00
def v885 : W := 0xe84a807602820f80f007f03c00
def v886 : W := 0xe84ec05402820f80fe07803c00
def v887 : W := 0xe84ec07603a203003e01f00f00
def v888 : W := 0xe84ec07603a20c00ce06703300
def v889 : W := 0xe84ec07603a20c80c006703000
def v890 : W := 0xe84ec07603a20c80ce06003000
def v891 : W := 0xe84ec07603a20c80ce06703300
def v892 : W := 0xe84ec07603a20f80fe07f03f00
def v893 : W := 0xe84ec07f03f20c80ce07f03f00
def v894 : W := 0xe84ec07f03f20f80fe07f03f00
def v895 : W := 0xe84fe07603f20c80fe06703f00
def v896 : W := 0xe84fe07603f20f80fe07f03f00
def v897 : W := 0xed408076a0040ff80007ff0000
def v898 : W := 0xed4ed40400080ff8ffe0000000
def v899 : W := 0xef608054a0040fff00078f0000
def v900 : W := 0xef608076e804031f0001f3c000
def v901 : W := 0xef608076e8040c6700067cc000
def v902 : W := 0xef608076e8040ce000067c0000
def v903 : W := 0xef608076e8040ce700060c0000
def v904 : W := 0xef608076e8040ce700067cc000
def v905 : W := 0xef608076e8040fff0007ffc000
def v906 : W := 0xef60807ffc040ce70007ffc000
def v907 : W := 0xef60807ffc040fff0007ffc000
def v908 : W := 0xef6a940400080ffff1e0000000
def v909 : W := 0xef6edd040008031f3e78000000
def v910 : W := 0xef6edd0400080c67cf98000000
def v911 : W := 0xef6edd0400080ce0cf80000000
def v912 : W := 0xef6edd0400080ce7c180000000
def v913 : W := 0xef6edd0400080ce7cf98000000
def v914 : W := 0xef6edd0400080ffffff8000000
def v915 : W := 0xef6edd76ebaea31f3e79f3cff7
def v916 : W := 0xef6edd76ebafa0070e1870c3f3
def v917 : W := 0xef6edd76ebafac67cf9e7cf3fb
def v918 : W := 0xef6edd76ebaface0cf867c33f8
def v919 : W := 0xef6edd76ebaface7c1867cf0f8
def v920 : W := 0xef6edd76ebaface7cf9e0c30f8
def v921 : W := 0xef6fff8400080ce7fff8000000
def v922 : W := 0xef6fff8400080ffffff8000000
def v923 : W := 0xeff08076fc040cff00067fc000
def v924 : W := 0xeff08076fc040fff0007ffc000
def v925 : W := 0xeffedf8400080cffcff8000000
def v926 : W := 0xeffedf8400080ffffff8000000
def v927 : W := 0xf00f607b03f20f00f007803c00
def v928 : W := 0xf59f76fbb7ff53183061830cf4
def v929 : W := 0xf59f76fbb7ff5f18f067833cf4
def v930 : W := 0xf72f7d7bebffac60c1860c30f8
def v931 : W := 0xf72f7d7bebffaf60f1878c3cf8
def v932 : W := 0xf7b0007bfc040f7800078f0000
def v933 : W := 0xf7bb36fbfedf53183061830cf4
def v934 : W := 0xf7bb36fbfedf5f7830678f0cf4
def v935 : W := 0xf7be5d7bffafac60c1860c30f8
def v936 : W := 0xf7be5d7bffafaf78c1878f30f8
def v937 : W := 0xf7bf7f8000080f78f1e0000000
def v938 : W := 0xf7bf7fd9b6df53183061830cf4
def v939 : W := 0xf7bf7fd9b6df5f78f1e1830cf4
def v940 : W := 0xf7bf7ff2ebafac60c1860c30f8
def v941 : W := 0xf7bf7ff2ebafaf78f1e60c30f8
def v942 : W := 0xf7bf7ffbfffff00000000000f0
def v943 : W := 0xf7bf7ffbfffff3183061830cf4
def v944 : W := 0xf7bf7ffbfffffc60c1860c30f8
def v945 : W := 0xf7bf7ffbffffff78f1e78f3cfc
def v946 : W := 0xf840800400000f800000000000
def v947 : W := 0xf840800403f20f800000003f00
def v948 : W := 0xf8408004fc040f8000000fc000
def v949 : W := 0xf840807f00000f800007f00000
def v950 : W := 0xf840807f02820f800007f03c00
def v951 : W := 0xf840807f02d20f800007f00c00
def v952 : W := 0xf840807f03a20f800007f03000
def v953 : W := 0xf840807f03f20f800007f03f00
def v954 : W := 0xf840807fa0040f800007ff0000
def v955 : W := 0xf840807fb4040f800007f30000
def v956 : W := 0xf840807fe8040f800007fc0000
def v957 : W := 0xf840807ffc040f800007ffc000
def v958 : W := 0xf840807ffff60f800007ffff00
def v959 : W := 0xf84096ff00095f800067f000f4
def v960 : W := 0xf8409d7f0009af800187f000f8
def v961 : W := 0xf8409f8400080f8001f8000000
def v962 : W := 0xf841a07f00500f803e07f00f00
def v963 : W := 0xf841a07f03f20f803e07f03f00
def v964 : W := 0xf844c07f01200f80ce07f03300
def v965 : W := 0xf844c07f03f20f80ce07f03f00
def v966 : W := 0xf845e07f01700f800e07f00300
def v967 : W := 0xf845e07f03f20f800e07f03f00
def v968 : W := 0xf84a805402820f80f007803c00
def v969 : W := 0xf84a807f02820f800007f00000
def v970 : W := 0xf84a807f02820f803007f00c00
def v971 : W := 0xf84a807f02820f80c007f03000
def v972 : W := 0xf84a807f02820f80f007f03c00
def v973 : W := 0xf84a807f03f20f80f007f03f00
def v974 : W := 0xf84a807ffe860f80f007fffc00
def v975 : W := 0xf84ba05d02d20f803001800c00
def v976 : W := 0xf84ba07f02d203003001f00c00
def v977 : W := 0xf84ba07f02d20f803007f00c00
def v978 : W := 0xf84ba07f02d20f803e07f00f00
def v979 : W := 0xf84ba07f02d20f80f007f03c00
def v980 : W := 0xf84ba07f02d20f80fe07f03f00
def v981 : W := 0xf84ba07f03f20f803007f03f00
def v982 : W := 0xf84ba07ffed60f803007ffcc00
def v983 : W := 0xf84bb6ff02db5f803067f00cf4
def v984 : W := 0xf84ec07603a20f80c006003000
def v985 : W := 0xf84ec07f03a20c00c006703000
def v986 : W := 0xf84ec07f03a20f80c007f03000
def v987 : W := 0xf84ec07f03a20f80ce07f03300
def v988 : W := 0xf84ec07f03a20f80f007f03c00
def v989 : W := 0xf84ec07f03a20f80fe07f03f00
def v990 : W := 0xf84ec07f03f20f80c007f03f00
def v991 : W := 0xf84ec07fffa60f80c007fff000
def v992 : W := 0xf84edd7f03abaf80c187f030f8
def v993 : W := 0xf84fe00400000f80fe00000000
def v994 : W := 0xf84fe00402820f80fe00003c00
def v995 : W := 0xf84fe00402d20f80fe00000c00
def v996 : W := 0xf84fe00403a20f80fe00003000
def v997 : W := 0xf84fe00403f20f80fe00003f00
def v998 : W := 0xf84fe004b4055f80fe000300f4
def v999 : W := 0xf84fe004e805af80fe000c00f8
def v1000 : W := 0xf84fe00d00500f80fe01f00f00
def v1001 : W := 0xf84fe00d03f20f80fe01f03f00
def v1002 : W := 0xf84fe02601200f80fe06703300
def v1003 : W := 0xf84fe02603f20f80fe06703f00
def v1004 : W := 0xf84fe02f01700f80fe00700300
def v1005 : W := 0xf84fe02f03f20f80fe00703f00
def v1006 : W := 0xf84fe05402820f80fe00000000
def v1007 : W := 0xf84fe05402820f80fe01800c00
def v1008 : W := 0xf84fe05402820f80fe06003000
def v1009 : W := 0xf84fe05402820f80fe07803c00
def v1010 : W := 0xf84fe05403f20f80fe07803f00
def v1011 : W := 0xf84fe05d02d203003e01800c00
def v1012 : W := 0xf84fe05d02d20f80fe01800c00
def v1013 : W := 0xf84fe05d02d20f80fe01f00f00
def v1014 : W := 0xf84fe05d02d20f80fe07803c00
def v1015 : W := 0xf84fe05d02d20f80fe07f03f00
def v1016 : W := 0xf84fe05d03f20f80fe01803f00
def v1017 : W := 0xf84fe05db6d75f80fe01830cf4
def v1018 : W := 0xf84fe07603a20c00ce06003000
def v1019 : W := 0xf84fe07603a20f80fe06003000
def v1020 : W := 0xf84fe07603a20f80fe06703300
def v1021 : W := 0xf84fe07603a20f80fe07803c00
def v1022 : W := 0xf84fe07603a20f80fe07f03f00
def v1023 : W := 0xf84fe07603f20f80fe06003f00
def v1024 : W := 0xf84fe076eba7af80fe060c30f8
def v1025 : W := 0xf84fe07f00000f80fe07f00000
def v1026 : W := 0xf84fe07f02820f80fe07f03c00
def v1027 : W := 0xf84fe07f02d20f80fe07f00c00
def v1028 : W := 0xf84fe07f03a20f80fe07f03000
def v1029 : W := 0xf84fe07f03f200000e00700300
def v1030 : W := 0xf84fe07f03f203003e01f00f00
def v1031 : W := 0xf84fe07f03f203003e07f03f00
def v1032 : W := 0xf84fe07f03f20300fe01f03f00
def v1033 : W := 0xf84fe07f03f203803e01f00f00
def v1034 : W := 0xf84fe07f03f20c00ce06703300
def v1035 : W := 0xf84fe07f03f20c00ce07f03f00
def v1036 : W := 0xf84fe07f03f20c00fe06703f00
def v1037 : W := 0xf84fe07f03f20c80ce06703300
def v1038 : W := 0xf84fe07f03f20f00fe07f03f00
def v1039 : W := 0xf84fe07f03f20f803e07f00f00
def v1040 : W := 0xf84fe07f03f20f80ce07f03300
def v1041 : W := 0xf84fe07f03f20f80f007f03c00
def v1042 : W := 0xf84fe07f03f20f80fe01f00f00
def v1043 : W := 0xf84fe07f03f20f80fe06703300
def v1044 : W := 0xf84fe07f03f20f80fe07803c00
def v1045 : W := 0xf84fe07f03f20f80fe07f03f00
def v1046 : W := 0xf84fe07f03f20f98fe07f33f00
def v1047 : W := 0xf84fe07f03f20f98fe67f03f00
def v1048 : W := 0xf84fe07f03f20f98fe67f33f04
def v1049 : W := 0xf84fe07f03f20fe0fe07fc3f00
def v1050 : W := 0xf84fe07f03f20fe0ff87f03f00
def v1051 : W := 0xf84fe07f03f20fe0ff87fc3f08
def v1052 : W := 0xf84fe07f03f30f80fe07f03f00
def v1053 : W := 0xf84fe07f03f3ff80fe07f03f03
def v1054 : W := 0xf84fe07f17f20f80fe07f3ff00
def v1055 : W := 0xf84fe07f17f25f80fe07f0ff03
def v1056 : W := 0xf84fe07f17f25f80fe07f33f04
def v1057 : W := 0xf84fe07f17f35f80fe07f03f00
def v1058 : W := 0xf84fe07f4bf20f80fe07fcff00
def v1059 : W := 0xf84fe07f4bf2af80fe07f0ff03
def v1060 : W := 0xf84fe07f4bf2af80fe07fc3f08
def v1061 : W := 0xf84fe07f4bf3af80fe07f03f00
def v1062 : W := 0xf84fe07f5ff20f80fe07f0ff00
def v1063 : W := 0xf84fe07f5ff3ff80fe07f0ff03
def v1064 : W := 0xf84fe07fa3f60f80fe07ff3f00
def v1065 : W := 0xf84fe07fb7f60f80fe07f33f00
def v1066 : W := 0xf84fe07fb7f75f80fe07f33ff4
def v1067 : W := 0xf84fe07febf60f80fe07fc3f00
def v1068 : W := 0xf84fe07febf7af80fe07fc3ff8
def v1069 : W := 0xf84fe07ffff60f80fe07ffff00
def v1070 : W := 0xf84fe07ffff7ff80fe07ffff03
def v1071 : W := 0xf84fe2ff03f20f80fe7ff03f00
def v1072 : W := 0xf84fe2ff03f25f80fe1ff03f03
def v1073 : W := 0xf84fe2ff03f25f80fe67f03f04
def v1074 : W := 0xf84fe2ff03f35f80fe07f03f00
def v1075 : W := 0xf84fe97f03f20f80ff9ff03f00
def v1076 : W := 0xf84fe97f03f2af80fe1ff03f03
def v1077 : W := 0xf84fe97f03f2af80ff87f03f08
def v1078 : W := 0xf84fe97f03f3af80fe07f03f00
def v1079 : W := 0xf84febff03f20f80fe1ff03f00
def v1080 : W := 0xf84febff03f3ff80fe1ff03f03
def v1081 : W := 0xf84febff5ff3ff80fe1ff0ff03
def v1082 : W := 0xf84ff40400080f80ffe0000000
def v1083 : W := 0xf84ff47f03fa0f80ffe7f03f00
def v1084 : W := 0xf84ff68400080f80fe60000000
def v1085 : W := 0xf84ff6ff03fa0f80fe67f03f00
def v1086 : W := 0xf84ff6ff03fb5f80fe67f03ff4
def v1087 : W := 0xf84ffd0400080f80ff80000000
def v1088 : W := 0xf84ffd7f03fa0f80ff87f03f00
def v1089 : W := 0xf84ffd7f03fbaf80ff87f03ff8
def v1090 : W := 0xf84fff8400080f80fff8000000
def v1091 : W := 0xf84fff8403fa0f80fff8003f00
def v1092 : W := 0xf84fffd4028a0f80ffff803c00
def v1093 : W := 0xf84fffdd02da0f80fff9800c00
def v1094 : W := 0xf84ffff603aa0f80fffe003000
def v1095 : W := 0xf84fffff03fa0f80fffff03f00
def v1096 : W := 0xf84fffff03fbff80fffff03f03
def v1097 : W := 0xf84ffffffffe0f80ffffffff00
def v1098 : W := 0xf8d0807f14000f9f0007f3c000
def v1099 : W := 0xf8d0807ffc040f9f0007ffc000
def v1100 : W := 0xf8dfe07f17f20f80fe07f03f00
def v1101 : W := 0xf8dfe07f17f20f98fe07f33f00
def v1102 : W := 0xf8dfe07f17f20f9ffe07f3ff00
def v1103 : W := 0xf8dfe28400000f9ffe78000000
def v1104 : W := 0xf8dfe2ff03f20f80fe07f03f00
def v1105 : W := 0xf8dfe2ff03f20f98fe67f03f00
def v1106 : W := 0xf8dfe2ff03f20f9ffe7ff03f00
def v1107 : W := 0xf8dfe2ff17f25f80fe07f03f00
def v1108 : W := 0xf8dfe2ff17f25f87fe1ff0ff03
def v1109 : W := 0xf8dfe2ff17f25f98fe67f33f04
def v1110 : W := 0xf8dfe2ff17f35f80fe07f03f00
def v1111 : W := 0xf8dfe2ff17f35f98fe67f33f04
def v1112 : W := 0xf8dfe2ff5ff3ff80fe07f0ff03
def v1113 : W := 0xf8dfebff17f3ff80fe1ff03f03
def v1114 : W := 0xf8dfff8400080f9ffff8000000
def v1115 : W := 0xfa60807f48000fe70007fcc000
def v1116 : W := 0xfa60807ffc040fe70007ffc000
def v1117 : W := 0xfa6fe07f4bf20f80fe07f03f00
def v1118 : W := 0xfa6fe07f4bf20fe0fe07fc3f00
def v1119 : W := 0xfa6fe07f4bf20fe7fe07fcff00
def v1120 : W := 0xfa6fe90400000fe7ff98000000
def v1121 : W := 0xfa6fe97f03f20f80fe07f03f00
def v1122 : W := 0xfa6fe97f03f20fe0ff87f03f00
def v1123 : W := 0xfa6fe97f03f20fe7ff9ff03f00
def v1124 : W := 0xfa6fe97f4bf2af80fe07f03f00
def v1125 : W := 0xfa6fe97f4bf2af87fe1ff0ff03
def v1126 : W := 0xfa6fe97f4bf2afe0ff87fc3f08
def v1127 : W := 0xfa6fe97f4bf3af80fe07f03f00
def v1128 : W := 0xfa6fe97f4bf3afe0ff87fc3f08
def v1129 : W := 0xfa6fe97f5ff3ff80fe07f0ff03
def v1130 : W := 0xfa6febff4bf3ff80fe1ff03f03
def v1131 : W := 0xfa6fff8400080fe7fff8000000
def v1132 : W := 0xfaf0807f5c000f870007f0c000
def v1133 : W := 0xfaf0807ffc040f870007ffc000
def v1134 : W := 0xfaf5ebff5d71ff870e1ff0c303
def v1135 : W := 0xfaffe07f5ff20f87fe07f0ff00
def v1136 : W := 0xfaffeb8400000f87fe18000000
def v1137 : W := 0xfaffebaf5d71ff87fe1870c303
def v1138 : W := 0xfaffebff03f20f87fe1ff03f00
def v1139 : W := 0xfaffebff5ff2fff8ffe7ff3f0c
def v1140 : W := 0xfaffebff5ff3f0070e1870c303
def v1141 : W := 0xfaffebff5ff3f3073e19f0cf03
def v1142 : W := 0xfaffebff5ff3fc07ce1e70f303
def v1143 : W := 0xfaffebff5ff3ff80fe07f03f00
def v1144 : W := 0xfaffebff5ff3ff87fe1ff0ff03
def v1145 : W := 0xfaffff8400080f87fff8000000
def v1146 : W := 0xfd408054a0040ff800078f0000
def v1147 : W := 0xfd40807fa0040f800007f00000
def v1148 : W := 0xfd40807fa0040f980007f30000
def v1149 : W := 0xfd40807fa0040fe00007fc0000
def v1150 : W := 0xfd40807fa0040ff80007ff0000
def v1151 : W := 0xfd40807fa3f60ff80007ff3f00
def v1152 : W := 0xfd40807ffc040ff80007ffc000
def v1153 : W := 0xfd4a807fa2860ff8f007ff3c00
def v1154 : W := 0xfd4a940400080ff8f1e0000000
def v1155 : W := 0xfd4ba07fa2d60ff83007ff0c00
def v1156 : W := 0xfd4ec07fa3a60ff8c007ff3000
def v1157 : W := 0xfd4fe07f03f20ff8fe07f03f00
def v1158 : W := 0xfd4fe07fa3f60f80fe07f03f00
def v1159 : W := 0xfd4fe07fa3f60f98fe07f33f00
def v1160 : W := 0xfd4fe07fa3f60fe0fe07fc3f00
def v1161 : W := 0xfd4fe07fa3f60ff8fe07ff3f00
def v1162 : W := 0xfd4fe07ffff60ff8fe07ffff00
def v1163 : W := 0xfd4febffa3f7fff8fe1fff3f03
def v1164 : W := 0xfd4ff40400080f80fe00000000
def v1165 : W := 0xfd4ff40400080f98fe60000000
def v1166 : W := 0xfd4ff40400080fe0ff80000000
def v1167 : W := 0xfd4ff40400080ff8ffe0000000
def v1168 : W := 0xfd4ff40403fa0ff8ffe0003f00
def v1169 : W := 0xfd4ff454028a0ff8ffe7803c00
def v1170 : W := 0xfd4ff45d02da0ff8ffe1800c00
def v1171 : W := 0xfd4ff47603aa0ff8ffe6003000
def v1172 : W := 0xfd4ff47f03fa0f80fe07f03f00
def v1173 : W := 0xfd4ff47f03fa0f98fe67f03f00
def v1174 : W := 0xfd4ff47f03fa0fe0ff87f03f00
def v1175 : W := 0xfd4ff47f03fa0ff8ffe7f03f00
def v1176 : W := 0xfd4ff47f5ffbfff8ffe7f0ff03
def v1177 : W := 0xfd4ff47fa3fe0f98fe67f33ff4
def v1178 : W := 0xfd4ff47fa3fe0fe0ff87fc3ff8
def v1179 : W := 0xfd4ff47fa3fe0ff8ffe7ff3f00
def v1180 : W := 0xfd4ff47fa3ff0f80fe07f03ff0
def v1181 : W := 0xfd4fff8400080ff8fff8000000
def v1182 : W := 0xfd4fffff03fa0ff8fffff03f00
def v1183 : W := 0xfdd0805db4040f980001830000
def v1184 : W := 0xfdd0807fb40403180001f30000
def v1185 : W := 0xfdd0807fb4040f980007f30000
def v1186 : W := 0xfdd0807fb4040f9f0007f3c000
def v1187 : W := 0xfdd0807fb4040ff80007ff0000
def v1188 : W := 0xfdd0807fb4040fff0007ffc000
def v1189 : W := 0xfdd0807fb7f60f980007f33f00
def v1190 : W := 0xfdd0807ffc040f980007ffc000
def v1191 : W := 0xfdd096ffb40d5f980067f300f4
def v1192 : W := 0xfdda807fb6860f98f007f33c00
def v1193 : W := 0xfddba07fb6d60f983007f30c00
def v1194 : W := 0xfddbb68400080f983060000000
def v1195 : W := 0xfddbb6ffb6df5f983067f30cf4
def v1196 : W := 0xfddec07fb7a60f98c007f33000
def v1197 : W := 0xfddfe07f03f20f98fe07f03f00
def v1198 : W := 0xfddfe07fb7f60f98fe07f33f00
def v1199 : W := 0xfddfe07fb7f60ff8fe07ff3f00
def v1200 : W := 0xfddfe07ffff60f98fe07ffff00
def v1201 : W := 0xfddfe2ffb7f65f98fe67f33f04
def v1202 : W := 0xfddfe2ffb7f75f98fe07f33f00
def v1203 : W := 0xfddff684000803183e60000000
def v1204 : W := 0xfddff68400080f98fe60000000
def v1205 : W := 0xfddff68400080f9ffe78000000
def v1206 : W := 0xfddff68400080ff8ffe0000000
def v1207 : W := 0xfddff68400080ffffff8000000
def v1208 : W := 0xfddff68403fa0f98fe60003f00
def v1209 : W := 0xfddff684b40d5f98fe600300f4
def v1210 : W := 0xfddff6d4028a0f98fe67803c00
def v1211 : W := 0xfddff6dd02da0f98fe61800c00
def v1212 : W := 0xfddff6ddb6df5f98fe61830cf4
def v1213 : W := 0xfddff6f603aa0f98fe66003000
def v1214 : W := 0xfddff6ff03fa0f98fe67f03f00
def v1215 : W := 0xfddff6ff03fa0ff8ffe7f03f00
def v1216 : W := 0xfddff6ff17fa5f98fe67f33f04
def v1217 : W := 0xfddff6ff17fb5f98fe67f03f00
def v1218 : W := 0xfddff6ffb7fe0f98fe67f33f00
def v1219 : W := 0xfddff6ffb7ff53183e61f30ff4
def v1220 : W := 0xfddff6ffb7ff5f98fe67f33ff4
def v1221 : W := 0xfddfff8400080f98fff8000000
def v1222 : W := 0xfddfffff03fa0f98fffff03f00
def v1223 : W := 0xff608076e8040fe000060c0000
def v1224 : W := 0xff60807fe8040c6000067c0000
def v1225 : W := 0xff60807fe8040fe00007fc0000
def v1226 : W := 0xff60807fe8040fe70007fcc000
def v1227 : W := 0xff60807fe8040ff80007ff0000
def v1228 : W := 0xff60807fe8040fff0007ffc000
def v1229 : W := 0xff60807febf60fe00007fc3f00
def v1230 : W := 0xff60807ffc040fe00007ffc000
def v1231 : W := 0xff609d7fe80dafe00187fc00f8
def v1232 : W := 0xff6a807fea860fe0f007fc3c00
def v1233 : W := 0xff6ba07fead60fe03007fc0c00
def v1234 : W := 0xff6ec07feba60fe0c007fc3000
def v1235 : W := 0xff6edd0400080fe0c180000000
def v1236 : W := 0xff6edd7febafafe0c187fc30f8
def v1237 : W := 0xff6fe07f03f20fe0fe07f03f00
def v1238 : W := 0xff6fe07febf60fe0fe07fc3f00
def v1239 : W := 0xff6fe07febf60ff8fe07ff3f00
def v1240 : W := 0xff6fe07ffff60fe0fe07ffff00
def v1241 : W := 0xff6fe97febf6afe0ff87fc3f08
def v1242 : W := 0xff6fe97febf7afe0fe07fc3f00
def v1243 : W := 0xff6ffd0400080c60cf80000000
def v1244 : W := 0xff6ffd0400080fe0ff80000000
def v1245 : W := 0xff6ffd0400080fe7ff98000000
def v1246 : W := 0xff6ffd0400080ff8ffe0000000
def v1247 : W := 0xff6ffd0400080ffffff8000000
def v1248 : W := 0xff6ffd0403fa0fe0ff80003f00
def v1249 : W := 0xff6ffd04e80dafe0ff800c00f8
def v1250 : W := 0xff6ffd54028a0fe0ff87803c00
def v1251 : W := 0xff6ffd5d02da0fe0ff81800c00
def v1252 : W := 0xff6ffd7603aa0fe0ff86003000
def v1253 : W := 0xff6ffd76ebafafe0ff860c30f8
def v1254 : W := 0xff6ffd7f03fa0fe0ff87f03f00
def v1255 : W := 0xff6ffd7f03fa0ff8ffe7f03f00
def v1256 : W := 0xff6ffd7f4bfaafe0ff87fc3f08
def v1257 : W := 0xff6ffd7f4bfbafe0ff87f03f00
def v1258 : W := 0xff6ffd7febfe0fe0ff87fc3f00
def v1259 : W := 0xff6ffd7febffac60cf867c33f8
def v1260 : W := 0xff6ffd7febffafe0ff87fc3ff8
def v1261 : W := 0xff6fff8400080fe0fff8000000
def v1262 : W := 0xff6fffff03fa0fe0fffff03f00
def v1263 : W := 0xfff0800400000fff0000000000
def v1264 : W := 0xfff0800402d35fff0000000cf4
def v1265 : W := 0xfff0800403a3afff00000030f8
def v1266 : W := 0xfff08004a0040fff00000f0000
def v1267 : W := 0xfff08004b4040fff0000030000
def v1268 : W := 0xfff08004e8040fff00000c0000
def v1269 : W := 0xfff08004fc040fff00000fc000
def v1270 : W := 0xfff0800d14000fff0001f3c000
def v1271 : W := 0xfff0800dfc040fff0001ffc000
def v1272 : W := 0xfff0802648000fff00067cc000
def v1273 : W := 0xfff08026fc040fff00067fc000
def v1274 : W := 0xfff0802f5c000fff000070c000
def v1275 : W := 0xfff0802ffc040fff00007fc000
def v1276 : W := 0xfff08054a0040fff0000000000
def v1277 : W := 0xfff08054a0040fff0001830000
def v1278 : W := 0xfff08054a0040fff00060c0000
def v1279 : W := 0xfff08054a0040fff00078f0000
def v1280 : W := 0xfff08054fc040fff00078fc000
def v1281 : W := 0xfff0805db404031f0001830000
def v1282 : W := 0xfff0805db4040fff0001830000
def v1283 : W := 0xfff0805db4040fff0001f3c000
def v1284 : W := 0xfff0805db4040fff00078f0000
def v1285 : W := 0xfff0805db4040fff0007ffc000
def v1286 : W := 0xfff0805db6d75fff0001830cf4
def v1287 : W := 0xfff0805dfc040fff00018fc000
def v1288 : W := 0xfff08076e8040c6700060c0000
def v1289 : W := 0xfff08076e8040fff00060c0000
def v1290 : W := 0xfff08076e8040fff00067cc000
def v1291 : W := 0xfff08076e8040fff00078f0000
def v1292 : W := 0xfff08076e8040fff0007ffc000
def v1293 : W := 0xfff08076eba7afff00060c30f8
def v1294 : W := 0xfff08076fc040fff00060fc000
def v1295 : W := 0xfff0807f00000fff0007f00000
def v1296 : W := 0xfff0807fa0040fff0007ff0000
def v1297 : W := 0xfff0807fb4040fff0007f30000
def v1298 : W := 0xfff0807fe8040fff0007fc0000
def v1299 : W := 0xfff0807ffc040007000070c000
def v1300 : W := 0xfff0807ffc04031f0001f3c000
def v1301 : W := 0xfff0807ffc04031f0007ffc000
def v1302 : W := 0xfff0807ffc04037f0001ffc000
def v1303 : W := 0xfff0807ffc04039f0001f3c000
def v1304 : W := 0xfff0807ffc040c6700067cc000
def v1305 : W := 0xfff0807ffc040c670007ffc000
def v1306 : W := 0xfff0807ffc040c7f00067fc000
def v1307 : W := 0xfff0807ffc040ce700067cc000
def v1308 : W := 0xfff0807ffc040f7f0007ffc000
def v1309 : W := 0xfff0807ffc040f9f0007f3c000
def v1310 : W := 0xfff0807ffc040fe70007fcc000
def v1311 : W := 0xfff0807ffc040ff80007ff0000
def v1312 : W := 0xfff0807ffc040fff0001f3c000
def v1313 : W := 0xfff0807ffc040fff00067cc000
def v1314 : W := 0xfff0807ffc040fff00078f0000
def v1315 : W := 0xfff0807ffc040fff0007ffc000
def v1316 : W := 0xfff0807ffc040fff3007ffcc00
def v1317 : W := 0xfff0807ffc040fff3067ffc000
def v1318 : W := 0xfff0807ffc040fff3067ffcc04
def v1319 : W := 0xfff0807ffc040fffc007fff000
def v1320 : W := 0xfff0807ffc040fffc187ffc000
def v1321 : W := 0xfff0807ffc040fffc187fff008
def v1322 : W := 0xfff0807ffc050fff0007ffc000
def v1323 : W := 0xfff0807ffc05ffff0007ffc003
def v1324 : W := 0xfff0807ffc540fff0007ffcf00
def v1325 : W := 0xfff0807ffc545fff0007ffc303
def v1326 : W := 0xfff0807ffc545fff0007ffcc04
def v1327 : W := 0xfff0807ffc555fff0007ffc000
def v1328 : W := 0xfff0807ffd240fff0007fff300
def v1329 : W := 0xfff0807ffd24afff0007ffc303
def v1330 : W := 0xfff0807ffd24afff0007fff008
def v1331 : W := 0xfff0807ffd25afff0007ffc000
def v1332 : W := 0xfff0807ffd740fff0007ffc300
def v1333 : W := 0xfff0807ffd75ffff0007ffc303
def v1334 : W := 0xfff0807ffe860fff0007fffc00
def v1335 : W := 0xfff0807ffed60fff0007ffcc00
def v1336 : W := 0xfff0807ffed75fff0007ffccf4
def v1337 : W := 0xfff0807fffa60fff0007fff000
def v1338 : W := 0xfff0807fffa7afff0007fff0f8
def v1339 : W := 0xfff0807ffff60fff0007ffff00
def v1340 : W := 0xfff0807ffff7ffff0007ffff03
def v1341 : W := 0xfff082fffc040fff007fffc000
def v1342 : W := 0xfff082fffc045fff001fffc003
def v1343 : W := 0xfff082fffc045fff0067ffc004
def v1344 : W := 0xfff082fffc055fff0007ffc000
def v1345 : W := 0xfff0897ffc040fff019fffc000
def v1346 : W := 0xfff0897ffc04afff001fffc003
def v1347 : W := 0xfff0897ffc04afff0187ffc008
def v1348 : W := 0xfff0897ffc05afff0007ffc000
def v1349 : W := 0xfff08bfffc040fff001fffc000
def v1350 : W := 0xfff08bfffc05ffff001fffc003
def v1351 : W := 0xfff08bfffd75ffff001fffc303
def v1352 : W := 0xfff0940400080fff01e0000000
def v1353 : W := 0xfff0947ffc0c0fff01e7ffc000
def v1354 : W := 0xfff0968400080fff0060000000
def v1355 : W := 0xfff096fffc0c0fff0067ffc000
def v1356 : W := 0xfff096fffc0d5fff0067ffc0f4
def v1357 : W := 0xfff09d0400080fff0180000000
def v1358 : W := 0xfff09d7ffc0c0fff0187ffc000
def v1359 : W := 0xfff09d7ffc0dafff0187ffc0f8
def v1360 : W := 0xfff09f8400080fff01f8000000
def v1361 : W := 0xfff09f84fc0c0fff01f80fc000
def v1362 : W := 0xfff09fd4a00c0fff01ff8f0000
def v1363 : W := 0xfff09fddb40c0fff01f9830000
def v1364 : W := 0xfff09ff6e80c0fff01fe0c0000
def v1365 : W := 0xfff09ffffc0c0fff01ffffc000
def v1366 : W := 0xfff09ffffc0dffff01ffffc003
def v1367 : W := 0xfff09ffffffe0fff01ffffff00
def v1368 : W := 0xfff1a07ffc540fff0007ffc000
def v1369 : W := 0xfff1a07ffc540fff3007ffcc00
def v1370 : W := 0xfff1a07ffc540fff3e07ffcf00
def v1371 : W := 0xfff1a28400000fff3e78000000
def v1372 : W := 0xfff1a2fffc040fff0007ffc000
def v1373 : W := 0xfff1a2fffc040fff3067ffc000
def v1374 : W := 0xfff1a2fffc040fff3e7fffc000
def v1375 : W := 0xfff1a2fffc545fff0007ffc000
def v1376 : W := 0xfff1a2fffc545fff0e1fffc303
def v1377 : W := 0xfff1a2fffc545fff3067ffcc04
def v1378 : W := 0xfff1a2fffc555fff0007ffc000
def v1379 : W := 0xfff1a2fffc555fff3067ffcc04
def v1380 : W := 0xfff1a2fffd75ffff0007ffc303
def v1381 : W := 0xfff1abfffc55ffff001fffc003
def v1382 : W := 0xfff1bf8400080fff3ff8000000
def v1383 : W := 0xfff4c07ffd240fff0007ffc000
def v1384 : W := 0xfff4c07ffd240fffc007fff000
def v1385 : W := 0xfff4c07ffd240fffce07fff300
def v1386 : W := 0xfff4c90400000fffcf98000000
def v1387 : W := 0xfff4c97ffc040fff0007ffc000
def v1388 : W := 0xfff4c97ffc040fffc187ffc000
def v1389 : W := 0xfff4c97ffc040fffcf9fffc000
def v1390 : W := 0xfff4c97ffd24afff0007ffc000
def v1391 : W := 0xfff4c97ffd24afff0e1fffc303
def v1392 : W := 0xfff4c97ffd24afffc187fff008
def v1393 : W := 0xfff4c97ffd25afff0007ffc000
def v1394 : W := 0xfff4c97ffd25afffc187fff008
def v1395 : W := 0xfff4c97ffd75ffff0007ffc303
def v1396 : W := 0xfff4cbfffd25ffff001fffc003
def v1397 : W := 0xfff4df8400080fffcff8000000
def v1398 : W := 0xfff5e07ffd740fff0e07ffc300
def v1399 : W := 0xfff5eb8400000fff0e18000000
def v1400 : W := 0xfff5ebaf5d71ffff0e1870c303
def v1401 : W := 0xfff5ebfffc040fff0e1fffc000
def v1402 : W := 0xfff5ebfffd74fffff1e7fffc0c
def v1403 : W := 0xfff5ebfffd75f0070e1870c303
def v1404 : W := 0xfff5ebfffd75f31f0e19f3c303
def v1405 : W := 0xfff5ebfffd75fc670e1e7cc303
def v1406 : W := 0xfff5ebfffd75ffff0007ffc000
def v1407 : W := 0xfff5ebfffd75ffff0e1fffc303
def v1408 : W := 0xfff5ff8400080fff0ff8000000
def v1409 : W := 0xfffa807ffc040ffff007ffc000
def v1410 : W := 0xfffa807ffe860fff0007ffc000
def v1411 : W := 0xfffa807ffe860fff3007ffcc00
def v1412 : W := 0xfffa807ffe860fffc007fff000
def v1413 : W := 0xfffa807ffe860ffff007fffc00
def v1414 : W := 0xfffa807ffff60ffff007ffff00
def v1415 : W := 0xfffa8bfffe87fffff01ffffc03
def v1416 : W := 0xfffa940400080fff0000000000
def v1417 : W := 0xfffa940400080fff3060000000
def v1418 : W := 0xfffa940400080fffc180000000
def v1419 : W := 0xfffa940400080ffff1e0000000
def v1420 : W := 0xfffa9404fc0c0ffff1e00fc000
def v1421 : W := 0xfffa9454a00c0ffff1e78f0000
def v1422 : W := 0xfffa945db40c0ffff1e1830000
def v1423 : W := 0xfffa9476e80c0ffff1e60c0000
def v1424 : W := 0xfffa947ffc0c0fff0007ffc000
def v1425 : W := 0xfffa947ffc0c0fff3067ffc000
def v1426 : W := 0xfffa947ffc0c0fffc187ffc000
def v1427 : W := 0xfffa947ffc0c0ffff1e7ffc000
def v1428 : W := 0xfffa947ffd7dfffff1e7ffc303
def v1429 : W := 0xfffa947ffe8e0fff3067ffccf4
def v1430 : W := 0xfffa947ffe8e0fffc187fff0f8
def v1431 : W := 0xfffa947ffe8e0ffff1e7fffc00
def v1432 : W := 0xfffa947ffe8f0fff0007ffc0f0
def v1433 : W := 0xfffa9f8400080ffff1f8000000
def v1434 : W := 0xfffa9ffffc0c0ffff1ffffc000
def v1435 : W := 0xfffba07ffc040fff3007ffc000
def v1436 : W := 0xfffba07ffed60fff3007ffcc00
def v1437 : W := 0xfffba07ffed60ffff007fffc00
def v1438 : W := 0xfffba07ffff60fff3007ffff00
def v1439 : W := 0xfffba2fffed65fff3067ffcc04
def v1440 : W := 0xfffba2fffed75fff3007ffcc00
def v1441 : W := 0xfffbb6840008031f3060000000
def v1442 : W := 0xfffbb68400080fff3060000000
def v1443 : W := 0xfffbb68400080fff3e78000000
def v1444 : W := 0xfffbb68400080ffff1e0000000
def v1445 : W := 0xfffbb68400080ffffff8000000
def v1446 : W := 0xfffbb68402db5fff3060000cf4
def v1447 : W := 0xfffbb684fc0c0fff30600fc000
def v1448 : W := 0xfffbb6d4a00c0fff30678f0000
def v1449 : W := 0xfffbb6ddb40c0fff3061830000
def v1450 : W := 0xfffbb6ddb6df5fff3061830cf4
def v1451 : W := 0xfffbb6f6e80c0fff30660c0000
def v1452 : W := 0xfffbb6fffc0c0fff3067ffc000
def v1453 : W := 0xfffbb6fffc0c0ffff1e7ffc000
def v1454 : W := 0xfffbb6fffc5c5fff3067ffcc04
def v1455 : W := 0xfffbb6fffc5d5fff3067ffc000
def v1456 : W := 0xfffbb6fffede0fff3067ffcc00
def v1457 : W := 0xfffbb6fffedf531f3061f3ccf4
def v1458 : W := 0xfffbb6fffedf5fff3067ffccf4
def v1459 : W := 0xfffbbf8400080fff31f8000000
def v1460 : W := 0xfffbbffffc0c0fff31ffffc000
def v1461 : W := 0xfffec07ffc040fffc007ffc000
def v1462 : W := 0xfffec07fffa60fffc007fff000
def v1463 : W := 0xfffec07fffa60ffff007fffc00
def v1464 : W := 0xfffec07ffff60fffc007ffff00
def v1465 : W := 0xfffec97fffa6afffc187fff008
def v1466 : W := 0xfffec97fffa7afffc007fff000
def v1467 : W := 0xfffedd0400080c67c180000000
def v1468 : W := 0xfffedd0400080fffc180000000
def v1469 : W := 0xfffedd0400080fffcf98000000
def v1470 : W := 0xfffedd0400080ffff1e0000000
def v1471 : W := 0xfffedd0400080ffffff8000000
def v1472 : W := 0xfffedd0403abafffc1800030f8
def v1473 : W := 0xfffedd04fc0c0fffc1800fc000
def v1474 : W := 0xfffedd54a00c0fffc1878f0000
def v1475 : W := 0xfffedd5db40c0fffc181830000
def v1476 : W := 0xfffedd76e80c0fffc1860c0000
def v1477 : W := 0xfffedd76ebafafffc1860c30f8
def v1478 : W := 0xfffedd7ffc0c0fffc187ffc000
def v1479 : W := 0xfffedd7ffc0c0ffff1e7ffc000
def v1480 : W := 0xfffedd7ffd2cafffc187fff008
def v1481 : W := 0xfffedd7ffd2dafffc187ffc000
def v1482 : W := 0xfffedd7fffae0fffc187fff000
def v1483 : W := 0xfffedd7fffafac67c1867cf0f8
def v1484 : W := 0xfffedd7fffafafffc187fff0f8
def v1485 : W := 0xfffedf8400080fffc1f8000000
def v1486 : W := 0xfffedffffc0c0fffc1ffffc000
def v1487 : W := 0xffffe00400000ffffe00000000
def v1488 : W := 0xffffe07f03f20ffffe07f03f00
def v1489 : W := 0xffffe07ffc040ffffe07ffc000
def v1490 : W := 0xffffe07ffff60ff8fe07ff3f00
def v1491 : W := 0xffffe07ffff60ffff007fffc00
def v1492 : W := 0xffffe07ffff60ffffe07ffff00
def v1493 : W := 0xffffebfffff7fffffe1fffff03
def v1494 : W := 0xfffff40400080fffffe0000000
def v1495 : W := 0xfffff68400080ffffe60000000
def v1496 : W := 0xfffff6ffffff5ffffe67fffff4
def v1497 : W := 0xfffffd0400080fffff80000000
def v1498 : W := 0xfffffd7fffffafffff87fffff8
def v1499 : W := 0xffffff84000800070e18000000
def v1500 : W := 0xffffff840008031f3e78000000
def v1501 : W := 0xffffff840008031ffff8000000
def v1502 : W := 0xffffff840008037f3ff8000000
def v1503 : W := 0xffffff840008039f3e78000000
def v1504 : W := 0xffffff8400080c67cf98000000
def v1505 : W := 0xffffff8400080c67fff8000000
def v1506 : W := 0xffffff8400080c7fcff8000000
def v1507 : W := 0xffffff8400080ce7cf98000000
def v1508 : W := 0xffffff8400080f7ffff8000000
def v1509 : W := 0xffffff8400080f9ffe78000000
def v1510 : W := 0xffffff8400080fe7ff98000000
def v1511 : W := 0xffffff8400080ff8ffe0000000
def v1512 : W := 0xffffff8400080fff3e78000000
def v1513 : W := 0xffffff8400080fffcf98000000
def v1514 : W := 0xffffff8400080ffff1e0000000
def v1515 : W := 0xffffff8400080ffffff8000000
def v1516 : W := 0xffffff8400080ffffff9800c00
def v1517 : W := 0xffffff8400080ffffff9830000
def v1518 : W := 0xffffff8400080ffffff9830c04
def v1519 : W := 0xffffff8400080ffffffe003000
def v1520 : W := 0xffffff8400080ffffffe0c0000
def v1521 : W := 0xffffff8400080ffffffe0c3008
def v1522 : W := 0xffffff8400090ffffff8000000
def v1523 : W := 0xffffff840009fffffff8000003
def v1524 : W := 0xffffff8400580ffffff8000f00
def v1525 : W := 0xffffff8400585ffffff8000303
def v1526 : W := 0xffffff8400585ffffff8000c04
def v1527 : W := 0xffffff8400595ffffff8000000
def v1528 : W := 0xffffff8401280ffffff8003300
def v1529 : W := 0xffffff840128affffff8000303
def v1530 : W := 0xffffff840128affffff8003008
def v1531 : W := 0xffffff840129affffff8000000
def v1532 : W := 0xffffff8401780ffffff8000300
def v1533 : W := 0xffffff840179fffffff8000303
def v1534 : W := 0xffffff84028a0ffffff8003c00
def v1535 : W := 0xffffff8402da0ffffff8000c00
def v1536 : W := 0xffffff8402db5ffffff8000cf4
def v1537 : W := 0xffffff8403aa0ffffff8003000
def v1538 : W := 0xffffff8403abaffffff80030f8
def v1539 : W := 0xffffff8403fa0ffffff8003f00
def v1540 : W := 0xffffff8403fbfffffff8003f03
def v1541 : W := 0xffffff8414080ffffff803c000
def v1542 : W := 0xffffff8414085ffffff800c003
def v1543 : W := 0xffffff8414085ffffff8030004
def v1544 : W := 0xffffff8414095ffffff8000000
def v1545 : W := 0xffffff8448080ffffff80cc000
def v1546 : W := 0xffffff844808affffff800c003
def v1547 : W := 0xffffff844808affffff80c0008
def v1548 : W := 0xffffff844809affffff8000000
def v1549 : W := 0xffffff845c080ffffff800c000
def v1550 : W := 0xffffff845c09fffffff800c003
def v1551 : W := 0xffffff845d79fffffff800c303
def v1552 : W := 0xffffff84a00c0ffffff80f0000
def v1553 : W := 0xffffff84b40c0ffffff8030000
def v1554 : W := 0xffffff84b40d5ffffff80300f4
def v1555 : W := 0xffffff84e80c0ffffff80c0000
def v1556 : W := 0xffffff84e80daffffff80c00f8
def v1557 : W := 0xffffff84fc0c0ffffff80fc000
def v1558 : W := 0xffffff84fc0dfffffff80fc003
def v1559 : W := 0xffffff84fffe0ffffff80fff00
def v1560 : W := 0xffffff8d00580ffffff8000000
def v1561 : W := 0xffffff8d00580ffffff9800c00
def v1562 : W := 0xffffff8d00580ffffff9f00f00
def v1563 : W := 0xffffff8d14080ffffff8000000
def v1564 : W := 0xffffff8d14080ffffff9830000
def v1565 : W := 0xffffff8d14080ffffff9f3c000
def v1566 : W := 0xffffff8d14585ffffff8000000
def v1567 : W := 0xffffff8d14585ffffff870c303
def v1568 : W := 0xffffff8d14585ffffff9830c04
def v1569 : W := 0xffffff8d14595ffffff8000000
def v1570 : W := 0xffffff8d14595ffffff9830c04
def v1571 : W := 0xffffff8d1579fffffff8000303
def v1572 : W := 0xffffff8d5c59fffffff800c003
def v1573 : W := 0xffffffa601280ffffff8000000
def v1574 : W := 0xffffffa601280ffffffe003000
def v1575 : W := 0xffffffa601280ffffffe703300
def v1576 : W := 0xffffffa648080ffffff8000000
def v1577 : W := 0xffffffa648080ffffffe0c0000
def v1578 : W := 0xffffffa648080ffffffe7cc000
def v1579 : W := 0xffffffa64928affffff8000000
def v1580 : W := 0xffffffa64928affffff870c303
def v1581 : W := 0xffffffa64928affffffe0c3008
def v1582 : W := 0xffffffa64929affffff8000000
def v1583 : W := 0xffffffa64929affffffe0c3008
def v1584 : W := 0xffffffa64979fffffff8000303
def v1585 : W := 0xffffffa65d29fffffff800c003
def v1586 : W := 0xffffffaf01780ffffff8700300
def v1587 : W := 0xffffffaf5c080ffffff870c000
def v1588 : W := 0xffffffaf5d78ffffffff8f3c0c
def v1589 : W := 0xffffffaf5d79f0070e1870c303
def v1590 : W := 0xffffffaf5d79f31f3e7870c303
def v1591 : W := 0xffffffaf5d79fc67cf9870c303
def v1592 : W := 0xffffffaf5d79fffffff8000000
def v1593 : W := 0xffffffaf5d79fffffff870c303
def v1594 : W := 0xffffffd400080fffffff800000
def v1595 : W := 0xffffffd4028a0ffffff8000000
def v1596 : W := 0xffffffd4028a0ffffff9800c00
def v1597 : W := 0xffffffd4028a0ffffffe003000
def v1598 : W := 0xffffffd4028a0fffffff803c00
def v1599 : W := 0xffffffd403fa0fffffff803f00
def v1600 : W := 0xffffffd45e8bffffffff80fc03
def v1601 : W := 0xffffffd4a00c0ffffff8000000
def v1602 : W := 0xffffffd4a00c0ffffff9830000
def v1603 : W := 0xffffffd4a00c0ffffffe0c0000
def v1604 : W := 0xffffffd4a00c0fffffff8f0000
def v1605 : W := 0xffffffd4a17dffffffff8f0303
def v1606 : W := 0xffffffd4a28e0ffffff9830cf4
def v1607 : W := 0xffffffd4a28e0ffffffe0c30f8
def v1608 : W := 0xffffffd4a28e0fffffff8f3c00
def v1609 : W := 0xffffffd4a28f0ffffff80000f0
def v1610 : W := 0xffffffd4fc0c0fffffff8fc000
def v1611 : W := 0xffffffdd00080ffffff9800000
def v1612 : W := 0xffffffdd02da0ffffff9800c00
def v1613 : W := 0xffffffdd02da0fffffff803c00
def v1614 : W := 0xffffffdd03fa0ffffff9803f00
def v1615 : W := 0xffffffdd16da5ffffff9830c04
def v1616 : W := 0xffffffdd16db5ffffff9800c00
def v1617 : W := 0xffffffddb40c0ffffff9830000
def v1618 : W := 0xffffffddb40c0fffffff8f0000
def v1619 : W := 0xffffffddb45c5ffffff9830c04
def v1620 : W := 0xffffffddb45d5ffffff9830000
def v1621 : W := 0xffffffddb6de0ffffff9830c00
def v1622 : W := 0xffffffddb6df531f3e79830cf4
def v1623 : W := 0xffffffddb6df5ffffff9830cf4
def v1624 : W := 0xffffffddfc0c0ffffff98fc000
def v1625 : W := 0xfffffff600080ffffffe000000
def v1626 : W := 0xfffffff603aa0ffffffe003000
def v1627 : W := 0xfffffff603aa0fffffff803c00
def v1628 : W := 0xfffffff603fa0ffffffe003f00
def v1629 : W := 0xfffffff64baaaffffffe0c3008
def v1630 : W := 0xfffffff64babaffffffe003000
def v1631 : W := 0xfffffff6e80c0ffffffe0c0000
def v1632 : W := 0xfffffff6e80c0fffffff8f0000
def v1633 : W := 0xfffffff6e92caffffffe0c3008
def v1634 : W := 0xfffffff6e92daffffffe0c0000
def v1635 : W := 0xfffffff6ebae0ffffffe0c3000
def v1636 : W := 0xfffffff6ebafac67cf9e0c30f8
def v1637 : W := 0xfffffff6ebafaffffffe0c30f8
def v1638 : W := 0xfffffff6fc0c0ffffffe0fc000
def v1639 : W := 0xffffffff00080ffffffff00000
def v1640 : W := 0xffffffff03fa0ff8ffe7f03f00
def v1641 : W := 0xffffffff03fa0fffffff803c00
def v1642 : W := 0xffffffff03fa0ffffffff03f00
def v1643 : W := 0xffffffff5ffbfffffffff0ff03
def v1644 : W := 0xffffffffb7ff5ffffffff33ff4
def v1645 : W := 0xffffffffebffaffffffffc3ff8
def v1646 : W := 0xfffffffffc0c0ffff1e7ffc000
def v1647 : W := 0xfffffffffc0c0fffffff8f0000
def v1648 : W := 0xfffffffffc0c0fffffffffc000
def v1649 : W := 0xfffffffffd7dffffffffffc303
def v1650 : W := 0xfffffffffedf5fffffffffccf4
def v1651 : W := 0xffffffffffafaffffffffff0f8
def v1652 : W := 0xfffffffffffe0fffffffffff00
def v1653 : W := 0xfffffffffffff0070e1870c3f3
def v1654 : W := 0xfffffffffffff31f3e79f3cff7
def v1655 : W := 0xfffffffffffffc67cf9e7cf3fb
def v1656 : W := 0xffffffffffffff7fffffffffff
def v1657 : W := 0xffffffffffffff9ffe7ff3fff7
def v1658 : W := 0xffffffffffffffe7ff9ffcfffb
def v1659 : W := 0xfffffffffffffff8ffe7ff3ffc
def v1660 : W := 0xffffffffffffffff3e7fffcff7
def v1661 : W := 0xffffffffffffffffcf9ffff3fb
def v1662 : W := 0xfffffffffffffffff1e7fffcfc
def v1663 : W := 0xfffffffffffffffffff9f3cff7
def v1664 : W := 0xfffffffffffffffffffe7cf3fb
def v1665 : W := 0xffffffffffffffffffff8f3cfc

def ins : List W := [v565, v732, v852, v1045, v1315, v1515]
theorem sampled : ∀ j : Fin 104, Nat.testBit 0xeae8e8e8e8e8e8a8 (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
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
def level3 : BinaryTree (List W) := (.node [v295, v565, v732, v852] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level3_ok : everyKey (rowOK 2 level2) level3 = true := by decide +kernel
theorem closed3 : Closed 3 level3 := closed_next 2 (by decide) level3 level2 closed2 level3_ok
def level4llll : BinaryTree (List W) := (.node [v87, v852, v915, v1045, v1315] (.node [v59, v291, v565, v732, v852] (.node [v31, v478, v565, v852, v1315] (.node [v24, v391, v565, v732, v1315] (.node [v23, v380, v565, v732, v1045] .nil .nil) (.node [v30, v469, v565, v852, v1045] .nil .nil)) (.node [v53, v852, v915, v1045, v1315] (.node [v46, v732, v795, v1045, v1315] .nil .nil) .nil)) (.node [v80, v469, v565, v852, v1045] (.node [v71, v391, v565, v732, v1315] (.node [v68, v478, v565, v852, v1315] .nil .nil) (.node [v72, v290, v565, v732, v852] .nil .nil)) (.node [v83, v289, v565, v732, v852] (.node [v82, v380, v565, v732, v1045] .nil .nil) .nil))) (.node [v131, v732, v795, v1045, v1515] (.node [v113, v464, v565, v852, v1045] (.node [v106, v373, v565, v732, v1045] (.node [v88, v732, v795, v1045, v1315] .nil .nil) (.node [v107, v391, v565, v732, v1515] .nil .nil)) (.node [v120, v641, v732, v852, v1045] (.node [v114, v478, v565, v852, v1515] .nil .nil) .nil)) (.node [v150, v255, v565, v732, v852] (.node [v146, v283, v565, v732, v852] (.node [v139, v852, v915, v1045, v1515] .nil .nil) (.node [v149, v266, v565, v732, v852] .nil .nil)) (.node [v160, v391, v565, v732, v1515] (.node [v157, v478, v565, v852, v1515] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llll_ok : everyKey (rowOK 3 level3) level4llll = true := by decide +kernel
def level4lllr : BinaryTree (List W) := (.node [v189, v565, v732, v852, v1045] (.node [v188, v565, v732, v852, v947] (.node [v176, v852, v915, v1045, v1515] (.node [v171, v373, v565, v732, v1045] (.node [v169, v464, v565, v852, v1045] .nil .nil) (.node [v172, v243, v565, v732, v852] .nil .nil)) (.node [v187, v240, v565, v732, v852] (.node [v177, v732, v795, v1045, v1515] .nil .nil) .nil)) (.node [v188, v565, v732, v852, v1069] (.node [v188, v565, v732, v852, v997] (.node [v188, v565, v732, v852, v953] .nil .nil) (.node [v188, v565, v732, v852, v1045] .nil .nil)) (.node [v188, v565, v732, v852, v1097] (.node [v188, v565, v732, v852, v1095] .nil .nil) .nil))) (.node [v214, v634, v732, v852, v1515] (.node [v203, v464, v565, v852, v1315] (.node [v196, v373, v565, v732, v1315] (.node [v190, v565, v732, v852, v1045] .nil .nil) (.node [v197, v380, v565, v732, v1515] .nil .nil)) (.node [v210, v640, v732, v852, v1315] (.node [v204, v469, v565, v852, v1515] .nil .nil) .nil)) (.node [v251, v469, v565, v852, v1515] (.node [v232, v852, v915, v1315, v1515] (.node [v223, v732, v795, v1315, v1515] .nil .nil) .nil) (.node [v263, v464, v565, v852, v1315] (.node [v254, v380, v565, v732, v1515] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lllr_ok : everyKey (rowOK 3 level3) level4lllr = true := by decide +kernel
def level4lll : BinaryTree (List W) := .node [v161, v244, v565, v732, v852] level4llll level4lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lll_ok : everyKey (rowOK 3 level3) level4lll = true := by
  change (_ && everyKey (rowOK 3 level3) level4llll && everyKey (rowOK 3 level3) level4lllr) = true
  rw [level4llll_ok, level4lllr_ok]
  decide +kernel
def level4llrl : BinaryTree (List W) := (.node [v286, v565, v732, v852, v1360] (.node [v281, v565, v732, v852, v1339] (.node [v281, v565, v732, v852, v957] (.node [v271, v732, v795, v1315, v1515] (.node [v270, v852, v915, v1315, v1515] .nil .nil) (.node [v281, v565, v732, v852, v948] .nil .nil)) (.node [v281, v565, v732, v852, v1315] (.node [v281, v565, v732, v852, v1269] .nil .nil) .nil)) (.node [v284, v565, v732, v852, v1315] (.node [v281, v565, v732, v852, v1367] (.node [v281, v565, v732, v852, v1365] .nil .nil) (.node [v282, v565, v732, v852, v1315] .nil .nil)) (.node [v286, v565, v732, v852, v1090] (.node [v286, v565, v732, v852, v961] .nil .nil) .nil))) (.node [v292, v565, v732, v852, v1515] (.node [v286, v565, v732, v852, v1559] (.node [v286, v565, v732, v852, v1539] (.node [v286, v565, v732, v852, v1515] .nil .nil) (.node [v286, v565, v732, v852, v1557] .nil .nil)) (.node [v288, v565, v732, v852, v1515] (.node [v287, v565, v732, v852, v1515] .nil .nil) .nil)) (.node [v300, v915, v1045, v1315, v1515] (.node [v294, v565, v732, v852, v1045] (.node [v293, v565, v732, v852, v1315] .nil .nil) .nil) (.node [v316, v845, v1030, v1315, v1515] (.node [v301, v795, v1045, v1315, v1515] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llrl_ok : everyKey (rowOK 3 level3) level4llrl = true := by decide +kernel
def level4llrr : BinaryTree (List W) := (.node [v379, v380, v565, v732, v1045] (.node [v355, v373, v565, v732, v1045] (.node [v341, v380, v565, v732, v1515] (.node [v336, v373, v565, v732, v1315] (.node [v316, v845, v1045, v1315, v1500] .nil .nil) (.node [v338, v373, v565, v732, v1315] .nil .nil)) (.node [v353, v373, v565, v732, v1045] (.node [v344, v380, v565, v732, v1515] .nil .nil) .nil)) (.node [v373, v565, v732, v1045, v1315] (.node [v373, v565, v732, v1019, v1315] (.node [v362, v915, v1045, v1315, v1515] .nil .nil) (.node [v373, v565, v732, v1045, v1289] .nil .nil)) (.node [v373, v565, v732, v1254, v1315] (.node [v373, v565, v732, v1045, v1478] .nil .nil) .nil))) (.node [v389, v391, v565, v732, v1515] (.node [v380, v565, v732, v1045, v1515] (.node [v380, v565, v732, v986, v1515] (.node [v380, v382, v565, v732, v1045] .nil .nil) (.node [v380, v565, v732, v1045, v1468] .nil .nil)) (.node [v380, v565, v732, v1238, v1515] (.node [v380, v565, v732, v1045, v1631] .nil .nil) .nil)) (.node [v391, v398, v565, v732, v1315] (.node [v391, v394, v565, v732, v1515] (.node [v390, v391, v565, v732, v1315] .nil .nil) .nil) (.node [v391, v565, v732, v1244, v1315] (.node [v391, v565, v732, v1225, v1515] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llrr_ok : everyKey (rowOK 3 level3) level4llrr = true := by decide +kernel
def level4llr : BinaryTree (List W) := .node [v316, v845, v1045, v1300, v1515] level4llrl level4llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llr_ok : everyKey (rowOK 3 level3) level4llr = true := by
  change (_ && everyKey (rowOK 3 level3) level4llrl && everyKey (rowOK 3 level3) level4llrr) = true
  rw [level4llrl_ok, level4llrr_ok]
  decide +kernel
def level4ll : BinaryTree (List W) := .node [v265, v373, v565, v732, v1315] level4lll level4llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4ll_ok : everyKey (rowOK 3 level3) level4ll = true := by
  change (_ && everyKey (rowOK 3 level3) level4lll && everyKey (rowOK 3 level3) level4llr) = true
  rw [level4lll_ok, level4llr_ok]
  decide +kernel
def level4lrll : BinaryTree (List W) := (.node [v464, v565, v852, v1045, v1282] (.node [v430, v464, v565, v852, v1315] (.node [v408, v725, v1045, v1304, v1515] (.node [v391, v565, v732, v1462, v1515] (.node [v391, v565, v732, v1315, v1626] .nil .nil) (.node [v408, v725, v1034, v1315, v1515] .nil .nil)) (.node [v426, v464, v565, v852, v1315] (.node [v408, v725, v1045, v1315, v1504] .nil .nil) .nil)) (.node [v447, v464, v565, v852, v1045] (.node [v436, v469, v565, v852, v1515] (.node [v431, v469, v565, v852, v1515] .nil .nil) (.node [v443, v464, v565, v852, v1045] .nil .nil)) (.node [v464, v565, v852, v1012, v1315] (.node [v454, v795, v1045, v1315, v1515] .nil .nil) .nil))) (.node [v469, v565, v852, v1045, v1442] (.node [v468, v469, v565, v852, v1045] (.node [v464, v565, v852, v1045, v1452] (.node [v464, v565, v852, v1045, v1315] .nil .nil) (.node [v464, v565, v852, v1214, v1315] .nil .nil)) (.node [v469, v565, v852, v977, v1515] (.node [v469, v474, v565, v852, v1045] .nil .nil) .nil)) (.node [v476, v478, v565, v852, v1515] (.node [v469, v565, v852, v1045, v1617] (.node [v469, v565, v852, v1045, v1515] .nil .nil) (.node [v469, v565, v852, v1198, v1515] .nil .nil)) (.node [v478, v486, v565, v852, v1515] (.node [v477, v478, v565, v852, v1315] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrll_ok : everyKey (rowOK 3 level3) level4lrll = true := by decide +kernel
def level4lrlr : BinaryTree (List W) := (.node [v492, v565, v913, v1045, v1315] (.node [v492, v565, v682, v1045, v1515] (.node [v478, v565, v852, v1315, v1612] (.node [v478, v565, v852, v1204, v1315] (.node [v478, v565, v852, v1185, v1515] .nil .nil) (.node [v478, v565, v852, v1315, v1515] .nil .nil)) (.node [v492, v565, v680, v1315, v1515] (.node [v478, v565, v852, v1436, v1515] .nil .nil) .nil)) (.node [v492, v565, v792, v1045, v1315] (.node [v492, v565, v770, v1315, v1515] (.node [v492, v565, v684, v1045, v1315] .nil .nil) (.node [v492, v565, v783, v1045, v1515] .nil .nil)) (.node [v492, v565, v904, v1045, v1515] (.node [v492, v565, v891, v1315, v1515] .nil .nil) .nil))) (.node [v492, v565, v1045, v1402, v1515] (.node [v492, v565, v1045, v1315, v1588] (.node [v492, v565, v1045, v1315, v1568] (.node [v492, v565, v1045, v1315, v1515] .nil .nil) (.node [v492, v565, v1045, v1315, v1581] .nil .nil)) (.node [v492, v565, v1045, v1392, v1515] (.node [v492, v565, v1045, v1377, v1515] .nil .nil) .nil)) (.node [v492, v565, v1139, v1315, v1515] (.node [v492, v565, v1126, v1315, v1515] (.node [v492, v565, v1109, v1315, v1515] .nil .nil) .nil) (.node [v496, v565, v1045, v1315, v1515] (.node [v493, v1045, v1315, v1515, v1653] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrlr_ok : everyKey (rowOK 3 level3) level4lrlr = true := by decide +kernel
def level4lrl : BinaryTree (List W) := .node [v478, v490, v565, v852, v1315] level4lrll level4lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrl_ok : everyKey (rowOK 3 level3) level4lrl = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrll && everyKey (rowOK 3 level3) level4lrlr) = true
  rw [level4lrll_ok, level4lrlr_ok]
  decide +kernel
def level4lrrl : BinaryTree (List W) := (.node [v565, v732, v763, v852, v1315] (.node [v565, v678, v732, v852, v1315] (.node [v536, v639, v732, v852, v1045] (.node [v515, v633, v732, v852, v1515] (.node [v510, v639, v732, v852, v1315] .nil .nil) (.node [v519, v633, v732, v852, v1515] .nil .nil)) (.node [v565, v669, v732, v852, v1045] (.node [v539, v639, v732, v852, v1045] .nil .nil) .nil)) (.node [v565, v721, v852, v1212, v1315] (.node [v565, v686, v1045, v1315, v1515] (.node [v565, v679, v732, v852, v1515] .nil .nil) (.node [v565, v711, v852, v1195, v1515] .nil .nil)) (.node [v565, v732, v753, v852, v1045] (.node [v565, v722, v852, v1045, v1450] .nil .nil) .nil))) (.node [v565, v732, v852, v884, v1515] (.node [v565, v732, v842, v1045, v1477] (.node [v565, v732, v831, v1236, v1515] (.node [v565, v732, v764, v852, v1515] .nil .nil) (.node [v565, v732, v841, v1253, v1315] .nil .nil)) (.node [v565, v732, v852, v883, v1315] (.node [v565, v732, v852, v873, v1045] .nil .nil) .nil)) (.node [v565, v732, v852, v948, v1642] (.node [v565, v732, v852, v947, v1648] (.node [v565, v732, v852, v946, v1652] .nil .nil) .nil) (.node [v565, v732, v852, v949, v1608] (.node [v565, v732, v852, v949, v1559] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrrl_ok : everyKey (rowOK 3 level3) level4lrrl = true := by decide +kernel
def level4lrrr : BinaryTree (List W) := (.node [v565, v732, v852, v968, v1648] (.node [v565, v732, v852, v957, v1598] (.node [v565, v732, v852, v953, v1617] (.node [v565, v732, v852, v953, v1557] (.node [v565, v732, v852, v949, v1635] .nil .nil) (.node [v565, v732, v852, v953, v1604] .nil .nil)) (.node [v565, v732, v852, v957, v1539] (.node [v565, v732, v852, v953, v1631] .nil .nil) .nil)) (.node [v565, v732, v852, v959, v1515] (.node [v565, v732, v852, v957, v1626] (.node [v565, v732, v852, v957, v1612] .nil .nil) (.node [v565, v732, v852, v958, v1515] .nil .nil)) (.node [v565, v732, v852, v961, v1492] (.node [v565, v732, v852, v960, v1515] .nil .nil) .nil))) (.node [v565, v732, v852, v977, v1557] (.node [v565, v732, v852, v972, v1631] (.node [v565, v732, v852, v972, v1604] (.node [v565, v732, v852, v972, v1557] .nil .nil) (.node [v565, v732, v852, v972, v1617] .nil .nil)) (.node [v565, v732, v852, v975, v1648] (.node [v565, v732, v852, v974, v1515] .nil .nil) .nil)) (.node [v565, v732, v852, v977, v1631] (.node [v565, v732, v852, v977, v1617] (.node [v565, v732, v852, v977, v1604] .nil .nil) .nil) (.node [v565, v732, v852, v984, v1648] (.node [v565, v732, v852, v982, v1515] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrrr_ok : everyKey (rowOK 3 level3) level4lrrr = true := by decide +kernel
def level4lrr : BinaryTree (List W) := .node [v565, v732, v852, v949, v1621] level4lrrl level4lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrr_ok : everyKey (rowOK 3 level3) level4lrr = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrrl && everyKey (rowOK 3 level3) level4lrrr) = true
  rw [level4lrrl_ok, level4lrrr_ok]
  decide +kernel
def level4lr : BinaryTree (List W) := .node [v507, v639, v732, v852, v1315] level4lrl level4lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lr_ok : everyKey (rowOK 3 level3) level4lr = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrl && everyKey (rowOK 3 level3) level4lrr) = true
  rw [level4lrl_ok, level4lrr_ok]
  decide +kernel
def level4l : BinaryTree (List W) := .node [v391, v565, v732, v1315, v1515] level4ll level4lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4l_ok : everyKey (rowOK 3 level3) level4l = true := by
  change (_ && everyKey (rowOK 3 level3) level4ll && everyKey (rowOK 3 level3) level4lr) = true
  rw [level4ll_ok, level4lr_ok]
  decide +kernel
def level4rlll : BinaryTree (List W) := (.node [v565, v732, v852, v999, v1315] (.node [v565, v732, v852, v993, v1456] (.node [v565, v732, v852, v991, v1515] (.node [v565, v732, v852, v986, v1617] (.node [v565, v732, v852, v986, v1604] .nil .nil) (.node [v565, v732, v852, v986, v1631] .nil .nil)) (.node [v565, v732, v852, v993, v1431] (.node [v565, v732, v852, v993, v1367] .nil .nil) .nil)) (.node [v565, v732, v852, v997, v1452] (.node [v565, v732, v852, v997, v1365] (.node [v565, v732, v852, v993, v1482] .nil .nil) (.node [v565, v732, v852, v997, v1427] .nil .nil)) (.node [v565, v732, v852, v998, v1315] (.node [v565, v732, v852, v997, v1478] .nil .nil) .nil))) (.node [v565, v732, v852, v1012, v1452] (.node [v565, v732, v852, v1009, v1478] (.node [v565, v732, v852, v1009, v1427] (.node [v565, v732, v852, v1009, v1365] .nil .nil) (.node [v565, v732, v852, v1009, v1452] .nil .nil)) (.node [v565, v732, v852, v1012, v1427] (.node [v565, v732, v852, v1012, v1365] .nil .nil) .nil)) (.node [v565, v732, v852, v1019, v1452] (.node [v565, v732, v852, v1019, v1365] (.node [v565, v732, v852, v1012, v1478] .nil .nil) (.node [v565, v732, v852, v1019, v1427] .nil .nil)) (.node [v565, v732, v852, v1045, v1264] (.node [v565, v732, v852, v1019, v1478] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlll_ok : everyKey (rowOK 3 level3) level4rlll = true := by decide +kernel
def level4rllr : BinaryTree (List W) := (.node [v565, v732, v852, v1045, v1474] (.node [v565, v732, v852, v1045, v1422] (.node [v565, v732, v852, v1045, v1364] (.node [v565, v732, v852, v1045, v1362] (.node [v565, v732, v852, v1045, v1361] .nil .nil) (.node [v565, v732, v852, v1045, v1363] .nil .nil)) (.node [v565, v732, v852, v1045, v1421] (.node [v565, v732, v852, v1045, v1420] .nil .nil) .nil)) (.node [v565, v732, v852, v1045, v1449] (.node [v565, v732, v852, v1045, v1447] (.node [v565, v732, v852, v1045, v1423] .nil .nil) (.node [v565, v732, v852, v1045, v1448] .nil .nil)) (.node [v565, v732, v852, v1045, v1473] (.node [v565, v732, v852, v1045, v1451] .nil .nil) .nil))) (.node [v565, v732, v852, v1090, v1339] (.node [v565, v732, v852, v1069, v1419] (.node [v565, v732, v852, v1045, v1476] (.node [v565, v732, v852, v1045, v1475] .nil .nil) (.node [v565, v732, v852, v1069, v1360] .nil .nil)) (.node [v565, v732, v852, v1069, v1468] (.node [v565, v732, v852, v1069, v1442] .nil .nil) .nil)) (.node [v565, v732, v852, v1090, v1462] (.node [v565, v732, v852, v1090, v1436] (.node [v565, v732, v852, v1090, v1413] .nil .nil) .nil) (.node [v565, v732, v852, v1092, v1315] (.node [v565, v732, v852, v1091, v1315] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rllr_ok : everyKey (rowOK 3 level3) level4rllr = true := by decide +kernel
def level4rll : BinaryTree (List W) := .node [v565, v732, v852, v1045, v1265] level4rlll level4rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rll_ok : everyKey (rowOK 3 level3) level4rll = true := by
  change (_ && everyKey (rowOK 3 level3) level4rlll && everyKey (rowOK 3 level3) level4rllr) = true
  rw [level4rlll_ok, level4rllr_ok]
  decide +kernel
def level4rlrl : BinaryTree (List W) := (.node [v565, v732, v852, v1154, v1492] (.node [v565, v732, v852, v1146, v1642] (.node [v565, v732, v852, v1095, v1282] (.node [v565, v732, v852, v1095, v1269] (.node [v565, v732, v852, v1094, v1315] .nil .nil) (.node [v565, v732, v852, v1095, v1279] .nil .nil)) (.node [v565, v732, v852, v1097, v1263] (.node [v565, v732, v852, v1095, v1289] .nil .nil) .nil)) (.node [v565, v732, v852, v1150, v1626] (.node [v565, v732, v852, v1150, v1598] (.node [v565, v732, v852, v1150, v1539] .nil .nil) (.node [v565, v732, v852, v1150, v1612] .nil .nil)) (.node [v565, v732, v852, v1153, v1515] (.node [v565, v732, v852, v1151, v1515] .nil .nil) .nil))) (.node [v565, v732, v852, v1167, v1339] (.node [v565, v732, v852, v1161, v1419] (.node [v565, v732, v852, v1156, v1515] (.node [v565, v732, v852, v1155, v1515] .nil .nil) (.node [v565, v732, v852, v1161, v1360] .nil .nil)) (.node [v565, v732, v852, v1161, v1468] (.node [v565, v732, v852, v1161, v1442] .nil .nil) .nil)) (.node [v565, v732, v852, v1167, v1462] (.node [v565, v732, v852, v1167, v1436] (.node [v565, v732, v852, v1167, v1413] .nil .nil) .nil) (.node [v565, v732, v852, v1169, v1315] (.node [v565, v732, v852, v1168, v1315] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlrl_ok : everyKey (rowOK 3 level3) level4rlrl = true := by decide +kernel
def level4rlrr : BinaryTree (List W) := (.node [v565, v732, v852, v1193, v1515] (.node [v565, v732, v852, v1183, v1642] (.node [v565, v732, v852, v1175, v1282] (.node [v565, v732, v852, v1175, v1269] (.node [v565, v732, v852, v1171, v1315] .nil .nil) (.node [v565, v732, v852, v1175, v1279] .nil .nil)) (.node [v565, v732, v852, v1179, v1263] (.node [v565, v732, v852, v1175, v1289] .nil .nil) .nil)) (.node [v565, v732, v852, v1185, v1626] (.node [v565, v732, v852, v1185, v1598] (.node [v565, v732, v852, v1185, v1539] .nil .nil) (.node [v565, v732, v852, v1185, v1612] .nil .nil)) (.node [v565, v732, v852, v1192, v1515] (.node [v565, v732, v852, v1189, v1515] .nil .nil) .nil))) (.node [v565, v732, v852, v1204, v1339] (.node [v565, v732, v852, v1198, v1419] (.node [v565, v732, v852, v1196, v1515] (.node [v565, v732, v852, v1194, v1492] .nil .nil) (.node [v565, v732, v852, v1198, v1360] .nil .nil)) (.node [v565, v732, v852, v1198, v1468] (.node [v565, v732, v852, v1198, v1442] .nil .nil) .nil)) (.node [v565, v732, v852, v1204, v1462] (.node [v565, v732, v852, v1204, v1436] (.node [v565, v732, v852, v1204, v1413] .nil .nil) .nil) (.node [v565, v732, v852, v1210, v1315] (.node [v565, v732, v852, v1208, v1315] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlrr_ok : everyKey (rowOK 3 level3) level4rlrr = true := by decide +kernel
def level4rlr : BinaryTree (List W) := .node [v565, v732, v852, v1170, v1315] level4rlrl level4rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlr_ok : everyKey (rowOK 3 level3) level4rlr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rlrl && everyKey (rowOK 3 level3) level4rlrr) = true
  rw [level4rlrl_ok, level4rlrr_ok]
  decide +kernel
def level4rl : BinaryTree (List W) := .node [v565, v732, v852, v1093, v1315] level4rll level4rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rl_ok : everyKey (rowOK 3 level3) level4rl = true := by
  change (_ && everyKey (rowOK 3 level3) level4rll && everyKey (rowOK 3 level3) level4rlr) = true
  rw [level4rll_ok, level4rlr_ok]
  decide +kernel
def level4rrll : BinaryTree (List W) := (.node [v565, v732, v852, v1233, v1515] (.node [v565, v732, v852, v1223, v1642] (.node [v565, v732, v852, v1214, v1282] (.node [v565, v732, v852, v1214, v1269] (.node [v565, v732, v852, v1213, v1315] .nil .nil) (.node [v565, v732, v852, v1214, v1279] .nil .nil)) (.node [v565, v732, v852, v1218, v1263] (.node [v565, v732, v852, v1214, v1289] .nil .nil) .nil)) (.node [v565, v732, v852, v1225, v1626] (.node [v565, v732, v852, v1225, v1598] (.node [v565, v732, v852, v1225, v1539] .nil .nil) (.node [v565, v732, v852, v1225, v1612] .nil .nil)) (.node [v565, v732, v852, v1232, v1515] (.node [v565, v732, v852, v1229, v1515] .nil .nil) .nil))) (.node [v565, v732, v852, v1244, v1339] (.node [v565, v732, v852, v1238, v1419] (.node [v565, v732, v852, v1235, v1492] (.node [v565, v732, v852, v1234, v1515] .nil .nil) (.node [v565, v732, v852, v1238, v1360] .nil .nil)) (.node [v565, v732, v852, v1238, v1468] (.node [v565, v732, v852, v1238, v1442] .nil .nil) .nil)) (.node [v565, v732, v852, v1244, v1462] (.node [v565, v732, v852, v1244, v1436] (.node [v565, v732, v852, v1244, v1413] .nil .nil) .nil) (.node [v565, v732, v852, v1250, v1315] (.node [v565, v732, v852, v1248, v1315] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrll_ok : everyKey (rowOK 3 level3) level4rrll = true := by decide +kernel
def level4rrlr : BinaryTree (List W) := (.node [v626, v732, v852, v1150, v1515] (.node [v565, v942, v1045, v1315, v1515] (.node [v565, v732, v852, v1254, v1282] (.node [v565, v732, v852, v1254, v1269] (.node [v565, v732, v852, v1252, v1315] .nil .nil) (.node [v565, v732, v852, v1254, v1279] .nil .nil)) (.node [v565, v732, v852, v1258, v1263] (.node [v565, v732, v852, v1254, v1289] .nil .nil) .nil)) (.node [v595, v626, v732, v852, v1315] (.node [v587, v633, v732, v852, v1045] (.node [v581, v633, v732, v852, v1045] .nil .nil) (.node [v594, v626, v732, v852, v1515] .nil .nil)) (.node [v610, v626, v732, v852, v1315] (.node [v601, v626, v732, v852, v1515] .nil .nil) .nil))) (.node [v626, v732, v852, v1413, v1515] (.node [v626, v732, v852, v1315, v1598] (.node [v626, v732, v852, v1315, v1515] (.node [v626, v732, v852, v1167, v1315] .nil .nil) (.node [v626, v732, v852, v1315, v1550] .nil .nil)) (.node [v626, v732, v852, v1350, v1515] (.node [v626, v732, v852, v1315, v1600] .nil .nil) .nil)) (.node [v633, v732, v852, v1045, v1419] (.node [v633, v732, v852, v972, v1515] (.node [v626, v732, v852, v1415, v1515] .nil .nil) .nil) (.node [v633, v732, v852, v1045, v1533] (.node [v633, v732, v852, v1045, v1515] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrlr_ok : everyKey (rowOK 3 level3) level4rrlr = true := by decide +kernel
def level4rrl : BinaryTree (List W) := .node [v565, v732, v852, v1251, v1315] level4rrll level4rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrl_ok : everyKey (rowOK 3 level3) level4rrl = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrll && everyKey (rowOK 3 level3) level4rrlr) = true
  rw [level4rrll_ok, level4rrlr_ok]
  decide +kernel
def level4rrrl : BinaryTree (List W) := (.node [v723, v795, v1045, v1315, v1515] (.node [v639, v732, v852, v1045, v1315] (.node [v633, v732, v852, v1163, v1515] (.node [v633, v732, v852, v1080, v1515] (.node [v633, v732, v852, v1045, v1605] .nil .nil) (.node [v633, v732, v852, v1161, v1515] .nil .nil)) (.node [v639, v732, v852, v1045, v1279] (.node [v639, v732, v852, v1009, v1315] .nil .nil) .nil)) (.node [v639, v732, v852, v1063, v1315] (.node [v639, v732, v852, v1045, v1427] (.node [v639, v732, v852, v1045, v1333] .nil .nil) (.node [v639, v732, v852, v1045, v1428] .nil .nil)) (.node [v639, v732, v852, v1176, v1315] (.node [v639, v732, v852, v1175, v1315] .nil .nil) .nil))) (.node [v732, v793, v795, v1045, v1315] (.node [v732, v772, v795, v1315, v1515] (.node [v725, v795, v1045, v1315, v1515] (.node [v724, v795, v1045, v1315, v1515] .nil .nil) (.node [v732, v771, v795, v1315, v1515] .nil .nil)) (.node [v732, v785, v795, v1045, v1515] (.node [v732, v784, v795, v1045, v1515] .nil .nil) .nil)) (.node [v732, v795, v1045, v1304, v1515] (.node [v732, v795, v1034, v1315, v1515] (.node [v732, v794, v795, v1045, v1315] .nil .nil) .nil) (.node [v732, v795, v1045, v1315, v1515] (.node [v732, v795, v1045, v1315, v1504] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrrl_ok : everyKey (rowOK 3 level3) level4rrrl = true := by decide +kernel
def level4rrrr : BinaryTree (List W) := (.node [v852, v915, v1045, v1300, v1515] (.node [v852, v887, v915, v1315, v1515] (.node [v843, v915, v1045, v1315, v1515] (.node [v732, v795, v1127, v1315, v1515] (.node [v732, v795, v1045, v1393, v1515] .nil .nil) (.node [v795, v943, v1045, v1315, v1515] .nil .nil)) (.node [v845, v915, v1045, v1315, v1515] (.node [v844, v915, v1045, v1315, v1515] .nil .nil) .nil)) (.node [v852, v909, v915, v1045, v1315] (.node [v852, v900, v915, v1045, v1515] (.node [v852, v892, v915, v1315, v1515] .nil .nil) (.node [v852, v905, v915, v1045, v1515] .nil .nil)) (.node [v852, v915, v1030, v1315, v1515] (.node [v852, v914, v915, v1045, v1315] .nil .nil) .nil))) (.node [v943, v1045, v1315, v1582, v1655] (.node [v852, v915, v1045, v1378, v1515] (.node [v852, v915, v1045, v1315, v1515] (.node [v852, v915, v1045, v1315, v1500] .nil .nil) (.node [v852, v915, v1045, v1315, v1569] .nil .nil)) (.node [v915, v944, v1045, v1315, v1515] (.node [v852, v915, v1110, v1315, v1515] .nil .nil) .nil)) (.node [v944, v1045, v1315, v1569, v1654] (.node [v943, v1127, v1315, v1515, v1655] (.node [v943, v1045, v1393, v1515, v1655] .nil .nil) .nil) (.node [v944, v1110, v1315, v1515, v1654] (.node [v944, v1045, v1378, v1515, v1654] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrrr_ok : everyKey (rowOK 3 level3) level4rrrr = true := by decide +kernel
def level4rrr : BinaryTree (List W) := .node [v732, v795, v1045, v1315, v1582] level4rrrl level4rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrr_ok : everyKey (rowOK 3 level3) level4rrr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrrl && everyKey (rowOK 3 level3) level4rrrr) = true
  rw [level4rrrl_ok, level4rrrr_ok]
  decide +kernel
def level4rr : BinaryTree (List W) := .node [v633, v732, v852, v1045, v1604] level4rrl level4rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rr_ok : everyKey (rowOK 3 level3) level4rr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrl && everyKey (rowOK 3 level3) level4rrr) = true
  rw [level4rrl_ok, level4rrr_ok]
  decide +kernel
def level4r : BinaryTree (List W) := .node [v565, v732, v852, v1211, v1315] level4rl level4rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4r_ok : everyKey (rowOK 3 level3) level4r = true := by
  change (_ && everyKey (rowOK 3 level3) level4rl && everyKey (rowOK 3 level3) level4rr) = true
  rw [level4rl_ok, level4rr_ok]
  decide +kernel
def level4 : BinaryTree (List W) := .node [v565, v732, v852, v986, v1557] level4l level4r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4_ok : everyKey (rowOK 3 level3) level4 = true := by
  change (_ && everyKey (rowOK 3 level3) level4l && everyKey (rowOK 3 level3) level4r) = true
  rw [level4l_ok, level4r_ok]
  decide +kernel
theorem closed4 : Closed 4 level4 := closed_next 3 (by decide) level4 level3 closed3 level4_ok
def level5llllll : BinaryTree (List W) := (.node [v34, v638, v732, v852, v1009, v1315] (.node [v34, v565, v732, v852, v1045, v1452] (.node [v34, v510, v638, v732, v852, v1315] (.node [v15, v565, v732, v852, v993, v1315] (.node [v12, v565, v732, v852, v1045, v1263] (.node [v11, v565, v732, v852, v1045, v1263] .nil .nil) .nil) (.node [v16, v565, v732, v852, v993, v1315] .nil .nil)) (.node [v34, v565, v732, v852, v1045, v1365] (.node [v34, v539, v638, v732, v852, v1045] .nil .nil) (.node [v34, v565, v732, v852, v1045, v1427] .nil .nil))) (.node [v34, v565, v732, v852, v1214, v1315] (.node [v34, v565, v732, v852, v1095, v1315] (.node [v34, v565, v732, v852, v1045, v1478] .nil .nil) (.node [v34, v565, v732, v852, v1175, v1315] .nil .nil)) (.node [v34, v578, v732, v852, v1045, v1315] (.node [v34, v565, v732, v852, v1254, v1315] .nil .nil) (.node [v34, v579, v732, v852, v1045, v1315] .nil .nil)))) (.node [v34, v641, v732, v852, v1045, v1315] (.node [v34, v638, v732, v852, v1063, v1315] (.node [v34, v638, v732, v852, v1045, v1333] (.node [v34, v638, v732, v852, v1045, v1315] (.node [v34, v638, v732, v852, v1045, v1279] .nil .nil) .nil) (.node [v34, v638, v732, v852, v1045, v1427] .nil .nil)) (.node [v34, v639, v732, v852, v1045, v1315] (.node [v34, v638, v732, v852, v1175, v1315] .nil .nil) (.node [v34, v640, v732, v852, v1045, v1315] .nil .nil))) (.node [v38, v565, v732, v852, v1045, v1315] (.node [v36, v565, v732, v852, v1045, v1315] (.node [v35, v565, v732, v852, v1045, v1315] .nil .nil) (.node [v37, v565, v732, v852, v1045, v1315] .nil .nil)) (.node [v47, v460, v565, v852, v1045, v1315] (.node [v47, v450, v565, v852, v1045, v1315] .nil .nil) (.node [v47, v464, v565, v852, v1045, v1315] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llllll_ok : everyKey (rowOK 4 level4) level5llllll = true := by decide +kernel
def level5lllllr : BinaryTree (List W) := (.node [v54, v565, v732, v852, v997, v1315] (.node [v47, v565, v741, v852, v1045, v1315] (.node [v47, v565, v732, v852, v1045, v1279] (.node [v47, v565, v732, v852, v1019, v1315] (.node [v47, v565, v732, v852, v1012, v1315] (.node [v47, v565, v732, v852, v1009, v1315] .nil .nil) .nil) (.node [v47, v565, v732, v852, v1045, v1269] .nil .nil)) (.node [v47, v565, v732, v852, v1045, v1289] (.node [v47, v565, v732, v852, v1045, v1282] .nil .nil) (.node [v47, v565, v739, v852, v1045, v1315] .nil .nil))) (.node [v50, v565, v732, v852, v1045, v1315] (.node [v48, v565, v732, v852, v1045, v1315] (.node [v47, v565, v743, v852, v1045, v1315] .nil .nil) (.node [v49, v565, v732, v852, v1045, v1315] .nil .nil)) (.node [v54, v368, v565, v732, v1045, v1315] (.node [v54, v358, v565, v732, v1045, v1315] .nil .nil) (.node [v54, v373, v565, v732, v1045, v1315] .nil .nil)))) (.node [v54, v565, v732, v861, v1045, v1315] (.node [v54, v565, v732, v852, v1045, v1279] (.node [v54, v565, v732, v852, v1019, v1315] (.node [v54, v565, v732, v852, v1012, v1315] (.node [v54, v565, v732, v852, v1009, v1315] .nil .nil) .nil) (.node [v54, v565, v732, v852, v1045, v1269] .nil .nil)) (.node [v54, v565, v732, v852, v1045, v1289] (.node [v54, v565, v732, v852, v1045, v1282] .nil .nil) (.node [v54, v565, v732, v859, v1045, v1315] .nil .nil))) (.node [v57, v565, v732, v852, v1045, v1315] (.node [v55, v565, v732, v852, v1045, v1315] (.node [v54, v565, v732, v863, v1045, v1315] .nil .nil) (.node [v56, v565, v732, v852, v1045, v1315] .nil .nil)) (.node [v59, v255, v565, v732, v852, v957] (.node [v59, v161, v240, v565, v732, v852] .nil .nil) (.node [v59, v255, v565, v732, v852, v1269] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllllr_ok : everyKey (rowOK 4 level4) level5lllllr = true := by decide +kernel
def level5lllll : BinaryTree (List W) := .node [v47, v565, v732, v852, v997, v1315] level5llllll level5lllllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllll_ok : everyKey (rowOK 4 level4) level5lllll = true := by
  change (_ && everyKey (rowOK 4 level4) level5llllll && everyKey (rowOK 4 level4) level5lllllr) = true
  rw [level5llllll_ok, level5lllllr_ok]
  decide +kernel
def level5llllrl : BinaryTree (List W) := (.node [v59, v565, v732, v852, v1068, v1315] (.node [v59, v565, v732, v852, v877, v1315] (.node [v59, v281, v565, v732, v852, v1315] (.node [v59, v258, v565, v732, v852, v1315] (.node [v59, v255, v565, v732, v852, v1365] (.node [v59, v255, v565, v732, v852, v1339] .nil .nil) .nil) (.node [v59, v266, v565, v732, v852, v1315] .nil .nil)) (.node [v59, v565, v676, v732, v852, v1315] (.node [v59, v289, v565, v732, v852, v1315] .nil .nil) (.node [v59, v565, v732, v757, v852, v1315] .nil .nil))) (.node [v59, v565, v732, v852, v1045, v1427] (.node [v59, v565, v732, v852, v957, v1515] (.node [v59, v565, v732, v852, v949, v1648] .nil .nil) (.node [v59, v565, v732, v852, v1045, v1365] .nil .nil)) (.node [v59, v565, v732, v852, v1045, v1478] (.node [v59, v565, v732, v852, v1045, v1452] .nil .nil) (.node [v59, v565, v732, v852, v1066, v1315] .nil .nil)))) (.node [v59, v565, v732, v852, v1225, v1515] (.node [v59, v565, v732, v852, v1175, v1315] (.node [v59, v565, v732, v852, v1150, v1515] (.node [v59, v565, v732, v852, v1095, v1315] (.node [v59, v565, v732, v852, v1090, v1315] .nil .nil) .nil) (.node [v59, v565, v732, v852, v1167, v1315] .nil .nil)) (.node [v59, v565, v732, v852, v1204, v1315] (.node [v59, v565, v732, v852, v1185, v1515] .nil .nil) (.node [v59, v565, v732, v852, v1214, v1315] .nil .nil))) (.node [v61, v565, v732, v852, v1045, v1315] (.node [v59, v565, v732, v852, v1254, v1315] (.node [v59, v565, v732, v852, v1244, v1315] .nil .nil) (.node [v60, v565, v732, v852, v1045, v1315] .nil .nil)) (.node [v63, v565, v732, v852, v1045, v1315] (.node [v62, v255, v565, v732, v852, v1315] .nil .nil) (.node [v64, v565, v732, v852, v1045, v1315] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llllrl_ok : everyKey (rowOK 4 level4) level5llllrl = true := by decide +kernel
def level5llllrr : BinaryTree (List W) := (.node [v72, v161, v565, v732, v852, v1069] (.node [v71, v160, v565, v732, v852, v1045] (.node [v68, v565, v732, v852, v1045, v1185] (.node [v68, v157, v565, v732, v852, v1045] (.node [v67, v565, v732, v852, v1045, v1315] (.node [v66, v565, v732, v852, v1045, v1315] .nil .nil) .nil) (.node [v68, v565, v689, v852, v1220, v1315] .nil .nil)) (.node [v69, v565, v732, v852, v1045, v1315] (.node [v68, v565, v732, v852, v1045, v1315] .nil .nil) (.node [v70, v565, v732, v852, v1045, v1315] .nil .nil))) (.node [v72, v146, v255, v565, v732, v852] (.node [v71, v565, v732, v852, v1045, v1225] (.node [v71, v565, v732, v809, v1260, v1315] .nil .nil) (.node [v71, v565, v732, v852, v1045, v1315] .nil .nil)) (.node [v72, v161, v565, v732, v852, v997] (.node [v72, v161, v565, v732, v852, v953] .nil .nil) (.node [v72, v161, v565, v732, v852, v1045] .nil .nil)))) (.node [v72, v565, v732, v852, v949, v1642] (.node [v72, v289, v565, v732, v852, v1045] (.node [v72, v172, v565, v732, v852, v1045] (.node [v72, v164, v565, v732, v852, v1045] (.node [v72, v161, v565, v732, v852, v1095] .nil .nil) .nil) (.node [v72, v188, v565, v732, v852, v1045] .nil .nil)) (.node [v72, v565, v732, v747, v852, v1045] (.node [v72, v565, v667, v732, v852, v1045] .nil .nil) (.node [v72, v565, v732, v852, v867, v1045] .nil .nil))) (.node [v72, v565, v732, v852, v986, v1515] (.node [v72, v565, v732, v852, v972, v1515] (.node [v72, v565, v732, v852, v953, v1515] .nil .nil) (.node [v72, v565, v732, v852, v977, v1515] .nil .nil)) (.node [v72, v565, v732, v852, v1045, v1338] (.node [v72, v565, v732, v852, v1045, v1336] .nil .nil) (.node [v72, v565, v732, v852, v1045, v1360] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llllrr_ok : everyKey (rowOK 4 level4) level5llllrr = true := by decide +kernel
def level5llllr : BinaryTree (List W) := .node [v65, v565, v732, v852, v1045, v1315] level5llllrl level5llllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llllr_ok : everyKey (rowOK 4 level4) level5llllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llllrl && everyKey (rowOK 4 level4) level5llllrr) = true
  rw [level5llllrl_ok, level5llllrr_ok]
  decide +kernel
def level5llll : BinaryTree (List W) := .node [v59, v255, v565, v732, v852, v1315] level5lllll level5llllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llll_ok : everyKey (rowOK 4 level4) level5llll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lllll && everyKey (rowOK 4 level4) level5llllr) = true
  rw [level5lllll_ok, level5llllr_ok]
  decide +kernel
def level5lllrll : BinaryTree (List W) := (.node [v79, v565, v732, v852, v1045, v1315] (.node [v72, v565, v732, v852, v1214, v1315] (.node [v72, v565, v732, v852, v1045, v1468] (.node [v72, v565, v732, v852, v1045, v1442] (.node [v72, v565, v732, v852, v1045, v1427] (.node [v72, v565, v732, v852, v1045, v1419] .nil .nil) .nil) (.node [v72, v565, v732, v852, v1045, v1452] .nil .nil)) (.node [v72, v565, v732, v852, v1095, v1315] (.node [v72, v565, v732, v852, v1045, v1478] .nil .nil) (.node [v72, v565, v732, v852, v1175, v1315] .nil .nil))) (.node [v75, v161, v565, v732, v852, v1045] (.node [v73, v565, v732, v852, v1045, v1315] (.node [v72, v565, v732, v852, v1254, v1315] .nil .nil) (.node [v74, v565, v732, v852, v1045, v1315] .nil .nil)) (.node [v77, v565, v732, v852, v1045, v1315] (.node [v76, v565, v732, v852, v1045, v1315] .nil .nil) (.node [v78, v565, v732, v852, v1045, v1315] .nil .nil)))) (.node [v82, v565, v732, v852, v1045, v1315] (.node [v81, v565, v732, v852, v1045, v1315] (.node [v80, v565, v732, v852, v977, v1315] (.node [v80, v565, v701, v852, v1045, v1458] (.node [v80, v251, v565, v732, v852, v1315] .nil .nil) .nil) (.node [v80, v565, v732, v852, v1045, v1315] .nil .nil)) (.node [v82, v565, v732, v821, v1045, v1484] (.node [v82, v254, v565, v732, v852, v1315] .nil .nil) (.node [v82, v565, v732, v852, v986, v1315] .nil .nil))) (.node [v84, v565, v732, v852, v1045, v1315] (.node [v83, v255, v565, v732, v852, v1315] (.node [v83, v161, v565, v732, v852, v1045] .nil .nil) (.node [v83, v565, v732, v852, v949, v1515] .nil .nil)) (.node [v86, v565, v732, v852, v1045, v1315] (.node [v85, v565, v732, v852, v1045, v1315] .nil .nil) (.node [v87, v176, v565, v732, v852, v1045] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrll_ok : everyKey (rowOK 4 level4) level5lllrll = true := by decide +kernel
def level5lllrlr : BinaryTree (List W) := (.node [v92, v565, v732, v852, v1045, v1315] (.node [v88, v408, v732, v1045, v1315, v1655] (.node [v87, v565, v732, v852, v1045, v1300] (.node [v87, v565, v732, v845, v1045, v1315] (.node [v87, v362, v565, v732, v1045, v1315] (.node [v87, v316, v852, v1045, v1315, v1654] .nil .nil) .nil) (.node [v87, v565, v732, v852, v1030, v1315] .nil .nil)) (.node [v88, v177, v565, v732, v852, v1045] (.node [v87, v565, v732, v852, v1045, v1315] .nil .nil) (.node [v88, v271, v565, v732, v852, v1315] .nil .nil))) (.node [v88, v565, v732, v852, v1045, v1304] (.node [v88, v565, v725, v852, v1045, v1315] (.node [v88, v454, v565, v852, v1045, v1315] .nil .nil) (.node [v88, v565, v732, v852, v1034, v1315] .nil .nil)) (.node [v90, v565, v732, v852, v1045, v1315] (.node [v88, v565, v732, v852, v1045, v1315] .nil .nil) (.node [v91, v565, v732, v852, v1045, v1315] .nil .nil)))) (.node [v117, v565, v732, v852, v1045, v1604] (.node [v98, v565, v732, v852, v949, v1515] (.node [v95, v565, v732, v852, v1045, v1315] (.node [v94, v565, v732, v852, v1045, v1315] (.node [v93, v565, v732, v852, v1045, v1315] .nil .nil) .nil) (.node [v96, v565, v732, v852, v1045, v1315] .nil .nil)) (.node [v117, v519, v631, v732, v852, v1515] (.node [v99, v565, v732, v852, v949, v1515] .nil .nil) (.node [v117, v565, v732, v852, v1045, v1557] .nil .nil))) (.node [v117, v565, v732, v852, v1161, v1515] (.node [v117, v565, v732, v852, v1045, v1631] (.node [v117, v565, v732, v852, v1045, v1617] .nil .nil) (.node [v117, v565, v732, v852, v1069, v1515] .nil .nil)) (.node [v117, v565, v732, v852, v1238, v1515] (.node [v117, v565, v732, v852, v1198, v1515] .nil .nil) (.node [v117, v587, v631, v732, v852, v1045] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrlr_ok : everyKey (rowOK 4 level4) level5lllrlr = true := by decide +kernel
def level5lllrl : BinaryTree (List W) := .node [v87, v270, v565, v732, v852, v1315] level5lllrll level5lllrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrl_ok : everyKey (rowOK 4 level4) level5lllrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lllrll && everyKey (rowOK 4 level4) level5lllrlr) = true
  rw [level5lllrll_ok, level5lllrlr_ok]
  decide +kernel
def level5lllrrl : BinaryTree (List W) := (.node [v121, v565, v732, v852, v1045, v1515] (.node [v117, v633, v732, v852, v1045, v1515] (.node [v117, v631, v732, v852, v1045, v1533] (.node [v117, v631, v732, v852, v1045, v1419] (.node [v117, v631, v732, v852, v972, v1515] (.node [v117, v593, v732, v852, v1045, v1515] .nil .nil) .nil) (.node [v117, v631, v732, v852, v1045, v1515] .nil .nil)) (.node [v117, v631, v732, v852, v1080, v1515] (.node [v117, v631, v732, v852, v1045, v1604] .nil .nil) (.node [v117, v631, v732, v852, v1161, v1515] .nil .nil))) (.node [v119, v565, v732, v852, v1045, v1515] (.node [v117, v641, v732, v852, v1045, v1515] (.node [v117, v634, v732, v852, v1045, v1515] .nil .nil) (.node [v118, v565, v732, v852, v1045, v1515] .nil .nil)) (.node [v120, v631, v732, v852, v1045, v1515] (.node [v120, v565, v732, v852, v1045, v1648] .nil .nil) (.node [v120, v638, v732, v852, v1045, v1315] .nil .nil)))) (.node [v132, v565, v732, v852, v986, v1515] (.node [v132, v469, v565, v852, v1045, v1515] (.node [v132, v441, v565, v852, v1045, v1515] (.node [v123, v565, v732, v852, v1045, v1515] (.node [v122, v565, v732, v852, v1045, v1515] .nil .nil) .nil) (.node [v132, v458, v565, v852, v1045, v1515] .nil .nil)) (.node [v132, v565, v732, v852, v972, v1515] (.node [v132, v565, v732, v852, v953, v1515] .nil .nil) (.node [v132, v565, v732, v852, v977, v1515] .nil .nil))) (.node [v132, v565, v732, v852, v1045, v1468] (.node [v132, v565, v732, v852, v1045, v1419] (.node [v132, v565, v732, v852, v1045, v1360] .nil .nil) (.node [v132, v565, v732, v852, v1045, v1442] .nil .nil)) (.node [v132, v565, v749, v852, v1045, v1515] (.node [v132, v565, v746, v852, v1045, v1515] .nil .nil) (.node [v132, v565, v751, v852, v1045, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrrl_ok : everyKey (rowOK 4 level4) level5lllrrl = true := by decide +kernel
def level5lllrrr : BinaryTree (List W) := (.node [v141, v565, v732, v852, v1045, v1515] (.node [v140, v565, v732, v852, v986, v1515] (.node [v140, v380, v565, v732, v1045, v1515] (.node [v140, v349, v565, v732, v1045, v1515] (.node [v135, v565, v732, v852, v1045, v1515] (.node [v134, v565, v732, v852, v1045, v1515] .nil .nil) .nil) (.node [v140, v366, v565, v732, v1045, v1515] .nil .nil)) (.node [v140, v565, v732, v852, v972, v1515] (.node [v140, v565, v732, v852, v953, v1515] .nil .nil) (.node [v140, v565, v732, v852, v977, v1515] .nil .nil))) (.node [v140, v565, v732, v852, v1045, v1468] (.node [v140, v565, v732, v852, v1045, v1419] (.node [v140, v565, v732, v852, v1045, v1360] .nil .nil) (.node [v140, v565, v732, v852, v1045, v1442] .nil .nil)) (.node [v140, v565, v732, v869, v1045, v1515] (.node [v140, v565, v732, v866, v1045, v1515] .nil .nil) (.node [v140, v565, v732, v871, v1045, v1515] .nil .nil)))) (.node [v146, v245, v565, v732, v852, v1515] (.node [v146, v240, v565, v732, v852, v1515] (.node [v146, v240, v565, v732, v852, v1090] (.node [v143, v565, v732, v852, v1045, v1515] (.node [v142, v565, v732, v852, v1045, v1515] .nil .nil) .nil) (.node [v146, v240, v565, v732, v852, v1360] .nil .nil)) (.node [v146, v240, v565, v732, v852, v1557] (.node [v146, v240, v565, v732, v852, v1539] .nil .nil) (.node [v146, v243, v565, v732, v852, v1515] .nil .nil))) (.node [v146, v565, v732, v754, v852, v1515] (.node [v146, v286, v565, v732, v852, v1515] (.node [v146, v266, v565, v732, v852, v1515] .nil .nil) (.node [v146, v565, v674, v732, v852, v1515] .nil .nil)) (.node [v146, v565, v732, v852, v957, v1515] (.node [v146, v565, v732, v852, v874, v1515] .nil .nil) (.node [v146, v565, v732, v852, v993, v1648] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrrr_ok : everyKey (rowOK 4 level4) level5lllrrr = true := by decide +kernel
def level5lllrr : BinaryTree (List W) := .node [v133, v565, v732, v852, v1045, v1515] level5lllrrl level5lllrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrr_ok : everyKey (rowOK 4 level4) level5lllrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lllrrl && everyKey (rowOK 4 level4) level5lllrrr) = true
  rw [level5lllrrl_ok, level5lllrrr_ok]
  decide +kernel
def level5lllr : BinaryTree (List W) := .node [v117, v592, v732, v852, v1045, v1515] level5lllrl level5lllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllr_ok : everyKey (rowOK 4 level4) level5lllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lllrl && everyKey (rowOK 4 level4) level5lllrr) = true
  rw [level5lllrl_ok, level5lllrr_ok]
  decide +kernel
def level5lll : BinaryTree (List W) := .node [v72, v565, v732, v852, v1045, v1365] level5llll level5lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lll_ok : everyKey (rowOK 4 level4) level5lll = true := by
  change (_ && everyKey (rowOK 4 level4) level5llll && everyKey (rowOK 4 level4) level5lllr) = true
  rw [level5llll_ok, level5lllr_ok]
  decide +kernel
def level5llrlll : BinaryTree (List W) := (.node [v147, v565, v732, v852, v1045, v1515] (.node [v146, v565, v732, v852, v1161, v1515] (.node [v146, v565, v732, v852, v1086, v1515] (.node [v146, v565, v732, v852, v1045, v1631] (.node [v146, v565, v732, v852, v1045, v1617] (.node [v146, v565, v732, v852, v1045, v1604] .nil .nil) .nil) (.node [v146, v565, v732, v852, v1069, v1515] .nil .nil)) (.node [v146, v565, v732, v852, v1090, v1315] (.node [v146, v565, v732, v852, v1089, v1515] .nil .nil) (.node [v146, v565, v732, v852, v1150, v1515] .nil .nil))) (.node [v146, v565, v732, v852, v1204, v1315] (.node [v146, v565, v732, v852, v1185, v1515] (.node [v146, v565, v732, v852, v1167, v1315] .nil .nil) (.node [v146, v565, v732, v852, v1198, v1515] .nil .nil)) (.node [v146, v565, v732, v852, v1238, v1515] (.node [v146, v565, v732, v852, v1225, v1515] .nil .nil) (.node [v146, v565, v732, v852, v1244, v1315] .nil .nil)))) (.node [v154, v565, v732, v852, v1045, v1515] (.node [v150, v565, v732, v852, v1045, v1515] (.node [v149, v255, v565, v732, v852, v1315] (.node [v149, v240, v565, v732, v852, v1515] (.node [v148, v565, v732, v852, v1045, v1515] .nil .nil) .nil) (.node [v149, v565, v732, v852, v1045, v1648] .nil .nil)) (.node [v152, v565, v732, v852, v1045, v1515] (.node [v151, v240, v565, v732, v852, v1515] .nil .nil) (.node [v153, v565, v732, v852, v1045, v1515] .nil .nil))) (.node [v157, v565, v732, v852, v1045, v1204] (.node [v156, v565, v732, v852, v1045, v1515] (.node [v155, v565, v732, v852, v1045, v1515] .nil .nil) (.node [v157, v565, v689, v852, v1220, v1515] .nil .nil)) (.node [v158, v565, v732, v852, v1045, v1515] (.node [v157, v565, v732, v852, v1045, v1515] .nil .nil) (.node [v159, v565, v732, v852, v1045, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrlll_ok : everyKey (rowOK 4 level4) level5llrlll = true := by decide +kernel
def level5llrllr : BinaryTree (List W) := (.node [v161, v565, v732, v852, v1045, v1536] (.node [v161, v565, v732, v852, v997, v1315] (.node [v161, v565, v632, v732, v852, v1045] (.node [v161, v188, v565, v732, v852, v1045] (.node [v160, v565, v732, v852, v1045, v1515] (.node [v160, v565, v732, v852, v1045, v1244] .nil .nil) .nil) (.node [v161, v243, v565, v732, v852, v1045] .nil .nil)) (.node [v161, v565, v732, v824, v852, v1045] (.node [v161, v565, v704, v732, v852, v1045] .nil .nil) (.node [v161, v565, v732, v852, v993, v1492] .nil .nil))) (.node [v161, v565, v732, v852, v1045, v1269] (.node [v161, v565, v732, v852, v1012, v1315] (.node [v161, v565, v732, v852, v1009, v1315] .nil .nil) (.node [v161, v565, v732, v852, v1019, v1315] .nil .nil)) (.node [v161, v565, v732, v852, v1045, v1282] (.node [v161, v565, v732, v852, v1045, v1279] .nil .nil) (.node [v161, v565, v732, v852, v1045, v1289] .nil .nil)))) (.node [v161, v565, v732, v852, v1238, v1515] (.node [v161, v565, v732, v852, v1045, v1631] (.node [v161, v565, v732, v852, v1045, v1604] (.node [v161, v565, v732, v852, v1045, v1557] (.node [v161, v565, v732, v852, v1045, v1538] .nil .nil) .nil) (.node [v161, v565, v732, v852, v1045, v1617] .nil .nil)) (.node [v161, v565, v732, v852, v1161, v1515] (.node [v161, v565, v732, v852, v1069, v1515] .nil .nil) (.node [v161, v565, v732, v852, v1198, v1515] .nil .nil))) (.node [v166, v565, v732, v852, v1045, v1515] (.node [v163, v565, v732, v852, v1045, v1515] (.node [v162, v565, v732, v852, v1045, v1515] .nil .nil) (.node [v165, v565, v732, v852, v1045, v1515] .nil .nil)) (.node [v168, v565, v732, v852, v1045, v1515] (.node [v167, v565, v732, v852, v1045, v1515] .nil .nil) (.node [v169, v263, v565, v732, v852, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrllr_ok : everyKey (rowOK 4 level4) level5llrllr = true := by decide +kernel
def level5llrll : BinaryTree (List W) := .node [v160, v565, v732, v809, v1260, v1515] level5llrlll level5llrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrll_ok : everyKey (rowOK 4 level4) level5llrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrlll && everyKey (rowOK 4 level4) level5llrllr) = true
  rw [level5llrlll_ok, level5llrllr_ok]
  decide +kernel
def level5llrlrl : BinaryTree (List W) := (.node [v176, v565, v732, v852, v1030, v1515] (.node [v172, v565, v732, v852, v993, v1315] (.node [v171, v565, v732, v832, v1045, v1637] (.node [v170, v565, v732, v852, v1045, v1515] (.node [v169, v565, v732, v852, v1045, v1515] (.node [v169, v565, v732, v852, v1012, v1515] .nil .nil) .nil) (.node [v171, v265, v565, v732, v852, v1515] .nil .nil)) (.node [v171, v565, v732, v852, v1045, v1515] (.node [v171, v565, v732, v852, v1019, v1515] .nil .nil) (.node [v172, v240, v565, v732, v852, v1515] .nil .nil))) (.node [v176, v270, v565, v732, v852, v1515] (.node [v174, v565, v732, v852, v1045, v1515] (.node [v173, v565, v732, v852, v1045, v1515] .nil .nil) (.node [v175, v565, v732, v852, v1045, v1515] .nil .nil)) (.node [v176, v362, v565, v732, v1045, v1515] (.node [v176, v316, v852, v1045, v1515, v1654] .nil .nil) (.node [v176, v565, v732, v845, v1045, v1515] .nil .nil)))) (.node [v177, v565, v732, v852, v1045, v1515] (.node [v177, v454, v565, v852, v1045, v1515] (.node [v177, v271, v565, v732, v852, v1515] (.node [v176, v565, v732, v852, v1045, v1515] (.node [v176, v565, v732, v852, v1045, v1500] .nil .nil) .nil) (.node [v177, v408, v732, v1045, v1515, v1655] .nil .nil)) (.node [v177, v565, v732, v852, v1034, v1515] (.node [v177, v565, v725, v852, v1045, v1515] .nil .nil) (.node [v177, v565, v732, v852, v1045, v1504] .nil .nil))) (.node [v182, v565, v732, v852, v1045, v1515] (.node [v180, v565, v732, v852, v1045, v1515] (.node [v179, v565, v732, v852, v1045, v1515] .nil .nil) (.node [v181, v565, v732, v852, v1045, v1515] .nil .nil)) (.node [v184, v565, v732, v852, v1045, v1515] (.node [v183, v565, v732, v852, v1045, v1515] .nil .nil) (.node [v185, v565, v732, v852, v1045, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrlrl_ok : everyKey (rowOK 4 level4) level5llrlrl = true := by decide +kernel
def level5llrlrr : BinaryTree (List W) := (.node [v207, v615, v732, v852, v1315, v1515] (.node [v207, v565, v732, v852, v1315, v1612] (.node [v188, v565, v732, v852, v1045, v1515] (.node [v188, v565, v732, v852, v1045, v1263] (.node [v188, v565, v732, v852, v1045] (.node [v187, v565, v732, v852, v1045, v1315] .nil .nil) .nil) (.node [v188, v565, v732, v852, v1045, v1315] .nil .nil)) (.node [v207, v565, v732, v852, v1315, v1539] (.node [v188, v565, v732, v852, v1045, v1648] .nil .nil) (.node [v207, v565, v732, v852, v1315, v1598] .nil .nil))) (.node [v207, v565, v732, v852, v1436, v1515] (.node [v207, v565, v732, v852, v1339, v1515] (.node [v207, v565, v732, v852, v1315, v1626] .nil .nil) (.node [v207, v565, v732, v852, v1413, v1515] .nil .nil)) (.node [v207, v601, v623, v732, v852, v1515] (.node [v207, v565, v732, v852, v1462, v1515] .nil .nil) (.node [v207, v610, v623, v732, v852, v1315] .nil .nil)))) (.node [v207, v626, v732, v852, v1315, v1515] (.node [v207, v623, v732, v852, v1315, v1550] (.node [v207, v623, v732, v852, v1167, v1315] (.node [v207, v623, v732, v852, v1150, v1515] (.node [v207, v616, v732, v852, v1315, v1515] .nil .nil) .nil) (.node [v207, v623, v732, v852, v1315, v1515] .nil .nil)) (.node [v207, v623, v732, v852, v1350, v1515] (.node [v207, v623, v732, v852, v1315, v1598] .nil .nil) (.node [v207, v623, v732, v852, v1413, v1515] .nil .nil))) (.node [v209, v565, v732, v852, v1315, v1515] (.node [v207, v640, v732, v852, v1315, v1515] (.node [v207, v634, v732, v852, v1315, v1515] .nil .nil) (.node [v208, v565, v732, v852, v1315, v1515] .nil .nil)) (.node [v210, v623, v732, v852, v1315, v1515] (.node [v210, v565, v732, v852, v1315, v1642] .nil .nil) (.node [v210, v638, v732, v852, v1045, v1315] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrlrr_ok : everyKey (rowOK 4 level4) level5llrlrr = true := by decide +kernel
def level5llrlr : BinaryTree (List W) := .node [v186, v565, v732, v852, v1045, v1315] level5llrlrl level5llrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrlr_ok : everyKey (rowOK 4 level4) level5llrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrlrl && everyKey (rowOK 4 level4) level5llrlrr) = true
  rw [level5llrlrl_ok, level5llrlrr_ok]
  decide +kernel
def level5llrl : BinaryTree (List W) := .node [v169, v565, v712, v852, v1045, v1623] level5llrll level5llrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrl_ok : everyKey (rowOK 4 level4) level5llrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrll && everyKey (rowOK 4 level4) level5llrlr) = true
  rw [level5llrll_ok, level5llrlr_ok]
  decide +kernel
def level5llrrll : BinaryTree (List W) := (.node [v224, v565, v732, v852, v1244, v1315] (.node [v224, v478, v565, v852, v1315, v1515] (.node [v214, v631, v732, v852, v1045, v1515] (.node [v214, v565, v732, v852, v1492, v1515] (.node [v213, v565, v732, v852, v1315, v1515] (.node [v212, v565, v732, v852, v1315, v1515] .nil .nil) .nil) (.node [v214, v623, v732, v852, v1315, v1515] .nil .nil)) (.node [v224, v424, v565, v852, v1315, v1515] (.node [v215, v565, v732, v852, v1315, v1515] .nil .nil) (.node [v224, v456, v565, v852, v1315, v1515] .nil .nil))) (.node [v224, v565, v732, v852, v1167, v1315] (.node [v224, v565, v732, v852, v1090, v1315] (.node [v224, v565, v732, v852, v957, v1515] .nil .nil) (.node [v224, v565, v732, v852, v1150, v1515] .nil .nil)) (.node [v224, v565, v732, v852, v1204, v1315] (.node [v224, v565, v732, v852, v1185, v1515] .nil .nil) (.node [v224, v565, v732, v852, v1225, v1515] .nil .nil)))) (.node [v233, v391, v565, v732, v1315, v1515] (.node [v226, v565, v732, v852, v1315, v1515] (.node [v224, v565, v761, v852, v1315, v1515] (.node [v224, v565, v759, v852, v1315, v1515] (.node [v224, v565, v756, v852, v1315, v1515] .nil .nil) .nil) (.node [v225, v565, v732, v852, v1315, v1515] .nil .nil)) (.node [v233, v332, v565, v732, v1315, v1515] (.node [v227, v565, v732, v852, v1315, v1515] .nil .nil) (.node [v233, v364, v565, v732, v1315, v1515] .nil .nil))) (.node [v233, v565, v732, v852, v1167, v1315] (.node [v233, v565, v732, v852, v1090, v1315] (.node [v233, v565, v732, v852, v957, v1515] .nil .nil) (.node [v233, v565, v732, v852, v1150, v1515] .nil .nil)) (.node [v233, v565, v732, v852, v1204, v1315] (.node [v233, v565, v732, v852, v1185, v1515] .nil .nil) (.node [v233, v565, v732, v852, v1225, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrll_ok : everyKey (rowOK 4 level4) level5llrrll = true := by decide +kernel
def level5llrrlr : BinaryTree (List W) := (.node [v240, v565, v732, v852, v1045, v1442] (.node [v240, v565, v694, v732, v852, v1515] (.node [v235, v565, v732, v852, v1315, v1515] (.node [v233, v565, v732, v881, v1315, v1515] (.node [v233, v565, v732, v879, v1315, v1515] (.node [v233, v565, v732, v876, v1315, v1515] .nil .nil) .nil) (.node [v234, v565, v732, v852, v1315, v1515] .nil .nil)) (.node [v240, v286, v565, v732, v852, v1515] (.node [v236, v565, v732, v852, v1315, v1515] .nil .nil) (.node [v240, v565, v625, v732, v852, v1515] .nil .nil))) (.node [v240, v565, v732, v852, v977, v1515] (.node [v240, v565, v732, v852, v953, v1515] (.node [v240, v565, v732, v814, v852, v1515] .nil .nil) (.node [v240, v565, v732, v852, v972, v1515] .nil .nil)) (.node [v240, v565, v732, v852, v1045, v1360] (.node [v240, v565, v732, v852, v986, v1515] .nil .nil) (.node [v240, v565, v732, v852, v1045, v1419] .nil .nil)))) (.node [v240, v565, v732, v852, v1359, v1515] (.node [v240, v565, v732, v852, v1315, v1612] (.node [v240, v565, v732, v852, v1315, v1539] (.node [v240, v565, v732, v852, v1263, v1642] (.node [v240, v565, v732, v852, v1045, v1468] .nil .nil) .nil) (.node [v240, v565, v732, v852, v1315, v1598] .nil .nil)) (.node [v240, v565, v732, v852, v1339, v1515] (.node [v240, v565, v732, v852, v1315, v1626] .nil .nil) (.node [v240, v565, v732, v852, v1356, v1515] .nil .nil))) (.node [v241, v565, v732, v852, v1315, v1515] (.node [v240, v565, v732, v852, v1436, v1515] (.node [v240, v565, v732, v852, v1413, v1515] .nil .nil) (.node [v240, v565, v732, v852, v1462, v1515] .nil .nil)) (.node [v243, v565, v732, v852, v1315, v1642] (.node [v242, v565, v732, v852, v1315, v1515] .nil .nil) (.node [v244, v565, v732, v852, v1315, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrlr_ok : everyKey (rowOK 4 level4) level5llrrlr = true := by decide +kernel
def level5llrrl : BinaryTree (List W) := .node [v233, v565, v732, v852, v1244, v1315] level5llrrll level5llrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrl_ok : everyKey (rowOK 4 level4) level5llrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrrll && everyKey (rowOK 4 level4) level5llrrlr) = true
  rw [level5llrrll_ok, level5llrrlr_ok]
  decide +kernel
def level5llrrrl : BinaryTree (List W) := (.node [v255, v565, v732, v852, v997, v1315] (.node [v253, v565, v732, v852, v1315, v1515] (.node [v251, v565, v701, v852, v1458, v1515] (.node [v249, v565, v732, v852, v1315, v1515] (.node [v248, v565, v732, v852, v1315, v1515] (.node [v247, v565, v732, v852, v1315, v1515] .nil .nil) .nil) (.node [v250, v565, v732, v852, v1315, v1515] .nil .nil)) (.node [v251, v565, v732, v852, v1315, v1515] (.node [v251, v565, v732, v852, v1315, v1442] .nil .nil) (.node [v252, v565, v732, v852, v1315, v1515] .nil .nil))) (.node [v255, v281, v565, v732, v852, v1315] (.node [v254, v565, v732, v852, v1315, v1468] (.node [v254, v565, v732, v821, v1484, v1515] .nil .nil) (.node [v254, v565, v732, v852, v1315, v1515] .nil .nil)) (.node [v255, v565, v692, v732, v852, v1315] (.node [v255, v565, v624, v732, v852, v1315] .nil .nil) (.node [v255, v565, v732, v812, v852, v1315] .nil .nil)))) (.node [v255, v565, v732, v852, v1315, v1539] (.node [v255, v565, v732, v852, v1045, v1279] (.node [v255, v565, v732, v852, v1019, v1315] (.node [v255, v565, v732, v852, v1012, v1315] (.node [v255, v565, v732, v852, v1009, v1315] .nil .nil) .nil) (.node [v255, v565, v732, v852, v1045, v1269] .nil .nil)) (.node [v255, v565, v732, v852, v1045, v1289] (.node [v255, v565, v732, v852, v1045, v1282] .nil .nil) (.node [v255, v565, v732, v852, v1263, v1492] .nil .nil))) (.node [v255, v565, v732, v852, v1315, v1612] (.node [v255, v565, v732, v852, v1315, v1556] (.node [v255, v565, v732, v852, v1315, v1554] .nil .nil) (.node [v255, v565, v732, v852, v1315, v1598] .nil .nil)) (.node [v255, v565, v732, v852, v1339, v1515] (.node [v255, v565, v732, v852, v1315, v1626] .nil .nil) (.node [v255, v565, v732, v852, v1413, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrrl_ok : everyKey (rowOK 4 level4) level5llrrrl = true := by decide +kernel
def level5llrrrr : BinaryTree (List W) := (.node [v268, v565, v732, v852, v1315, v1515] (.node [v263, v565, v732, v852, v1282, v1515] (.node [v260, v565, v732, v852, v1315, v1515] (.node [v257, v565, v732, v852, v1315, v1515] (.node [v256, v565, v732, v852, v1315, v1515] (.node [v255, v565, v732, v852, v1462, v1515] .nil .nil) .nil) (.node [v259, v565, v732, v852, v1315, v1515] .nil .nil)) (.node [v262, v565, v732, v852, v1315, v1515] (.node [v261, v565, v732, v852, v1315, v1515] .nil .nil) (.node [v263, v565, v712, v852, v1315, v1623] .nil .nil))) (.node [v265, v565, v732, v852, v1289, v1515] (.node [v264, v565, v732, v852, v1315, v1515] (.node [v263, v565, v732, v852, v1315, v1515] .nil .nil) (.node [v265, v565, v732, v832, v1315, v1637] .nil .nil)) (.node [v266, v565, v732, v852, v1045, v1263] (.node [v265, v565, v732, v852, v1315, v1515] .nil .nil) (.node [v267, v565, v732, v852, v1315, v1515] .nil .nil)))) (.node [v271, v454, v565, v852, v1315, v1515] (.node [v270, v565, v732, v852, v1300, v1515] (.node [v270, v362, v565, v732, v1315, v1515] (.node [v270, v316, v852, v1315, v1515, v1654] (.node [v269, v565, v732, v852, v1315, v1515] .nil .nil) .nil) (.node [v270, v565, v732, v845, v1315, v1515] .nil .nil)) (.node [v270, v565, v732, v852, v1315, v1515] (.node [v270, v565, v732, v852, v1315, v1500] .nil .nil) (.node [v271, v408, v732, v1315, v1515, v1655] .nil .nil))) (.node [v271, v565, v732, v852, v1315, v1515] (.node [v271, v565, v732, v852, v1304, v1515] (.node [v271, v565, v725, v852, v1315, v1515] .nil .nil) (.node [v271, v565, v732, v852, v1315, v1504] .nil .nil)) (.node [v274, v565, v732, v852, v1315, v1515] (.node [v273, v565, v732, v852, v1315, v1515] .nil .nil) (.node [v275, v565, v732, v852, v1315, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrrr_ok : everyKey (rowOK 4 level4) level5llrrrr = true := by decide +kernel
def level5llrrr : BinaryTree (List W) := .node [v255, v565, v732, v852, v1436, v1515] level5llrrrl level5llrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrr_ok : everyKey (rowOK 4 level4) level5llrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrrrl && everyKey (rowOK 4 level4) level5llrrrr) = true
  rw [level5llrrrl_ok, level5llrrrr_ok]
  decide +kernel
def level5llrr : BinaryTree (List W) := .node [v246, v565, v732, v852, v1315, v1515] level5llrrl level5llrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrr_ok : everyKey (rowOK 4 level4) level5llrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrrl && everyKey (rowOK 4 level4) level5llrrr) = true
  rw [level5llrrl_ok, level5llrrr_ok]
  decide +kernel
def level5llr : BinaryTree (List W) := .node [v211, v565, v732, v852, v1315, v1515] level5llrl level5llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llr_ok : everyKey (rowOK 4 level4) level5llr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrl && everyKey (rowOK 4 level4) level5llrr) = true
  rw [level5llrl_ok, level5llrr_ok]
  decide +kernel
def level5ll : BinaryTree (List W) := .node [v146, v565, v732, v852, v1045, v1557] level5lll level5llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5ll_ok : everyKey (rowOK 4 level4) level5ll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lll && everyKey (rowOK 4 level4) level5llr) = true
  rw [level5lll_ok, level5llr_ok]
  decide +kernel
def level5lrllll : BinaryTree (List W) := (.node [v289, v565, v732, v852, v1492, v1515] (.node [v281, v565, v732, v852, v1315, v1642] (.node [v281, v565, v732, v852, v993, v1315] (.node [v279, v565, v732, v852, v1315, v1515] (.node [v278, v565, v732, v852, v1315, v1515] (.node [v277, v565, v732, v852, v1315, v1515] .nil .nil) .nil) (.node [v280, v565, v732, v852, v1045, v1315] .nil .nil)) (.node [v281, v565, v732, v852, v1315] (.node [v281, v565, v732, v852, v1045, v1315] .nil .nil) (.node [v281, v565, v732, v852, v1315, v1515] .nil .nil))) (.node [v286, v565, v732, v852, v1045, v1515] (.node [v285, v565, v732, v852, v1045, v1515] (.node [v283, v565, v732, v852, v1045, v1315] .nil .nil) (.node [v286, v565, v732, v852, v949, v1515] .nil .nil)) (.node [v286, v565, v732, v852, v1492, v1515] (.node [v286, v565, v732, v852, v1315, v1515] .nil .nil) (.node [v286, v565, v732, v852, v1515] .nil .nil)))) (.node [v307, v565, v732, v852, v1045, v1315] (.node [v303, v565, v732, v852, v1045, v1515] (.node [v296, v565, v653, v1045, v1315, v1515] (.node [v291, v565, v732, v852, v1045, v1515] (.node [v290, v565, v732, v852, v1315, v1515] .nil .nil) .nil) (.node [v302, v565, v732, v852, v1315, v1515] .nil .nil)) (.node [v305, v565, v732, v852, v1045, v1315] (.node [v304, v565, v732, v852, v1315, v1515] .nil .nil) (.node [v306, v565, v732, v852, v1045, v1515] .nil .nil))) (.node [v315, v407, v565, v891, v1315, v1515] (.node [v315, v407, v565, v783, v1045, v1515] (.node [v315, v407, v565, v770, v1315, v1515] .nil .nil) (.node [v315, v407, v565, v792, v1045, v1315] .nil .nil)) (.node [v315, v407, v565, v913, v1045, v1315] (.node [v315, v407, v565, v904, v1045, v1515] .nil .nil) (.node [v315, v407, v565, v1045, v1315, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrllll_ok : everyKey (rowOK 4 level4) level5lrllll = true := by decide +kernel
def level5lrlllr : BinaryTree (List W) := (.node [v316, v852, v914, v1045, v1315, v1654] (.node [v315, v565, v845, v1045, v1315, v1515] (.node [v315, v407, v565, v1126, v1315, v1515] (.node [v315, v407, v565, v1045, v1392, v1515] (.node [v315, v407, v565, v1045, v1377, v1515] (.node [v315, v407, v565, v1045, v1315, v1581] .nil .nil) .nil) (.node [v315, v407, v565, v1109, v1315, v1515] .nil .nil)) (.node [v315, v492, v565, v1045, v1315, v1515] (.node [v315, v409, v565, v1045, v1315, v1515] .nil .nil) (.node [v315, v565, v797, v1045, v1315, v1515] .nil .nil))) (.node [v316, v844, v1045, v1315, v1515, v1654] (.node [v316, v362, v1045, v1315, v1515, v1654] (.node [v315, v565, v943, v1045, v1315, v1515] .nil .nil) (.node [v316, v565, v845, v1045, v1315, v1515] .nil .nil)) (.node [v316, v852, v892, v1315, v1515, v1654] (.node [v316, v845, v1045, v1315, v1515, v1654] .nil .nil) (.node [v316, v852, v905, v1045, v1515, v1654] .nil .nil)))) (.node [v316, v852, v1110, v1315, v1515, v1654] (.node [v316, v852, v1045, v1315, v1515, v1653] (.node [v316, v852, v1045, v1300, v1515, v1654] (.node [v316, v852, v1030, v1315, v1515, v1654] (.node [v316, v852, v915, v1045, v1315, v1515] .nil .nil) .nil) (.node [v316, v852, v1045, v1315, v1500, v1654] .nil .nil)) (.node [v316, v852, v1045, v1315, v1569, v1654] (.node [v316, v852, v1045, v1315, v1515, v1654] .nil .nil) (.node [v316, v852, v1045, v1378, v1515, v1654] .nil .nil))) (.node [v319, v450, v565, v852, v1045, v1315] (.node [v317, v407, v565, v1045, v1315, v1515] (.node [v316, v944, v1045, v1315, v1515, v1654] .nil .nil) (.node [v318, v638, v732, v852, v1045, v1315] .nil .nil)) (.node [v321, v631, v732, v852, v1045, v1515] (.node [v320, v450, v565, v852, v1045, v1315] .nil .nil) (.node [v322, v441, v565, v852, v1045, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlllr_ok : everyKey (rowOK 4 level4) level5lrlllr = true := by decide +kernel
def level5lrlll : BinaryTree (List W) := .node [v315, v407, v565, v1045, v1315, v1568] level5lrllll level5lrlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlll_ok : everyKey (rowOK 4 level4) level5lrlll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrllll && everyKey (rowOK 4 level4) level5lrlllr) = true
  rw [level5lrllll_ok, level5lrlllr_ok]
  decide +kernel
def level5lrllrl : BinaryTree (List W) := (.node [v332, v565, v732, v852, v1339, v1515] (.node [v332, v417, v565, v732, v1315, v1515] (.node [v328, v565, v732, v852, v1315, v1515] (.node [v326, v424, v565, v852, v1315, v1515] (.node [v325, v424, v565, v852, v1315, v1515] (.node [v324, v623, v732, v852, v1315, v1515] .nil .nil) .nil) (.node [v327, v565, v732, v852, v1492, v1515] .nil .nil)) (.node [v330, v565, v732, v852, v1315, v1642] (.node [v329, v565, v732, v852, v1045, v1515] .nil .nil) (.node [v332, v391, v565, v732, v1315, v1515] .nil .nil))) (.node [v332, v565, v732, v852, v1315, v1539] (.node [v332, v565, v732, v825, v1315, v1515] (.node [v332, v418, v565, v732, v1315, v1515] .nil .nil) (.node [v332, v565, v732, v835, v1315, v1515] .nil .nil)) (.node [v332, v565, v732, v852, v1315, v1612] (.node [v332, v565, v732, v852, v1315, v1598] .nil .nil) (.node [v332, v565, v732, v852, v1315, v1626] .nil .nil)))) (.node [v338, v565, v732, v832, v1315, v1637] (.node [v334, v565, v732, v852, v1315, v1515] (.node [v332, v565, v732, v852, v1462, v1515] (.node [v332, v565, v732, v852, v1436, v1515] (.node [v332, v565, v732, v852, v1413, v1515] .nil .nil) .nil) (.node [v333, v565, v732, v852, v1315, v1515] .nil .nil)) (.node [v337, v565, v732, v852, v1315, v1515] (.node [v335, v565, v732, v852, v1315, v1515] .nil .nil) (.node [v338, v355, v565, v732, v852, v1515] .nil .nil))) (.node [v340, v565, v732, v852, v1315, v1515] (.node [v338, v565, v732, v852, v1478, v1515] (.node [v338, v565, v732, v852, v1315, v1515] .nil .nil) (.node [v339, v565, v732, v852, v1315, v1515] .nil .nil)) (.node [v343, v565, v732, v852, v1315, v1515] (.node [v342, v565, v732, v852, v1315, v1515] .nil .nil) (.node [v344, v382, v565, v732, v852, v1315] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrllrl_ok : everyKey (rowOK 4 level4) level5lrllrl = true := by decide +kernel
def level5lrllrr : BinaryTree (List W) := (.node [v349, v565, v732, v852, v1198, v1515] (.node [v349, v565, v732, v813, v1045, v1515] (.node [v347, v565, v732, v852, v1045, v1648] (.node [v345, v565, v732, v852, v1315, v1515] (.node [v344, v565, v732, v852, v1315, v1631] (.node [v344, v565, v732, v852, v1315, v1515] .nil .nil) .nil) (.node [v346, v565, v732, v852, v1045, v1315] .nil .nil)) (.node [v349, v414, v565, v732, v1045, v1515] (.node [v349, v380, v565, v732, v1045, v1515] .nil .nil) (.node [v349, v415, v565, v732, v1045, v1515] .nil .nil))) (.node [v349, v565, v732, v852, v1045, v1617] (.node [v349, v565, v732, v852, v1045, v1557] (.node [v349, v565, v732, v834, v1045, v1515] .nil .nil) (.node [v349, v565, v732, v852, v1045, v1604] .nil .nil)) (.node [v349, v565, v732, v852, v1069, v1515] (.node [v349, v565, v732, v852, v1045, v1631] .nil .nil) (.node [v349, v565, v732, v852, v1161, v1515] .nil .nil)))) (.node [v358, v373, v565, v732, v1045, v1315] (.node [v354, v565, v732, v852, v1045, v1515] (.node [v351, v565, v732, v852, v1045, v1515] (.node [v350, v565, v732, v852, v1045, v1515] (.node [v349, v565, v732, v852, v1238, v1515] .nil .nil) .nil) (.node [v352, v565, v732, v852, v1045, v1515] .nil .nil)) (.node [v355, v565, v732, v852, v1045, v1515] (.node [v355, v565, v732, v832, v1045, v1637] .nil .nil) (.node [v355, v565, v732, v852, v1254, v1515] .nil .nil))) (.node [v358, v565, v732, v823, v1045, v1315] (.node [v358, v412, v565, v732, v1045, v1315] (.node [v358, v411, v565, v732, v1045, v1315] .nil .nil) (.node [v358, v565, v732, v811, v1045, v1315] .nil .nil)) (.node [v358, v565, v732, v852, v1045, v1427] (.node [v358, v565, v732, v852, v1045, v1365] .nil .nil) (.node [v358, v565, v732, v852, v1045, v1452] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrllrr_ok : everyKey (rowOK 4 level4) level5lrllrr = true := by decide +kernel
def level5lrllr : BinaryTree (List W) := .node [v344, v565, v732, v821, v1484, v1515] level5lrllrl level5lrllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrllr_ok : everyKey (rowOK 4 level4) level5lrllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrllrl && everyKey (rowOK 4 level4) level5lrllrr) = true
  rw [level5lrllrl_ok, level5lrllrr_ok]
  decide +kernel
def level5lrll : BinaryTree (List W) := .node [v323, v441, v565, v852, v1045, v1515] level5lrlll level5lrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrll_ok : everyKey (rowOK 4 level4) level5lrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrlll && everyKey (rowOK 4 level4) level5lrllr) = true
  rw [level5lrlll_ok, level5lrllr_ok]
  decide +kernel
def level5lrlrll : BinaryTree (List W) := (.node [v373, v565, v732, v852, v1045, v1315] (.node [v362, v565, v732, v1030, v1315, v1515] (.node [v361, v565, v725, v1045, v1315, v1515] (.node [v358, v565, v732, v852, v1214, v1315] (.node [v358, v565, v732, v852, v1175, v1315] (.node [v358, v565, v732, v852, v1095, v1315] .nil .nil) .nil) (.node [v358, v565, v732, v852, v1254, v1315] .nil .nil)) (.node [v361, v644, v732, v1045, v1315, v1515] (.node [v361, v566, v732, v1045, v1315, v1515] .nil .nil) (.node [v361, v732, v795, v1045, v1315, v1515] .nil .nil))) (.node [v369, v565, v732, v1045, v1315, v1515] (.node [v362, v565, v732, v1045, v1315, v1500] (.node [v362, v565, v732, v1045, v1300, v1515] .nil .nil) (.node [v362, v565, v732, v1045, v1315, v1515] .nil .nil)) (.node [v372, v565, v732, v852, v1045, v1315] (.node [v370, v644, v732, v1045, v1315, v1515] .nil .nil) (.node [v373, v565, v732, v832, v1045, v1315] .nil .nil)))) (.node [v380, v565, v732, v852, v1045, v1515] (.node [v376, v565, v732, v852, v1045, v1315] (.node [v373, v565, v732, v1045, v1315, v1637] (.node [v373, v565, v732, v1045, v1315, v1515] (.node [v373, v565, v732, v1045, v1315] .nil .nil) .nil) (.node [v374, v565, v732, v852, v1045, v1315] .nil .nil)) (.node [v378, v565, v732, v852, v1045, v1515] (.node [v377, v565, v732, v852, v1045, v1315] .nil .nil) (.node [v380, v565, v732, v821, v1045, v1515] .nil .nil))) (.node [v381, v565, v732, v852, v1045, v1315] (.node [v380, v565, v732, v1045, v1484, v1515] (.node [v380, v565, v732, v1045, v1315, v1515] .nil .nil) (.node [v380, v565, v732, v1045, v1515] .nil .nil)) (.node [v382, v565, v732, v852, v1045, v1315] (.node [v382, v565, v732, v821, v1045, v1484] .nil .nil) (.node [v382, v565, v732, v852, v1238, v1315] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrll_ok : everyKey (rowOK 4 level4) level5lrlrll = true := by decide +kernel
def level5lrlrlr : BinaryTree (List W) := (.node [v396, v565, v732, v852, v1045, v1315] (.node [v391, v565, v732, v1315, v1515] (.node [v391, v565, v732, v809, v1315, v1515] (.node [v387, v565, v732, v852, v1045, v1315] (.node [v386, v565, v732, v852, v1045, v1315] (.node [v385, v565, v732, v852, v1045, v1515] .nil .nil) .nil) (.node [v388, v565, v732, v852, v1315, v1515] .nil .nil)) (.node [v391, v565, v732, v1045, v1315, v1515] (.node [v391, v565, v732, v852, v1315, v1515] .nil .nil) (.node [v391, v565, v732, v1260, v1315, v1515] .nil .nil))) (.node [v394, v565, v732, v809, v1260, v1515] (.node [v393, v565, v732, v852, v1045, v1515] (.node [v392, v565, v732, v852, v1045, v1515] .nil .nil) (.node [v394, v398, v565, v732, v852, v1045] .nil .nil)) (.node [v394, v565, v732, v852, v1045, v1626] (.node [v394, v565, v732, v852, v1045, v1515] .nil .nil) (.node [v395, v565, v732, v852, v1045, v1515] .nil .nil)))) (.node [v407, v565, v944, v1045, v1315, v1515] (.node [v399, v565, v732, v852, v1045, v1315] (.node [v398, v565, v732, v852, v1045, v1315] (.node [v398, v565, v732, v809, v1260, v1315] (.node [v397, v565, v732, v852, v1045, v1315] .nil .nil) .nil) (.node [v398, v565, v732, v852, v1045, v1462] .nil .nil)) (.node [v407, v565, v725, v1045, v1315, v1515] (.node [v407, v492, v565, v1045, v1315, v1515] .nil .nil) (.node [v407, v565, v917, v1045, v1315, v1515] .nil .nil))) (.node [v408, v725, v1045, v1315, v1515, v1655] (.node [v408, v565, v725, v1045, v1315, v1515] (.node [v408, v454, v1045, v1315, v1515, v1655] .nil .nil) (.node [v408, v724, v1045, v1315, v1515, v1655] .nil .nil)) (.node [v408, v732, v785, v1045, v1515, v1655] (.node [v408, v732, v772, v1315, v1515, v1655] .nil .nil) (.node [v408, v732, v794, v1045, v1315, v1655] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrlr_ok : everyKey (rowOK 4 level4) level5lrlrlr = true := by decide +kernel
def level5lrlrl : BinaryTree (List W) := .node [v384, v565, v732, v852, v1045, v1515] level5lrlrll level5lrlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrl_ok : everyKey (rowOK 4 level4) level5lrlrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrlrll && everyKey (rowOK 4 level4) level5lrlrlr) = true
  rw [level5lrlrll_ok, level5lrlrlr_ok]
  decide +kernel
def level5lrlrrl : BinaryTree (List W) := (.node [v424, v478, v565, v852, v1315, v1515] (.node [v408, v943, v1045, v1315, v1515, v1655] (.node [v408, v732, v1045, v1315, v1515, v1655] (.node [v408, v732, v1045, v1315, v1504, v1655] (.node [v408, v732, v1045, v1304, v1515, v1655] (.node [v408, v732, v1034, v1315, v1515, v1655] .nil .nil) .nil) (.node [v408, v732, v1045, v1315, v1515, v1653] .nil .nil)) (.node [v408, v732, v1045, v1393, v1515, v1655] (.node [v408, v732, v1045, v1315, v1582, v1655] .nil .nil) (.node [v408, v732, v1127, v1315, v1515, v1655] .nil .nil))) (.node [v419, v565, v732, v852, v1492, v1515] (.node [v413, v631, v732, v852, v1045, v1515] (.node [v410, v638, v732, v852, v1045, v1315] .nil .nil) (.node [v416, v623, v732, v852, v1315, v1515] .nil .nil)) (.node [v421, v565, v732, v852, v1045, v1515] (.node [v420, v565, v732, v852, v1315, v1515] .nil .nil) (.node [v422, v565, v732, v852, v1315, v1642] .nil .nil)))) (.node [v424, v565, v732, v852, v1436, v1515] (.node [v424, v565, v732, v852, v1315, v1612] (.node [v424, v565, v732, v852, v1315, v1539] (.node [v424, v565, v715, v852, v1315, v1515] (.node [v424, v565, v705, v852, v1315, v1515] .nil .nil) .nil) (.node [v424, v565, v732, v852, v1315, v1598] .nil .nil)) (.node [v424, v565, v732, v852, v1339, v1515] (.node [v424, v565, v732, v852, v1315, v1626] .nil .nil) (.node [v424, v565, v732, v852, v1413, v1515] .nil .nil))) (.node [v428, v565, v732, v852, v1315, v1515] (.node [v425, v565, v732, v852, v1315, v1515] (.node [v424, v565, v732, v852, v1462, v1515] .nil .nil) (.node [v427, v565, v732, v852, v1315, v1515] .nil .nil)) (.node [v430, v447, v565, v732, v852, v1515] (.node [v429, v565, v732, v852, v1315, v1515] .nil .nil) (.node [v430, v565, v712, v852, v1315, v1623] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrrl_ok : everyKey (rowOK 4 level4) level5lrlrrl = true := by decide +kernel
def level5lrlrrr : BinaryTree (List W) := (.node [v441, v565, v732, v852, v1045, v1604] (.node [v436, v565, v732, v852, v1315, v1617] (.node [v435, v565, v732, v852, v1315, v1515] (.node [v433, v565, v732, v852, v1315, v1515] (.node [v432, v565, v732, v852, v1315, v1515] (.node [v430, v565, v732, v852, v1452, v1515] .nil .nil) .nil) (.node [v434, v565, v732, v852, v1315, v1515] .nil .nil)) (.node [v436, v565, v701, v852, v1458, v1515] (.node [v436, v474, v565, v732, v852, v1315] .nil .nil) (.node [v436, v565, v732, v852, v1315, v1515] .nil .nil))) (.node [v441, v469, v565, v852, v1045, v1515] (.node [v438, v565, v732, v852, v1045, v1315] (.node [v437, v565, v732, v852, v1315, v1515] .nil .nil) (.node [v439, v565, v732, v852, v1045, v1648] .nil .nil)) (.node [v441, v565, v714, v852, v1045, v1515] (.node [v441, v565, v693, v852, v1045, v1515] .nil .nil) (.node [v441, v565, v732, v852, v1045, v1557] .nil .nil)))) (.node [v445, v565, v732, v852, v1045, v1515] (.node [v441, v565, v732, v852, v1198, v1515] (.node [v441, v565, v732, v852, v1069, v1515] (.node [v441, v565, v732, v852, v1045, v1631] (.node [v441, v565, v732, v852, v1045, v1617] .nil .nil) .nil) (.node [v441, v565, v732, v852, v1161, v1515] .nil .nil)) (.node [v442, v565, v732, v852, v1045, v1515] (.node [v441, v565, v732, v852, v1238, v1515] .nil .nil) (.node [v444, v565, v732, v852, v1045, v1515] .nil .nil))) (.node [v447, v565, v732, v852, v1214, v1515] (.node [v447, v565, v712, v852, v1045, v1623] (.node [v446, v565, v732, v852, v1045, v1515] .nil .nil) (.node [v447, v565, v732, v852, v1045, v1515] .nil .nil)) (.node [v450, v565, v691, v852, v1045, v1315] (.node [v450, v464, v565, v852, v1045, v1315] .nil .nil) (.node [v450, v565, v703, v852, v1045, v1315] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrrr_ok : everyKey (rowOK 4 level4) level5lrlrrr = true := by decide +kernel
def level5lrlrr : BinaryTree (List W) := .node [v430, v565, v732, v852, v1315, v1515] level5lrlrrl level5lrlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrr_ok : everyKey (rowOK 4 level4) level5lrlrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrlrrl && everyKey (rowOK 4 level4) level5lrlrrr) = true
  rw [level5lrlrrl_ok, level5lrlrrr_ok]
  decide +kernel
def level5lrlr : BinaryTree (List W) := .node [v408, v732, v795, v1045, v1315, v1515] level5lrlrl level5lrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlr_ok : everyKey (rowOK 4 level4) level5lrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrlrl && everyKey (rowOK 4 level4) level5lrlrr) = true
  rw [level5lrlrl_ok, level5lrlrr_ok]
  decide +kernel
def level5lrl : BinaryTree (List W) := .node [v358, v565, v732, v852, v1045, v1478] level5lrll level5lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrl_ok : everyKey (rowOK 4 level4) level5lrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrll && everyKey (rowOK 4 level4) level5lrlr) = true
  rw [level5lrll_ok, level5lrlr_ok]
  decide +kernel
def level5lrrlll : BinaryTree (List W) := (.node [v462, v643, v852, v1045, v1315, v1515] (.node [v453, v570, v852, v1045, v1315, v1515] (.node [v450, v565, v732, v852, v1175, v1315] (.node [v450, v565, v732, v852, v1045, v1478] (.node [v450, v565, v732, v852, v1045, v1452] (.node [v450, v565, v732, v852, v1045, v1427] .nil .nil) .nil) (.node [v450, v565, v732, v852, v1095, v1315] .nil .nil)) (.node [v450, v565, v732, v852, v1254, v1315] (.node [v450, v565, v732, v852, v1214, v1315] .nil .nil) (.node [v453, v565, v845, v1045, v1315, v1515] .nil .nil))) (.node [v454, v565, v852, v1045, v1304, v1515] (.node [v453, v852, v915, v1045, v1315, v1515] (.node [v453, v643, v852, v1045, v1315, v1515] .nil .nil) (.node [v454, v565, v852, v1034, v1315, v1515] .nil .nil)) (.node [v454, v565, v852, v1045, v1315, v1515] (.node [v454, v565, v852, v1045, v1315, v1504] .nil .nil) (.node [v461, v565, v852, v1045, v1315, v1515] .nil .nil)))) (.node [v469, v565, v732, v852, v1045, v1515] (.node [v464, v565, v852, v1045, v1315, v1623] (.node [v464, v565, v852, v1045, v1315] (.node [v464, v565, v732, v852, v1045, v1315] (.node [v464, v565, v712, v852, v1045, v1315] .nil .nil) .nil) (.node [v464, v565, v852, v1045, v1315, v1515] .nil .nil)) (.node [v466, v565, v732, v852, v1045, v1315] (.node [v465, v565, v732, v852, v1045, v1315] .nil .nil) (.node [v469, v565, v701, v852, v1045, v1515] .nil .nil))) (.node [v470, v565, v732, v852, v1045, v1315] (.node [v469, v565, v852, v1045, v1458, v1515] (.node [v469, v565, v852, v1045, v1315, v1515] .nil .nil) (.node [v469, v565, v852, v1045, v1515] .nil .nil)) (.node [v472, v565, v732, v852, v1045, v1515] (.node [v471, v565, v732, v852, v1045, v1315] .nil .nil) (.node [v473, v565, v732, v852, v1045, v1315] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrlll_ok : everyKey (rowOK 4 level4) level5lrrlll = true := by decide +kernel
def level5lrrllr : BinaryTree (List W) := (.node [v486, v565, v732, v852, v1045, v1515] (.node [v480, v565, v732, v852, v1045, v1515] (.node [v478, v565, v852, v1045, v1315, v1515] (.node [v478, v565, v689, v852, v1315, v1515] (.node [v474, v565, v732, v852, v1198, v1315] (.node [v474, v565, v732, v852, v1045, v1315] .nil .nil) .nil) (.node [v478, v565, v732, v852, v1315, v1515] .nil .nil)) (.node [v478, v565, v852, v1315, v1515] (.node [v478, v565, v852, v1220, v1315, v1515] .nil .nil) (.node [v479, v565, v732, v852, v1045, v1515] .nil .nil))) (.node [v484, v565, v732, v852, v1045, v1515] (.node [v482, v565, v732, v852, v1045, v1315] (.node [v481, v565, v732, v852, v1045, v1315] .nil .nil) (.node [v483, v565, v732, v852, v1315, v1515] .nil .nil)) (.node [v486, v490, v565, v732, v852, v1045] (.node [v485, v565, v732, v852, v1045, v1515] .nil .nil) (.node [v486, v565, v689, v852, v1220, v1515] .nil .nil)))) (.node [v492, v565, v653, v1045, v1315, v1515] (.node [v490, v565, v689, v852, v1220, v1315] (.node [v488, v565, v732, v852, v1045, v1315] (.node [v487, v565, v732, v852, v1045, v1515] (.node [v486, v565, v732, v852, v1045, v1612] .nil .nil) .nil) (.node [v489, v565, v732, v852, v1045, v1315] .nil .nil)) (.node [v490, v565, v732, v852, v1045, v1436] (.node [v490, v565, v732, v852, v1045, v1315] .nil .nil) (.node [v491, v565, v732, v852, v1045, v1315] .nil .nil))) (.node [v492, v565, v1045, v1315, v1515] (.node [v492, v565, v852, v1045, v1315, v1515] (.node [v492, v565, v732, v1045, v1315, v1515] .nil .nil) (.node [v492, v565, v945, v1045, v1315, v1515] .nil .nil)) (.node [v493, v732, v1045, v1315, v1515, v1655] (.node [v493, v565, v653, v1045, v1315, v1515] .nil .nil) (.node [v493, v852, v1045, v1315, v1515, v1654] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrllr_ok : everyKey (rowOK 4 level4) level5lrrllr = true := by decide +kernel
def level5lrrll : BinaryTree (List W) := .node [v474, v565, v701, v852, v1045, v1458] level5lrrlll level5lrrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrll_ok : everyKey (rowOK 4 level4) level5lrrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrlll && everyKey (rowOK 4 level4) level5lrrllr) = true
  rw [level5lrrlll_ok, level5lrrllr_ok]
  decide +kernel
def level5lrrlrl : BinaryTree (List W) := (.node [v501, v732, v852, v1141, v1315, v1515] (.node [v501, v565, v732, v852, v1315, v1626] (.node [v500, v565, v732, v852, v1315, v1642] (.node [v498, v565, v732, v852, v1315, v1515] (.node [v497, v565, v732, v852, v1492, v1515] (.node [v495, v565, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v499, v565, v732, v852, v1045, v1515] .nil .nil)) (.node [v501, v565, v732, v852, v1315, v1598] (.node [v501, v565, v732, v852, v1315, v1539] .nil .nil) (.node [v501, v565, v732, v852, v1315, v1612] .nil .nil))) (.node [v501, v565, v732, v852, v1462, v1515] (.node [v501, v565, v732, v852, v1413, v1515] (.node [v501, v565, v732, v852, v1339, v1515] .nil .nil) (.node [v501, v565, v732, v852, v1436, v1515] .nil .nil)) (.node [v501, v584, v732, v852, v1315, v1515] (.node [v501, v576, v732, v852, v1315, v1515] .nil .nil) (.node [v501, v626, v732, v852, v1315, v1515] .nil .nil)))) (.node [v510, v565, v732, v852, v1427, v1515] (.node [v508, v565, v732, v852, v1315, v1515] (.node [v505, v565, v732, v852, v1315, v1515] (.node [v501, v732, v852, v1144, v1315, v1515] (.node [v501, v732, v852, v1142, v1315, v1515] .nil .nil) .nil) (.node [v506, v732, v852, v1144, v1315, v1515] .nil .nil)) (.node [v510, v539, v565, v732, v852, v1515] (.node [v509, v565, v732, v852, v1315, v1515] .nil .nil) (.node [v510, v565, v732, v852, v1315, v1515] .nil .nil))) (.node [v514, v732, v852, v1144, v1315, v1515] (.node [v512, v565, v732, v852, v1315, v1515] (.node [v511, v565, v732, v852, v1315, v1515] .nil .nil) (.node [v513, v565, v732, v852, v1315, v1515] .nil .nil)) (.node [v517, v565, v732, v852, v1315, v1515] (.node [v516, v565, v732, v852, v1315, v1515] .nil .nil) (.node [v518, v565, v732, v852, v1315, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrlrl_ok : everyKey (rowOK 4 level4) level5lrrlrl = true := by decide +kernel
def level5lrrlrr : BinaryTree (List W) := (.node [v530, v565, v732, v852, v1198, v1515] (.node [v528, v732, v852, v1144, v1315, v1515] (.node [v522, v565, v732, v852, v1315, v1515] (.node [v520, v565, v732, v852, v1315, v1515] (.node [v519, v565, v732, v852, v1315, v1604] (.node [v519, v565, v732, v852, v1315, v1515] .nil .nil) .nil) (.node [v521, v565, v732, v852, v1315, v1515] .nil .nil)) (.node [v524, v565, v732, v852, v1045, v1315] (.node [v523, v565, v732, v852, v1315, v1515] .nil .nil) (.node [v526, v732, v852, v1144, v1315, v1515] .nil .nil))) (.node [v530, v565, v732, v852, v1045, v1617] (.node [v530, v565, v732, v852, v1045, v1557] (.node [v529, v565, v732, v852, v1045, v1648] .nil .nil) (.node [v530, v565, v732, v852, v1045, v1604] .nil .nil)) (.node [v530, v565, v732, v852, v1069, v1515] (.node [v530, v565, v732, v852, v1045, v1631] .nil .nil) (.node [v530, v565, v732, v852, v1161, v1515] .nil .nil)))) (.node [v535, v565, v732, v852, v1045, v1515] (.node [v530, v732, v852, v1045, v1404, v1515] (.node [v530, v607, v732, v852, v1045, v1515] (.node [v530, v577, v732, v852, v1045, v1515] (.node [v530, v565, v732, v852, v1238, v1515] .nil .nil) .nil) (.node [v530, v633, v732, v852, v1045, v1515] .nil .nil)) (.node [v530, v732, v852, v1045, v1407, v1515] (.node [v530, v732, v852, v1045, v1405, v1515] .nil .nil) (.node [v534, v732, v852, v1045, v1407, v1515] .nil .nil))) (.node [v539, v565, v732, v852, v1175, v1515] (.node [v538, v565, v732, v852, v1045, v1515] (.node [v537, v565, v732, v852, v1045, v1515] .nil .nil) (.node [v539, v565, v732, v852, v1045, v1515] .nil .nil)) (.node [v541, v565, v732, v852, v1045, v1515] (.node [v540, v565, v732, v852, v1045, v1515] .nil .nil) (.node [v542, v565, v732, v852, v1045, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrlrr_ok : everyKey (rowOK 4 level4) level5lrrlrr = true := by decide +kernel
def level5lrrlr : BinaryTree (List W) := .node [v519, v565, v587, v732, v852, v1315] level5lrrlrl level5lrrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrlr_ok : everyKey (rowOK 4 level4) level5lrrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrlrl && everyKey (rowOK 4 level4) level5lrrlrr) = true
  rw [level5lrrlrl_ok, level5lrrlrr_ok]
  decide +kernel
def level5lrrl : BinaryTree (List W) := .node [v494, v565, v732, v1045, v1315, v1515] level5lrrll level5lrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrl_ok : everyKey (rowOK 4 level4) level5lrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrll && everyKey (rowOK 4 level4) level5lrrlr) = true
  rw [level5lrrll_ok, level5lrrlr_ok]
  decide +kernel
def level5lrrrll : BinaryTree (List W) := (.node [v553, v732, v852, v1045, v1315, v1593] (.node [v549, v565, v732, v852, v1214, v1315] (.node [v549, v565, v732, v852, v1045, v1452] (.node [v549, v565, v732, v852, v1045, v1365] (.node [v547, v732, v852, v1045, v1407, v1515] (.node [v545, v732, v852, v1045, v1407, v1515] .nil .nil) .nil) (.node [v549, v565, v732, v852, v1045, v1427] .nil .nil)) (.node [v549, v565, v732, v852, v1095, v1315] (.node [v549, v565, v732, v852, v1045, v1478] .nil .nil) (.node [v549, v565, v732, v852, v1175, v1315] .nil .nil))) (.node [v549, v639, v732, v852, v1045, v1315] (.node [v549, v591, v732, v852, v1045, v1315] (.node [v549, v565, v732, v852, v1254, v1315] .nil .nil) (.node [v549, v614, v732, v852, v1045, v1315] .nil .nil)) (.node [v549, v732, v852, v1045, v1315, v1591] (.node [v549, v732, v852, v1045, v1315, v1590] .nil .nil) (.node [v549, v732, v852, v1045, v1315, v1593] .nil .nil)))) (.node [v565, v580, v732, v852, v1045, v1315] (.node [v563, v732, v852, v1045, v1315, v1515] (.node [v558, v732, v852, v1045, v1315, v1593] (.node [v556, v732, v852, v1045, v1315, v1593] (.node [v554, v732, v852, v1045, v1315, v1593] .nil .nil) .nil) (.node [v562, v732, v852, v1045, v1315, v1515] .nil .nil)) (.node [v565, v574, v732, v852, v1045, v1315] (.node [v564, v732, v852, v1045, v1315, v1515] .nil .nil) (.node [v565, v575, v732, v852, v1045, v1315] .nil .nil))) (.node [v565, v586, v732, v852, v1045, v1315] (.node [v565, v583, v732, v852, v1045, v1515] (.node [v565, v582, v732, v852, v1045, v1515] .nil .nil) (.node [v565, v585, v732, v852, v1045, v1315] .nil .nil)) (.node [v565, v587, v732, v852, v1161, v1315] (.node [v565, v587, v732, v852, v1045, v1315] .nil .nil) (.node [v565, v588, v732, v852, v1045, v1315] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrll_ok : everyKey (rowOK 4 level4) level5lrrrll = true := by decide +kernel
def level5lrrrlr : BinaryTree (List W) := (.node [v565, v610, v732, v852, v1045, v1315] (.node [v565, v601, v732, v852, v1045, v1598] (.node [v565, v599, v732, v852, v1045, v1515] (.node [v565, v597, v732, v852, v1315, v1515] (.node [v565, v596, v732, v852, v1315, v1515] (.node [v565, v590, v732, v852, v1045, v1315] .nil .nil) .nil) (.node [v565, v598, v732, v852, v1045, v1515] .nil .nil)) (.node [v565, v601, v610, v732, v852, v1045] (.node [v565, v600, v732, v852, v1045, v1515] .nil .nil) (.node [v565, v601, v732, v852, v1045, v1515] .nil .nil))) (.node [v565, v605, v732, v852, v1045, v1515] (.node [v565, v603, v732, v852, v1045, v1515] (.node [v565, v602, v732, v852, v1045, v1515] .nil .nil) (.node [v565, v604, v732, v852, v1045, v1515] .nil .nil)) (.node [v565, v608, v732, v852, v1045, v1315] (.node [v565, v606, v732, v852, v1045, v1315] .nil .nil) (.node [v565, v609, v732, v852, v1045, v1315] .nil .nil)))) (.node [v565, v623, v732, v852, v1167, v1315] (.node [v565, v617, v732, v852, v1045, v1315] (.node [v565, v612, v732, v852, v1045, v1315] (.node [v565, v611, v732, v852, v1045, v1315] (.node [v565, v610, v732, v852, v1045, v1413] .nil .nil) .nil) (.node [v565, v613, v732, v852, v1045, v1315] .nil .nil)) (.node [v565, v623, v732, v852, v1090, v1315] (.node [v565, v623, v732, v852, v957, v1515] .nil .nil) (.node [v565, v623, v732, v852, v1150, v1515] .nil .nil))) (.node [v565, v623, v732, v852, v1244, v1315] (.node [v565, v623, v732, v852, v1204, v1315] (.node [v565, v623, v732, v852, v1185, v1515] .nil .nil) (.node [v565, v623, v732, v852, v1225, v1515] .nil .nil)) (.node [v565, v631, v732, v852, v953, v1515] (.node [v565, v626, v732, v852, v1315, v1515] .nil .nil) (.node [v565, v631, v732, v852, v972, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrlr_ok : everyKey (rowOK 4 level4) level5lrrrlr = true := by decide +kernel
def level5lrrrl : BinaryTree (List W) := .node [v565, v589, v732, v852, v1045, v1315] level5lrrrll level5lrrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrl_ok : everyKey (rowOK 4 level4) level5lrrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrrll && everyKey (rowOK 4 level4) level5lrrrlr) = true
  rw [level5lrrrll_ok, level5lrrrlr_ok]
  decide +kernel
def level5lrrrrl : BinaryTree (List W) := (.node [v565, v640, v732, v852, v993, v1315] (.node [v565, v638, v732, v852, v1009, v1315] (.node [v565, v631, v732, v852, v1045, v1468] (.node [v565, v631, v732, v852, v1045, v1419] (.node [v565, v631, v732, v852, v1045, v1360] (.node [v565, v631, v732, v852, v986, v1515] .nil .nil) .nil) (.node [v565, v631, v732, v852, v1045, v1442] .nil .nil)) (.node [v565, v634, v732, v852, v949, v1515] (.node [v565, v633, v732, v852, v1045, v1515] .nil .nil) (.node [v565, v638, v732, v852, v997, v1315] .nil .nil))) (.node [v565, v638, v732, v852, v1045, v1279] (.node [v565, v638, v732, v852, v1019, v1315] (.node [v565, v638, v732, v852, v1012, v1315] .nil .nil) (.node [v565, v638, v732, v852, v1045, v1269] .nil .nil)) (.node [v565, v638, v732, v852, v1045, v1289] (.node [v565, v638, v732, v852, v1045, v1282] .nil .nil) (.node [v565, v639, v732, v852, v1045, v1315] .nil .nil)))) (.node [v565, v661, v732, v852, v1045, v1315] (.node [v565, v653, v943, v1045, v1315, v1515] (.node [v565, v643, v944, v1045, v1315, v1515] (.node [v565, v642, v945, v1045, v1315, v1515] (.node [v565, v641, v732, v852, v1045, v1263] .nil .nil) .nil) (.node [v565, v644, v943, v1045, v1315, v1515] .nil .nil)) (.node [v565, v653, v945, v1045, v1315, v1515] (.node [v565, v653, v944, v1045, v1315, v1515] .nil .nil) (.node [v565, v660, v732, v852, v1045, v1315] .nil .nil))) (.node [v565, v677, v732, v852, v1315, v1515] (.node [v565, v668, v732, v852, v1045, v1515] (.node [v565, v666, v732, v852, v1045, v1515] .nil .nil) (.node [v565, v675, v732, v852, v1315, v1515] .nil .nil)) (.node [v565, v683, v732, v852, v1045, v1515] (.node [v565, v681, v732, v852, v1315, v1515] .nil .nil) (.node [v565, v685, v732, v852, v1045, v1315] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrrl_ok : everyKey (rowOK 4 level4) level5lrrrrl = true := by decide +kernel
def level5lrrrrr : BinaryTree (List W) := (.node [v565, v695, v852, v1220, v1315, v1515] (.node [v565, v689, v852, v1185, v1220, v1515] (.node [v565, v689, v732, v852, v1204, v1315] (.node [v565, v689, v732, v852, v1167, v1315] (.node [v565, v689, v732, v852, v1150, v1515] (.node [v565, v689, v732, v852, v1090, v1315] .nil .nil) .nil) (.node [v565, v689, v732, v852, v1185, v1515] .nil .nil)) (.node [v565, v689, v732, v852, v1244, v1315] (.node [v565, v689, v732, v852, v1225, v1515] .nil .nil) (.node [v565, v689, v798, v852, v1315, v1515] .nil .nil))) (.node [v565, v689, v852, v1219, v1315, v1515] (.node [v565, v689, v852, v1204, v1220, v1315] (.node [v565, v689, v852, v1195, v1315, v1515] .nil .nil) (.node [v565, v689, v852, v1212, v1315, v1515] .nil .nil)) (.node [v565, v689, v852, v1220, v1315, v1612] (.node [v565, v689, v852, v1220, v1315, v1515] .nil .nil) (.node [v565, v689, v852, v1220, v1436, v1515] .nil .nil)))) (.node [v565, v701, v732, v852, v1045, v1442] (.node [v565, v701, v732, v852, v977, v1515] (.node [v565, v701, v732, v852, v953, v1515] (.node [v565, v697, v732, v852, v1315, v1515] (.node [v565, v696, v852, v1220, v1315, v1515] .nil .nil) .nil) (.node [v565, v701, v732, v852, v972, v1515] .nil .nil)) (.node [v565, v701, v732, v852, v1045, v1360] (.node [v565, v701, v732, v852, v986, v1515] .nil .nil) (.node [v565, v701, v732, v852, v1045, v1419] .nil .nil))) (.node [v565, v701, v852, v1045, v1195, v1515] (.node [v565, v701, v799, v852, v1045, v1515] (.node [v565, v701, v732, v852, v1045, v1468] .nil .nil) (.node [v565, v701, v852, v977, v1458, v1515] .nil .nil)) (.node [v565, v701, v852, v1045, v1450, v1515] (.node [v565, v701, v852, v1045, v1442, v1458] .nil .nil) (.node [v565, v701, v852, v1045, v1457, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrrr_ok : everyKey (rowOK 4 level4) level5lrrrrr = true := by decide +kernel
def level5lrrrr : BinaryTree (List W) := .node [v565, v689, v732, v852, v957, v1515] level5lrrrrl level5lrrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrr_ok : everyKey (rowOK 4 level4) level5lrrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrrrl && everyKey (rowOK 4 level4) level5lrrrrr) = true
  rw [level5lrrrrl_ok, level5lrrrrr_ok]
  decide +kernel
def level5lrrr : BinaryTree (List W) := .node [v565, v631, v732, v852, v977, v1515] level5lrrrl level5lrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrr_ok : everyKey (rowOK 4 level4) level5lrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrrl && everyKey (rowOK 4 level4) level5lrrrr) = true
  rw [level5lrrrl_ok, level5lrrrr_ok]
  decide +kernel
def level5lrr : BinaryTree (List W) := .node [v543, v732, v852, v1045, v1407, v1515] level5lrrl level5lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrr_ok : everyKey (rowOK 4 level4) level5lrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrl && everyKey (rowOK 4 level4) level5lrrr) = true
  rw [level5lrrl_ok, level5lrrr_ok]
  decide +kernel
def level5lr : BinaryTree (List W) := .node [v450, v565, v732, v852, v1045, v1365] level5lrl level5lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lr_ok : everyKey (rowOK 4 level4) level5lr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrl && everyKey (rowOK 4 level4) level5lrr) = true
  rw [level5lrl_ok, level5lrr_ok]
  decide +kernel
def level5l : BinaryTree (List W) := .node [v276, v565, v732, v852, v1315, v1515] level5ll level5lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5l_ok : everyKey (rowOK 4 level4) level5l = true := by
  change (_ && everyKey (rowOK 4 level4) level5ll && everyKey (rowOK 4 level4) level5lr) = true
  rw [level5ll_ok, level5lr_ok]
  decide +kernel
def level5rlllll : BinaryTree (List W) := (.node [v565, v712, v800, v852, v1045, v1315] (.node [v565, v712, v732, v852, v997, v1315] (.node [v565, v708, v732, v852, v1045, v1515] (.node [v565, v706, v852, v1045, v1458, v1515] (.node [v565, v701, v852, v1198, v1458, v1515] (.node [v565, v701, v852, v1045, v1458, v1617] .nil .nil) .nil) (.node [v565, v707, v852, v1045, v1458, v1515] .nil .nil)) (.node [v565, v711, v852, v1045, v1458, v1515] (.node [v565, v711, v732, v852, v949, v1515] .nil .nil) (.node [v565, v711, v852, v1220, v1315, v1515] .nil .nil))) (.node [v565, v712, v732, v852, v1045, v1269] (.node [v565, v712, v732, v852, v1012, v1315] (.node [v565, v712, v732, v852, v1009, v1315] .nil .nil) (.node [v565, v712, v732, v852, v1019, v1315] .nil .nil)) (.node [v565, v712, v732, v852, v1045, v1282] (.node [v565, v712, v732, v852, v1045, v1279] .nil .nil) (.node [v565, v712, v732, v852, v1045, v1289] .nil .nil)))) (.node [v565, v716, v852, v1045, v1315, v1623] (.node [v565, v712, v852, v1045, v1315, v1622] (.node [v565, v712, v852, v1045, v1282, v1623] (.node [v565, v712, v852, v1045, v1212, v1315] (.node [v565, v712, v852, v1012, v1315, v1623] .nil .nil) .nil) (.node [v565, v712, v852, v1045, v1315, v1450] .nil .nil)) (.node [v565, v712, v852, v1045, v1452, v1623] (.node [v565, v712, v852, v1045, v1315, v1623] .nil .nil) (.node [v565, v712, v852, v1214, v1315, v1623] .nil .nil))) (.node [v565, v721, v852, v1045, v1315, v1623] (.node [v565, v718, v732, v852, v1045, v1315] (.node [v565, v717, v852, v1045, v1315, v1623] .nil .nil) (.node [v565, v721, v732, v852, v993, v1315] .nil .nil)) (.node [v565, v722, v732, v852, v1045, v1263] (.node [v565, v721, v852, v1220, v1315, v1515] .nil .nil) (.node [v565, v722, v852, v1045, v1315, v1623] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlllll_ok : everyKey (rowOK 4 level4) level5rlllll = true := by decide +kernel
def level5rllllr : BinaryTree (List W) := (.node [v565, v729, v852, v1045, v1315, v1515] (.node [v565, v725, v852, v1045, v1304, v1515] (.node [v565, v724, v852, v1045, v1315, v1582] (.node [v565, v724, v794, v852, v1045, v1315] (.node [v565, v724, v785, v852, v1045, v1515] (.node [v565, v724, v772, v852, v1315, v1515] .nil .nil) .nil) (.node [v565, v724, v852, v1045, v1315, v1515] .nil .nil)) (.node [v565, v724, v852, v1127, v1315, v1515] (.node [v565, v724, v852, v1045, v1393, v1515] .nil .nil) (.node [v565, v725, v852, v1034, v1315, v1515] .nil .nil))) (.node [v565, v725, v945, v1045, v1315, v1515] (.node [v565, v725, v852, v1045, v1315, v1515] (.node [v565, v725, v852, v1045, v1315, v1504] .nil .nil) (.node [v565, v725, v944, v1045, v1315, v1515] .nil .nil)) (.node [v565, v727, v852, v1045, v1315, v1515] (.node [v565, v726, v852, v1045, v1315, v1515] .nil .nil) (.node [v565, v728, v852, v1045, v1315, v1515] .nil .nil)))) (.node [v565, v732, v765, v852, v1315, v1515] (.node [v565, v732, v745, v852, v1045, v1515] (.node [v565, v732, v738, v852, v1045, v1315] (.node [v565, v731, v852, v1045, v1315, v1515] (.node [v565, v730, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v740, v852, v1045, v1315] .nil .nil)) (.node [v565, v732, v755, v852, v1315, v1515] (.node [v565, v732, v748, v852, v1045, v1515] .nil .nil) (.node [v565, v732, v758, v852, v1315, v1515] .nil .nil))) (.node [v565, v732, v769, v852, v1315, v1515] (.node [v565, v732, v767, v852, v1315, v1515] (.node [v565, v732, v766, v852, v1315, v1515] .nil .nil) (.node [v565, v732, v768, v852, v1315, v1515] .nil .nil)) (.node [v565, v732, v770, v792, v852, v1315] (.node [v565, v732, v770, v783, v852, v1515] .nil .nil) (.node [v565, v732, v770, v852, v1315, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllllr_ok : everyKey (rowOK 4 level4) level5rllllr = true := by decide +kernel
def level5rllll : BinaryTree (List W) := .node [v565, v722, v852, v1045, v1458, v1515] level5rlllll level5rllllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllll_ok : everyKey (rowOK 4 level4) level5rllll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlllll && everyKey (rowOK 4 level4) level5rllllr) = true
  rw [level5rlllll_ok, level5rllllr_ok]
  decide +kernel
def level5rlllrl : BinaryTree (List W) := (.node [v565, v732, v783, v792, v852, v1045] (.node [v565, v732, v775, v852, v1315, v1515] (.node [v565, v732, v772, v852, v1315, v1582] (.node [v565, v732, v772, v794, v852, v1315] (.node [v565, v732, v772, v785, v852, v1515] (.node [v565, v732, v770, v852, v1392, v1515] .nil .nil) .nil) (.node [v565, v732, v772, v852, v1315, v1515] .nil .nil)) (.node [v565, v732, v773, v852, v1315, v1515] (.node [v565, v732, v772, v852, v1393, v1515] .nil .nil) (.node [v565, v732, v774, v852, v1315, v1515] .nil .nil))) (.node [v565, v732, v779, v852, v1045, v1515] (.node [v565, v732, v777, v852, v1045, v1515] (.node [v565, v732, v776, v852, v1315, v1515] .nil .nil) (.node [v565, v732, v778, v852, v1045, v1315] .nil .nil)) (.node [v565, v732, v781, v852, v1045, v1515] (.node [v565, v732, v780, v852, v1045, v1515] .nil .nil) (.node [v565, v732, v782, v852, v1045, v1515] .nil .nil)))) (.node [v565, v732, v787, v852, v1045, v1515] (.node [v565, v732, v785, v852, v1045, v1515] (.node [v565, v732, v783, v852, v1126, v1515] (.node [v565, v732, v783, v852, v1045, v1581] (.node [v565, v732, v783, v852, v1045, v1515] .nil .nil) .nil) (.node [v565, v732, v785, v794, v852, v1045] .nil .nil)) (.node [v565, v732, v785, v852, v1127, v1515] (.node [v565, v732, v785, v852, v1045, v1582] .nil .nil) (.node [v565, v732, v786, v852, v1045, v1515] .nil .nil))) (.node [v565, v732, v791, v852, v1045, v1315] (.node [v565, v732, v789, v852, v1045, v1315] (.node [v565, v732, v788, v852, v1045, v1315] .nil .nil) (.node [v565, v732, v790, v852, v1045, v1315] .nil .nil)) (.node [v565, v732, v792, v852, v1045, v1392] (.node [v565, v732, v792, v852, v1045, v1315] .nil .nil) (.node [v565, v732, v792, v852, v1126, v1315] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlllrl_ok : everyKey (rowOK 4 level4) level5rlllrl = true := by decide +kernel
def level5rlllrr : BinaryTree (List W) := (.node [v565, v732, v809, v852, v1225, v1515] (.node [v565, v732, v805, v852, v1045, v1315] (.node [v565, v732, v801, v852, v1045, v1315] (.node [v565, v732, v795, v1045, v1315, v1515] (.node [v565, v732, v794, v852, v1127, v1315] (.node [v565, v732, v794, v852, v1045, v1393] .nil .nil) .nil) (.node [v565, v732, v796, v1045, v1315, v1515] .nil .nil)) (.node [v565, v732, v803, v852, v1045, v1515] (.node [v565, v732, v802, v852, v1045, v1315] .nil .nil) (.node [v565, v732, v804, v852, v1045, v1515] .nil .nil))) (.node [v565, v732, v809, v852, v1150, v1515] (.node [v565, v732, v809, v852, v957, v1515] (.node [v565, v732, v806, v852, v1045, v1315] .nil .nil) (.node [v565, v732, v809, v852, v1090, v1315] .nil .nil)) (.node [v565, v732, v809, v852, v1185, v1515] (.node [v565, v732, v809, v852, v1167, v1315] .nil .nil) (.node [v565, v732, v809, v852, v1204, v1315] .nil .nil)))) (.node [v565, v732, v809, v1260, v1315, v1626] (.node [v565, v732, v809, v1244, v1260, v1315] (.node [v565, v732, v809, v1225, v1260, v1515] (.node [v565, v732, v809, v918, v1315, v1515] (.node [v565, v732, v809, v852, v1244, v1315] .nil .nil) .nil) (.node [v565, v732, v809, v1236, v1315, v1515] .nil .nil)) (.node [v565, v732, v809, v1259, v1315, v1515] (.node [v565, v732, v809, v1253, v1315, v1515] .nil .nil) (.node [v565, v732, v809, v1260, v1315, v1515] .nil .nil))) (.node [v565, v732, v817, v852, v1315, v1515] (.node [v565, v732, v815, v1260, v1315, v1515] (.node [v565, v732, v809, v1260, v1462, v1515] .nil .nil) (.node [v565, v732, v816, v1260, v1315, v1515] .nil .nil)) (.node [v565, v732, v821, v852, v972, v1515] (.node [v565, v732, v821, v852, v953, v1515] .nil .nil) (.node [v565, v732, v821, v852, v977, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlllrr_ok : everyKey (rowOK 4 level4) level5rlllrr = true := by decide +kernel
def level5rlllr : BinaryTree (List W) := .node [v565, v732, v794, v852, v1045, v1315] level5rlllrl level5rlllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlllr_ok : everyKey (rowOK 4 level4) level5rlllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlllrl && everyKey (rowOK 4 level4) level5rlllrr) = true
  rw [level5rlllrl_ok, level5rlllrr_ok]
  decide +kernel
def level5rlll : BinaryTree (List W) := .node [v565, v732, v770, v852, v1315, v1581] level5rllll level5rlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlll_ok : everyKey (rowOK 4 level4) level5rlll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rllll && everyKey (rowOK 4 level4) level5rlllr) = true
  rw [level5rllll_ok, level5rlllr_ok]
  decide +kernel
def level5rllrll : BinaryTree (List W) := (.node [v565, v732, v831, v852, v949, v1515] (.node [v565, v732, v821, v1045, v1477, v1515] (.node [v565, v732, v821, v919, v1045, v1515] (.node [v565, v732, v821, v852, v1045, v1442] (.node [v565, v732, v821, v852, v1045, v1419] (.node [v565, v732, v821, v852, v1045, v1360] .nil .nil) .nil) (.node [v565, v732, v821, v852, v1045, v1468] .nil .nil)) (.node [v565, v732, v821, v1045, v1236, v1515] (.node [v565, v732, v821, v986, v1484, v1515] .nil .nil) (.node [v565, v732, v821, v1045, v1468, v1484] .nil .nil))) (.node [v565, v732, v821, v1238, v1484, v1515] (.node [v565, v732, v821, v1045, v1484, v1515] (.node [v565, v732, v821, v1045, v1483, v1515] .nil .nil) (.node [v565, v732, v821, v1045, v1484, v1631] .nil .nil)) (.node [v565, v732, v827, v1045, v1484, v1515] (.node [v565, v732, v826, v1045, v1484, v1515] .nil .nil) (.node [v565, v732, v828, v852, v1045, v1515] .nil .nil)))) (.node [v565, v732, v832, v852, v1045, v1282] (.node [v565, v732, v832, v852, v1012, v1315] (.node [v565, v732, v832, v852, v997, v1315] (.node [v565, v732, v831, v1260, v1315, v1515] (.node [v565, v732, v831, v1045, v1484, v1515] .nil .nil) .nil) (.node [v565, v732, v832, v852, v1009, v1315] .nil .nil)) (.node [v565, v732, v832, v852, v1045, v1269] (.node [v565, v732, v832, v852, v1019, v1315] .nil .nil) (.node [v565, v732, v832, v852, v1045, v1279] .nil .nil))) (.node [v565, v732, v832, v1045, v1253, v1315] (.node [v565, v732, v832, v920, v1045, v1315] (.node [v565, v732, v832, v852, v1045, v1289] .nil .nil) (.node [v565, v732, v832, v1019, v1315, v1637] .nil .nil)) (.node [v565, v732, v832, v1045, v1315, v1477] (.node [v565, v732, v832, v1045, v1289, v1637] .nil .nil) (.node [v565, v732, v832, v1045, v1315, v1636] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrll_ok : everyKey (rowOK 4 level4) level5rllrll = true := by decide +kernel
def level5rllrlr : BinaryTree (List W) := (.node [v565, v732, v844, v1045, v1378, v1515] (.node [v565, v732, v842, v852, v1045, v1263] (.node [v565, v732, v838, v852, v1045, v1315] (.node [v565, v732, v836, v1045, v1315, v1637] (.node [v565, v732, v832, v1254, v1315, v1637] (.node [v565, v732, v832, v1045, v1478, v1637] .nil .nil) .nil) (.node [v565, v732, v837, v1045, v1315, v1637] .nil .nil)) (.node [v565, v732, v841, v1045, v1315, v1637] (.node [v565, v732, v841, v852, v993, v1315] .nil .nil) (.node [v565, v732, v841, v1260, v1315, v1515] .nil .nil))) (.node [v565, v732, v844, v905, v1045, v1515] (.node [v565, v732, v842, v1045, v1484, v1515] (.node [v565, v732, v842, v1045, v1315, v1637] .nil .nil) (.node [v565, v732, v844, v892, v1315, v1515] .nil .nil)) (.node [v565, v732, v844, v1045, v1315, v1515] (.node [v565, v732, v844, v914, v1045, v1315] .nil .nil) (.node [v565, v732, v844, v1045, v1315, v1569] .nil .nil)))) (.node [v565, v732, v849, v1045, v1315, v1515] (.node [v565, v732, v845, v1045, v1315, v1515] (.node [v565, v732, v845, v1045, v1300, v1515] (.node [v565, v732, v845, v1030, v1315, v1515] (.node [v565, v732, v844, v1110, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v845, v1045, v1315, v1500] .nil .nil)) (.node [v565, v732, v847, v1045, v1315, v1515] (.node [v565, v732, v846, v1045, v1315, v1515] .nil .nil) (.node [v565, v732, v848, v1045, v1315, v1515] .nil .nil))) (.node [v565, v732, v852, v860, v1045, v1315] (.node [v565, v732, v851, v1045, v1315, v1515] (.node [v565, v732, v850, v1045, v1315, v1515] .nil .nil) (.node [v565, v732, v852, v858, v1045, v1315] .nil .nil)) (.node [v565, v732, v852, v868, v1045, v1515] (.node [v565, v732, v852, v865, v1045, v1515] .nil .nil) (.node [v565, v732, v852, v875, v1315, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrlr_ok : everyKey (rowOK 4 level4) level5rllrlr = true := by decide +kernel
def level5rllrl : BinaryTree (List W) := .node [v565, v732, v832, v1045, v1315, v1637] level5rllrll level5rllrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrl_ok : everyKey (rowOK 4 level4) level5rllrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rllrll && everyKey (rowOK 4 level4) level5rllrlr) = true
  rw [level5rllrll_ok, level5rllrlr_ok]
  decide +kernel
def level5rllrrl : BinaryTree (List W) := (.node [v565, v732, v852, v894, v1315, v1515] (.node [v565, v732, v852, v891, v1315, v1568] (.node [v565, v732, v852, v890, v1315, v1515] (.node [v565, v732, v852, v888, v1315, v1515] (.node [v565, v732, v852, v886, v1315, v1515] (.node [v565, v732, v852, v885, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v889, v1315, v1515] .nil .nil)) (.node [v565, v732, v852, v891, v913, v1315] (.node [v565, v732, v852, v891, v904, v1515] .nil .nil) (.node [v565, v732, v852, v891, v1315, v1515] .nil .nil))) (.node [v565, v732, v852, v892, v1315, v1515] (.node [v565, v732, v852, v892, v905, v1515] (.node [v565, v732, v852, v891, v1377, v1515] .nil .nil) (.node [v565, v732, v852, v892, v914, v1315] .nil .nil)) (.node [v565, v732, v852, v892, v1378, v1515] (.node [v565, v732, v852, v892, v1315, v1569] .nil .nil) (.node [v565, v732, v852, v893, v1315, v1515] .nil .nil)))) (.node [v565, v732, v852, v904, v913, v1045] (.node [v565, v732, v852, v899, v1045, v1515] (.node [v565, v732, v852, v897, v1045, v1515] (.node [v565, v732, v852, v896, v1315, v1515] (.node [v565, v732, v852, v895, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v898, v1045, v1315] .nil .nil)) (.node [v565, v732, v852, v902, v1045, v1515] (.node [v565, v732, v852, v901, v1045, v1515] .nil .nil) (.node [v565, v732, v852, v903, v1045, v1515] .nil .nil))) (.node [v565, v732, v852, v905, v914, v1045] (.node [v565, v732, v852, v904, v1045, v1568] (.node [v565, v732, v852, v904, v1045, v1515] .nil .nil) (.node [v565, v732, v852, v904, v1109, v1515] .nil .nil)) (.node [v565, v732, v852, v905, v1045, v1569] (.node [v565, v732, v852, v905, v1045, v1515] .nil .nil) (.node [v565, v732, v852, v905, v1110, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrrl_ok : everyKey (rowOK 4 level4) level5rllrrl = true := by decide +kernel
def level5rllrrr : BinaryTree (List W) := (.node [v565, v732, v852, v926, v1045, v1315] (.node [v565, v732, v852, v914, v1045, v1315] (.node [v565, v732, v852, v912, v1045, v1315] (.node [v565, v732, v852, v910, v1045, v1315] (.node [v565, v732, v852, v908, v1045, v1315] (.node [v565, v732, v852, v907, v1045, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v911, v1045, v1315] .nil .nil)) (.node [v565, v732, v852, v913, v1045, v1377] (.node [v565, v732, v852, v913, v1045, v1315] .nil .nil) (.node [v565, v732, v852, v913, v1109, v1315] .nil .nil))) (.node [v565, v732, v852, v922, v1045, v1315] (.node [v565, v732, v852, v914, v1110, v1315] (.node [v565, v732, v852, v914, v1045, v1378] .nil .nil) (.node [v565, v732, v852, v921, v1045, v1315] .nil .nil)) (.node [v565, v732, v852, v924, v1045, v1515] (.node [v565, v732, v852, v923, v1045, v1515] .nil .nil) (.node [v565, v732, v852, v925, v1045, v1315] .nil .nil)))) (.node [v565, v732, v852, v949, v1161, v1515] (.node [v565, v732, v852, v949, v1045, v1604] (.node [v565, v732, v852, v946, v1492, v1515] (.node [v565, v732, v852, v946, v1315, v1642] (.node [v565, v732, v852, v946, v1045, v1648] .nil .nil) .nil) (.node [v565, v732, v852, v949, v1045, v1557] .nil .nil)) (.node [v565, v732, v852, v949, v1045, v1631] (.node [v565, v732, v852, v949, v1045, v1617] .nil .nil) (.node [v565, v732, v852, v949, v1069, v1515] .nil .nil))) (.node [v565, v732, v852, v949, v1315, v1598] (.node [v565, v732, v852, v949, v1238, v1515] (.node [v565, v732, v852, v949, v1198, v1515] .nil .nil) (.node [v565, v732, v852, v949, v1315, v1539] .nil .nil)) (.node [v565, v732, v852, v949, v1315, v1626] (.node [v565, v732, v852, v949, v1315, v1612] .nil .nil) (.node [v565, v732, v852, v949, v1339, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrrr_ok : everyKey (rowOK 4 level4) level5rllrrr = true := by decide +kernel
def level5rllrr : BinaryTree (List W) := .node [v565, v732, v852, v906, v1045, v1515] level5rllrrl level5rllrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrr_ok : everyKey (rowOK 4 level4) level5rllrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rllrrl && everyKey (rowOK 4 level4) level5rllrrr) = true
  rw [level5rllrrl_ok, level5rllrrr_ok]
  decide +kernel
def level5rllr : BinaryTree (List W) := .node [v565, v732, v852, v878, v1315, v1515] level5rllrl level5rllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllr_ok : everyKey (rowOK 4 level4) level5rllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rllrl && everyKey (rowOK 4 level4) level5rllrr) = true
  rw [level5rllrl_ok, level5rllrr_ok]
  decide +kernel
def level5rll : BinaryTree (List W) := .node [v565, v732, v821, v852, v986, v1515] level5rlll level5rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rll_ok : everyKey (rowOK 4 level4) level5rll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlll && everyKey (rowOK 4 level4) level5rllr) = true
  rw [level5rlll_ok, level5rllr_ok]
  decide +kernel
def level5rlrlll : BinaryTree (List W) := (.node [v565, v732, v852, v957, v1045, v1515] (.node [v565, v732, v852, v953, v1315, v1515] (.node [v565, v732, v852, v949, v1515, v1652] (.node [v565, v732, v852, v949, v1492, v1515] (.node [v565, v732, v852, v949, v1462, v1515] (.node [v565, v732, v852, v949, v1436, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v949, v1493, v1515] .nil .nil)) (.node [v565, v732, v852, v951, v1315, v1515] (.node [v565, v732, v852, v950, v1315, v1515] .nil .nil) (.node [v565, v732, v852, v952, v1315, v1515] .nil .nil))) (.node [v565, v732, v852, v953, v1515, v1648] (.node [v565, v732, v852, v953, v1407, v1515] (.node [v565, v732, v852, v953, v1339, v1515] .nil .nil) (.node [v565, v732, v852, v953, v1492, v1515] .nil .nil)) (.node [v565, v732, v852, v955, v1045, v1515] (.node [v565, v732, v852, v954, v1045, v1515] .nil .nil) (.node [v565, v732, v852, v956, v1045, v1515] .nil .nil)))) (.node [v565, v732, v852, v969, v1315, v1515] (.node [v565, v732, v852, v963, v1315, v1515] (.node [v565, v732, v852, v957, v1492, v1515] (.node [v565, v732, v852, v957, v1144, v1515] (.node [v565, v732, v852, v957, v1069, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v957, v1515, v1642] .nil .nil)) (.node [v565, v732, v852, v967, v1315, v1515] (.node [v565, v732, v852, v965, v1315, v1515] .nil .nil) (.node [v565, v732, v852, v968, v1315, v1515] .nil .nil))) (.node [v565, v732, v852, v972, v1315, v1515] (.node [v565, v732, v852, v971, v1315, v1515] (.node [v565, v732, v852, v970, v1315, v1515] .nil .nil) (.node [v565, v732, v852, v972, v1315, v1419] .nil .nil)) (.node [v565, v732, v852, v972, v1407, v1515] (.node [v565, v732, v852, v972, v1315, v1533] .nil .nil) (.node [v565, v732, v852, v972, v1413, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrlll_ok : everyKey (rowOK 4 level4) level5rlrlll = true := by decide +kernel
def level5rlrllr : BinaryTree (List W) := (.node [v565, v732, v852, v985, v1315, v1515] (.node [v565, v732, v852, v977, v1492, v1515] (.node [v565, v732, v852, v977, v1315, v1442] (.node [v565, v732, v852, v975, v1315, v1515] (.node [v565, v732, v852, v973, v1315, v1515] (.node [v565, v732, v852, v972, v1515, v1648] .nil .nil) .nil) (.node [v565, v732, v852, v976, v1315, v1515] .nil .nil)) (.node [v565, v732, v852, v977, v1407, v1515] (.node [v565, v732, v852, v977, v1315, v1515] .nil .nil) (.node [v565, v732, v852, v977, v1436, v1515] .nil .nil))) (.node [v565, v732, v852, v980, v1315, v1515] (.node [v565, v732, v852, v978, v1315, v1515] (.node [v565, v732, v852, v977, v1515, v1648] .nil .nil) (.node [v565, v732, v852, v979, v1315, v1515] .nil .nil)) (.node [v565, v732, v852, v983, v1045, v1515] (.node [v565, v732, v852, v981, v1315, v1515] .nil .nil) (.node [v565, v732, v852, v984, v1315, v1515] .nil .nil)))) (.node [v565, v732, v852, v989, v1315, v1515] (.node [v565, v732, v852, v986, v1492, v1515] (.node [v565, v732, v852, v986, v1407, v1515] (.node [v565, v732, v852, v986, v1315, v1515] (.node [v565, v732, v852, v986, v1315, v1468] .nil .nil) .nil) (.node [v565, v732, v852, v986, v1462, v1515] .nil .nil)) (.node [v565, v732, v852, v987, v1315, v1515] (.node [v565, v732, v852, v986, v1515, v1648] .nil .nil) (.node [v565, v732, v852, v988, v1315, v1515] .nil .nil))) (.node [v565, v732, v852, v993, v1045, v1427] (.node [v565, v732, v852, v992, v1045, v1515] (.node [v565, v732, v852, v990, v1315, v1515] .nil .nil) (.node [v565, v732, v852, v993, v1045, v1365] .nil .nil)) (.node [v565, v732, v852, v993, v1045, v1478] (.node [v565, v732, v852, v993, v1045, v1452] .nil .nil) (.node [v565, v732, v852, v993, v1095, v1315] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrllr_ok : everyKey (rowOK 4 level4) level5rlrllr = true := by decide +kernel
def level5rlrll : BinaryTree (List W) := .node [v565, v732, v852, v972, v1492, v1515] level5rlrlll level5rlrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrll_ok : everyKey (rowOK 4 level4) level5rlrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrlll && everyKey (rowOK 4 level4) level5rlrllr) = true
  rw [level5rlrlll_ok, level5rlrllr_ok]
  decide +kernel
def level5rlrlrl : BinaryTree (List W) := (.node [v565, v732, v852, v997, v1315, v1515] (.node [v565, v732, v852, v993, v1315, v1652] (.node [v565, v732, v852, v993, v1315, v1612] (.node [v565, v732, v852, v993, v1315, v1539] (.node [v565, v732, v852, v993, v1254, v1315] (.node [v565, v732, v852, v993, v1214, v1315] .nil .nil) .nil) (.node [v565, v732, v852, v993, v1315, v1598] .nil .nil)) (.node [v565, v732, v852, v993, v1315, v1642] (.node [v565, v732, v852, v993, v1315, v1626] .nil .nil) (.node [v565, v732, v852, v993, v1315, v1643] .nil .nil))) (.node [v565, v732, v852, v993, v1462, v1515] (.node [v565, v732, v852, v993, v1413, v1515] (.node [v565, v732, v852, v993, v1339, v1515] .nil .nil) (.node [v565, v732, v852, v993, v1436, v1515] .nil .nil)) (.node [v565, v732, v852, v995, v1315, v1515] (.node [v565, v732, v852, v994, v1315, v1515] .nil .nil) (.node [v565, v732, v852, v996, v1315, v1515] .nil .nil)))) (.node [v565, v732, v852, v1007, v1315, v1515] (.node [v565, v732, v852, v1001, v1315, v1515] (.node [v565, v732, v852, v997, v1315, v1642] (.node [v565, v732, v852, v997, v1315, v1593] (.node [v565, v732, v852, v997, v1315, v1539] .nil .nil) .nil) (.node [v565, v732, v852, v997, v1315, v1648] .nil .nil)) (.node [v565, v732, v852, v1005, v1315, v1515] (.node [v565, v732, v852, v1003, v1315, v1515] .nil .nil) (.node [v565, v732, v852, v1006, v1315, v1515] .nil .nil))) (.node [v565, v732, v852, v1009, v1315, v1593] (.node [v565, v732, v852, v1009, v1279, v1515] (.node [v565, v732, v852, v1008, v1315, v1515] .nil .nil) (.node [v565, v732, v852, v1009, v1315, v1515] .nil .nil)) (.node [v565, v732, v852, v1009, v1315, v1642] (.node [v565, v732, v852, v1009, v1315, v1598] .nil .nil) (.node [v565, v732, v852, v1009, v1315, v1648] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrlrl_ok : everyKey (rowOK 4 level4) level5rlrlrl = true := by decide +kernel
def level5rlrlrr : BinaryTree (List W) := (.node [v565, v732, v852, v1019, v1315, v1593] (.node [v565, v732, v852, v1013, v1315, v1515] (.node [v565, v732, v852, v1012, v1315, v1593] (.node [v565, v732, v852, v1012, v1282, v1515] (.node [v565, v732, v852, v1011, v1315, v1515] (.node [v565, v732, v852, v1010, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1012, v1315, v1515] .nil .nil)) (.node [v565, v732, v852, v1012, v1315, v1642] (.node [v565, v732, v852, v1012, v1315, v1612] .nil .nil) (.node [v565, v732, v852, v1012, v1315, v1648] .nil .nil))) (.node [v565, v732, v852, v1017, v1045, v1315] (.node [v565, v732, v852, v1015, v1315, v1515] (.node [v565, v732, v852, v1014, v1315, v1515] .nil .nil) (.node [v565, v732, v852, v1016, v1315, v1515] .nil .nil)) (.node [v565, v732, v852, v1019, v1289, v1515] (.node [v565, v732, v852, v1018, v1315, v1515] .nil .nil) (.node [v565, v732, v852, v1019, v1315, v1515] .nil .nil)))) (.node [v565, v732, v852, v1026, v1315, v1515] (.node [v565, v732, v852, v1021, v1315, v1515] (.node [v565, v732, v852, v1019, v1315, v1648] (.node [v565, v732, v852, v1019, v1315, v1642] (.node [v565, v732, v852, v1019, v1315, v1626] .nil .nil) .nil) (.node [v565, v732, v852, v1020, v1315, v1515] .nil .nil)) (.node [v565, v732, v852, v1023, v1315, v1515] (.node [v565, v732, v852, v1022, v1315, v1515] .nil .nil) (.node [v565, v732, v852, v1024, v1045, v1315] .nil .nil))) (.node [v565, v732, v852, v1030, v1300, v1515] (.node [v565, v732, v852, v1028, v1315, v1515] (.node [v565, v732, v852, v1027, v1315, v1515] .nil .nil) (.node [v565, v732, v852, v1029, v1315, v1515] .nil .nil)) (.node [v565, v732, v852, v1030, v1315, v1515] (.node [v565, v732, v852, v1030, v1315, v1500] .nil .nil) (.node [v565, v732, v852, v1031, v1315, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrlrr_ok : everyKey (rowOK 4 level4) level5rlrlrr = true := by decide +kernel
def level5rlrlr : BinaryTree (List W) := .node [v565, v732, v852, v1009, v1333, v1515] level5rlrlrl level5rlrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrlr_ok : everyKey (rowOK 4 level4) level5rlrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrlrl && everyKey (rowOK 4 level4) level5rlrlrr) = true
  rw [level5rlrlrl_ok, level5rlrlrr_ok]
  decide +kernel
def level5rlrl : BinaryTree (List W) := .node [v565, v732, v852, v993, v1175, v1315] level5rlrll level5rlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrl_ok : everyKey (rowOK 4 level4) level5rlrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrll && everyKey (rowOK 4 level4) level5rlrlr) = true
  rw [level5rlrll_ok, level5rlrlr_ok]
  decide +kernel
def level5rlrrll : BinaryTree (List W) := (.node [v565, v732, v852, v1045, v1087, v1315] (.node [v565, v732, v852, v1039, v1315, v1515] (.node [v565, v732, v852, v1035, v1315, v1515] (.node [v565, v732, v852, v1034, v1315, v1504] (.node [v565, v732, v852, v1034, v1304, v1515] (.node [v565, v732, v852, v1033, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1034, v1315, v1515] .nil .nil)) (.node [v565, v732, v852, v1037, v1315, v1515] (.node [v565, v732, v852, v1036, v1315, v1515] .nil .nil) (.node [v565, v732, v852, v1038, v1315, v1515] .nil .nil))) (.node [v565, v732, v852, v1043, v1315, v1515] (.node [v565, v732, v852, v1041, v1315, v1515] (.node [v565, v732, v852, v1040, v1315, v1515] .nil .nil) (.node [v565, v732, v852, v1042, v1315, v1515] .nil .nil)) (.node [v565, v732, v852, v1045, v1082, v1315] (.node [v565, v732, v852, v1044, v1315, v1515] .nil .nil) (.node [v565, v732, v852, v1045, v1084, v1315] .nil .nil)))) (.node [v565, v732, v852, v1045, v1147, v1515] (.node [v565, v732, v852, v1045, v1131, v1315] (.node [v565, v732, v852, v1045, v1114, v1315] (.node [v565, v732, v852, v1045, v1099, v1515] (.node [v565, v732, v852, v1045, v1090, v1315] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1116, v1515] .nil .nil)) (.node [v565, v732, v852, v1045, v1145, v1315] (.node [v565, v732, v852, v1045, v1133, v1515] .nil .nil) (.node [v565, v732, v852, v1045, v1146, v1515] .nil .nil))) (.node [v565, v732, v852, v1045, v1150, v1515] (.node [v565, v732, v852, v1045, v1149, v1515] (.node [v565, v732, v852, v1045, v1148, v1515] .nil .nil) (.node [v565, v732, v852, v1045, v1150, v1167] .nil .nil)) (.node [v565, v732, v852, v1045, v1152, v1515] (.node [v565, v732, v852, v1045, v1150, v1550] .nil .nil) (.node [v565, v732, v852, v1045, v1154, v1315] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrll_ok : everyKey (rowOK 4 level4) level5rlrrll = true := by decide +kernel
def level5rlrrlr : BinaryTree (List W) := (.node [v565, v732, v852, v1045, v1205, v1315] (.node [v565, v732, v852, v1045, v1185, v1515] (.node [v565, v732, v852, v1045, v1181, v1315] (.node [v565, v732, v852, v1045, v1167, v1315] (.node [v565, v732, v852, v1045, v1166, v1315] (.node [v565, v732, v852, v1045, v1165, v1315] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1167, v1350] .nil .nil)) (.node [v565, v732, v852, v1045, v1184, v1515] (.node [v565, v732, v852, v1045, v1183, v1515] .nil .nil) (.node [v565, v732, v852, v1045, v1185, v1204] .nil .nil))) (.node [v565, v732, v852, v1045, v1190, v1515] (.node [v565, v732, v852, v1045, v1187, v1515] (.node [v565, v732, v852, v1045, v1186, v1515] .nil .nil) (.node [v565, v732, v852, v1045, v1188, v1515] .nil .nil)) (.node [v565, v732, v852, v1045, v1203, v1315] (.node [v565, v732, v852, v1045, v1194, v1315] .nil .nil) (.node [v565, v732, v852, v1045, v1204, v1315] .nil .nil)))) (.node [v565, v732, v852, v1045, v1227, v1515] (.node [v565, v732, v852, v1045, v1224, v1515] (.node [v565, v732, v852, v1045, v1221, v1315] (.node [v565, v732, v852, v1045, v1207, v1315] (.node [v565, v732, v852, v1045, v1206, v1315] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1223, v1515] .nil .nil)) (.node [v565, v732, v852, v1045, v1225, v1515] (.node [v565, v732, v852, v1045, v1225, v1244] .nil .nil) (.node [v565, v732, v852, v1045, v1226, v1515] .nil .nil))) (.node [v565, v732, v852, v1045, v1243, v1315] (.node [v565, v732, v852, v1045, v1230, v1515] (.node [v565, v732, v852, v1045, v1228, v1515] .nil .nil) (.node [v565, v732, v852, v1045, v1235, v1315] .nil .nil)) (.node [v565, v732, v852, v1045, v1245, v1315] (.node [v565, v732, v852, v1045, v1244, v1315] .nil .nil) (.node [v565, v732, v852, v1045, v1246, v1315] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrlr_ok : everyKey (rowOK 4 level4) level5rlrrlr = true := by decide +kernel
def level5rlrrl : BinaryTree (List W) := .node [v565, v732, v852, v1045, v1164, v1315] level5rlrrll level5rlrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrl_ok : everyKey (rowOK 4 level4) level5rlrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrrll && everyKey (rowOK 4 level4) level5rlrrlr) = true
  rw [level5rlrrll_ok, level5rlrrlr_ok]
  decide +kernel
def level5rlrrrl : BinaryTree (List W) := (.node [v565, v732, v852, v1045, v1269, v1557] (.node [v565, v732, v852, v1045, v1263, v1631] (.node [v565, v732, v852, v1045, v1263, v1478] (.node [v565, v732, v852, v1045, v1263, v1427] (.node [v565, v732, v852, v1045, v1263, v1365] (.node [v565, v732, v852, v1045, v1261, v1315] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1263, v1452] .nil .nil)) (.node [v565, v732, v852, v1045, v1263, v1604] (.node [v565, v732, v852, v1045, v1263, v1557] .nil .nil) (.node [v565, v732, v852, v1045, v1263, v1617] .nil .nil))) (.node [v565, v732, v852, v1045, v1266, v1515] (.node [v565, v732, v852, v1045, v1263, v1649] (.node [v565, v732, v852, v1045, v1263, v1648] .nil .nil) (.node [v565, v732, v852, v1045, v1263, v1652] .nil .nil)) (.node [v565, v732, v852, v1045, v1268, v1515] (.node [v565, v732, v852, v1045, v1267, v1515] .nil .nil) (.node [v565, v732, v852, v1045, v1269, v1515] .nil .nil)))) (.node [v565, v732, v852, v1045, v1278, v1515] (.node [v565, v732, v852, v1045, v1273, v1515] (.node [v565, v732, v852, v1045, v1269, v1648] (.node [v565, v732, v852, v1045, v1269, v1642] (.node [v565, v732, v852, v1045, v1269, v1593] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1271, v1515] .nil .nil)) (.node [v565, v732, v852, v1045, v1276, v1515] (.node [v565, v732, v852, v1045, v1275, v1515] .nil .nil) (.node [v565, v732, v852, v1045, v1277, v1515] .nil .nil))) (.node [v565, v732, v852, v1045, v1279, v1642] (.node [v565, v732, v852, v1045, v1279, v1593] (.node [v565, v732, v852, v1045, v1279, v1515] .nil .nil) (.node [v565, v732, v852, v1045, v1279, v1604] .nil .nil)) (.node [v565, v732, v852, v1045, v1280, v1515] (.node [v565, v732, v852, v1045, v1279, v1648] .nil .nil) (.node [v565, v732, v852, v1045, v1281, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrrl_ok : everyKey (rowOK 4 level4) level5rlrrrl = true := by decide +kernel
def level5rlrrrr : BinaryTree (List W) := (.node [v565, v732, v852, v1045, v1291, v1515] (.node [v565, v732, v852, v1045, v1287, v1515] (.node [v565, v732, v852, v1045, v1283, v1515] (.node [v565, v732, v852, v1045, v1282, v1642] (.node [v565, v732, v852, v1045, v1282, v1617] (.node [v565, v732, v852, v1045, v1282, v1593] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1282, v1648] .nil .nil)) (.node [v565, v732, v852, v1045, v1285, v1515] (.node [v565, v732, v852, v1045, v1284, v1515] .nil .nil) (.node [v565, v732, v852, v1045, v1286, v1315] .nil .nil))) (.node [v565, v732, v852, v1045, v1289, v1631] (.node [v565, v732, v852, v1045, v1289, v1515] (.node [v565, v732, v852, v1045, v1288, v1515] .nil .nil) (.node [v565, v732, v852, v1045, v1289, v1593] .nil .nil)) (.node [v565, v732, v852, v1045, v1289, v1648] (.node [v565, v732, v852, v1045, v1289, v1642] .nil .nil) (.node [v565, v732, v852, v1045, v1290, v1515] .nil .nil)))) (.node [v565, v732, v852, v1045, v1300, v1515] (.node [v565, v732, v852, v1045, v1297, v1515] (.node [v565, v732, v852, v1045, v1294, v1515] (.node [v565, v732, v852, v1045, v1293, v1315] (.node [v565, v732, v852, v1045, v1292, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1296, v1515] .nil .nil)) (.node [v565, v732, v852, v1045, v1299, v1515] (.node [v565, v732, v852, v1045, v1298, v1515] .nil .nil) (.node [v565, v732, v852, v1045, v1300, v1500] .nil .nil))) (.node [v565, v732, v852, v1045, v1304, v1504] (.node [v565, v732, v852, v1045, v1302, v1515] (.node [v565, v732, v852, v1045, v1301, v1515] .nil .nil) (.node [v565, v732, v852, v1045, v1303, v1515] .nil .nil)) (.node [v565, v732, v852, v1045, v1305, v1515] (.node [v565, v732, v852, v1045, v1304, v1515] .nil .nil) (.node [v565, v732, v852, v1045, v1306, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrrr_ok : everyKey (rowOK 4 level4) level5rlrrrr = true := by decide +kernel
def level5rlrrr : BinaryTree (List W) := .node [v565, v732, v852, v1045, v1282, v1515] level5rlrrrl level5rlrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrr_ok : everyKey (rowOK 4 level4) level5rlrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrrrl && everyKey (rowOK 4 level4) level5rlrrrr) = true
  rw [level5rlrrrl_ok, level5rlrrrr_ok]
  decide +kernel
def level5rlrr : BinaryTree (List W) := .node [v565, v732, v852, v1045, v1247, v1315] level5rlrrl level5rlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrr_ok : everyKey (rowOK 4 level4) level5rlrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrrl && everyKey (rowOK 4 level4) level5rlrrr) = true
  rw [level5rlrrl_ok, level5rlrrr_ok]
  decide +kernel
def level5rlr : BinaryTree (List W) := .node [v565, v732, v852, v1032, v1315, v1515] level5rlrl level5rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlr_ok : everyKey (rowOK 4 level4) level5rlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrl && everyKey (rowOK 4 level4) level5rlrr) = true
  rw [level5rlrl_ok, level5rlrr_ok]
  decide +kernel
def level5rl : BinaryTree (List W) := .node [v565, v732, v852, v949, v1413, v1515] level5rll level5rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rl_ok : everyKey (rowOK 4 level4) level5rl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rll && everyKey (rowOK 4 level4) level5rlr) = true
  rw [level5rll_ok, level5rlr_ok]
  decide +kernel
def level5rrllll : BinaryTree (List W) := (.node [v565, v732, v852, v1045, v1315, v1418] (.node [v565, v732, v852, v1045, v1315, v1354] (.node [v565, v732, v852, v1045, v1312, v1515] (.node [v565, v732, v852, v1045, v1310, v1515] (.node [v565, v732, v852, v1045, v1309, v1515] (.node [v565, v732, v852, v1045, v1308, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1311, v1515] .nil .nil)) (.node [v565, v732, v852, v1045, v1314, v1515] (.node [v565, v732, v852, v1045, v1313, v1515] .nil .nil) (.node [v565, v732, v852, v1045, v1315, v1352] .nil .nil))) (.node [v565, v732, v852, v1045, v1315, v1397] (.node [v565, v732, v852, v1045, v1315, v1360] (.node [v565, v732, v852, v1045, v1315, v1357] .nil .nil) (.node [v565, v732, v852, v1045, v1315, v1382] .nil .nil)) (.node [v565, v732, v852, v1045, v1315, v1416] (.node [v565, v732, v852, v1045, v1315, v1408] .nil .nil) (.node [v565, v732, v852, v1045, v1315, v1417] .nil .nil)))) (.node [v565, v732, v852, v1045, v1315, v1467] (.node [v565, v732, v852, v1045, v1315, v1443] (.node [v565, v732, v852, v1045, v1315, v1441] (.node [v565, v732, v852, v1045, v1315, v1433] (.node [v565, v732, v852, v1045, v1315, v1419] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1315, v1442] .nil .nil)) (.node [v565, v732, v852, v1045, v1315, v1445] (.node [v565, v732, v852, v1045, v1315, v1444] .nil .nil) (.node [v565, v732, v852, v1045, v1315, v1459] .nil .nil))) (.node [v565, v732, v852, v1045, v1315, v1471] (.node [v565, v732, v852, v1045, v1315, v1469] (.node [v565, v732, v852, v1045, v1315, v1468] .nil .nil) (.node [v565, v732, v852, v1045, v1315, v1470] .nil .nil)) (.node [v565, v732, v852, v1045, v1315, v1494] (.node [v565, v732, v852, v1045, v1315, v1485] .nil .nil) (.node [v565, v732, v852, v1045, v1315, v1495] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrllll_ok : everyKey (rowOK 4 level4) level5rrllll = true := by decide +kernel
def level5rrlllr : BinaryTree (List W) := (.node [v565, v732, v852, v1045, v1315, v1515] (.node [v565, v732, v852, v1045, v1315, v1507] (.node [v565, v732, v852, v1045, v1315, v1503] (.node [v565, v732, v852, v1045, v1315, v1501] (.node [v565, v732, v852, v1045, v1315, v1500] (.node [v565, v732, v852, v1045, v1315, v1499] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1315, v1502] .nil .nil)) (.node [v565, v732, v852, v1045, v1315, v1505] (.node [v565, v732, v852, v1045, v1315, v1504] .nil .nil) (.node [v565, v732, v852, v1045, v1315, v1506] .nil .nil))) (.node [v565, v732, v852, v1045, v1315, v1511] (.node [v565, v732, v852, v1045, v1315, v1509] (.node [v565, v732, v852, v1045, v1315, v1508] .nil .nil) (.node [v565, v732, v852, v1045, v1315, v1510] .nil .nil)) (.node [v565, v732, v852, v1045, v1315, v1513] (.node [v565, v732, v852, v1045, v1315, v1512] .nil .nil) (.node [v565, v732, v852, v1045, v1315, v1514] .nil .nil)))) (.node [v565, v732, v852, v1045, v1315, v1524] (.node [v565, v732, v852, v1045, v1315, v1520] (.node [v565, v732, v852, v1045, v1315, v1518] (.node [v565, v732, v852, v1045, v1315, v1517] (.node [v565, v732, v852, v1045, v1315, v1516] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1315, v1519] .nil .nil)) (.node [v565, v732, v852, v1045, v1315, v1522] (.node [v565, v732, v852, v1045, v1315, v1521] .nil .nil) (.node [v565, v732, v852, v1045, v1315, v1523] .nil .nil))) (.node [v565, v732, v852, v1045, v1315, v1528] (.node [v565, v732, v852, v1045, v1315, v1526] (.node [v565, v732, v852, v1045, v1315, v1525] .nil .nil) (.node [v565, v732, v852, v1045, v1315, v1527] .nil .nil)) (.node [v565, v732, v852, v1045, v1315, v1530] (.node [v565, v732, v852, v1045, v1315, v1529] .nil .nil) (.node [v565, v732, v852, v1045, v1315, v1531] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlllr_ok : everyKey (rowOK 4 level4) level5rrlllr = true := by decide +kernel
def level5rrlll : BinaryTree (List W) := .node [v565, v732, v852, v1045, v1315, v1497] level5rrllll level5rrlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlll_ok : everyKey (rowOK 4 level4) level5rrlll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrllll && everyKey (rowOK 4 level4) level5rrlllr) = true
  rw [level5rrllll_ok, level5rrlllr_ok]
  decide +kernel
def level5rrllrl : BinaryTree (List W) := (.node [v565, v732, v852, v1045, v1315, v1551] (.node [v565, v732, v852, v1045, v1315, v1543] (.node [v565, v732, v852, v1045, v1315, v1539] (.node [v565, v732, v852, v1045, v1315, v1535] (.node [v565, v732, v852, v1045, v1315, v1534] (.node [v565, v732, v852, v1045, v1315, v1533] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1315, v1537] .nil .nil)) (.node [v565, v732, v852, v1045, v1315, v1541] (.node [v565, v732, v852, v1045, v1315, v1540] .nil .nil) (.node [v565, v732, v852, v1045, v1315, v1542] .nil .nil))) (.node [v565, v732, v852, v1045, v1315, v1547] (.node [v565, v732, v852, v1045, v1315, v1545] (.node [v565, v732, v852, v1045, v1315, v1544] .nil .nil) (.node [v565, v732, v852, v1045, v1315, v1546] .nil .nil)) (.node [v565, v732, v852, v1045, v1315, v1549] (.node [v565, v732, v852, v1045, v1315, v1548] .nil .nil) (.node [v565, v732, v852, v1045, v1315, v1550] .nil .nil)))) (.node [v565, v732, v852, v1045, v1315, v1564] (.node [v565, v732, v852, v1045, v1315, v1558] (.node [v565, v732, v852, v1045, v1315, v1555] (.node [v565, v732, v852, v1045, v1315, v1553] (.node [v565, v732, v852, v1045, v1315, v1552] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1315, v1557] .nil .nil)) (.node [v565, v732, v852, v1045, v1315, v1561] (.node [v565, v732, v852, v1045, v1315, v1560] .nil .nil) (.node [v565, v732, v852, v1045, v1315, v1563] .nil .nil))) (.node [v565, v732, v852, v1045, v1315, v1570] (.node [v565, v732, v852, v1045, v1315, v1568] (.node [v565, v732, v852, v1045, v1315, v1566] .nil .nil) (.node [v565, v732, v852, v1045, v1315, v1569] .nil .nil)) (.node [v565, v732, v852, v1045, v1315, v1572] (.node [v565, v732, v852, v1045, v1315, v1571] .nil .nil) (.node [v565, v732, v852, v1045, v1315, v1573] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrllrl_ok : everyKey (rowOK 4 level4) level5rrllrl = true := by decide +kernel
def level5rrllrr : BinaryTree (List W) := (.node [v565, v732, v852, v1045, v1315, v1602] (.node [v565, v732, v852, v1045, v1315, v1592] (.node [v565, v732, v852, v1045, v1315, v1582] (.node [v565, v732, v852, v1045, v1315, v1579] (.node [v565, v732, v852, v1045, v1315, v1577] (.node [v565, v732, v852, v1045, v1315, v1576] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1315, v1581] .nil .nil)) (.node [v565, v732, v852, v1045, v1315, v1584] (.node [v565, v732, v852, v1045, v1315, v1583] .nil .nil) (.node [v565, v732, v852, v1045, v1315, v1585] .nil .nil))) (.node [v565, v732, v852, v1045, v1315, v1597] (.node [v565, v732, v852, v1045, v1315, v1595] (.node [v565, v732, v852, v1045, v1315, v1594] .nil .nil) (.node [v565, v732, v852, v1045, v1315, v1596] .nil .nil)) (.node [v565, v732, v852, v1045, v1315, v1599] (.node [v565, v732, v852, v1045, v1315, v1598] .nil .nil) (.node [v565, v732, v852, v1045, v1315, v1601] .nil .nil)))) (.node [v565, v732, v852, v1045, v1315, v1615] (.node [v565, v732, v852, v1045, v1315, v1611] (.node [v565, v732, v852, v1045, v1315, v1608] (.node [v565, v732, v852, v1045, v1315, v1604] (.node [v565, v732, v852, v1045, v1315, v1603] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1315, v1610] .nil .nil)) (.node [v565, v732, v852, v1045, v1315, v1613] (.node [v565, v732, v852, v1045, v1315, v1612] .nil .nil) (.node [v565, v732, v852, v1045, v1315, v1614] .nil .nil))) (.node [v565, v732, v852, v1045, v1315, v1619] (.node [v565, v732, v852, v1045, v1315, v1617] (.node [v565, v732, v852, v1045, v1315, v1616] .nil .nil) (.node [v565, v732, v852, v1045, v1315, v1618] .nil .nil)) (.node [v565, v732, v852, v1045, v1315, v1621] (.node [v565, v732, v852, v1045, v1315, v1620] .nil .nil) (.node [v565, v732, v852, v1045, v1315, v1624] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrllrr_ok : everyKey (rowOK 4 level4) level5rrllrr = true := by decide +kernel
def level5rrllr : BinaryTree (List W) := .node [v565, v732, v852, v1045, v1315, v1574] level5rrllrl level5rrllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrllr_ok : everyKey (rowOK 4 level4) level5rrllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrllrl && everyKey (rowOK 4 level4) level5rrllrr) = true
  rw [level5rrllrl_ok, level5rrllrr_ok]
  decide +kernel
def level5rrll : BinaryTree (List W) := .node [v565, v732, v852, v1045, v1315, v1532] level5rrlll level5rrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrll_ok : everyKey (rowOK 4 level4) level5rrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrlll && everyKey (rowOK 4 level4) level5rrllr) = true
  rw [level5rrlll_ok, level5rrllr_ok]
  decide +kernel
def level5rrlrll : BinaryTree (List W) := (.node [v565, v732, v852, v1045, v1319, v1515] (.node [v565, v732, v852, v1045, v1315, v1634] (.node [v565, v732, v852, v1045, v1315, v1630] (.node [v565, v732, v852, v1045, v1315, v1628] (.node [v565, v732, v852, v1045, v1315, v1627] (.node [v565, v732, v852, v1045, v1315, v1626] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1315, v1629] .nil .nil)) (.node [v565, v732, v852, v1045, v1315, v1632] (.node [v565, v732, v852, v1045, v1315, v1631] .nil .nil) (.node [v565, v732, v852, v1045, v1315, v1633] .nil .nil))) (.node [v565, v732, v852, v1045, v1315, v1647] (.node [v565, v732, v852, v1045, v1315, v1638] (.node [v565, v732, v852, v1045, v1315, v1635] .nil .nil) (.node [v565, v732, v852, v1045, v1315, v1641] .nil .nil)) (.node [v565, v732, v852, v1045, v1317, v1515] (.node [v565, v732, v852, v1045, v1316, v1515] .nil .nil) (.node [v565, v732, v852, v1045, v1318, v1515] .nil .nil)))) (.node [v565, v732, v852, v1045, v1328, v1515] (.node [v565, v732, v852, v1045, v1324, v1515] (.node [v565, v732, v852, v1045, v1322, v1515] (.node [v565, v732, v852, v1045, v1321, v1515] (.node [v565, v732, v852, v1045, v1320, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1323, v1515] .nil .nil)) (.node [v565, v732, v852, v1045, v1326, v1515] (.node [v565, v732, v852, v1045, v1325, v1515] .nil .nil) (.node [v565, v732, v852, v1045, v1327, v1515] .nil .nil))) (.node [v565, v732, v852, v1045, v1332, v1515] (.node [v565, v732, v852, v1045, v1330, v1515] (.node [v565, v732, v852, v1045, v1329, v1515] .nil .nil) (.node [v565, v732, v852, v1045, v1331, v1515] .nil .nil)) (.node [v565, v732, v852, v1045, v1334, v1515] (.node [v565, v732, v852, v1045, v1333, v1515] .nil .nil) (.node [v565, v732, v852, v1045, v1335, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrll_ok : everyKey (rowOK 4 level4) level5rrlrll = true := by decide +kernel
def level5rrlrlr : BinaryTree (List W) := (.node [v565, v732, v852, v1045, v1358, v1515] (.node [v565, v732, v852, v1045, v1347, v1515] (.node [v565, v732, v852, v1045, v1343, v1515] (.node [v565, v732, v852, v1045, v1341, v1515] (.node [v565, v732, v852, v1045, v1340, v1515] (.node [v565, v732, v852, v1045, v1339, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1342, v1515] .nil .nil)) (.node [v565, v732, v852, v1045, v1345, v1515] (.node [v565, v732, v852, v1045, v1344, v1515] .nil .nil) (.node [v565, v732, v852, v1045, v1346, v1515] .nil .nil))) (.node [v565, v732, v852, v1045, v1350, v1550] (.node [v565, v732, v852, v1045, v1349, v1515] (.node [v565, v732, v852, v1045, v1348, v1515] .nil .nil) (.node [v565, v732, v852, v1045, v1350, v1515] .nil .nil)) (.node [v565, v732, v852, v1045, v1353, v1515] (.node [v565, v732, v852, v1045, v1351, v1515] .nil .nil) (.node [v565, v732, v852, v1045, v1355, v1515] .nil .nil)))) (.node [v565, v732, v852, v1045, v1368, v1515] (.node [v565, v732, v852, v1045, v1365, v1515] (.node [v565, v732, v852, v1045, v1360, v1492] (.node [v565, v732, v852, v1045, v1360, v1407] (.node [v565, v732, v852, v1045, v1360, v1365] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1360, v1648] .nil .nil)) (.node [v565, v732, v852, v1045, v1365, v1637] (.node [v565, v732, v852, v1045, v1365, v1623] .nil .nil) (.node [v565, v732, v852, v1045, v1366, v1515] .nil .nil))) (.node [v565, v732, v852, v1045, v1375, v1515] (.node [v565, v732, v852, v1045, v1372, v1515] (.node [v565, v732, v852, v1045, v1369, v1515] .nil .nil) (.node [v565, v732, v852, v1045, v1373, v1515] .nil .nil)) (.node [v565, v732, v852, v1045, v1377, v1568] (.node [v565, v732, v852, v1045, v1377, v1515] .nil .nil) (.node [v565, v732, v852, v1045, v1378, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrlr_ok : everyKey (rowOK 4 level4) level5rrlrlr = true := by decide +kernel
def level5rrlrl : BinaryTree (List W) := .node [v565, v732, v852, v1045, v1337, v1515] level5rrlrll level5rrlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrl_ok : everyKey (rowOK 4 level4) level5rrlrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrlrll && everyKey (rowOK 4 level4) level5rrlrlr) = true
  rw [level5rrlrll_ok, level5rrlrlr_ok]
  decide +kernel
def level5rrlrrl : BinaryTree (List W) := (.node [v565, v732, v852, v1045, v1407, v1419] (.node [v565, v732, v852, v1045, v1392, v1515] (.node [v565, v732, v852, v1045, v1384, v1515] (.node [v565, v732, v852, v1045, v1381, v1515] (.node [v565, v732, v852, v1045, v1380, v1515] (.node [v565, v732, v852, v1045, v1379, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1383, v1515] .nil .nil)) (.node [v565, v732, v852, v1045, v1388, v1515] (.node [v565, v732, v852, v1045, v1387, v1515] .nil .nil) (.node [v565, v732, v852, v1045, v1390, v1515] .nil .nil))) (.node [v565, v732, v852, v1045, v1394, v1515] (.node [v565, v732, v852, v1045, v1393, v1515] (.node [v565, v732, v852, v1045, v1392, v1581] .nil .nil) (.node [v565, v732, v852, v1045, v1393, v1582] .nil .nil)) (.node [v565, v732, v852, v1045, v1396, v1515] (.node [v565, v732, v852, v1045, v1395, v1515] .nil .nil) (.node [v565, v732, v852, v1045, v1406, v1515] .nil .nil)))) (.node [v565, v732, v852, v1045, v1414, v1515] (.node [v565, v732, v852, v1045, v1411, v1515] (.node [v565, v732, v852, v1045, v1409, v1515] (.node [v565, v732, v852, v1045, v1407, v1468] (.node [v565, v732, v852, v1045, v1407, v1442] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1410, v1515] .nil .nil)) (.node [v565, v732, v852, v1045, v1413, v1515] (.node [v565, v732, v852, v1045, v1412, v1515] .nil .nil) (.node [v565, v732, v852, v1045, v1413, v1598] .nil .nil))) (.node [v565, v732, v852, v1045, v1424, v1515] (.node [v565, v732, v852, v1045, v1419, v1492] (.node [v565, v732, v852, v1045, v1419, v1427] .nil .nil) (.node [v565, v732, v852, v1045, v1419, v1648] .nil .nil)) (.node [v565, v732, v852, v1045, v1426, v1515] (.node [v565, v732, v852, v1045, v1425, v1515] .nil .nil) (.node [v565, v732, v852, v1045, v1427, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrrl_ok : everyKey (rowOK 4 level4) level5rrlrrl = true := by decide +kernel
def level5rrlrrr : BinaryTree (List W) := (.node [v565, v732, v852, v1045, v1452, v1623] (.node [v565, v732, v852, v1045, v1439, v1515] (.node [v565, v732, v852, v1045, v1436, v1515] (.node [v565, v732, v852, v1045, v1434, v1515] (.node [v565, v732, v852, v1045, v1431, v1515] (.node [v565, v732, v852, v1045, v1427, v1637] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1435, v1515] .nil .nil)) (.node [v565, v732, v852, v1045, v1437, v1515] (.node [v565, v732, v852, v1045, v1436, v1612] .nil .nil) (.node [v565, v732, v852, v1045, v1438, v1515] .nil .nil))) (.node [v565, v732, v852, v1045, v1442, v1648] (.node [v565, v732, v852, v1045, v1442, v1452] (.node [v565, v732, v852, v1045, v1440, v1515] .nil .nil) (.node [v565, v732, v852, v1045, v1442, v1492] .nil .nil)) (.node [v565, v732, v852, v1045, v1450, v1648] (.node [v565, v732, v852, v1045, v1446, v1515] .nil .nil) (.node [v565, v732, v852, v1045, v1452, v1515] .nil .nil)))) (.node [v565, v732, v852, v1045, v1458, v1631] (.node [v565, v732, v852, v1045, v1456, v1515] (.node [v565, v732, v852, v1045, v1454, v1515] (.node [v565, v732, v852, v1045, v1453, v1515] (.node [v565, v732, v852, v1045, v1452, v1637] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1455, v1515] .nil .nil)) (.node [v565, v732, v852, v1045, v1458, v1604] (.node [v565, v732, v852, v1045, v1458, v1557] .nil .nil) (.node [v565, v732, v852, v1045, v1458, v1617] .nil .nil))) (.node [v565, v732, v852, v1045, v1462, v1626] (.node [v565, v732, v852, v1045, v1461, v1515] (.node [v565, v732, v852, v1045, v1460, v1515] .nil .nil) (.node [v565, v732, v852, v1045, v1462, v1515] .nil .nil)) (.node [v565, v732, v852, v1045, v1464, v1515] (.node [v565, v732, v852, v1045, v1463, v1515] .nil .nil) (.node [v565, v732, v852, v1045, v1465, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrrr_ok : everyKey (rowOK 4 level4) level5rrlrrr = true := by decide +kernel
def level5rrlrr : BinaryTree (List W) := .node [v565, v732, v852, v1045, v1427, v1623] level5rrlrrl level5rrlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrr_ok : everyKey (rowOK 4 level4) level5rrlrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrlrrl && everyKey (rowOK 4 level4) level5rrlrrr) = true
  rw [level5rrlrrl_ok, level5rrlrrr_ok]
  decide +kernel
def level5rrlr : BinaryTree (List W) := .node [v565, v732, v852, v1045, v1378, v1569] level5rrlrl level5rrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlr_ok : everyKey (rowOK 4 level4) level5rrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrlrl && everyKey (rowOK 4 level4) level5rrlrr) = true
  rw [level5rrlrl_ok, level5rrlrr_ok]
  decide +kernel
def level5rrl : BinaryTree (List W) := .node [v565, v732, v852, v1045, v1315, v1625] level5rrll level5rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrl_ok : everyKey (rowOK 4 level4) level5rrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrll && everyKey (rowOK 4 level4) level5rrlr) = true
  rw [level5rrll_ok, level5rrlr_ok]
  decide +kernel
def level5rrrlll : BinaryTree (List W) := (.node [v565, v732, v852, v1045, v1486, v1515] (.node [v565, v732, v852, v1045, v1479, v1515] (.node [v565, v732, v852, v1045, v1477, v1648] (.node [v565, v732, v852, v1045, v1468, v1648] (.node [v565, v732, v852, v1045, v1468, v1492] (.node [v565, v732, v852, v1045, v1468, v1478] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1472, v1515] .nil .nil)) (.node [v565, v732, v852, v1045, v1478, v1623] (.node [v565, v732, v852, v1045, v1478, v1515] .nil .nil) (.node [v565, v732, v852, v1045, v1478, v1637] .nil .nil))) (.node [v565, v732, v852, v1045, v1484, v1557] (.node [v565, v732, v852, v1045, v1481, v1515] (.node [v565, v732, v852, v1045, v1480, v1515] .nil .nil) (.node [v565, v732, v852, v1045, v1482, v1515] .nil .nil)) (.node [v565, v732, v852, v1045, v1484, v1617] (.node [v565, v732, v852, v1045, v1484, v1604] .nil .nil) (.node [v565, v732, v852, v1045, v1484, v1631] .nil .nil)))) (.node [v565, v732, v852, v1052, v1315, v1515] (.node [v565, v732, v852, v1048, v1315, v1515] (.node [v565, v732, v852, v1046, v1315, v1515] (.node [v565, v732, v852, v1045, v1515, v1646] (.node [v565, v732, v852, v1045, v1491, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1047, v1315, v1515] .nil .nil)) (.node [v565, v732, v852, v1050, v1315, v1515] (.node [v565, v732, v852, v1049, v1315, v1515] .nil .nil) (.node [v565, v732, v852, v1051, v1315, v1515] .nil .nil))) (.node [v565, v732, v852, v1056, v1315, v1515] (.node [v565, v732, v852, v1054, v1315, v1515] (.node [v565, v732, v852, v1053, v1315, v1515] .nil .nil) (.node [v565, v732, v852, v1055, v1315, v1515] .nil .nil)) (.node [v565, v732, v852, v1058, v1315, v1515] (.node [v565, v732, v852, v1057, v1315, v1515] .nil .nil) (.node [v565, v732, v852, v1059, v1315, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrlll_ok : everyKey (rowOK 4 level4) level5rrrlll = true := by decide +kernel
def level5rrrllr : BinaryTree (List W) := (.node [v565, v732, v852, v1074, v1315, v1515] (.node [v565, v732, v852, v1069, v1263, v1515] (.node [v565, v732, v852, v1063, v1333, v1515] (.node [v565, v732, v852, v1063, v1279, v1515] (.node [v565, v732, v852, v1062, v1315, v1515] (.node [v565, v732, v852, v1061, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1063, v1315, v1515] .nil .nil)) (.node [v565, v732, v852, v1065, v1315, v1515] (.node [v565, v732, v852, v1064, v1315, v1515] .nil .nil) (.node [v565, v732, v852, v1067, v1315, v1515] .nil .nil))) (.node [v565, v732, v852, v1070, v1315, v1515] (.node [v565, v732, v852, v1069, v1458, v1515] (.node [v565, v732, v852, v1069, v1315, v1515] .nil .nil) (.node [v565, v732, v852, v1069, v1484, v1515] .nil .nil)) (.node [v565, v732, v852, v1072, v1315, v1515] (.node [v565, v732, v852, v1071, v1315, v1515] .nil .nil) (.node [v565, v732, v852, v1073, v1315, v1515] .nil .nil)))) (.node [v565, v732, v852, v1081, v1315, v1515] (.node [v565, v732, v852, v1079, v1315, v1515] (.node [v565, v732, v852, v1077, v1315, v1515] (.node [v565, v732, v852, v1076, v1315, v1515] (.node [v565, v732, v852, v1075, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1078, v1315, v1515] .nil .nil)) (.node [v565, v732, v852, v1080, v1315, v1515] (.node [v565, v732, v852, v1080, v1315, v1419] .nil .nil) (.node [v565, v732, v852, v1080, v1315, v1533] .nil .nil))) (.node [v565, v732, v852, v1090, v1095, v1315] (.node [v565, v732, v852, v1085, v1315, v1515] (.node [v565, v732, v852, v1083, v1315, v1515] .nil .nil) (.node [v565, v732, v852, v1088, v1315, v1515] .nil .nil)) (.node [v565, v732, v852, v1090, v1315, v1492] (.node [v565, v732, v852, v1090, v1144, v1315] .nil .nil) (.node [v565, v732, v852, v1090, v1315, v1642] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrllr_ok : everyKey (rowOK 4 level4) level5rrrllr = true := by decide +kernel
def level5rrrll : BinaryTree (List W) := .node [v565, v732, v852, v1060, v1315, v1515] level5rrrlll level5rrrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrll_ok : everyKey (rowOK 4 level4) level5rrrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrlll && everyKey (rowOK 4 level4) level5rrrllr) = true
  rw [level5rrrlll_ok, level5rrrllr_ok]
  decide +kernel
def level5rrrlrl : BinaryTree (List W) := (.node [v565, v732, v852, v1112, v1315, v1515] (.node [v565, v732, v852, v1107, v1315, v1515] (.node [v565, v732, v852, v1100, v1315, v1515] (.node [v565, v732, v852, v1095, v1315, v1637] (.node [v565, v732, v852, v1095, v1315, v1623] (.node [v565, v732, v852, v1095, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1096, v1315, v1515] .nil .nil)) (.node [v565, v732, v852, v1104, v1315, v1515] (.node [v565, v732, v852, v1101, v1315, v1515] .nil .nil) (.node [v565, v732, v852, v1105, v1315, v1515] .nil .nil))) (.node [v565, v732, v852, v1110, v1315, v1515] (.node [v565, v732, v852, v1109, v1315, v1568] (.node [v565, v732, v852, v1109, v1315, v1515] .nil .nil) (.node [v565, v732, v852, v1109, v1377, v1515] .nil .nil)) (.node [v565, v732, v852, v1110, v1378, v1515] (.node [v565, v732, v852, v1110, v1315, v1569] .nil .nil) (.node [v565, v732, v852, v1111, v1315, v1515] .nil .nil)))) (.node [v565, v732, v852, v1126, v1392, v1515] (.node [v565, v732, v852, v1122, v1315, v1515] (.node [v565, v732, v852, v1118, v1315, v1515] (.node [v565, v732, v852, v1117, v1315, v1515] (.node [v565, v732, v852, v1113, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1121, v1315, v1515] .nil .nil)) (.node [v565, v732, v852, v1126, v1315, v1515] (.node [v565, v732, v852, v1124, v1315, v1515] .nil .nil) (.node [v565, v732, v852, v1126, v1315, v1581] .nil .nil))) (.node [v565, v732, v852, v1128, v1315, v1515] (.node [v565, v732, v852, v1127, v1315, v1582] (.node [v565, v732, v852, v1127, v1315, v1515] .nil .nil) (.node [v565, v732, v852, v1127, v1393, v1515] .nil .nil)) (.node [v565, v732, v852, v1130, v1315, v1515] (.node [v565, v732, v852, v1129, v1315, v1515] .nil .nil) (.node [v565, v732, v852, v1143, v1315, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrlrl_ok : everyKey (rowOK 4 level4) level5rrrlrl = true := by decide +kernel
def level5rrrlrr : BinaryTree (List W) := (.node [v565, v732, v852, v1161, v1484, v1515] (.node [v565, v732, v852, v1157, v1315, v1515] (.node [v565, v732, v852, v1144, v1244, v1315] (.node [v565, v732, v852, v1144, v1204, v1315] (.node [v565, v732, v852, v1144, v1185, v1515] (.node [v565, v732, v852, v1144, v1167, v1315] .nil .nil) .nil) (.node [v565, v732, v852, v1144, v1225, v1515] .nil .nil)) (.node [v565, v732, v852, v1150, v1492, v1515] (.node [v565, v732, v852, v1150, v1161, v1515] .nil .nil) (.node [v565, v732, v852, v1150, v1515, v1642] .nil .nil))) (.node [v565, v732, v852, v1161, v1263, v1515] (.node [v565, v732, v852, v1159, v1315, v1515] (.node [v565, v732, v852, v1158, v1315, v1515] .nil .nil) (.node [v565, v732, v852, v1160, v1315, v1515] .nil .nil)) (.node [v565, v732, v852, v1161, v1315, v1604] (.node [v565, v732, v852, v1161, v1315, v1515] .nil .nil) (.node [v565, v732, v852, v1161, v1458, v1515] .nil .nil)))) (.node [v565, v732, v852, v1175, v1315, v1515] (.node [v565, v732, v852, v1172, v1315, v1515] (.node [v565, v732, v852, v1167, v1315, v1492] (.node [v565, v732, v852, v1167, v1175, v1315] (.node [v565, v732, v852, v1162, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1167, v1315, v1642] .nil .nil)) (.node [v565, v732, v852, v1174, v1315, v1515] (.node [v565, v732, v852, v1173, v1315, v1515] .nil .nil) (.node [v565, v732, v852, v1175, v1263, v1315] .nil .nil))) (.node [v565, v732, v852, v1179, v1315, v1515] (.node [v565, v732, v852, v1175, v1315, v1637] (.node [v565, v732, v852, v1175, v1315, v1623] .nil .nil) (.node [v565, v732, v852, v1175, v1427, v1515] .nil .nil)) (.node [v565, v732, v852, v1185, v1198, v1515] (.node [v565, v732, v852, v1182, v1315, v1515] .nil .nil) (.node [v565, v732, v852, v1185, v1492, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrlrr_ok : everyKey (rowOK 4 level4) level5rrrlrr = true := by decide +kernel
def level5rrrlr : BinaryTree (List W) := .node [v565, v732, v852, v1144, v1150, v1515] level5rrrlrl level5rrrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrlr_ok : everyKey (rowOK 4 level4) level5rrrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrlrl && everyKey (rowOK 4 level4) level5rrrlrr) = true
  rw [level5rrrlrl_ok, level5rrrlrr_ok]
  decide +kernel
def level5rrrl : BinaryTree (List W) := .node [v565, v732, v852, v1095, v1263, v1315] level5rrrll level5rrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrl_ok : everyKey (rowOK 4 level4) level5rrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrll && everyKey (rowOK 4 level4) level5rrrlr) = true
  rw [level5rrrll_ok, level5rrrlr_ok]
  decide +kernel
def level5rrrrll : BinaryTree (List W) := (.node [v565, v732, v852, v1212, v1315, v1642] (.node [v565, v732, v852, v1199, v1315, v1515] (.node [v565, v732, v852, v1198, v1315, v1515] (.node [v565, v732, v852, v1197, v1315, v1515] (.node [v565, v732, v852, v1195, v1492, v1515] (.node [v565, v732, v852, v1191, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1198, v1263, v1515] .nil .nil)) (.node [v565, v732, v852, v1198, v1458, v1515] (.node [v565, v732, v852, v1198, v1315, v1617] .nil .nil) (.node [v565, v732, v852, v1198, v1484, v1515] .nil .nil))) (.node [v565, v732, v852, v1204, v1214, v1315] (.node [v565, v732, v852, v1201, v1315, v1515] (.node [v565, v732, v852, v1200, v1315, v1515] .nil .nil) (.node [v565, v732, v852, v1202, v1315, v1515] .nil .nil)) (.node [v565, v732, v852, v1204, v1315, v1642] (.node [v565, v732, v852, v1204, v1315, v1492] .nil .nil) (.node [v565, v732, v852, v1209, v1315, v1515] .nil .nil)))) (.node [v565, v732, v852, v1218, v1315, v1515] (.node [v565, v732, v852, v1214, v1452, v1515] (.node [v565, v732, v852, v1214, v1315, v1623] (.node [v565, v732, v852, v1214, v1315, v1515] (.node [v565, v732, v852, v1214, v1263, v1315] .nil .nil) .nil) (.node [v565, v732, v852, v1214, v1315, v1637] .nil .nil)) (.node [v565, v732, v852, v1216, v1315, v1515] (.node [v565, v732, v852, v1215, v1315, v1515] .nil .nil) (.node [v565, v732, v852, v1217, v1315, v1515] .nil .nil))) (.node [v565, v732, v852, v1220, v1315, v1626] (.node [v565, v732, v852, v1220, v1315, v1598] (.node [v565, v732, v852, v1220, v1315, v1539] .nil .nil) (.node [v565, v732, v852, v1220, v1315, v1612] .nil .nil)) (.node [v565, v732, v852, v1220, v1413, v1515] (.node [v565, v732, v852, v1220, v1339, v1515] .nil .nil) (.node [v565, v732, v852, v1220, v1436, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrll_ok : everyKey (rowOK 4 level4) level5rrrrll = true := by decide +kernel
def level5rrrrlr : BinaryTree (List W) := (.node [v565, v732, v852, v1244, v1254, v1315] (.node [v565, v732, v852, v1238, v1315, v1515] (.node [v565, v732, v852, v1231, v1315, v1515] (.node [v565, v732, v852, v1225, v1492, v1515] (.node [v565, v732, v852, v1225, v1238, v1515] (.node [v565, v732, v852, v1222, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1225, v1515, v1642] .nil .nil)) (.node [v565, v732, v852, v1237, v1315, v1515] (.node [v565, v732, v852, v1236, v1492, v1515] .nil .nil) (.node [v565, v732, v852, v1238, v1263, v1515] .nil .nil))) (.node [v565, v732, v852, v1239, v1315, v1515] (.node [v565, v732, v852, v1238, v1458, v1515] (.node [v565, v732, v852, v1238, v1315, v1631] .nil .nil) (.node [v565, v732, v852, v1238, v1484, v1515] .nil .nil)) (.node [v565, v732, v852, v1241, v1315, v1515] (.node [v565, v732, v852, v1240, v1315, v1515] .nil .nil) (.node [v565, v732, v852, v1242, v1315, v1515] .nil .nil)))) (.node [v565, v732, v852, v1254, v1478, v1515] (.node [v565, v732, v852, v1254, v1263, v1315] (.node [v565, v732, v852, v1249, v1315, v1515] (.node [v565, v732, v852, v1244, v1315, v1642] (.node [v565, v732, v852, v1244, v1315, v1492] .nil .nil) .nil) (.node [v565, v732, v852, v1253, v1315, v1642] .nil .nil)) (.node [v565, v732, v852, v1254, v1315, v1623] (.node [v565, v732, v852, v1254, v1315, v1515] .nil .nil) (.node [v565, v732, v852, v1254, v1315, v1637] .nil .nil))) (.node [v565, v732, v852, v1258, v1315, v1515] (.node [v565, v732, v852, v1256, v1315, v1515] (.node [v565, v732, v852, v1255, v1315, v1515] .nil .nil) (.node [v565, v732, v852, v1257, v1315, v1515] .nil .nil)) (.node [v565, v732, v852, v1260, v1315, v1598] (.node [v565, v732, v852, v1260, v1315, v1539] .nil .nil) (.node [v565, v732, v852, v1260, v1315, v1612] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrlr_ok : everyKey (rowOK 4 level4) level5rrrrlr = true := by decide +kernel
def level5rrrrl : BinaryTree (List W) := .node [v565, v732, v852, v1220, v1462, v1515] level5rrrrll level5rrrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrl_ok : everyKey (rowOK 4 level4) level5rrrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrrll && everyKey (rowOK 4 level4) level5rrrrlr) = true
  rw [level5rrrrll_ok, level5rrrrlr_ok]
  decide +kernel
def level5rrrrrl : BinaryTree (List W) := (.node [v565, v732, v940, v1045, v1315, v1515] (.node [v565, v732, v862, v1045, v1315, v1515] (.node [v565, v732, v852, v1262, v1315, v1515] (.node [v565, v732, v852, v1260, v1436, v1515] (.node [v565, v732, v852, v1260, v1413, v1515] (.node [v565, v732, v852, v1260, v1339, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1260, v1462, v1515] .nil .nil)) (.node [v565, v732, v852, v1315, v1515, v1640] (.node [v565, v732, v852, v1315, v1490, v1515] .nil .nil) (.node [v565, v732, v853, v1045, v1315, v1515] .nil .nil))) (.node [v565, v732, v905, v944, v1045, v1515] (.node [v565, v732, v880, v1045, v1315, v1515] (.node [v565, v732, v870, v1045, v1315, v1515] .nil .nil) (.node [v565, v732, v892, v944, v1315, v1515] .nil .nil)) (.node [v565, v732, v930, v1045, v1315, v1515] (.node [v565, v732, v914, v944, v1045, v1315] .nil .nil) (.node [v565, v732, v935, v1045, v1315, v1515] .nil .nil)))) (.node [v565, v772, v852, v943, v1315, v1515] (.node [v565, v733, v852, v1045, v1315, v1515] (.node [v565, v732, v944, v1045, v1378, v1515] (.node [v565, v732, v944, v1045, v1315, v1569] (.node [v565, v732, v944, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v944, v1110, v1315, v1515] .nil .nil)) (.node [v565, v750, v852, v1045, v1315, v1515] (.node [v565, v742, v852, v1045, v1315, v1515] .nil .nil) (.node [v565, v760, v852, v1045, v1315, v1515] .nil .nil))) (.node [v565, v845, v945, v1045, v1315, v1515] (.node [v565, v794, v852, v943, v1045, v1315] (.node [v565, v785, v852, v943, v1045, v1515] .nil .nil) (.node [v565, v845, v943, v1045, v1315, v1515] .nil .nil)) (.node [v565, v852, v916, v1045, v1315, v1515] (.node [v565, v852, v915, v1045, v1315, v1515] .nil .nil) (.node [v565, v852, v928, v1045, v1315, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrrl_ok : everyKey (rowOK 4 level4) level5rrrrrl = true := by decide +kernel
def level5rrrrrr : BinaryTree (List W) := (.node [v638, v639, v732, v852, v1045, v1315] (.node [v623, v626, v732, v852, v1315, v1515] (.node [v565, v852, v943, v1127, v1315, v1515] (.node [v565, v852, v943, v1045, v1315, v1582] (.node [v565, v852, v943, v1045, v1315, v1515] (.node [v565, v852, v938, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v852, v943, v1045, v1393, v1515] .nil .nil)) (.node [v565, v944, v1045, v1315, v1515, v1654] (.node [v565, v943, v1045, v1315, v1515, v1655] .nil .nil) (.node [v565, v945, v1045, v1315, v1515, v1653] .nil .nil))) (.node [v631, v633, v732, v852, v1045, v1515] (.node [v626, v732, v852, v1144, v1315, v1515] (.node [v626, v732, v852, v1045, v1315, v1515] .nil .nil) (.node [v626, v732, v852, v1315, v1515] .nil .nil)) (.node [v633, v732, v852, v1045, v1407, v1515] (.node [v633, v732, v852, v1045, v1315, v1515] .nil .nil) (.node [v633, v732, v852, v1045, v1515] .nil .nil)))) (.node [v732, v795, v1045, v1315, v1515] (.node [v643, v852, v915, v1045, v1315, v1515] (.node [v639, v732, v852, v1045, v1315, v1515] (.node [v639, v732, v852, v1045, v1315] .nil .nil) (.node [v639, v732, v852, v1045, v1315, v1593] .nil .nil)) (.node [v652, v732, v852, v1045, v1315, v1515] (.node [v644, v732, v795, v1045, v1315, v1515] .nil .nil) (.node [v732, v795, v852, v1045, v1315, v1515] .nil .nil))) (.node [v732, v852, v1045, v1315, v1403, v1515] (.node [v732, v852, v915, v1045, v1315, v1515] (.node [v732, v795, v1045, v1315, v1515, v1655] .nil .nil) (.node [v732, v852, v1045, v1140, v1315, v1515] .nil .nil)) (.node [v852, v915, v1045, v1315, v1515] (.node [v732, v852, v1045, v1315, v1515, v1589] .nil .nil) (.node [v852, v915, v1045, v1315, v1515, v1654] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrrr_ok : everyKey (rowOK 4 level4) level5rrrrrr = true := by decide +kernel
def level5rrrrr : BinaryTree (List W) := .node [v565, v852, v933, v1045, v1315, v1515] level5rrrrrl level5rrrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrr_ok : everyKey (rowOK 4 level4) level5rrrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrrrl && everyKey (rowOK 4 level4) level5rrrrrr) = true
  rw [level5rrrrrl_ok, level5rrrrrr_ok]
  decide +kernel
def level5rrrr : BinaryTree (List W) := .node [v565, v732, v852, v1260, v1315, v1626] level5rrrrl level5rrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrr_ok : everyKey (rowOK 4 level4) level5rrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrrl && everyKey (rowOK 4 level4) level5rrrrr) = true
  rw [level5rrrrl_ok, level5rrrrr_ok]
  decide +kernel
def level5rrr : BinaryTree (List W) := .node [v565, v732, v852, v1185, v1515, v1642] level5rrrl level5rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrr_ok : everyKey (rowOK 4 level4) level5rrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrl && everyKey (rowOK 4 level4) level5rrrr) = true
  rw [level5rrrl_ok, level5rrrr_ok]
  decide +kernel
def level5rr : BinaryTree (List W) := .node [v565, v732, v852, v1045, v1466, v1515] level5rrl level5rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rr_ok : everyKey (rowOK 4 level4) level5rr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrl && everyKey (rowOK 4 level4) level5rrr) = true
  rw [level5rrl_ok, level5rrr_ok]
  decide +kernel
def level5r : BinaryTree (List W) := .node [v565, v732, v852, v1045, v1307, v1515] level5rl level5rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5r_ok : everyKey (rowOK 4 level4) level5r = true := by
  change (_ && everyKey (rowOK 4 level4) level5rl && everyKey (rowOK 4 level4) level5rr) = true
  rw [level5rl_ok, level5rr_ok]
  decide +kernel
def level5 : BinaryTree (List W) := .node [v565, v701, v852, v1045, v1458, v1515] level5l level5r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5_ok : everyKey (rowOK 4 level4) level5 = true := by
  change (_ && everyKey (rowOK 4 level4) level5l && everyKey (rowOK 4 level4) level5r) = true
  rw [level5l_ok, level5r_ok]
  decide +kernel
theorem closed5 : Closed 5 level5 := closed_next 4 (by decide) level5 level4 closed4 level5_ok
def level6lllll : BinaryTree (List W) := (.node [v21, v565, v732, v852, v1045, v1315, v1515] (.node [v10, v565, v732, v852, v1045, v1315, v1515] (.node [v5, v565, v732, v852, v1045, v1315, v1515] (.node [v2, v565, v732, v852, v1045, v1315, v1515] (.node [v1, v565, v732, v852, v1045, v1315, v1515] (.node [v0, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v4, v565, v732, v852, v1045, v1315, v1515] (.node [v3, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil)) (.node [v8, v565, v732, v852, v1045, v1315, v1515] (.node [v7, v565, v732, v852, v1045, v1315, v1515] (.node [v6, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v9, v565, v732, v852, v1045, v1315, v1515] .nil .nil))) (.node [v16, v565, v732, v852, v1045, v1315, v1515] (.node [v13, v565, v732, v852, v1045, v1315, v1515] (.node [v12, v565, v732, v852, v1045, v1315, v1515] (.node [v11, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v15, v565, v732, v852, v1045, v1315, v1515] (.node [v14, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil)) (.node [v19, v565, v732, v852, v1045, v1315, v1515] (.node [v18, v565, v732, v852, v1045, v1315, v1515] (.node [v17, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v20, v565, v732, v852, v1045, v1315, v1515] .nil .nil)))) (.node [v34, v161, v565, v732, v852, v1045, v1315] (.node [v29, v565, v732, v852, v1045, v1315, v1515] (.node [v26, v565, v732, v852, v1045, v1315, v1515] (.node [v25, v565, v732, v852, v1045, v1315, v1515] (.node [v22, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v28, v565, v732, v852, v1045, v1315, v1515] (.node [v27, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil)) (.node [v34, v47, v565, v732, v852, v1045, v1315] (.node [v33, v565, v732, v852, v1045, v1315, v1515] (.node [v32, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v34, v54, v565, v732, v852, v1045, v1315] .nil .nil))) (.node [v34, v565, v732, v832, v852, v1045, v1315] (.node [v34, v565, v638, v732, v852, v1045, v1315] (.node [v34, v549, v732, v852, v1045, v1315, v1515] (.node [v34, v255, v565, v732, v852, v1045, v1315] .nil .nil) .nil) (.node [v34, v565, v712, v732, v852, v1045, v1315] .nil .nil)) (.node [v34, v565, v732, v852, v1045, v1315, v1515] (.node [v34, v565, v732, v852, v1045, v1279, v1515] (.node [v34, v565, v732, v852, v1009, v1315, v1515] .nil .nil) .nil) (.node [v34, v565, v732, v852, v1045, v1315, v1593] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllll_ok : everyKey (rowOK 5 level5) level6lllll = true := by decide +kernel
def level6llllr : BinaryTree (List W) := (.node [v47, v565, v732, v852, v1045, v1263, v1315] (.node [v44, v565, v732, v852, v1045, v1315, v1515] (.node [v39, v565, v732, v852, v1045, v1315, v1515] (.node [v34, v565, v732, v852, v1063, v1315, v1515] (.node [v34, v565, v732, v852, v1045, v1333, v1515] (.node [v34, v565, v732, v852, v1045, v1315, v1648] .nil .nil) .nil) (.node [v34, v638, v732, v852, v1045, v1315, v1515] (.node [v34, v638, v732, v852, v1045, v1315] .nil .nil) .nil)) (.node [v42, v565, v732, v852, v1045, v1315, v1515] (.node [v41, v565, v732, v852, v1045, v1315, v1515] (.node [v40, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v43, v565, v732, v852, v1045, v1315, v1515] .nil .nil))) (.node [v47, v450, v565, v852, v1045, v1315] (.node [v47, v72, v565, v732, v852, v1045, v1315] (.node [v47, v59, v565, v732, v852, v1045, v1315] (.node [v45, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v47, v450, v565, v732, v852, v1045, v1315] (.node [v47, v358, v565, v732, v852, v1045, v1315] .nil .nil) .nil)) (.node [v47, v565, v712, v852, v1045, v1315, v1515] (.node [v47, v549, v565, v732, v852, v1045, v1315] (.node [v47, v450, v565, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v47, v565, v732, v852, v993, v1045, v1315] .nil .nil)))) (.node [v54, v450, v565, v732, v852, v1045, v1315] (.node [v54, v59, v565, v732, v852, v1045, v1315] (.node [v47, v565, v732, v852, v1045, v1315, v1637] (.node [v47, v565, v732, v852, v1045, v1315, v1623] (.node [v47, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v52, v565, v732, v852, v1045, v1315, v1515] (.node [v51, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil)) (.node [v54, v358, v565, v732, v1045, v1315] (.node [v54, v358, v565, v732, v852, v1045, v1315] (.node [v54, v72, v565, v732, v852, v1045, v1315] .nil .nil) .nil) (.node [v54, v358, v565, v732, v1045, v1315, v1515] .nil .nil))) (.node [v54, v565, v732, v852, v1045, v1315, v1515] (.node [v54, v565, v732, v852, v993, v1045, v1315] (.node [v54, v565, v732, v832, v1045, v1315, v1515] (.node [v54, v549, v565, v732, v852, v1045, v1315] .nil .nil) .nil) (.node [v54, v565, v732, v852, v1045, v1263, v1315] .nil .nil)) (.node [v58, v565, v732, v852, v1045, v1315, v1515] (.node [v54, v565, v732, v852, v1045, v1315, v1637] (.node [v54, v565, v732, v852, v1045, v1315, v1623] .nil .nil) .nil) (.node [v59, v161, v565, v732, v852, v1045, v1315] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llllr_ok : everyKey (rowOK 5 level5) level6llllr = true := by decide +kernel
def level6llll : BinaryTree (List W) := .node [v34, v565, v732, v852, v1045, v1315, v1642] level6lllll level6llllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llll_ok : everyKey (rowOK 5 level5) level6llll = true := by
  change (_ && everyKey (rowOK 5 level5) level6lllll && everyKey (rowOK 5 level5) level6llllr) = true
  rw [level6lllll_ok, level6llllr_ok]
  decide +kernel
def level6lllrl : BinaryTree (List W) := (.node [v68, v565, v732, v852, v1045, v1220, v1315] (.node [v59, v565, v732, v852, v949, v1315, v1515] (.node [v59, v424, v565, v732, v852, v1315, v1515] (.node [v59, v255, v565, v732, v852, v1315] (.node [v59, v255, v565, v732, v852, v1045, v1315] (.node [v59, v240, v565, v732, v852, v1315, v1515] .nil .nil) .nil) (.node [v59, v332, v565, v732, v852, v1315, v1515] (.node [v59, v255, v565, v732, v852, v1315, v1515] .nil .nil) .nil)) (.node [v59, v565, v712, v732, v852, v1045, v1315] (.node [v59, v565, v638, v732, v852, v1045, v1315] (.node [v59, v501, v565, v732, v852, v1315, v1515] .nil .nil) .nil) (.node [v59, v565, v732, v832, v852, v1045, v1315] .nil .nil))) (.node [v59, v565, v732, v852, v1045, v1315, v1648] (.node [v59, v565, v732, v852, v1045, v1315, v1515] (.node [v59, v565, v732, v852, v1045, v1269, v1515] (.node [v59, v565, v732, v852, v993, v1315, v1515] .nil .nil) .nil) (.node [v59, v565, v732, v852, v1045, v1315, v1642] (.node [v59, v565, v732, v852, v1045, v1315, v1593] .nil .nil) .nil)) (.node [v59, v565, v732, v852, v1260, v1315, v1515] (.node [v59, v565, v732, v852, v1220, v1315, v1515] (.node [v59, v565, v732, v852, v1045, v1339, v1515] .nil .nil) .nil) (.node [v62, v565, v732, v852, v1045, v1315, v1515] .nil .nil)))) (.node [v72, v255, v565, v732, v852, v1045, v1315] (.node [v72, v117, v565, v732, v852, v1045, v1515] (.node [v71, v565, v732, v852, v1045, v1260, v1315] (.node [v68, v565, v732, v852, v1045, v1315, v1515] (.node [v68, v565, v732, v852, v1045, v1315] .nil .nil) .nil) (.node [v71, v565, v732, v852, v1045, v1315, v1515] (.node [v71, v565, v732, v852, v1045, v1315] .nil .nil) .nil)) (.node [v72, v161, v565, v732, v852, v1045, v1315] (.node [v72, v161, v565, v732, v852, v1045] (.node [v72, v146, v565, v732, v852, v1045, v1515] .nil .nil) .nil) (.node [v72, v161, v565, v732, v852, v1045, v1515] .nil .nil))) (.node [v72, v565, v712, v732, v852, v1045, v1315] (.node [v72, v530, v565, v732, v852, v1045, v1515] (.node [v72, v441, v565, v732, v852, v1045, v1515] (.node [v72, v349, v565, v732, v852, v1045, v1515] .nil .nil) .nil) (.node [v72, v565, v638, v732, v852, v1045, v1315] .nil .nil)) (.node [v72, v565, v732, v852, v997, v1315, v1515] (.node [v72, v565, v732, v852, v949, v1045, v1515] (.node [v72, v565, v732, v832, v852, v1045, v1315] .nil .nil) .nil) (.node [v72, v565, v732, v852, v1045, v1263, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllrl_ok : everyKey (rowOK 5 level5) level6lllrl = true := by decide +kernel
def level6lllrr : BinaryTree (List W) := (.node [v97, v565, v732, v852, v1045, v1315, v1515] (.node [v82, v565, v732, v852, v1045, v1315] (.node [v72, v565, v732, v852, v1069, v1315, v1515] (.node [v72, v565, v732, v852, v1045, v1315, v1648] (.node [v72, v565, v732, v852, v1045, v1315, v1642] (.node [v72, v565, v732, v852, v1045, v1315, v1593] .nil .nil) .nil) (.node [v72, v565, v732, v852, v1045, v1484, v1515] (.node [v72, v565, v732, v852, v1045, v1458, v1515] .nil .nil) .nil)) (.node [v80, v565, v732, v852, v1045, v1315, v1458] (.node [v80, v565, v732, v852, v1045, v1315] (.node [v75, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v80, v565, v732, v852, v1045, v1315, v1515] .nil .nil))) (.node [v87, v565, v732, v852, v1045, v1315, v1654] (.node [v83, v565, v732, v852, v1045, v1315, v1515] (.node [v82, v565, v732, v852, v1045, v1315, v1515] (.node [v82, v565, v732, v852, v1045, v1315, v1484] .nil .nil) .nil) (.node [v87, v565, v732, v852, v1045, v1315, v1515] (.node [v87, v565, v732, v852, v1045, v1315] .nil .nil) .nil)) (.node [v88, v565, v732, v852, v1045, v1315, v1655] (.node [v88, v565, v732, v852, v1045, v1315, v1515] (.node [v88, v565, v732, v852, v1045, v1315] .nil .nil) .nil) (.node [v89, v565, v732, v852, v1045, v1315, v1515] .nil .nil)))) (.node [v110, v565, v732, v852, v1045, v1315, v1515] (.node [v103, v565, v732, v852, v1045, v1315, v1515] (.node [v100, v565, v732, v852, v1045, v1315, v1515] (.node [v99, v565, v732, v852, v1045, v1315, v1515] (.node [v98, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v102, v565, v732, v852, v1045, v1315, v1515] (.node [v101, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil)) (.node [v108, v565, v732, v852, v1045, v1315, v1515] (.node [v105, v565, v732, v852, v1045, v1315, v1515] (.node [v104, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v109, v565, v732, v852, v1045, v1315, v1515] .nil .nil))) (.node [v117, v132, v565, v732, v852, v1045, v1515] (.node [v115, v565, v732, v852, v1045, v1315, v1515] (.node [v112, v565, v732, v852, v1045, v1315, v1515] (.node [v111, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v116, v565, v732, v852, v1045, v1315, v1515] .nil .nil)) (.node [v117, v530, v732, v852, v1045, v1315, v1515] (.node [v117, v240, v565, v732, v852, v1045, v1515] (.node [v117, v140, v565, v732, v852, v1045, v1515] .nil .nil) .nil) (.node [v117, v565, v631, v732, v852, v1045, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllrr_ok : everyKey (rowOK 5 level5) level6lllrr = true := by decide +kernel
def level6lllr : BinaryTree (List W) := .node [v72, v565, v732, v852, v1045, v1315, v1515] level6lllrl level6lllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllr_ok : everyKey (rowOK 5 level5) level6lllr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lllrl && everyKey (rowOK 5 level5) level6lllrr) = true
  rw [level6lllrl_ok, level6lllrr_ok]
  decide +kernel
def level6lll : BinaryTree (List W) := .node [v59, v207, v565, v732, v852, v1315, v1515] level6llll level6lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lll_ok : everyKey (rowOK 5 level5) level6lll = true := by
  change (_ && everyKey (rowOK 5 level5) level6llll && everyKey (rowOK 5 level5) level6lllr) = true
  rw [level6llll_ok, level6lllr_ok]
  decide +kernel
def level6llrll : BinaryTree (List W) := (.node [v132, v349, v565, v732, v852, v1045, v1515] (.node [v117, v631, v732, v852, v1045, v1515] (.node [v117, v565, v732, v852, v1045, v1407, v1515] (.node [v117, v565, v732, v852, v1045, v1315, v1419] (.node [v117, v565, v732, v852, v972, v1315, v1515] (.node [v117, v565, v732, v821, v852, v1045, v1515] .nil .nil) .nil) (.node [v117, v565, v732, v852, v1045, v1315, v1533] (.node [v117, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil)) (.node [v117, v565, v732, v852, v1080, v1315, v1515] (.node [v117, v565, v732, v852, v1045, v1515, v1648] (.node [v117, v565, v732, v852, v1045, v1492, v1515] .nil .nil) .nil) (.node [v117, v631, v732, v852, v1045, v1315, v1515] .nil .nil))) (.node [v128, v565, v732, v852, v1045, v1315, v1515] (.node [v125, v565, v732, v852, v1045, v1315, v1515] (.node [v124, v565, v732, v852, v1045, v1315, v1515] (.node [v120, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v127, v565, v732, v852, v1045, v1315, v1515] (.node [v126, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil)) (.node [v132, v146, v565, v732, v852, v1045, v1515] (.node [v130, v565, v732, v852, v1045, v1315, v1515] (.node [v129, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v132, v161, v565, v732, v852, v1045, v1515] .nil .nil)))) (.node [v136, v565, v732, v852, v1045, v1315, v1515] (.node [v132, v565, v732, v852, v949, v1045, v1515] (.node [v132, v441, v565, v852, v1045, v1515] (.node [v132, v441, v565, v852, v1045, v1315, v1515] (.node [v132, v441, v565, v732, v852, v1045, v1515] .nil .nil) .nil) (.node [v132, v565, v701, v852, v1045, v1315, v1515] (.node [v132, v530, v565, v732, v852, v1045, v1515] .nil .nil) .nil)) (.node [v132, v565, v732, v852, v1045, v1458, v1515] (.node [v132, v565, v732, v852, v1045, v1315, v1515] (.node [v132, v565, v732, v852, v1045, v1263, v1515] .nil .nil) .nil) (.node [v132, v565, v732, v852, v1045, v1484, v1515] .nil .nil))) (.node [v140, v349, v565, v732, v852, v1045, v1515] (.node [v140, v146, v565, v732, v852, v1045, v1515] (.node [v138, v565, v732, v852, v1045, v1315, v1515] (.node [v137, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v140, v161, v565, v732, v852, v1045, v1515] .nil .nil)) (.node [v140, v441, v565, v732, v852, v1045, v1515] (.node [v140, v349, v565, v732, v1045, v1515] (.node [v140, v349, v565, v732, v1045, v1315, v1515] .nil .nil) .nil) (.node [v140, v530, v565, v732, v852, v1045, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrll_ok : everyKey (rowOK 5 level5) level6llrll = true := by decide +kernel
def level6llrlr : BinaryTree (List W) := (.node [v146, v565, v732, v852, v1045, v1315, v1515] (.node [v146, v240, v565, v732, v852, v1515] (.node [v144, v565, v732, v852, v1045, v1315, v1515] (.node [v140, v565, v732, v852, v1045, v1315, v1515] (.node [v140, v565, v732, v852, v1045, v1263, v1515] (.node [v140, v565, v732, v852, v949, v1045, v1515] .nil .nil) .nil) (.node [v140, v565, v732, v852, v1045, v1484, v1515] (.node [v140, v565, v732, v852, v1045, v1458, v1515] .nil .nil) .nil)) (.node [v146, v240, v565, v732, v852, v1045, v1515] (.node [v146, v207, v565, v732, v852, v1315, v1515] (.node [v145, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v146, v240, v565, v732, v852, v1315, v1515] .nil .nil))) (.node [v146, v565, v701, v732, v852, v1045, v1515] (.node [v146, v424, v565, v732, v852, v1315, v1515] (.node [v146, v332, v565, v732, v852, v1315, v1515] (.node [v146, v255, v565, v732, v852, v1315, v1515] .nil .nil) .nil) (.node [v146, v565, v631, v732, v852, v1045, v1515] (.node [v146, v501, v565, v732, v852, v1315, v1515] .nil .nil) .nil)) (.node [v146, v565, v732, v852, v993, v1315, v1515] (.node [v146, v565, v732, v852, v949, v1315, v1515] (.node [v146, v565, v732, v821, v852, v1045, v1515] .nil .nil) .nil) (.node [v146, v565, v732, v852, v1045, v1315, v1360] .nil .nil)))) (.node [v157, v565, v732, v852, v1045, v1515] (.node [v146, v565, v732, v852, v1260, v1315, v1515] (.node [v146, v565, v732, v852, v1045, v1492, v1515] (.node [v146, v565, v732, v852, v1045, v1407, v1515] (.node [v146, v565, v732, v852, v1045, v1315, v1539] .nil .nil) .nil) (.node [v146, v565, v732, v852, v1220, v1315, v1515] (.node [v146, v565, v732, v852, v1045, v1515, v1648] .nil .nil) .nil)) (.node [v157, v565, v732, v852, v1045, v1220, v1515] (.node [v151, v565, v732, v852, v1045, v1315, v1515] (.node [v149, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v157, v565, v732, v852, v1045, v1315, v1515] .nil .nil))) (.node [v161, v358, v565, v732, v852, v1045, v1315] (.node [v160, v565, v732, v852, v1045, v1515] (.node [v160, v565, v732, v852, v1045, v1315, v1515] (.node [v160, v565, v732, v852, v1045, v1260, v1515] .nil .nil) .nil) (.node [v161, v240, v565, v732, v852, v1045, v1515] .nil .nil)) (.node [v161, v565, v631, v732, v852, v1045, v1515] (.node [v161, v549, v565, v732, v852, v1045, v1315] (.node [v161, v450, v565, v732, v852, v1045, v1315] .nil .nil) .nil) (.node [v161, v565, v701, v732, v852, v1045, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrlr_ok : everyKey (rowOK 5 level5) level6llrlr = true := by decide +kernel
def level6llrl : BinaryTree (List W) := .node [v140, v565, v732, v821, v1045, v1315, v1515] level6llrll level6llrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrl_ok : everyKey (rowOK 5 level5) level6llrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6llrll && everyKey (rowOK 5 level5) level6llrlr) = true
  rw [level6llrll_ok, level6llrlr_ok]
  decide +kernel
def level6llrrl : BinaryTree (List W) := (.node [v177, v565, v732, v852, v1045, v1315, v1515] (.node [v164, v565, v732, v852, v1045, v1315, v1515] (.node [v161, v565, v732, v852, v1045, v1315, v1637] (.node [v161, v565, v732, v852, v1045, v1263, v1315] (.node [v161, v565, v732, v852, v993, v1045, v1315] (.node [v161, v565, v732, v852, v953, v1315, v1515] .nil .nil) .nil) (.node [v161, v565, v732, v852, v1045, v1315, v1623] (.node [v161, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil)) (.node [v161, v565, v732, v852, v1045, v1515, v1648] (.node [v161, v565, v732, v852, v1045, v1492, v1515] (.node [v161, v565, v732, v852, v1045, v1407, v1515] .nil .nil) .nil) (.node [v161, v565, v732, v852, v1095, v1315, v1515] .nil .nil))) (.node [v171, v565, v732, v852, v1045, v1515, v1637] (.node [v169, v565, v732, v852, v1045, v1515, v1623] (.node [v169, v565, v732, v852, v1045, v1515] (.node [v169, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v171, v565, v732, v852, v1045, v1515] (.node [v171, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil)) (.node [v176, v565, v732, v852, v1045, v1515] (.node [v176, v565, v732, v852, v1045, v1315, v1515] (.node [v172, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v176, v565, v732, v852, v1045, v1515, v1654] .nil .nil)))) (.node [v200, v565, v732, v852, v1045, v1315, v1515] (.node [v193, v565, v732, v852, v1045, v1315, v1515] (.node [v178, v565, v732, v852, v1045, v1315, v1515] (.node [v177, v565, v732, v852, v1045, v1515, v1655] (.node [v177, v565, v732, v852, v1045, v1515] .nil .nil) .nil) (.node [v192, v565, v732, v852, v1045, v1315, v1515] (.node [v191, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil)) (.node [v198, v565, v732, v852, v1045, v1315, v1515] (.node [v195, v565, v732, v852, v1045, v1315, v1515] (.node [v194, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v199, v565, v732, v852, v1045, v1315, v1515] .nil .nil))) (.node [v207, v224, v565, v732, v852, v1315, v1515] (.node [v205, v565, v732, v852, v1045, v1315, v1515] (.node [v202, v565, v732, v852, v1045, v1315, v1515] (.node [v201, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v206, v565, v732, v852, v1045, v1315, v1515] .nil .nil)) (.node [v207, v565, v623, v732, v852, v1315, v1515] (.node [v207, v501, v732, v852, v1045, v1315, v1515] (.node [v207, v233, v565, v732, v852, v1315, v1515] .nil .nil) .nil) (.node [v207, v565, v689, v732, v852, v1315, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrrl_ok : everyKey (rowOK 5 level5) level6llrrl = true := by decide +kernel
def level6llrrr : BinaryTree (List W) := (.node [v224, v255, v565, v732, v852, v1315, v1515] (.node [v210, v565, v732, v852, v1045, v1315, v1515] (.node [v207, v565, v732, v852, v1144, v1315, v1515] (.node [v207, v565, v732, v852, v1045, v1315, v1515] (.node [v207, v565, v732, v852, v1045, v1167, v1315] (.node [v207, v565, v732, v852, v1045, v1150, v1515] .nil .nil) .nil) (.node [v207, v565, v732, v852, v1045, v1350, v1515] (.node [v207, v565, v732, v852, v1045, v1315, v1550] .nil .nil) .nil)) (.node [v207, v623, v732, v852, v1045, v1315, v1515] (.node [v207, v565, v732, v852, v1315, v1515, v1642] (.node [v207, v565, v732, v852, v1315, v1492, v1515] .nil .nil) .nil) (.node [v207, v623, v732, v852, v1315, v1515] .nil .nil))) (.node [v219, v565, v732, v852, v1045, v1315, v1515] (.node [v217, v565, v732, v852, v1045, v1315, v1515] (.node [v216, v565, v732, v852, v1045, v1315, v1515] (.node [v214, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v218, v565, v732, v852, v1045, v1315, v1515] .nil .nil)) (.node [v222, v565, v732, v852, v1045, v1315, v1515] (.node [v221, v565, v732, v852, v1045, v1315, v1515] (.node [v220, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v224, v240, v565, v732, v852, v1315, v1515] .nil .nil)))) (.node [v224, v565, v732, v852, v1260, v1315, v1515] (.node [v224, v565, v689, v852, v1045, v1315, v1515] (.node [v224, v424, v565, v852, v1045, v1315, v1515] (.node [v224, v424, v565, v732, v852, v1315, v1515] (.node [v224, v332, v565, v732, v852, v1315, v1515] .nil .nil) .nil) (.node [v224, v501, v565, v732, v852, v1315, v1515] (.node [v224, v424, v565, v852, v1315, v1515] .nil .nil) .nil)) (.node [v224, v565, v732, v852, v1045, v1315, v1515] (.node [v224, v565, v732, v852, v993, v1315, v1515] (.node [v224, v565, v732, v852, v949, v1315, v1515] .nil .nil) .nil) (.node [v224, v565, v732, v852, v1220, v1315, v1515] .nil .nil))) (.node [v233, v240, v565, v732, v852, v1315, v1515] (.node [v230, v565, v732, v852, v1045, v1315, v1515] (.node [v229, v565, v732, v852, v1045, v1315, v1515] (.node [v228, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v231, v565, v732, v852, v1045, v1315, v1515] .nil .nil)) (.node [v233, v332, v565, v732, v1045, v1315, v1515] (.node [v233, v332, v565, v732, v852, v1315, v1515] (.node [v233, v255, v565, v732, v852, v1315, v1515] .nil .nil) .nil) (.node [v233, v332, v565, v732, v1315, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrrr_ok : everyKey (rowOK 5 level5) level6llrrr = true := by decide +kernel
def level6llrr : BinaryTree (List W) := .node [v207, v565, v732, v809, v852, v1315, v1515] level6llrrl level6llrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrr_ok : everyKey (rowOK 5 level5) level6llrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6llrrl && everyKey (rowOK 5 level5) level6llrrr) = true
  rw [level6llrrl_ok, level6llrrr_ok]
  decide +kernel
def level6llr : BinaryTree (List W) := .node [v161, v565, v732, v821, v852, v1045, v1515] level6llrl level6llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llr_ok : everyKey (rowOK 5 level5) level6llr = true := by
  change (_ && everyKey (rowOK 5 level5) level6llrl && everyKey (rowOK 5 level5) level6llrr) = true
  rw [level6llrl_ok, level6llrr_ok]
  decide +kernel
def level6ll : BinaryTree (List W) := .node [v117, v565, v701, v732, v852, v1045, v1515] level6lll level6llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6ll_ok : everyKey (rowOK 5 level5) level6ll = true := by
  change (_ && everyKey (rowOK 5 level5) level6lll && everyKey (rowOK 5 level5) level6llr) = true
  rw [level6lll_ok, level6llr_ok]
  decide +kernel
def level6lrlll : BinaryTree (List W) := (.node [v240, v565, v732, v852, v1045, v1458, v1515] (.node [v240, v349, v565, v732, v852, v1045, v1515] (.node [v233, v565, v732, v852, v1220, v1315, v1515] (.node [v233, v565, v732, v852, v949, v1315, v1515] (.node [v233, v565, v732, v809, v1045, v1315, v1515] (.node [v233, v501, v565, v732, v852, v1315, v1515] .nil .nil) .nil) (.node [v233, v565, v732, v852, v1045, v1315, v1515] (.node [v233, v565, v732, v852, v993, v1315, v1515] .nil .nil) .nil)) (.node [v238, v565, v732, v852, v1045, v1315, v1515] (.node [v237, v565, v732, v852, v1045, v1315, v1515] (.node [v233, v565, v732, v852, v1260, v1315, v1515] .nil .nil) .nil) (.node [v239, v565, v732, v852, v1045, v1315, v1515] .nil .nil))) (.node [v240, v565, v732, v852, v949, v1045, v1515] (.node [v240, v565, v623, v732, v852, v1315, v1515] (.node [v240, v530, v565, v732, v852, v1045, v1515] (.node [v240, v441, v565, v732, v852, v1045, v1515] .nil .nil) .nil) (.node [v240, v565, v732, v809, v852, v1315, v1515] (.node [v240, v565, v689, v732, v852, v1315, v1515] .nil .nil) .nil)) (.node [v240, v565, v732, v852, v1045, v1315, v1515] (.node [v240, v565, v732, v852, v1045, v1263, v1515] (.node [v240, v565, v732, v852, v1045, v1090, v1315] .nil .nil) .nil) (.node [v240, v565, v732, v852, v1045, v1315, v1557] .nil .nil)))) (.node [v254, v565, v732, v852, v1315, v1484, v1515] (.node [v245, v565, v732, v852, v1045, v1315, v1515] (.node [v240, v565, v732, v852, v1315, v1492, v1515] (.node [v240, v565, v732, v852, v1144, v1315, v1515] (.node [v240, v565, v732, v852, v1045, v1484, v1515] .nil .nil) .nil) (.node [v243, v565, v732, v852, v1045, v1315, v1515] (.node [v240, v565, v732, v852, v1315, v1515, v1642] .nil .nil) .nil)) (.node [v251, v565, v732, v852, v1315, v1515] (.node [v251, v565, v732, v852, v1315, v1458, v1515] (.node [v251, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v254, v565, v732, v852, v1045, v1315, v1515] .nil .nil))) (.node [v255, v565, v623, v732, v852, v1315, v1515] (.node [v255, v450, v565, v732, v852, v1045, v1315] (.node [v255, v358, v565, v732, v852, v1045, v1315] (.node [v254, v565, v732, v852, v1315, v1515] .nil .nil) .nil) (.node [v255, v549, v565, v732, v852, v1045, v1315] .nil .nil)) (.node [v255, v565, v732, v852, v957, v1045, v1515] (.node [v255, v565, v732, v809, v852, v1315, v1515] (.node [v255, v565, v689, v732, v852, v1315, v1515] .nil .nil) .nil) (.node [v255, v565, v732, v852, v993, v1045, v1315] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlll_ok : everyKey (rowOK 5 level5) level6lrlll = true := by decide +kernel
def level6lrllr : BinaryTree (List W) := (.node [v272, v565, v732, v852, v1045, v1315, v1515] (.node [v263, v565, v732, v852, v1315, v1515, v1623] (.node [v255, v565, v732, v852, v1315, v1492, v1515] (.node [v255, v565, v732, v852, v1045, v1315, v1637] (.node [v255, v565, v732, v852, v1045, v1315, v1623] (.node [v255, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v255, v565, v732, v852, v1144, v1315, v1515] (.node [v255, v565, v732, v852, v1045, v1365, v1515] .nil .nil) .nil)) (.node [v263, v565, v732, v852, v1045, v1315, v1515] (.node [v258, v565, v732, v852, v1045, v1315, v1515] (.node [v255, v565, v732, v852, v1315, v1515, v1642] .nil .nil) .nil) (.node [v263, v565, v732, v852, v1315, v1515] .nil .nil))) (.node [v270, v565, v732, v852, v1315, v1515] (.node [v265, v565, v732, v852, v1315, v1515, v1637] (.node [v265, v565, v732, v852, v1315, v1515] (.node [v265, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v270, v565, v732, v852, v1045, v1315, v1515] (.node [v266, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil)) (.node [v271, v565, v732, v852, v1315, v1515] (.node [v271, v565, v732, v852, v1045, v1315, v1515] (.node [v270, v565, v732, v852, v1315, v1515, v1654] .nil .nil) .nil) (.node [v271, v565, v732, v852, v1315, v1515, v1655] .nil .nil)))) (.node [v313, v565, v732, v852, v1045, v1315, v1515] (.node [v308, v565, v732, v852, v1045, v1315, v1515] (.node [v297, v565, v732, v852, v1045, v1315, v1515] (.node [v296, v565, v732, v852, v1045, v1315, v1515] (.node [v289, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v299, v565, v732, v852, v1045, v1315, v1515] (.node [v298, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil)) (.node [v311, v565, v732, v852, v1045, v1315, v1515] (.node [v310, v565, v732, v852, v1045, v1315, v1515] (.node [v309, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v312, v565, v732, v852, v1045, v1315, v1515] .nil .nil))) (.node [v315, v407, v565, v1045, v1315, v1515] (.node [v315, v407, v565, v732, v1045, v1315, v1515] (.node [v315, v361, v565, v732, v1045, v1315, v1515] (.node [v314, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v315, v407, v565, v852, v1045, v1315, v1515] .nil .nil)) (.node [v315, v565, v653, v852, v1045, v1315, v1515] (.node [v315, v565, v643, v852, v1045, v1315, v1515] (.node [v315, v408, v565, v732, v1045, v1315, v1515] .nil .nil) .nil) (.node [v315, v565, v732, v852, v891, v1315, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrllr_ok : everyKey (rowOK 5 level5) level6lrllr = true := by decide +kernel
def level6lrll : BinaryTree (List W) := .node [v255, v565, v732, v852, v1045, v1263, v1315] level6lrlll level6lrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrll_ok : everyKey (rowOK 5 level5) level6lrll = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrlll && everyKey (rowOK 5 level5) level6lrllr) = true
  rw [level6lrlll_ok, level6lrllr_ok]
  decide +kernel
def level6lrlrl : BinaryTree (List W) := (.node [v316, v732, v852, v1045, v1315, v1515, v1654] (.node [v316, v565, v653, v852, v1045, v1315, v1515] (.node [v315, v565, v732, v945, v1045, v1315, v1515] (.node [v315, v565, v732, v852, v1045, v1315, v1568] (.node [v315, v565, v732, v852, v1045, v1315, v1515] (.node [v315, v565, v732, v852, v913, v1045, v1315] .nil .nil) .nil) (.node [v315, v565, v732, v852, v1109, v1315, v1515] (.node [v315, v565, v732, v852, v1045, v1377, v1515] .nil .nil) .nil)) (.node [v316, v453, v732, v852, v1045, v1315, v1515] (.node [v316, v407, v565, v852, v1045, v1315, v1515] (.node [v315, v565, v852, v1045, v1315, v1515, v1654] .nil .nil) .nil) (.node [v316, v565, v643, v852, v1045, v1315, v1515] .nil .nil))) (.node [v316, v565, v732, v852, v1045, v1315, v1569] (.node [v316, v565, v732, v852, v905, v1045, v1515] (.node [v316, v565, v732, v852, v892, v1315, v1515] (.node [v316, v565, v732, v844, v1045, v1315, v1515] .nil .nil) .nil) (.node [v316, v565, v732, v852, v1045, v1315, v1515] (.node [v316, v565, v732, v852, v914, v1045, v1315] .nil .nil) .nil)) (.node [v316, v565, v732, v944, v1045, v1315, v1515] (.node [v316, v565, v732, v852, v1110, v1315, v1515] (.node [v316, v565, v732, v852, v1045, v1378, v1515] .nil .nil) .nil) (.node [v316, v565, v852, v1045, v1315, v1515, v1654] .nil .nil)))) (.node [v326, v565, v732, v852, v1045, v1315, v1515] (.node [v321, v565, v732, v852, v1045, v1315, v1515] (.node [v318, v565, v732, v852, v1045, v1315, v1515] (.node [v317, v565, v732, v852, v1045, v1315, v1515] (.node [v316, v852, v1045, v1315, v1515, v1654] .nil .nil) .nil) (.node [v320, v565, v732, v852, v1045, v1315, v1515] (.node [v319, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil)) (.node [v324, v565, v732, v852, v1045, v1315, v1515] (.node [v323, v565, v732, v852, v1045, v1315, v1515] (.node [v322, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v325, v565, v732, v852, v1045, v1315, v1515] .nil .nil))) (.node [v332, v565, v689, v732, v852, v1315, v1515] (.node [v331, v565, v732, v852, v1045, v1315, v1515] (.node [v330, v565, v732, v852, v1045, v1315, v1515] (.node [v327, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v332, v565, v623, v732, v852, v1315, v1515] .nil .nil)) (.node [v332, v565, v732, v852, v1144, v1315, v1515] (.node [v332, v565, v732, v852, v1045, v1315, v1515] (.node [v332, v565, v732, v809, v852, v1315, v1515] .nil .nil) .nil) (.node [v332, v565, v732, v852, v1315, v1492, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlrl_ok : everyKey (rowOK 5 level5) level6lrlrl = true := by decide +kernel
def level6lrlrr : BinaryTree (List W) := (.node [v357, v565, v732, v852, v1045, v1315, v1515] (.node [v349, v565, v701, v732, v852, v1045, v1515] (.node [v344, v565, v732, v852, v1045, v1315, v1515] (.node [v338, v565, v732, v852, v1045, v1315, v1515] (.node [v338, v565, v732, v832, v852, v1315, v1515] (.node [v332, v565, v732, v1045, v1260, v1315, v1515] .nil .nil) .nil) (.node [v344, v565, v732, v821, v852, v1315, v1515] (.node [v338, v565, v732, v852, v1315, v1515] .nil .nil) .nil)) (.node [v348, v565, v732, v852, v1045, v1315, v1515] (.node [v347, v565, v732, v852, v1045, v1315, v1515] (.node [v344, v565, v732, v852, v1315, v1515] .nil .nil) .nil) (.node [v349, v565, v631, v732, v852, v1045, v1515] .nil .nil))) (.node [v349, v565, v732, v1045, v1315, v1484, v1515] (.node [v349, v565, v732, v852, v1045, v1407, v1515] (.node [v349, v565, v732, v852, v1045, v1315, v1515] (.node [v349, v565, v732, v821, v852, v1045, v1515] .nil .nil) .nil) (.node [v349, v565, v732, v852, v1045, v1515, v1648] (.node [v349, v565, v732, v852, v1045, v1492, v1515] .nil .nil) .nil)) (.node [v355, v565, v732, v852, v1045, v1515] (.node [v355, v565, v732, v852, v1045, v1315, v1515] (.node [v355, v565, v732, v832, v852, v1045, v1515] .nil .nil) .nil) (.node [v356, v565, v732, v852, v1045, v1315, v1515] .nil .nil)))) (.node [v361, v408, v732, v852, v1045, v1315, v1515] (.node [v358, v565, v732, v852, v1045, v1315, v1642] (.node [v358, v565, v732, v832, v852, v1045, v1315] (.node [v358, v565, v712, v732, v852, v1045, v1315] (.node [v358, v565, v638, v732, v852, v1045, v1315] .nil .nil) .nil) (.node [v358, v565, v732, v852, v1045, v1315, v1593] (.node [v358, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil)) (.node [v359, v565, v732, v852, v1045, v1315, v1515] (.node [v358, v565, v732, v1045, v1315, v1515, v1637] (.node [v358, v565, v732, v852, v1045, v1315, v1648] .nil .nil) .nil) (.node [v360, v565, v732, v852, v1045, v1315, v1515] .nil .nil))) (.node [v361, v644, v732, v852, v1045, v1315, v1515] (.node [v361, v565, v732, v852, v1045, v1315, v1515] (.node [v361, v565, v653, v732, v1045, v1315, v1515] (.node [v361, v565, v644, v732, v1045, v1315, v1515] .nil .nil) .nil) (.node [v361, v565, v732, v1045, v1315, v1515, v1655] .nil .nil)) (.node [v362, v565, v732, v1045, v1315, v1515] (.node [v362, v565, v732, v852, v1045, v1315, v1515] (.node [v361, v644, v732, v1045, v1315, v1515] .nil .nil) .nil) (.node [v362, v565, v732, v1045, v1315, v1515, v1654] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlrr_ok : everyKey (rowOK 5 level5) level6lrlrr = true := by decide +kernel
def level6lrlr : BinaryTree (List W) := .node [v332, v565, v732, v852, v1315, v1515, v1642] level6lrlrl level6lrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlr_ok : everyKey (rowOK 5 level5) level6lrlr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrlrl && everyKey (rowOK 5 level5) level6lrlrr) = true
  rw [level6lrlrl_ok, level6lrlrr_ok]
  decide +kernel
def level6lrl : BinaryTree (List W) := .node [v315, v565, v732, v852, v904, v1045, v1515] level6lrll level6lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrl_ok : everyKey (rowOK 5 level5) level6lrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrll && everyKey (rowOK 5 level5) level6lrlr) = true
  rw [level6lrll_ok, level6lrlr_ok]
  decide +kernel
def level6lrrll : BinaryTree (List W) := (.node [v403, v565, v732, v852, v1045, v1315, v1515] (.node [v382, v565, v732, v852, v1045, v1315, v1515] (.node [v370, v565, v732, v852, v1045, v1315, v1515] (.node [v366, v565, v732, v852, v1045, v1315, v1515] (.node [v365, v565, v732, v852, v1045, v1315, v1515] (.node [v364, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v368, v565, v732, v852, v1045, v1315, v1515] (.node [v367, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil)) (.node [v382, v565, v732, v821, v852, v1045, v1315] (.node [v375, v565, v732, v852, v1045, v1315, v1515] (.node [v371, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v382, v565, v732, v852, v1045, v1315] .nil .nil))) (.node [v398, v565, v732, v852, v1045, v1315] (.node [v394, v565, v732, v852, v1045, v1315, v1515] (.node [v394, v565, v732, v809, v852, v1045, v1515] (.node [v383, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v398, v565, v732, v809, v852, v1045, v1315] (.node [v394, v565, v732, v852, v1045, v1515] .nil .nil) .nil)) (.node [v401, v565, v732, v852, v1045, v1315, v1515] (.node [v400, v565, v732, v852, v1045, v1315, v1515] (.node [v398, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v402, v565, v732, v852, v1045, v1315, v1515] .nil .nil)))) (.node [v407, v565, v732, v852, v1045, v1315, v1581] (.node [v407, v565, v653, v732, v1045, v1315, v1515] (.node [v406, v565, v732, v852, v1045, v1315, v1515] (.node [v405, v565, v732, v852, v1045, v1315, v1515] (.node [v404, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v407, v565, v644, v732, v1045, v1315, v1515] (.node [v407, v453, v565, v852, v1045, v1315, v1515] .nil .nil) .nil)) (.node [v407, v565, v732, v792, v852, v1045, v1315] (.node [v407, v565, v732, v783, v852, v1045, v1515] (.node [v407, v565, v732, v770, v852, v1315, v1515] .nil .nil) .nil) (.node [v407, v565, v732, v852, v1045, v1315, v1515] .nil .nil))) (.node [v408, v565, v644, v732, v1045, v1315, v1515] (.node [v407, v565, v732, v1045, v1315, v1515, v1655] (.node [v407, v565, v732, v852, v1126, v1315, v1515] (.node [v407, v565, v732, v852, v1045, v1392, v1515] .nil .nil) .nil) (.node [v407, v565, v852, v945, v1045, v1315, v1515] .nil .nil)) (.node [v408, v565, v732, v772, v852, v1315, v1515] (.node [v408, v565, v724, v852, v1045, v1315, v1515] (.node [v408, v565, v653, v732, v1045, v1315, v1515] .nil .nil) .nil) (.node [v408, v565, v732, v785, v852, v1045, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrll_ok : everyKey (rowOK 5 level5) level6lrrll = true := by decide +kernel
def level6lrrlr : BinaryTree (List W) := (.node [v424, v565, v623, v732, v852, v1315, v1515] (.node [v411, v565, v732, v852, v1045, v1315, v1515] (.node [v408, v565, v852, v943, v1045, v1315, v1515] (.node [v408, v565, v732, v852, v1045, v1393, v1515] (.node [v408, v565, v732, v852, v1045, v1315, v1582] (.node [v408, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v408, v565, v732, v1045, v1315, v1515, v1655] (.node [v408, v565, v732, v852, v1127, v1315, v1515] .nil .nil) .nil)) (.node [v409, v565, v732, v852, v1045, v1315, v1515] (.node [v408, v732, v1045, v1315, v1515, v1655] (.node [v408, v732, v852, v1045, v1315, v1515, v1655] .nil .nil) .nil) (.node [v410, v565, v732, v852, v1045, v1315, v1515] .nil .nil))) (.node [v417, v565, v732, v852, v1045, v1315, v1515] (.node [v414, v565, v732, v852, v1045, v1315, v1515] (.node [v413, v565, v732, v852, v1045, v1315, v1515] (.node [v412, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v416, v565, v732, v852, v1045, v1315, v1515] (.node [v415, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil)) (.node [v422, v565, v732, v852, v1045, v1315, v1515] (.node [v419, v565, v732, v852, v1045, v1315, v1515] (.node [v418, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v423, v565, v732, v852, v1045, v1315, v1515] .nil .nil)))) (.node [v436, v565, v701, v732, v852, v1315, v1515] (.node [v424, v565, v732, v852, v1315, v1515, v1642] (.node [v424, v565, v732, v852, v1045, v1315, v1515] (.node [v424, v565, v732, v809, v852, v1315, v1515] (.node [v424, v565, v689, v732, v852, v1315, v1515] .nil .nil) .nil) (.node [v424, v565, v732, v852, v1315, v1492, v1515] (.node [v424, v565, v732, v852, v1144, v1315, v1515] .nil .nil) .nil)) (.node [v430, v565, v732, v852, v1045, v1315, v1515] (.node [v430, v565, v712, v732, v852, v1315, v1515] (.node [v424, v565, v852, v1045, v1220, v1315, v1515] .nil .nil) .nil) (.node [v430, v565, v732, v852, v1315, v1515] .nil .nil))) (.node [v441, v565, v631, v732, v852, v1045, v1515] (.node [v439, v565, v732, v852, v1045, v1315, v1515] (.node [v436, v565, v732, v852, v1315, v1515] (.node [v436, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v440, v565, v732, v852, v1045, v1315, v1515] .nil .nil)) (.node [v441, v565, v732, v852, v1045, v1315, v1515] (.node [v441, v565, v732, v821, v852, v1045, v1515] (.node [v441, v565, v701, v732, v852, v1045, v1515] .nil .nil) .nil) (.node [v441, v565, v732, v852, v1045, v1407, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrlr_ok : everyKey (rowOK 5 level5) level6lrrlr = true := by decide +kernel
def level6lrrl : BinaryTree (List W) := .node [v408, v565, v732, v794, v852, v1045, v1315] level6lrrll level6lrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrl_ok : everyKey (rowOK 5 level5) level6lrrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrrll && everyKey (rowOK 5 level5) level6lrrlr) = true
  rw [level6lrrll_ok, level6lrrlr_ok]
  decide +kernel
def level6lrrrl : BinaryTree (List W) := (.node [v453, v643, v732, v852, v1045, v1315, v1515] (.node [v450, v565, v732, v852, v1045, v1315, v1515] (.node [v448, v565, v732, v852, v1045, v1315, v1515] (.node [v447, v565, v712, v732, v852, v1045, v1515] (.node [v441, v565, v852, v1045, v1315, v1458, v1515] (.node [v441, v565, v732, v852, v1045, v1515, v1648] .nil .nil) .nil) (.node [v447, v565, v732, v852, v1045, v1515] (.node [v447, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil)) (.node [v450, v565, v712, v732, v852, v1045, v1315] (.node [v450, v565, v638, v732, v852, v1045, v1315] (.node [v449, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v450, v565, v732, v832, v852, v1045, v1315] .nil .nil))) (.node [v452, v565, v732, v852, v1045, v1315, v1515] (.node [v450, v565, v732, v852, v1045, v1315, v1648] (.node [v450, v565, v732, v852, v1045, v1315, v1642] (.node [v450, v565, v732, v852, v1045, v1315, v1593] .nil .nil) .nil) (.node [v451, v565, v732, v852, v1045, v1315, v1515] (.node [v450, v565, v852, v1045, v1315, v1515, v1623] .nil .nil) .nil)) (.node [v453, v565, v732, v852, v1045, v1315, v1515] (.node [v453, v565, v653, v852, v1045, v1315, v1515] (.node [v453, v565, v643, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v453, v565, v852, v1045, v1315, v1515, v1654] .nil .nil)))) (.node [v462, v565, v732, v852, v1045, v1315, v1515] (.node [v456, v565, v732, v852, v1045, v1315, v1515] (.node [v454, v565, v852, v1045, v1315, v1515] (.node [v454, v565, v732, v852, v1045, v1315, v1515] (.node [v453, v643, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v455, v565, v732, v852, v1045, v1315, v1515] (.node [v454, v565, v852, v1045, v1315, v1515, v1655] .nil .nil) .nil)) (.node [v459, v565, v732, v852, v1045, v1315, v1515] (.node [v458, v565, v732, v852, v1045, v1315, v1515] (.node [v457, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v460, v565, v732, v852, v1045, v1315, v1515] .nil .nil))) (.node [v474, v565, v732, v852, v1045, v1315, v1515] (.node [v474, v565, v701, v732, v852, v1045, v1315] (.node [v467, v565, v732, v852, v1045, v1315, v1515] (.node [v463, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v474, v565, v732, v852, v1045, v1315] .nil .nil)) (.node [v486, v565, v732, v852, v1045, v1315, v1515] (.node [v486, v565, v689, v732, v852, v1045, v1515] (.node [v475, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v486, v565, v732, v852, v1045, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrrl_ok : everyKey (rowOK 5 level5) level6lrrrl = true := by decide +kernel
def level6lrrrr : BinaryTree (List W) := (.node [v510, v565, v732, v852, v1315, v1515] (.node [v501, v565, v732, v852, v1315, v1492, v1515] (.node [v501, v565, v623, v732, v852, v1315, v1515] (.node [v493, v565, v732, v852, v1045, v1315, v1515] (.node [v490, v565, v732, v852, v1045, v1315, v1515] (.node [v490, v565, v732, v852, v1045, v1315] .nil .nil) .nil) (.node [v500, v565, v732, v852, v1045, v1315, v1515] (.node [v497, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil)) (.node [v501, v565, v732, v852, v1045, v1315, v1515] (.node [v501, v565, v732, v809, v852, v1315, v1515] (.node [v501, v565, v689, v732, v852, v1315, v1515] .nil .nil) .nil) (.node [v501, v565, v732, v852, v1144, v1315, v1515] .nil .nil))) (.node [v503, v565, v732, v852, v1045, v1315, v1515] (.node [v501, v732, v852, v1144, v1315, v1515] (.node [v501, v732, v852, v1045, v1144, v1315, v1515] (.node [v501, v565, v732, v852, v1315, v1515, v1642] .nil .nil) .nil) (.node [v502, v565, v732, v852, v1045, v1315, v1515] .nil .nil)) (.node [v510, v565, v638, v732, v852, v1315, v1515] (.node [v506, v565, v732, v852, v1045, v1315, v1515] (.node [v504, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v510, v565, v732, v852, v1045, v1315, v1515] .nil .nil)))) (.node [v530, v565, v701, v732, v852, v1045, v1515] (.node [v526, v565, v732, v852, v1045, v1315, v1515] (.node [v519, v565, v732, v852, v1045, v1315, v1515] (.node [v519, v565, v631, v732, v852, v1315, v1515] (.node [v514, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v525, v565, v732, v852, v1045, v1315, v1515] (.node [v519, v565, v732, v852, v1315, v1515] .nil .nil) .nil)) (.node [v529, v565, v732, v852, v1045, v1315, v1515] (.node [v528, v565, v732, v852, v1045, v1315, v1515] (.node [v527, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v530, v565, v631, v732, v852, v1045, v1515] .nil .nil))) (.node [v530, v565, v732, v852, v1045, v1515, v1648] (.node [v530, v565, v732, v852, v1045, v1407, v1515] (.node [v530, v565, v732, v852, v1045, v1315, v1515] (.node [v530, v565, v732, v821, v852, v1045, v1515] .nil .nil) .nil) (.node [v530, v565, v732, v852, v1045, v1492, v1515] .nil .nil)) (.node [v531, v565, v732, v852, v1045, v1315, v1515] (.node [v530, v732, v852, v1045, v1407, v1515] (.node [v530, v732, v852, v1045, v1315, v1407, v1515] .nil .nil) .nil) (.node [v532, v565, v732, v852, v1045, v1315, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrrr_ok : everyKey (rowOK 5 level5) level6lrrrr = true := by decide +kernel
def level6lrrr : BinaryTree (List W) := .node [v490, v565, v689, v732, v852, v1045, v1315] level6lrrrl level6lrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrr_ok : everyKey (rowOK 5 level5) level6lrrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrrrl && everyKey (rowOK 5 level5) level6lrrrr) = true
  rw [level6lrrrl_ok, level6lrrrr_ok]
  decide +kernel
def level6lrr : BinaryTree (List W) := .node [v441, v565, v732, v852, v1045, v1492, v1515] level6lrrl level6lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrr_ok : everyKey (rowOK 5 level5) level6lrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrrl && everyKey (rowOK 5 level5) level6lrrr) = true
  rw [level6lrrl_ok, level6lrrr_ok]
  decide +kernel
def level6lr : BinaryTree (List W) := .node [v363, v565, v732, v852, v1045, v1315, v1515] level6lrl level6lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lr_ok : everyKey (rowOK 5 level5) level6lr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrl && everyKey (rowOK 5 level5) level6lrr) = true
  rw [level6lrl_ok, level6lrr_ok]
  decide +kernel
def level6l : BinaryTree (List W) := .node [v233, v424, v565, v732, v852, v1315, v1515] level6ll level6lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6l_ok : everyKey (rowOK 5 level5) level6l = true := by
  change (_ && everyKey (rowOK 5 level5) level6ll && everyKey (rowOK 5 level5) level6lr) = true
  rw [level6ll_ok, level6lr_ok]
  decide +kernel
def level6rllll : BinaryTree (List W) := (.node [v552, v565, v732, v852, v1045, v1315, v1515] (.node [v549, v565, v638, v732, v852, v1045, v1315] (.node [v544, v565, v732, v852, v1045, v1315, v1515] (.node [v539, v565, v732, v852, v1045, v1315, v1515] (.node [v539, v565, v638, v732, v852, v1045, v1515] (.node [v534, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v543, v565, v732, v852, v1045, v1315, v1515] (.node [v539, v565, v732, v852, v1045, v1515] .nil .nil) .nil)) (.node [v547, v565, v732, v852, v1045, v1315, v1515] (.node [v546, v565, v732, v852, v1045, v1315, v1515] (.node [v545, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v548, v565, v732, v852, v1045, v1315, v1515] .nil .nil))) (.node [v549, v565, v732, v852, v1045, v1315, v1648] (.node [v549, v565, v732, v852, v1045, v1315, v1515] (.node [v549, v565, v732, v832, v852, v1045, v1315] (.node [v549, v565, v712, v732, v852, v1045, v1315] .nil .nil) .nil) (.node [v549, v565, v732, v852, v1045, v1315, v1642] (.node [v549, v565, v732, v852, v1045, v1315, v1593] .nil .nil) .nil)) (.node [v550, v565, v732, v852, v1045, v1315, v1515] (.node [v549, v732, v852, v1045, v1315, v1593] (.node [v549, v732, v852, v1045, v1315, v1515, v1593] .nil .nil) .nil) (.node [v551, v565, v732, v852, v1045, v1315, v1515] .nil .nil)))) (.node [v565, v566, v732, v852, v1045, v1315, v1515] (.node [v558, v565, v732, v852, v1045, v1315, v1515] (.node [v555, v565, v732, v852, v1045, v1315, v1515] (.node [v554, v565, v732, v852, v1045, v1315, v1515] (.node [v553, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v557, v565, v732, v852, v1045, v1315, v1515] (.node [v556, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil)) (.node [v561, v565, v732, v852, v1045, v1315, v1515] (.node [v560, v565, v732, v852, v1045, v1315, v1515] (.node [v559, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v565, v732, v852, v1045, v1315, v1515] .nil .nil))) (.node [v565, v571, v732, v852, v1045, v1315, v1515] (.node [v565, v569, v732, v852, v1045, v1315, v1515] (.node [v565, v568, v732, v852, v1045, v1315, v1515] (.node [v565, v567, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v570, v732, v852, v1045, v1315, v1515] .nil .nil)) (.node [v565, v576, v732, v852, v1045, v1315, v1515] (.node [v565, v573, v732, v852, v1045, v1315, v1515] (.node [v565, v572, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v577, v732, v852, v1045, v1315, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllll_ok : everyKey (rowOK 5 level5) level6rllll = true := by decide +kernel
def level6rlllr : BinaryTree (List W) := (.node [v565, v621, v732, v852, v1045, v1315, v1515] (.node [v565, v601, v732, v852, v1045, v1515] (.node [v565, v591, v732, v852, v1045, v1315, v1515] (.node [v565, v587, v631, v732, v852, v1045, v1315] (.node [v565, v584, v732, v852, v1045, v1315, v1515] (.node [v565, v579, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v587, v732, v852, v1045, v1315, v1515] (.node [v565, v587, v732, v852, v1045, v1315] .nil .nil) .nil)) (.node [v565, v601, v623, v732, v852, v1045, v1515] (.node [v565, v593, v732, v852, v1045, v1315, v1515] (.node [v565, v592, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v601, v732, v852, v1045, v1315, v1515] .nil .nil))) (.node [v565, v615, v732, v852, v1045, v1315, v1515] (.node [v565, v610, v732, v852, v1045, v1315] (.node [v565, v610, v623, v732, v852, v1045, v1315] (.node [v565, v607, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v614, v732, v852, v1045, v1315, v1515] (.node [v565, v610, v732, v852, v1045, v1315, v1515] .nil .nil) .nil)) (.node [v565, v619, v732, v852, v1045, v1315, v1515] (.node [v565, v618, v732, v852, v1045, v1315, v1515] (.node [v565, v616, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v620, v732, v852, v1045, v1315, v1515] .nil .nil)))) (.node [v565, v627, v732, v852, v1045, v1315, v1515] (.node [v565, v623, v732, v852, v1045, v1413, v1515] (.node [v565, v623, v732, v852, v993, v1315, v1515] (.node [v565, v623, v732, v852, v949, v1315, v1515] (.node [v565, v622, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v623, v732, v852, v1045, v1315, v1598] (.node [v565, v623, v732, v852, v1045, v1315, v1515] .nil .nil) .nil)) (.node [v565, v624, v732, v852, v1045, v1315, v1515] (.node [v565, v623, v732, v852, v1260, v1315, v1515] (.node [v565, v623, v732, v852, v1220, v1315, v1515] .nil .nil) .nil) (.node [v565, v625, v732, v852, v1045, v1315, v1515] .nil .nil))) (.node [v565, v631, v732, v852, v1045, v1263, v1515] (.node [v565, v630, v732, v852, v1045, v1315, v1515] (.node [v565, v629, v732, v852, v1045, v1315, v1515] (.node [v565, v628, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v631, v732, v852, v949, v1045, v1515] .nil .nil)) (.node [v565, v631, v732, v852, v1045, v1458, v1515] (.node [v565, v631, v732, v852, v1045, v1315, v1604] (.node [v565, v631, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v631, v732, v852, v1045, v1484, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlllr_ok : everyKey (rowOK 5 level5) level6rlllr = true := by decide +kernel
def level6rlll : BinaryTree (List W) := .node [v565, v578, v732, v852, v1045, v1315, v1515] level6rllll level6rlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlll_ok : everyKey (rowOK 5 level5) level6rlll = true := by
  change (_ && everyKey (rowOK 5 level5) level6rllll && everyKey (rowOK 5 level5) level6rlllr) = true
  rw [level6rllll_ok, level6rlllr_ok]
  decide +kernel
def level6rllrl : BinaryTree (List W) := (.node [v565, v647, v732, v852, v1045, v1315, v1515] (.node [v565, v638, v732, v852, v1045, v1427, v1515] (.node [v565, v638, v732, v852, v993, v1045, v1315] (.node [v565, v635, v732, v852, v1045, v1315, v1515] (.node [v565, v634, v732, v852, v1045, v1315, v1515] (.node [v565, v632, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v637, v732, v852, v1045, v1315, v1515] (.node [v565, v636, v732, v852, v1045, v1315, v1515] .nil .nil) .nil)) (.node [v565, v638, v732, v852, v1045, v1315, v1623] (.node [v565, v638, v732, v852, v1045, v1315, v1515] (.node [v565, v638, v732, v852, v1045, v1263, v1315] .nil .nil) .nil) (.node [v565, v638, v732, v852, v1045, v1315, v1637] .nil .nil))) (.node [v565, v643, v852, v945, v1045, v1315, v1515] (.node [v565, v641, v732, v852, v1045, v1315, v1515] (.node [v565, v640, v732, v852, v1045, v1315, v1515] (.node [v565, v638, v732, v852, v1175, v1315, v1515] .nil .nil) .nil) (.node [v565, v643, v732, v852, v1045, v1315, v1515] (.node [v565, v642, v732, v852, v1045, v1315, v1515] .nil .nil) .nil)) (.node [v565, v645, v732, v852, v1045, v1315, v1515] (.node [v565, v644, v732, v945, v1045, v1315, v1515] (.node [v565, v644, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v646, v732, v852, v1045, v1315, v1515] .nil .nil)))) (.node [v565, v656, v732, v852, v1045, v1315, v1515] (.node [v565, v653, v732, v945, v1045, v1315, v1515] (.node [v565, v650, v732, v852, v1045, v1315, v1515] (.node [v565, v649, v732, v852, v1045, v1315, v1515] (.node [v565, v648, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v653, v732, v852, v1045, v1315, v1515] (.node [v565, v651, v732, v852, v1045, v1315, v1515] .nil .nil) .nil)) (.node [v565, v654, v732, v852, v1045, v1315, v1515] (.node [v565, v653, v945, v1045, v1315, v1515] (.node [v565, v653, v852, v945, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v655, v732, v852, v1045, v1315, v1515] .nil .nil))) (.node [v565, v663, v732, v852, v1045, v1315, v1515] (.node [v565, v659, v732, v852, v1045, v1315, v1515] (.node [v565, v658, v732, v852, v1045, v1315, v1515] (.node [v565, v657, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v662, v732, v852, v1045, v1315, v1515] .nil .nil)) (.node [v565, v667, v732, v852, v1045, v1315, v1515] (.node [v565, v665, v732, v852, v1045, v1315, v1515] (.node [v565, v664, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v670, v732, v852, v1045, v1315, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllrl_ok : everyKey (rowOK 5 level5) level6rllrl = true := by decide +kernel
def level6rllrr : BinaryTree (List W) := (.node [v565, v696, v732, v852, v1045, v1315, v1515] (.node [v565, v689, v732, v852, v1045, v1436, v1515] (.node [v565, v688, v732, v852, v1045, v1315, v1515] (.node [v565, v674, v732, v852, v1045, v1315, v1515] (.node [v565, v673, v732, v852, v1045, v1315, v1515] (.node [v565, v672, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v687, v732, v852, v1045, v1315, v1515] (.node [v565, v676, v732, v852, v1045, v1315, v1515] .nil .nil) .nil)) (.node [v565, v689, v732, v852, v1045, v1315, v1515] (.node [v565, v689, v732, v852, v993, v1315, v1515] (.node [v565, v689, v732, v852, v949, v1315, v1515] .nil .nil) .nil) (.node [v565, v689, v732, v852, v1045, v1315, v1612] .nil .nil))) (.node [v565, v691, v732, v852, v1045, v1315, v1515] (.node [v565, v689, v852, v1045, v1220, v1315, v1515] (.node [v565, v689, v732, v852, v1260, v1315, v1515] (.node [v565, v689, v732, v852, v1220, v1315, v1515] .nil .nil) .nil) (.node [v565, v690, v732, v852, v1045, v1315, v1515] (.node [v565, v689, v852, v1220, v1315, v1515] .nil .nil) .nil)) (.node [v565, v694, v732, v852, v1045, v1315, v1515] (.node [v565, v693, v732, v852, v1045, v1315, v1515] (.node [v565, v692, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v695, v732, v852, v1045, v1315, v1515] .nil .nil)))) (.node [v565, v701, v852, v1045, v1315, v1458, v1515] (.node [v565, v701, v732, v852, v1045, v1315, v1515] (.node [v565, v700, v732, v852, v1045, v1315, v1515] (.node [v565, v699, v732, v852, v1045, v1315, v1515] (.node [v565, v698, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v701, v732, v852, v1045, v1263, v1515] (.node [v565, v701, v732, v852, v949, v1045, v1515] .nil .nil) .nil)) (.node [v565, v701, v732, v852, v1045, v1484, v1515] (.node [v565, v701, v732, v852, v1045, v1458, v1515] (.node [v565, v701, v732, v852, v1045, v1315, v1617] .nil .nil) .nil) (.node [v565, v701, v732, v852, v1198, v1315, v1515] .nil .nil))) (.node [v565, v705, v732, v852, v1045, v1315, v1515] (.node [v565, v703, v732, v852, v1045, v1315, v1515] (.node [v565, v702, v732, v852, v1045, v1315, v1515] (.node [v565, v701, v852, v1045, v1458, v1515] .nil .nil) .nil) (.node [v565, v704, v732, v852, v1045, v1315, v1515] .nil .nil)) (.node [v565, v709, v732, v852, v1045, v1315, v1515] (.node [v565, v707, v732, v852, v1045, v1315, v1515] (.node [v565, v706, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v710, v732, v852, v1045, v1315, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllrr_ok : everyKey (rowOK 5 level5) level6rllrr = true := by decide +kernel
def level6rllr : BinaryTree (List W) := .node [v565, v671, v732, v852, v1045, v1315, v1515] level6rllrl level6rllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllr_ok : everyKey (rowOK 5 level5) level6rllr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rllrl && everyKey (rowOK 5 level5) level6rllrr) = true
  rw [level6rllrl_ok, level6rllrr_ok]
  decide +kernel
def level6rll : BinaryTree (List W) := .node [v565, v631, v732, v852, v1161, v1315, v1515] level6rlll level6rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rll_ok : everyKey (rowOK 5 level5) level6rll = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlll && everyKey (rowOK 5 level5) level6rllr) = true
  rw [level6rlll_ok, level6rllr_ok]
  decide +kernel
def level6rlrll : BinaryTree (List W) := (.node [v565, v725, v852, v1045, v1315, v1515] (.node [v565, v714, v732, v852, v1045, v1315, v1515] (.node [v565, v712, v732, v852, v1045, v1452, v1515] (.node [v565, v712, v732, v852, v1045, v1315, v1515] (.node [v565, v712, v732, v852, v1045, v1263, v1315] (.node [v565, v712, v732, v852, v993, v1045, v1315] .nil .nil) .nil) (.node [v565, v712, v732, v852, v1045, v1315, v1637] (.node [v565, v712, v732, v852, v1045, v1315, v1623] .nil .nil) .nil)) (.node [v565, v712, v852, v1045, v1315, v1623] (.node [v565, v712, v852, v1045, v1315, v1515, v1623] (.node [v565, v712, v732, v852, v1214, v1315, v1515] .nil .nil) .nil) (.node [v565, v713, v732, v852, v1045, v1315, v1515] .nil .nil))) (.node [v565, v721, v732, v852, v1045, v1315, v1515] (.node [v565, v717, v732, v852, v1045, v1315, v1515] (.node [v565, v716, v732, v852, v1045, v1315, v1515] (.node [v565, v715, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v720, v732, v852, v1045, v1315, v1515] (.node [v565, v719, v732, v852, v1045, v1315, v1515] .nil .nil) .nil)) (.node [v565, v724, v852, v1045, v1315, v1515] (.node [v565, v724, v732, v852, v1045, v1315, v1515] (.node [v565, v722, v732, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v725, v732, v852, v1045, v1315, v1515] .nil .nil)))) (.node [v565, v732, v746, v852, v1045, v1315, v1515] (.node [v565, v732, v737, v852, v1045, v1315, v1515] (.node [v565, v732, v734, v852, v1045, v1315, v1515] (.node [v565, v732, v732, v852, v1045, v1315, v1515] (.node [v565, v725, v852, v1045, v1315, v1515, v1655] .nil .nil) .nil) (.node [v565, v732, v736, v852, v1045, v1315, v1515] (.node [v565, v732, v735, v852, v1045, v1315, v1515] .nil .nil) .nil)) (.node [v565, v732, v743, v852, v1045, v1315, v1515] (.node [v565, v732, v741, v852, v1045, v1315, v1515] (.node [v565, v732, v739, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v744, v852, v1045, v1315, v1515] .nil .nil))) (.node [v565, v732, v754, v852, v1045, v1315, v1515] (.node [v565, v732, v751, v852, v1045, v1315, v1515] (.node [v565, v732, v749, v852, v1045, v1315, v1515] (.node [v565, v732, v747, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v752, v852, v1045, v1315, v1515] .nil .nil)) (.node [v565, v732, v759, v852, v1045, v1315, v1515] (.node [v565, v732, v757, v852, v1045, v1315, v1515] (.node [v565, v732, v756, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v761, v852, v1045, v1315, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrll_ok : everyKey (rowOK 5 level5) level6rlrll = true := by decide +kernel
def level6rlrlr : BinaryTree (List W) := (.node [v565, v732, v809, v852, v1045, v1315, v1626] (.node [v565, v732, v794, v852, v1045, v1315] (.node [v565, v732, v783, v852, v1045, v1515] (.node [v565, v732, v772, v852, v1045, v1315, v1515] (.node [v565, v732, v770, v852, v1315, v1515] (.node [v565, v732, v770, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v783, v852, v1045, v1315, v1515] (.node [v565, v732, v772, v852, v1315, v1515] .nil .nil) .nil)) (.node [v565, v732, v792, v852, v1045, v1315] (.node [v565, v732, v785, v852, v1045, v1515] (.node [v565, v732, v785, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v792, v852, v1045, v1315, v1515] .nil .nil))) (.node [v565, v732, v807, v852, v1045, v1315, v1515] (.node [v565, v732, v798, v852, v1045, v1315, v1515] (.node [v565, v732, v797, v852, v1045, v1315, v1515] (.node [v565, v732, v794, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v800, v852, v1045, v1315, v1515] (.node [v565, v732, v799, v852, v1045, v1315, v1515] .nil .nil) .nil)) (.node [v565, v732, v809, v852, v993, v1315, v1515] (.node [v565, v732, v809, v852, v949, v1315, v1515] (.node [v565, v732, v808, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v809, v852, v1045, v1315, v1515] .nil .nil)))) (.node [v565, v732, v815, v852, v1045, v1315, v1515] (.node [v565, v732, v810, v852, v1045, v1315, v1515] (.node [v565, v732, v809, v852, v1260, v1315, v1515] (.node [v565, v732, v809, v852, v1220, v1315, v1515] (.node [v565, v732, v809, v852, v1045, v1462, v1515] .nil .nil) .nil) (.node [v565, v732, v809, v1260, v1315, v1515] (.node [v565, v732, v809, v1045, v1260, v1315, v1515] .nil .nil) .nil)) (.node [v565, v732, v813, v852, v1045, v1315, v1515] (.node [v565, v732, v812, v852, v1045, v1315, v1515] (.node [v565, v732, v811, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v814, v852, v1045, v1315, v1515] .nil .nil))) (.node [v565, v732, v821, v852, v949, v1045, v1515] (.node [v565, v732, v819, v852, v1045, v1315, v1515] (.node [v565, v732, v818, v852, v1045, v1315, v1515] (.node [v565, v732, v816, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v820, v852, v1045, v1315, v1515] .nil .nil)) (.node [v565, v732, v821, v852, v1045, v1315, v1631] (.node [v565, v732, v821, v852, v1045, v1315, v1515] (.node [v565, v732, v821, v852, v1045, v1263, v1515] .nil .nil) .nil) (.node [v565, v732, v821, v852, v1045, v1458, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrlr_ok : everyKey (rowOK 5 level5) level6rlrlr = true := by decide +kernel
def level6rlrl : BinaryTree (List W) := .node [v565, v732, v762, v852, v1045, v1315, v1515] level6rlrll level6rlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrl_ok : everyKey (rowOK 5 level5) level6rlrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlrll && everyKey (rowOK 5 level5) level6rlrlr) = true
  rw [level6rlrll_ok, level6rlrlr_ok]
  decide +kernel
def level6rlrrl : BinaryTree (List W) := (.node [v565, v732, v833, v852, v1045, v1315, v1515] (.node [v565, v732, v830, v852, v1045, v1315, v1515] (.node [v565, v732, v824, v852, v1045, v1315, v1515] (.node [v565, v732, v821, v1045, v1484, v1515] (.node [v565, v732, v821, v1045, v1315, v1484, v1515] (.node [v565, v732, v821, v852, v1238, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v823, v852, v1045, v1315, v1515] (.node [v565, v732, v822, v852, v1045, v1315, v1515] .nil .nil) .nil)) (.node [v565, v732, v827, v852, v1045, v1315, v1515] (.node [v565, v732, v826, v852, v1045, v1315, v1515] (.node [v565, v732, v825, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v829, v852, v1045, v1315, v1515] .nil .nil))) (.node [v565, v732, v832, v852, v1045, v1315, v1637] (.node [v565, v732, v832, v852, v1045, v1263, v1315] (.node [v565, v732, v832, v852, v993, v1045, v1315] (.node [v565, v732, v831, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v832, v852, v1045, v1315, v1623] (.node [v565, v732, v832, v852, v1045, v1315, v1515] .nil .nil) .nil)) (.node [v565, v732, v832, v1045, v1315, v1515, v1637] (.node [v565, v732, v832, v852, v1254, v1315, v1515] (.node [v565, v732, v832, v852, v1045, v1478, v1515] .nil .nil) .nil) (.node [v565, v732, v832, v1045, v1315, v1637] .nil .nil)))) (.node [v565, v732, v845, v852, v1045, v1315, v1515] (.node [v565, v732, v840, v852, v1045, v1315, v1515] (.node [v565, v732, v836, v852, v1045, v1315, v1515] (.node [v565, v732, v835, v852, v1045, v1315, v1515] (.node [v565, v732, v834, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v839, v852, v1045, v1315, v1515] (.node [v565, v732, v837, v852, v1045, v1315, v1515] .nil .nil) .nil)) (.node [v565, v732, v844, v852, v1045, v1315, v1515] (.node [v565, v732, v842, v852, v1045, v1315, v1515] (.node [v565, v732, v841, v852, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v844, v1045, v1315, v1515] .nil .nil))) (.node [v565, v732, v852, v855, v1045, v1315, v1515] (.node [v565, v732, v852, v852, v1045, v1315, v1515] (.node [v565, v732, v845, v1045, v1315, v1515, v1654] (.node [v565, v732, v845, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v854, v1045, v1315, v1515] .nil .nil)) (.node [v565, v732, v852, v859, v1045, v1315, v1515] (.node [v565, v732, v852, v857, v1045, v1315, v1515] (.node [v565, v732, v852, v856, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v861, v1045, v1315, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrrl_ok : everyKey (rowOK 5 level5) level6rlrrl = true := by decide +kernel
def level6rlrrr : BinaryTree (List W) := (.node [v565, v732, v852, v913, v1045, v1315] (.node [v565, v732, v852, v881, v1045, v1315, v1515] (.node [v565, v732, v852, v872, v1045, v1315, v1515] (.node [v565, v732, v852, v867, v1045, v1315, v1515] (.node [v565, v732, v852, v866, v1045, v1315, v1515] (.node [v565, v732, v852, v864, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v871, v1045, v1315, v1515] (.node [v565, v732, v852, v869, v1045, v1315, v1515] .nil .nil) .nil)) (.node [v565, v732, v852, v877, v1045, v1315, v1515] (.node [v565, v732, v852, v876, v1045, v1315, v1515] (.node [v565, v732, v852, v874, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v879, v1045, v1315, v1515] .nil .nil))) (.node [v565, v732, v852, v892, v1315, v1515] (.node [v565, v732, v852, v891, v1315, v1515] (.node [v565, v732, v852, v891, v1045, v1315, v1515] (.node [v565, v732, v852, v882, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v892, v1045, v1315, v1515] .nil .nil)) (.node [v565, v732, v852, v905, v1045, v1315, v1515] (.node [v565, v732, v852, v904, v1045, v1515] (.node [v565, v732, v852, v904, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v905, v1045, v1515] .nil .nil)))) (.node [v565, v732, v852, v932, v1045, v1315, v1515] (.node [v565, v732, v852, v919, v1045, v1315, v1515] (.node [v565, v732, v852, v914, v1045, v1315, v1515] (.node [v565, v732, v852, v914, v1045, v1315] (.node [v565, v732, v852, v913, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v918, v1045, v1315, v1515] (.node [v565, v732, v852, v917, v1045, v1315, v1515] .nil .nil) .nil)) (.node [v565, v732, v852, v929, v1045, v1315, v1515] (.node [v565, v732, v852, v927, v1045, v1315, v1515] (.node [v565, v732, v852, v920, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v931, v1045, v1315, v1515] .nil .nil))) (.node [v565, v732, v852, v941, v1045, v1315, v1515] (.node [v565, v732, v852, v937, v1045, v1315, v1515] (.node [v565, v732, v852, v936, v1045, v1315, v1515] (.node [v565, v732, v852, v934, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v939, v1045, v1315, v1515] .nil .nil)) (.node [v565, v732, v852, v945, v1045, v1315, v1515] (.node [v565, v732, v852, v944, v1045, v1315, v1515] (.node [v565, v732, v852, v943, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v946, v1045, v1315, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrrr_ok : everyKey (rowOK 5 level5) level6rlrrr = true := by decide +kernel
def level6rlrr : BinaryTree (List W) := .node [v565, v732, v852, v863, v1045, v1315, v1515] level6rlrrl level6rlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrr_ok : everyKey (rowOK 5 level5) level6rlrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlrrl && everyKey (rowOK 5 level5) level6rlrrr) = true
  rw [level6rlrrl_ok, level6rlrrr_ok]
  decide +kernel
def level6rlr : BinaryTree (List W) := .node [v565, v732, v821, v852, v1045, v1484, v1515] level6rlrl level6rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlr_ok : everyKey (rowOK 5 level5) level6rlr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlrl && everyKey (rowOK 5 level5) level6rlrr) = true
  rw [level6rlrl_ok, level6rlrr_ok]
  decide +kernel
def level6rl : BinaryTree (List W) := .node [v565, v711, v732, v852, v1045, v1315, v1515] level6rll level6rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rl_ok : everyKey (rowOK 5 level5) level6rl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rll && everyKey (rowOK 5 level5) level6rlr) = true
  rw [level6rll_ok, level6rlr_ok]
  decide +kernel
def level6rrlll : BinaryTree (List W) := (.node [v565, v732, v852, v986, v1315, v1515] (.node [v565, v732, v852, v957, v1045, v1515] (.node [v565, v732, v852, v949, v1315, v1515, v1642] (.node [v565, v732, v852, v949, v1045, v1515, v1648] (.node [v565, v732, v852, v949, v1045, v1492, v1515] (.node [v565, v732, v852, v949, v1045, v1407, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v949, v1315, v1492, v1515] (.node [v565, v732, v852, v949, v1144, v1315, v1515] .nil .nil) .nil)) (.node [v565, v732, v852, v953, v1315, v1515] (.node [v565, v732, v852, v953, v1045, v1315, v1515] (.node [v565, v732, v852, v949, v1492, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v957, v1045, v1315, v1515] .nil .nil))) (.node [v565, v732, v852, v977, v1045, v1315, v1515] (.node [v565, v732, v852, v966, v1045, v1315, v1515] (.node [v565, v732, v852, v964, v1045, v1315, v1515] (.node [v565, v732, v852, v962, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v972, v1315, v1515] (.node [v565, v732, v852, v972, v1045, v1315, v1515] .nil .nil) .nil)) (.node [v565, v732, v852, v986, v1045, v1315, v1515] (.node [v565, v732, v852, v977, v1315, v1515] (.node [v565, v732, v852, v977, v1315, v1458, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v986, v1315, v1484, v1515] .nil .nil)))) (.node [v565, v732, v852, v1000, v1045, v1315, v1515] (.node [v565, v732, v852, v993, v1315, v1492, v1515] (.node [v565, v732, v852, v993, v1045, v1315, v1642] (.node [v565, v732, v852, v993, v1045, v1315, v1593] (.node [v565, v732, v852, v993, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v993, v1144, v1315, v1515] (.node [v565, v732, v852, v993, v1045, v1315, v1648] .nil .nil) .nil)) (.node [v565, v732, v852, v997, v1045, v1315, v1515] (.node [v565, v732, v852, v993, v1315, v1642] (.node [v565, v732, v852, v993, v1315, v1515, v1642] .nil .nil) .nil) (.node [v565, v732, v852, v997, v1315, v1515] .nil .nil))) (.node [v565, v732, v852, v1012, v1045, v1315, v1515] (.node [v565, v732, v852, v1009, v1045, v1315, v1515] (.node [v565, v732, v852, v1004, v1045, v1315, v1515] (.node [v565, v732, v852, v1002, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1009, v1315, v1515] .nil .nil)) (.node [v565, v732, v852, v1019, v1045, v1315, v1515] (.node [v565, v732, v852, v1012, v1315, v1515, v1623] (.node [v565, v732, v852, v1012, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1019, v1315, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlll_ok : everyKey (rowOK 5 level5) level6rrlll = true := by decide +kernel
def level6rrllr : BinaryTree (List W) := (.node [v565, v732, v852, v1045, v1106, v1315, v1515] (.node [v565, v732, v852, v1045, v1068, v1315, v1515] (.node [v565, v732, v852, v1034, v1315, v1515] (.node [v565, v732, v852, v1030, v1315, v1515] (.node [v565, v732, v852, v1030, v1045, v1315, v1515] (.node [v565, v732, v852, v1025, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1034, v1045, v1315, v1515] (.node [v565, v732, v852, v1030, v1315, v1515, v1654] .nil .nil) .nil)) (.node [v565, v732, v852, v1045, v1063, v1315, v1515] (.node [v565, v732, v852, v1045, v1045, v1315, v1515] (.node [v565, v732, v852, v1034, v1315, v1515, v1655] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1066, v1315, v1515] .nil .nil))) (.node [v565, v732, v852, v1045, v1090, v1315, v1515] (.node [v565, v732, v852, v1045, v1086, v1315, v1515] (.node [v565, v732, v852, v1045, v1080, v1315, v1515] (.node [v565, v732, v852, v1045, v1069, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1090, v1315] (.node [v565, v732, v852, v1045, v1089, v1315, v1515] .nil .nil) .nil)) (.node [v565, v732, v852, v1045, v1102, v1315, v1515] (.node [v565, v732, v852, v1045, v1098, v1315, v1515] (.node [v565, v732, v852, v1045, v1095, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1103, v1315, v1515] .nil .nil)))) (.node [v565, v732, v852, v1045, v1132, v1315, v1515] (.node [v565, v732, v852, v1045, v1120, v1315, v1515] (.node [v565, v732, v852, v1045, v1110, v1315, v1515] (.node [v565, v732, v852, v1045, v1109, v1315, v1515] (.node [v565, v732, v852, v1045, v1108, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1119, v1315, v1515] (.node [v565, v732, v852, v1045, v1115, v1315, v1515] .nil .nil) .nil)) (.node [v565, v732, v852, v1045, v1126, v1315, v1515] (.node [v565, v732, v852, v1045, v1125, v1315, v1515] (.node [v565, v732, v852, v1045, v1123, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1127, v1315, v1515] .nil .nil))) (.node [v565, v732, v852, v1045, v1138, v1315, v1515] (.node [v565, v732, v852, v1045, v1136, v1315, v1515] (.node [v565, v732, v852, v1045, v1135, v1315, v1515] (.node [v565, v732, v852, v1045, v1134, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1137, v1315, v1515] .nil .nil)) (.node [v565, v732, v852, v1045, v1144, v1315, v1515] (.node [v565, v732, v852, v1045, v1142, v1315, v1515] (.node [v565, v732, v852, v1045, v1141, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1150, v1315, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrllr_ok : everyKey (rowOK 5 level5) level6rrllr = true := by decide +kernel
def level6rrll : BinaryTree (List W) := .node [v565, v732, v852, v1019, v1315, v1515, v1637] level6rrlll level6rrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrll_ok : everyKey (rowOK 5 level5) level6rrll = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrlll && everyKey (rowOK 5 level5) level6rrllr) = true
  rw [level6rrlll_ok, level6rrllr_ok]
  decide +kernel
def level6rrlrl : BinaryTree (List W) := (.node [v565, v732, v852, v1045, v1225, v1515] (.node [v565, v732, v852, v1045, v1195, v1315, v1515] (.node [v565, v732, v852, v1045, v1178, v1315, v1515] (.node [v565, v732, v852, v1045, v1167, v1315, v1515] (.node [v565, v732, v852, v1045, v1167, v1315] (.node [v565, v732, v852, v1045, v1161, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1177, v1315, v1515] (.node [v565, v732, v852, v1045, v1175, v1315, v1515] .nil .nil) .nil)) (.node [v565, v732, v852, v1045, v1185, v1315, v1515] (.node [v565, v732, v852, v1045, v1185, v1220, v1515] (.node [v565, v732, v852, v1045, v1180, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1185, v1515] .nil .nil))) (.node [v565, v732, v852, v1045, v1214, v1315, v1515] (.node [v565, v732, v852, v1045, v1204, v1315] (.node [v565, v732, v852, v1045, v1204, v1220, v1315] (.node [v565, v732, v852, v1045, v1198, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1212, v1315, v1515] (.node [v565, v732, v852, v1045, v1204, v1315, v1515] .nil .nil) .nil)) (.node [v565, v732, v852, v1045, v1225, v1260, v1515] (.node [v565, v732, v852, v1045, v1220, v1315, v1515] (.node [v565, v732, v852, v1045, v1219, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1225, v1315, v1515] .nil .nil)))) (.node [v565, v732, v852, v1045, v1263, v1315, v1593] (.node [v565, v732, v852, v1045, v1253, v1315, v1515] (.node [v565, v732, v852, v1045, v1244, v1260, v1315] (.node [v565, v732, v852, v1045, v1238, v1315, v1515] (.node [v565, v732, v852, v1045, v1236, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1244, v1315, v1515] (.node [v565, v732, v852, v1045, v1244, v1315] .nil .nil) .nil)) (.node [v565, v732, v852, v1045, v1260, v1315, v1515] (.node [v565, v732, v852, v1045, v1259, v1315, v1515] (.node [v565, v732, v852, v1045, v1254, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1263, v1315, v1515] .nil .nil))) (.node [v565, v732, v852, v1045, v1263, v1515, v1648] (.node [v565, v732, v852, v1045, v1263, v1407, v1515] (.node [v565, v732, v852, v1045, v1263, v1315, v1648] (.node [v565, v732, v852, v1045, v1263, v1315, v1642] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1263, v1492, v1515] .nil .nil)) (.node [v565, v732, v852, v1045, v1269, v1515] (.node [v565, v732, v852, v1045, v1269, v1315, v1515] (.node [v565, v732, v852, v1045, v1263, v1648] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1270, v1315, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlrl_ok : everyKey (rowOK 5 level5) level6rrlrl = true := by decide +kernel
def level6rrlrr : BinaryTree (List W) := (.node [v565, v732, v852, v1045, v1315, v1339, v1515] (.node [v565, v732, v852, v1045, v1300, v1315, v1515] (.node [v565, v732, v852, v1045, v1282, v1515, v1623] (.node [v565, v732, v852, v1045, v1279, v1515] (.node [v565, v732, v852, v1045, v1279, v1315, v1515] (.node [v565, v732, v852, v1045, v1274, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1282, v1515] (.node [v565, v732, v852, v1045, v1282, v1315, v1515] .nil .nil) .nil)) (.node [v565, v732, v852, v1045, v1289, v1515, v1637] (.node [v565, v732, v852, v1045, v1289, v1515] (.node [v565, v732, v852, v1045, v1289, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1295, v1315, v1515] .nil .nil))) (.node [v565, v732, v852, v1045, v1304, v1515, v1655] (.node [v565, v732, v852, v1045, v1304, v1315, v1515] (.node [v565, v732, v852, v1045, v1300, v1515, v1654] (.node [v565, v732, v852, v1045, v1300, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1304, v1515] .nil .nil)) (.node [v565, v732, v852, v1045, v1315, v1336, v1515] (.node [v565, v732, v852, v1045, v1315, v1333, v1515] (.node [v565, v732, v852, v1045, v1315, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1315, v1338, v1515] .nil .nil)))) (.node [v565, v732, v852, v1045, v1315, v1377, v1515] (.node [v565, v732, v852, v1045, v1315, v1365, v1515] (.node [v565, v732, v852, v1045, v1315, v1359, v1515] (.node [v565, v732, v852, v1045, v1315, v1356, v1515] (.node [v565, v732, v852, v1045, v1315, v1350, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1315, v1360, v1515] (.node [v565, v732, v852, v1045, v1315, v1360] .nil .nil) .nil)) (.node [v565, v732, v852, v1045, v1315, v1374, v1515] (.node [v565, v732, v852, v1045, v1315, v1371, v1515] (.node [v565, v732, v852, v1045, v1315, v1370, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1315, v1376, v1515] .nil .nil))) (.node [v565, v732, v852, v1045, v1315, v1391, v1515] (.node [v565, v732, v852, v1045, v1315, v1386, v1515] (.node [v565, v732, v852, v1045, v1315, v1385, v1515] (.node [v565, v732, v852, v1045, v1315, v1378, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1315, v1389, v1515] .nil .nil)) (.node [v565, v732, v852, v1045, v1315, v1398, v1515] (.node [v565, v732, v852, v1045, v1315, v1393, v1515] (.node [v565, v732, v852, v1045, v1315, v1392, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1315, v1399, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlrr_ok : everyKey (rowOK 5 level5) level6rrlrr = true := by decide +kernel
def level6rrlr : BinaryTree (List W) := .node [v565, v732, v852, v1045, v1272, v1315, v1515] level6rrlrl level6rrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlr_ok : everyKey (rowOK 5 level5) level6rrlr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrlrl && everyKey (rowOK 5 level5) level6rrlrr) = true
  rw [level6rrlrl_ok, level6rrlrr_ok]
  decide +kernel
def level6rrl : BinaryTree (List W) := .node [v565, v732, v852, v1045, v1150, v1515] level6rrll level6rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrl_ok : everyKey (rowOK 5 level5) level6rrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrll && everyKey (rowOK 5 level5) level6rrlr) = true
  rw [level6rrll_ok, level6rrlr_ok]
  decide +kernel
def level6rrrll : BinaryTree (List W) := (.node [v565, v732, v852, v1045, v1315, v1468, v1484] (.node [v565, v732, v852, v1045, v1315, v1432, v1515] (.node [v565, v732, v852, v1045, v1315, v1419] (.node [v565, v732, v852, v1045, v1315, v1405, v1515] (.node [v565, v732, v852, v1045, v1315, v1404, v1515] (.node [v565, v732, v852, v1045, v1315, v1401, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1315, v1413, v1515] (.node [v565, v732, v852, v1045, v1315, v1407, v1515] .nil .nil) .nil)) (.node [v565, v732, v852, v1045, v1315, v1429, v1515] (.node [v565, v732, v852, v1045, v1315, v1427, v1515] (.node [v565, v732, v852, v1045, v1315, v1419, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1315, v1430, v1515] .nil .nil))) (.node [v565, v732, v852, v1045, v1315, v1452, v1515] (.node [v565, v732, v852, v1045, v1315, v1442, v1458] (.node [v565, v732, v852, v1045, v1315, v1442] (.node [v565, v732, v852, v1045, v1315, v1436, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1315, v1450, v1515] (.node [v565, v732, v852, v1045, v1315, v1442, v1515] .nil .nil) .nil)) (.node [v565, v732, v852, v1045, v1315, v1462, v1515] (.node [v565, v732, v852, v1045, v1315, v1458, v1515] (.node [v565, v732, v852, v1045, v1315, v1457, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1315, v1468] .nil .nil)))) (.node [v565, v732, v852, v1045, v1315, v1496, v1515] (.node [v565, v732, v852, v1045, v1315, v1487, v1515] (.node [v565, v732, v852, v1045, v1315, v1478, v1515] (.node [v565, v732, v852, v1045, v1315, v1477, v1515] (.node [v565, v732, v852, v1045, v1315, v1468, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1315, v1484, v1515] (.node [v565, v732, v852, v1045, v1315, v1483, v1515] .nil .nil) .nil)) (.node [v565, v732, v852, v1045, v1315, v1492, v1515] (.node [v565, v732, v852, v1045, v1315, v1489, v1515] (.node [v565, v732, v852, v1045, v1315, v1488, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1315, v1493, v1515] .nil .nil))) (.node [v565, v732, v852, v1045, v1315, v1504] (.node [v565, v732, v852, v1045, v1315, v1500, v1515] (.node [v565, v732, v852, v1045, v1315, v1500] (.node [v565, v732, v852, v1045, v1315, v1498, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1315, v1500, v1654] .nil .nil)) (.node [v565, v732, v852, v1045, v1315, v1515] (.node [v565, v732, v852, v1045, v1315, v1504, v1655] (.node [v565, v732, v852, v1045, v1315, v1504, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1315, v1515, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrll_ok : everyKey (rowOK 5 level5) level6rrrll = true := by decide +kernel
def level6rrrlr : BinaryTree (List W) := (.node [v565, v732, v852, v1045, v1315, v1515, v1593] (.node [v565, v732, v852, v1045, v1315, v1515, v1568] (.node [v565, v732, v852, v1045, v1315, v1515, v1556] (.node [v565, v732, v852, v1045, v1315, v1515, v1539] (.node [v565, v732, v852, v1045, v1315, v1515, v1538] (.node [v565, v732, v852, v1045, v1315, v1515, v1536] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1315, v1515, v1554] (.node [v565, v732, v852, v1045, v1315, v1515, v1550] .nil .nil) .nil)) (.node [v565, v732, v852, v1045, v1315, v1515, v1565] (.node [v565, v732, v852, v1045, v1315, v1515, v1562] (.node [v565, v732, v852, v1045, v1315, v1515, v1557] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1315, v1515, v1567] .nil .nil))) (.node [v565, v732, v852, v1045, v1315, v1515, v1582] (.node [v565, v732, v852, v1045, v1315, v1515, v1578] (.node [v565, v732, v852, v1045, v1315, v1515, v1575] (.node [v565, v732, v852, v1045, v1315, v1515, v1569] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1315, v1515, v1581] (.node [v565, v732, v852, v1045, v1315, v1515, v1580] .nil .nil) .nil)) (.node [v565, v732, v852, v1045, v1315, v1515, v1590] (.node [v565, v732, v852, v1045, v1315, v1515, v1587] (.node [v565, v732, v852, v1045, v1315, v1515, v1586] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1315, v1515, v1591] .nil .nil)))) (.node [v565, v732, v852, v1045, v1315, v1515, v1631] (.node [v565, v732, v852, v1045, v1315, v1515, v1612] (.node [v565, v732, v852, v1045, v1315, v1515, v1606] (.node [v565, v732, v852, v1045, v1315, v1515, v1604] (.node [v565, v732, v852, v1045, v1315, v1515, v1598] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1315, v1515, v1609] (.node [v565, v732, v852, v1045, v1315, v1515, v1607] .nil .nil) .nil)) (.node [v565, v732, v852, v1045, v1315, v1515, v1623] (.node [v565, v732, v852, v1045, v1315, v1515, v1622] (.node [v565, v732, v852, v1045, v1315, v1515, v1617] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1315, v1515, v1626] .nil .nil))) (.node [v565, v732, v852, v1045, v1315, v1515, v1643] (.node [v565, v732, v852, v1045, v1315, v1515, v1639] (.node [v565, v732, v852, v1045, v1315, v1515, v1637] (.node [v565, v732, v852, v1045, v1315, v1515, v1636] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1315, v1515, v1642] .nil .nil)) (.node [v565, v732, v852, v1045, v1315, v1515, v1648] (.node [v565, v732, v852, v1045, v1315, v1515, v1645] (.node [v565, v732, v852, v1045, v1315, v1515, v1644] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1315, v1515, v1649] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrlr_ok : everyKey (rowOK 5 level5) level6rrrlr = true := by decide +kernel
def level6rrrl : BinaryTree (List W) := .node [v565, v732, v852, v1045, v1315, v1515, v1533] level6rrrll level6rrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrl_ok : everyKey (rowOK 5 level5) level6rrrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrrll && everyKey (rowOK 5 level5) level6rrrlr) = true
  rw [level6rrrll_ok, level6rrrlr_ok]
  decide +kernel
def level6rrrrl : BinaryTree (List W) := (.node [v565, v732, v852, v1045, v1315, v1581] (.node [v565, v732, v852, v1045, v1315, v1515, v1661] (.node [v565, v732, v852, v1045, v1315, v1515, v1656] (.node [v565, v732, v852, v1045, v1315, v1515, v1653] (.node [v565, v732, v852, v1045, v1315, v1515, v1652] (.node [v565, v732, v852, v1045, v1315, v1515, v1651] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1315, v1515, v1655] (.node [v565, v732, v852, v1045, v1315, v1515, v1654] .nil .nil) .nil)) (.node [v565, v732, v852, v1045, v1315, v1515, v1659] (.node [v565, v732, v852, v1045, v1315, v1515, v1658] (.node [v565, v732, v852, v1045, v1315, v1515, v1657] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1315, v1515, v1660] .nil .nil))) (.node [v565, v732, v852, v1045, v1315, v1539] (.node [v565, v732, v852, v1045, v1315, v1515, v1664] (.node [v565, v732, v852, v1045, v1315, v1515, v1663] (.node [v565, v732, v852, v1045, v1315, v1515, v1662] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1315, v1533] (.node [v565, v732, v852, v1045, v1315, v1515, v1665] .nil .nil) .nil)) (.node [v565, v732, v852, v1045, v1315, v1568] (.node [v565, v732, v852, v1045, v1315, v1557] (.node [v565, v732, v852, v1045, v1315, v1550] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1315, v1569] .nil .nil)))) (.node [v565, v732, v852, v1045, v1315, v1631] (.node [v565, v732, v852, v1045, v1315, v1612] (.node [v565, v732, v852, v1045, v1315, v1593, v1637] (.node [v565, v732, v852, v1045, v1315, v1593, v1623] (.node [v565, v732, v852, v1045, v1315, v1582] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1315, v1604] (.node [v565, v732, v852, v1045, v1315, v1598] .nil .nil) .nil)) (.node [v565, v732, v852, v1045, v1315, v1623, v1648] (.node [v565, v732, v852, v1045, v1315, v1623, v1642] (.node [v565, v732, v852, v1045, v1315, v1617] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1315, v1626] .nil .nil))) (.node [v565, v732, v852, v1045, v1350, v1515] (.node [v565, v732, v852, v1045, v1333, v1515] (.node [v565, v732, v852, v1045, v1315, v1637, v1648] (.node [v565, v732, v852, v1045, v1315, v1637, v1642] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1339, v1515] .nil .nil)) (.node [v565, v732, v852, v1045, v1378, v1515] (.node [v565, v732, v852, v1045, v1377, v1515] (.node [v565, v732, v852, v1045, v1365, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1392, v1515] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrrl_ok : everyKey (rowOK 5 level5) level6rrrrl = true := by decide +kernel
def level6rrrrr : BinaryTree (List W) := (.node [v565, v732, v852, v1144, v1220, v1315, v1515] (.node [v565, v732, v852, v1045, v1484, v1492, v1515] (.node [v565, v732, v852, v1045, v1452, v1515] (.node [v565, v732, v852, v1045, v1413, v1515] (.node [v565, v732, v852, v1045, v1407, v1484, v1515] (.node [v565, v732, v852, v1045, v1407, v1458, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1436, v1515] (.node [v565, v732, v852, v1045, v1427, v1515] .nil .nil) .nil)) (.node [v565, v732, v852, v1045, v1462, v1515] (.node [v565, v732, v852, v1045, v1458, v1515, v1648] (.node [v565, v732, v852, v1045, v1458, v1492, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1045, v1478, v1515] .nil .nil))) (.node [v565, v732, v852, v1095, v1315, v1515] (.node [v565, v732, v852, v1069, v1315, v1515] (.node [v565, v732, v852, v1063, v1315, v1515] (.node [v565, v732, v852, v1045, v1484, v1515, v1648] .nil .nil) .nil) (.node [v565, v732, v852, v1080, v1315, v1515] .nil .nil)) (.node [v565, v732, v852, v1126, v1315, v1515] (.node [v565, v732, v852, v1110, v1315, v1515] (.node [v565, v732, v852, v1109, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1127, v1315, v1515] .nil .nil)))) (.node [v565, v732, v852, v1260, v1315, v1515, v1642] (.node [v565, v732, v852, v1220, v1315, v1492, v1515] (.node [v565, v732, v852, v1175, v1315, v1515] (.node [v565, v732, v852, v1161, v1315, v1515] (.node [v565, v732, v852, v1144, v1260, v1315, v1515] .nil .nil) .nil) (.node [v565, v732, v852, v1214, v1315, v1515] (.node [v565, v732, v852, v1198, v1315, v1515] .nil .nil) .nil)) (.node [v565, v732, v852, v1254, v1315, v1515] (.node [v565, v732, v852, v1238, v1315, v1515] (.node [v565, v732, v852, v1220, v1315, v1515, v1642] .nil .nil) .nil) (.node [v565, v732, v852, v1260, v1315, v1492, v1515] .nil .nil))) (.node [v623, v732, v852, v1045, v1144, v1315, v1515] (.node [v565, v852, v943, v1045, v1315, v1515] (.node [v565, v732, v945, v1045, v1315, v1515, v1655] (.node [v565, v732, v944, v1045, v1315, v1515] .nil .nil) .nil) (.node [v565, v852, v945, v1045, v1315, v1515, v1654] .nil .nil)) (.node [v643, v732, v852, v1045, v1315, v1515, v1654] (.node [v638, v732, v852, v1045, v1315, v1515, v1593] (.node [v631, v732, v852, v1045, v1315, v1407, v1515] .nil .nil) .nil) (.node [v644, v732, v852, v1045, v1315, v1515, v1655] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrrr_ok : everyKey (rowOK 5 level5) level6rrrrr = true := by decide +kernel
def level6rrrr : BinaryTree (List W) := .node [v565, v732, v852, v1045, v1393, v1515] level6rrrrl level6rrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrr_ok : everyKey (rowOK 5 level5) level6rrrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrrrl && everyKey (rowOK 5 level5) level6rrrrr) = true
  rw [level6rrrrl_ok, level6rrrrr_ok]
  decide +kernel
def level6rrr : BinaryTree (List W) := .node [v565, v732, v852, v1045, v1315, v1515, v1650] level6rrrl level6rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrr_ok : everyKey (rowOK 5 level5) level6rrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrrl && everyKey (rowOK 5 level5) level6rrrr) = true
  rw [level6rrrl_ok, level6rrrr_ok]
  decide +kernel
def level6rr : BinaryTree (List W) := .node [v565, v732, v852, v1045, v1315, v1400, v1515] level6rrl level6rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rr_ok : everyKey (rowOK 5 level5) level6rr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrl && everyKey (rowOK 5 level5) level6rrr) = true
  rw [level6rrl_ok, level6rrr_ok]
  decide +kernel
def level6r : BinaryTree (List W) := .node [v565, v732, v852, v949, v1045, v1315, v1515] level6rl level6rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6r_ok : everyKey (rowOK 5 level5) level6r = true := by
  change (_ && everyKey (rowOK 5 level5) level6rl && everyKey (rowOK 5 level5) level6rr) = true
  rw [level6rl_ok, level6rr_ok]
  decide +kernel
def level6 : BinaryTree (List W) := .node [v533, v565, v732, v852, v1045, v1315, v1515] level6l level6r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6_ok : everyKey (rowOK 5 level5) level6 = true := by
  change (_ && everyKey (rowOK 5 level5) level6l && everyKey (rowOK 5 level5) level6r) = true
  rw [level6l_ok, level6r_ok]
  decide +kernel
theorem closed6 : Closed 6 level6 := closed_next 5 (by decide) level6 level5 closed5 level6_ok
def level7l : BinaryTree (List W) := (.node [v315, v565, v732, v852, v1045, v1315, v1515] (.node [v140, v565, v732, v852, v1045, v1315, v1515] (.node [v59, v565, v732, v852, v1045, v1315, v1515] (.node [v47, v565, v732, v852, v1045, v1315, v1515] (.node [v34, v565, v732, v852, v1045, v1315, v1515] .nil .nil) (.node [v54, v565, v732, v852, v1045, v1315, v1515] .nil .nil)) (.node [v117, v565, v732, v852, v1045, v1315, v1515] (.node [v72, v565, v732, v852, v1045, v1315, v1515] .nil .nil) (.node [v132, v565, v732, v852, v1045, v1315, v1515] .nil .nil))) (.node [v224, v565, v732, v852, v1045, v1315, v1515] (.node [v161, v565, v732, v852, v1045, v1315, v1515] (.node [v146, v565, v732, v852, v1045, v1315, v1515] .nil .nil) (.node [v207, v565, v732, v852, v1045, v1315, v1515] .nil .nil)) (.node [v240, v565, v732, v852, v1045, v1315, v1515] (.node [v233, v565, v732, v852, v1045, v1315, v1515] .nil .nil) (.node [v255, v565, v732, v852, v1045, v1315, v1515] .nil .nil)))) (.node [v424, v565, v732, v852, v1045, v1315, v1515] (.node [v358, v565, v732, v852, v1045, v1315, v1515] (.node [v332, v565, v732, v852, v1045, v1315, v1515] (.node [v316, v565, v732, v852, v1045, v1315, v1515] .nil .nil) (.node [v349, v565, v732, v852, v1045, v1315, v1515] .nil .nil)) (.node [v407, v565, v732, v852, v1045, v1315, v1515] (.node [v361, v565, v732, v852, v1045, v1315, v1515] .nil .nil) (.node [v408, v565, v732, v852, v1045, v1315, v1515] .nil .nil))) (.node [v501, v565, v732, v852, v1045, v1315, v1515] (.node [v450, v565, v732, v852, v1045, v1315, v1515] (.node [v441, v565, v732, v852, v1045, v1315, v1515] .nil .nil) (.node [v453, v565, v732, v852, v1045, v1315, v1515] .nil .nil)) (.node [v549, v565, v732, v852, v1045, v1315, v1515] (.node [v530, v565, v732, v852, v1045, v1315, v1515] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7l_ok : everyKey (rowOK 6 level6) level7l = true := by decide +kernel
def level7r : BinaryTree (List W) := (.node [v565, v732, v852, v1045, v1144, v1315, v1515] (.node [v565, v712, v732, v852, v1045, v1315, v1515] (.node [v565, v644, v732, v852, v1045, v1315, v1515] (.node [v565, v638, v732, v852, v1045, v1315, v1515] (.node [v565, v631, v732, v852, v1045, v1315, v1515] .nil .nil) (.node [v565, v643, v732, v852, v1045, v1315, v1515] .nil .nil)) (.node [v565, v689, v732, v852, v1045, v1315, v1515] (.node [v565, v653, v732, v852, v1045, v1315, v1515] .nil .nil) (.node [v565, v701, v732, v852, v1045, v1315, v1515] .nil .nil))) (.node [v565, v732, v852, v945, v1045, v1315, v1515] (.node [v565, v732, v821, v852, v1045, v1315, v1515] (.node [v565, v732, v809, v852, v1045, v1315, v1515] .nil .nil) (.node [v565, v732, v832, v852, v1045, v1315, v1515] .nil .nil)) (.node [v565, v732, v852, v993, v1045, v1315, v1515] (.node [v565, v732, v852, v949, v1045, v1315, v1515] .nil .nil) .nil))) (.node [v565, v732, v852, v1045, v1315, v1515, v1593] (.node [v565, v732, v852, v1045, v1315, v1407, v1515] (.node [v565, v732, v852, v1045, v1260, v1315, v1515] (.node [v565, v732, v852, v1045, v1220, v1315, v1515] .nil .nil) (.node [v565, v732, v852, v1045, v1263, v1315, v1515] .nil .nil)) (.node [v565, v732, v852, v1045, v1315, v1484, v1515] (.node [v565, v732, v852, v1045, v1315, v1458, v1515] .nil .nil) (.node [v565, v732, v852, v1045, v1315, v1492, v1515] .nil .nil))) (.node [v565, v732, v852, v1045, v1315, v1515, v1648] (.node [v565, v732, v852, v1045, v1315, v1515, v1637] (.node [v565, v732, v852, v1045, v1315, v1515, v1623] .nil .nil) (.node [v565, v732, v852, v1045, v1315, v1515, v1642] .nil .nil)) (.node [v565, v732, v852, v1045, v1315, v1515, v1655] (.node [v565, v732, v852, v1045, v1315, v1515, v1654] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7r_ok : everyKey (rowOK 6 level6) level7r = true := by decide +kernel
def level7 : BinaryTree (List W) := .node [v565, v623, v732, v852, v1045, v1315, v1515] level7l level7r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7_ok : everyKey (rowOK 6 level6) level7 = true := by
  change (_ && everyKey (rowOK 6 level6) level7l && everyKey (rowOK 6 level6) level7r) = true
  rw [level7l_ok, level7r_ok]
  decide +kernel
theorem closed7 : Closed 7 level7 := closed_next 6 (by decide) level7 level6 closed6 level7_ok
def level8 : BinaryTree (List W) := (.node [v565, v732, v852, v1045, v1315, v1515] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8_ok : everyKey (rowOK 7 level7) level8 = true := by decide +kernel
theorem closed8 : Closed 8 level8 := closed_next 7 (by decide) level8 level7 closed7 level8_ok

theorem lower : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z 8 ins.toFinset :=
  @no_build 8 level8 ins (by decide +kernel) (by decide) closed8 (by decide +kernel)
def witness : List Gate := [⟨.or,[1,2]⟩, ⟨.and,[4,5]⟩, ⟨.and,[3,7]⟩, ⟨.or,[6,8]⟩, ⟨.and,[0,9]⟩, ⟨.and,[1,2]⟩, ⟨.or,[3,4]⟩, ⟨.or,[5,12]⟩, ⟨.and,[11,13]⟩, ⟨.or,[10,14]⟩]
theorem upper : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 10 ∧ ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xeae8e8e8e8e8e8a8 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact ⟨witness,15,by simp [witness],rfl,by decide +kernel⟩
end PEqualNP.Outside.L_meta_15459_aux

open PEqualNP.Outside.L_meta_15459_aux in
theorem PEqualNP.Outside.L_meta_15459 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941132520 * 2 ^ 32 + 3907578024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941132520 * 2 ^ 32 + 3907578024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  have code : 3941132520 * 2 ^ 32 + 3907578024 = 0xeae8e8e8e8e8e8a8 := by decide
  simp only [code] at h ⊢
  obtain ⟨C,legal,size,computes⟩ := h
  obtain ⟨gs,o,mono,bound,ev⟩ := replace 0xeae8e8e8e8e8e8a8 10 ins (by decide +kernel) sampled rfl lower upper C.gates C.output legal computes
  exact ⟨⟨gs,o⟩,mono,bound.trans size,ev⟩
