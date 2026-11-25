import PEqualNP.Defs

-- The live-wire search and circuit compiler are adapted from tacyon52 in L-meta-8639, pull request 12794 under Apache-2.0.
namespace PEqualNP.Outside.L_meta_15619_aux

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

theorem replace (T m : ℕ) (ins : List W) (nd : ins.Nodup)
    (row : ∀ j : Fin 108, Nat.testBit T (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
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

def v0 : W := 0x2d96b3628000000e39df9f
def v1 : W := 0x58f3387880000060c1e3e6
def v2 : W := 0x71e1997a0000018f0603f8
def v3 : W := 0x7d05bb2a000001f007fc00
def v4 : W := 0x7d97bb6a800001fe3fff9f
def v5 : W := 0x7df62250800001fff80000
def v6 : W := 0x7df6b372800001fff9df9f
def v7 : W := 0x7df7bb7a8000006ef9ffff
def v8 : W := 0x7df7bb7a8000018f3fdfff
def v9 : W := 0x1678000d5a74000000001df9f
def v10 : W := 0x2cd000158a90003740001e3e6
def v11 : W := 0x38e000199ae000c78000603f8
def v12 : W := 0x3e80001dd2a000f800007fc00
def v13 : W := 0x3e87d05ff2a000f81f007fc00
def v14 : W := 0x3ed0001ddab000ff40007ffe6
def v15 : W := 0x3ef80004485400ffe00000000
def v16 : W := 0x3ef8001ddaf4003740001ffff
def v17 : W := 0x3ef8001ddaf400c780007dfff
def v18 : W := 0x3effdf666d5c00ffffff80000
def v19 : W := 0x2c07829a00c5c000000e38039f
def v20 : W := 0x581500f200d180607400c003e6
def v21 : W := 0x701602e000d40180780f0003f8
def v22 : W := 0x7c1002fa005081f0000ff80000
def v23 : W := 0x7c107ffe225081f001fff80000
def v24 : W := 0x7c1602fa00d481f0780ff803f8
def v25 : W := 0x7c178208008541f07e00000000
def v26 : W := 0x7c1782fa00d5c060740ef803ff
def v27 : W := 0x7c1782fa00d5c180780f3803ff
def v28 : W := 0x7c17ff0dbbaf41f07ff007fc00
def v29 : W := 0x7ff802fbdd7a81ff800ffffc00
def v30 : W := 0x7fff8208448541fffe00000000
def v31 : W := 0x10841081260018c630460c1e006
def v32 : W := 0x10845089270e18000000001c386
def v33 : W := 0x180600c0466000e03807001fc00
def v34 : W := 0x188610c1666018e638470c1fc06
def v35 : W := 0x18c000c1e22008e700070f80000
def v36 : W := 0x18c600c1e66008e738070f9fc00
def v37 : W := 0x18c61800844014e738600000000
def v38 : W := 0x18c618c1e6601c000000039dc07
def v39 : W := 0x18c618c1e6601cc630460f9fc07
def v40 : W := 0x18c61f1e9dd7b4e73878f0603f8
def v41 : W := 0x18f8e0c1fbbae8e7c7870fe03f8
def v42 : W := 0x1f0760ee466d40f83f87f01fff8
def v43 : W := 0x1fc100efe22508ff0007ff80000
def v44 : W := 0x1fc77820844854ff3fe00000000
def v45 : W := 0x4210223008106318c098f060018
def v46 : W := 0x42106238091e60000000e000398
def v47 : W := 0x4812025048702320c8190061c00
def v48 : W := 0x483e82505df2a320f819007fc00
def v49 : W := 0x4a400270c02003390019f380000
def v50 : W := 0x4a502270c8306339c099f3e0018
def v51 : W := 0x4a520270c8702339c819f3e1c00
def v52 : W := 0x4a52282080404739c8a00000000
def v53 : W := 0x4a522a70c87064000000e381c19
def v54 : W := 0x4a522a70c8706718c098f3e1c19
def v55 : W := 0x4a522dafb3c7cf39c8a60c1e3e6
def v56 : W := 0x4a6cd270d5aa93393759f39e3e6
def v57 : W := 0x4a7ef82084485739ffe00000000
def v58 : W := 0x4d93525f687d3b26cf590c61fe6
def v59 : W := 0x529432b12e107bdef0defc7e01e
def v60 : W := 0x581602d04f7220000000001dc00
def v61 : W := 0x583e82d05ff2a000f800007fc00
def v62 : W := 0x5ac002f9e22408000000e380000
def v63 : W := 0x5ad678208448540000000000000
def v64 : W := 0x5ad67820844854e738600000000
def v65 : W := 0x5ad6782084485739c8a00000000
def v66 : W := 0x5ad67af9ef7e7c000000e39df9f
def v67 : W := 0x5afef82084485400ffe00000000
def v68 : W := 0x5fc102ffe225081f0000ff80000
def v69 : W := 0x5fd778208448541f07e00000000
def v70 : W := 0xa0288500108083e0f81f0062000
def v71 : W := 0xa02887d05bb2a3e0f81f007fc00
def v72 : W := 0xa2e8fd29b08cdfe0f81fe3e239f
def v73 : W := 0xa5010506000103ff001f1c00000
def v74 : W := 0xa50107df62250bff001fff80000
def v75 : W := 0xa5177d060d5b77ff001f1c1df9f
def v76 : W := 0xa5298000000003ffffe00000000
def v77 : W := 0xa52982d96b362bffffe0e39df9f
def v78 : W := 0xa5298506108180c637460c02060
def v79 : W := 0xa529850610818318c7981060060
def v80 : W := 0xa529858f338788c637460c1e3e6
def v81 : W := 0xa529871e1997a318c798f0603f8
def v82 : W := 0xa529c50e118f8000070000003e0
def v83 : W := 0xa529c58f338f880007060c1e3e6
def v84 : W := 0xa529c71e199fa0000718f0603f8
def v85 : W := 0xa539e506199be318c79810603f8
def v86 : W := 0xa539e50e199fe000c78000603f8
def v87 : W := 0xa5a9d50f308d98c637460c023e6
def v88 : W := 0xa5a9d50f318f980607400c003e6
def v89 : W := 0xb02c8580178280c03006001e000
def v90 : W := 0xb02c87d05fb2a0c0301f007fc00
def v91 : W := 0xb581058f220508c600060c00000
def v92 : W := 0xb58107df622508c6001fff80000
def v93 : W := 0xb5a9858f328588c637460c02060
def v94 : W := 0xb5a9c58f338f88c607060c003e0
def v95 : W := 0xb5ad858f378788c630060c1e000
def v96 : W := 0xb5add000040810c637400000000
def v97 : W := 0xb5add58f378f98000700001c3e6
def v98 : W := 0xb5add58f378f98c637460c1e3e6
def v99 : W := 0xb5bffd8f3fdffcc637460c1ffff
def v100 : W := 0xbdafd5cf77ef98e63f470c1ffe6
def v101 : W := 0xbdc105cfe22508e700070f80000
def v102 : W := 0xbdef9dc7f6e19f18c79813fdc67
def v103 : W := 0xbdefdd8fb7cf9ce73f660c1e3e6
def v104 : W := 0xe03887101992a300c0180060000
def v105 : W := 0xe03887d05bb2a300c01f007fc00
def v106 : W := 0xe53987161993a318c7981060060
def v107 : W := 0xe539c71e199fa300c71800603e0
def v108 : W := 0xe701073e000503180018f000000
def v109 : W := 0xe70107ff62250b18001fff80000
def v110 : W := 0xe739873e1997a318c018f060000
def v111 : W := 0xe739e02000084318c7800000000
def v112 : W := 0xe739e73e199fe0000700e0003f8
def v113 : W := 0xe739e73e199fe318c798f0603f8
def v114 : W := 0xe7f9ff3fb99fff18c798f3e03ff
def v115 : W := 0xe83a875059f2a320c8190061c00
def v116 : W := 0xef79e77ed9bfe339c799f3e03f8
def v117 : W := 0xef7baf76d8f1e4c63746ef83c79
def v118 : W := 0xef7bef3e99dfe739cfb8f0603f8
def v119 : W := 0xf7bdf7bf3f9ffbdef7defc7e3fe
def v120 : W := 0xf80007d0422003e0001f0000000
def v121 : W := 0xf83887d05bb2a3e0c01f0060000
def v122 : W := 0xf83e8000044003e0f8000000000
def v123 : W := 0xf83e87d05ff2a0c03006001fc00
def v124 : W := 0xf83e87d05ff2a300c018007dc00
def v125 : W := 0xf83e87d05ff2a3e0f81f007fc00
def v126 : W := 0xf8be97d17ff2bbe6f85f0c7fc06
def v127 : W := 0xf8fe9fd0dff2b7e7f87f007fc00
def v128 : W := 0xfa7eaff0dff2e7f9f8bf007fc00
def v129 : W := 0xfafef820844857e0f8000000000
def v130 : W := 0xfafefff0dffaf7e0f81f007fc00
def v131 : W := 0xfafefff9fffeffe0f81fe3fff9f
def v132 : W := 0xfd3f87d65ff3a3fff81f1c7fc00
def v133 : W := 0xfd8107df62250be6001f0c00000
def v134 : W := 0xfdbf87df7ff7abe6f81f0c7fc00
def v135 : W := 0xfdbfd7df7fffb8c637460c1ffe6
def v136 : W := 0xfdbfd7df7fffbbe6ff5f0c7ffe6
def v137 : W := 0xff3fe7fe5fffe3f8ff9ff07fff8
def v138 : W := 0xffc10020800003ff00000000000
def v139 : W := 0xffc107ffe22508c60006ef80000
def v140 : W := 0xffc107ffe2250b180018f380000
def v141 : W := 0xffc107ffe2250bff001fff80000
def v142 : W := 0xffc71fffe6651fff387fff80000
def v143 : W := 0xffd127ffea356bffc09fffe0018
def v144 : W := 0xffd32fffe2654fffc8bfff80000
def v145 : W := 0xffd77820844857ff00000000000
def v146 : W := 0xffd77fffe66d5fff001fff80000
def v147 : W := 0xffd77fffef7f7fff001fff9df9f
def v148 : W := 0xffe987fff2a58bfff81fffe2000
def v149 : W := 0xffedd7fff7af9bff375fff9e3e6
def v150 : W := 0xfff987fffbb7abffc01fffe0000
def v151 : W := 0xfff9e7fffbbfeb18c798f3e03f8
def v152 : W := 0xfff9e7fffbbfebffc79fffe03f8
def v153 : W := 0xffff87f0dff2a3fff81f007fc00
def v154 : W := 0xffff87ffe6650bfff81fff80000
def v155 : W := 0xffff87fffff7abfff81fffffc00
def v156 : W := 0xfffff820844854c637400000000
def v157 : W := 0xfffff82084485718c7800000000
def v158 : W := 0xfffff820844857ffffe00000000
def v159 : W := 0xfffffaf9ef7e7fffffe0e39df9f
def v160 : W := 0xfffffd2094c8d7ffffff0062000
def v161 : W := 0xfffffd26844957ffffff1c00000
def v162 : W := 0xfffffd2694c9d7ffffe60c02060
def v163 : W := 0xfffffd2694c9d7fffff81060060
def v164 : W := 0xfffffdafa64d5fffffe60c00000
def v165 : W := 0xfffffdafb7cfdcc637460c1e3e6
def v166 : W := 0xfffffdafb7cfdfffffe60c1e3e6
def v167 : W := 0xffffff309ddaf7fffff80060000
def v168 : W := 0xffffff3e9ddff718c798f0603f8
def v169 : W := 0xffffff3e9ddff7fffff8f0603f8
def v170 : W := 0xfffffff0c66857ffffff0000000
def v171 : W := 0xfffffff0dffaf7ffffff007fc00
def v172 : W := 0xffffffffe66d5fffffffff80000
def v173 : W := 0xfffffffffffffcc63746ef9ffff
def v174 : W := 0xffffffffffffff18c798f3fdfff

def ins : List W := [v66, v98, v113, v125, v141, v158]
theorem sampled : ∀ j : Fin 108, Nat.testBit 0xeaeaeaaaeac8e000 (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
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
def level4 : BinaryTree (List W) := (.node [v66, v98, v113, v130, v146] (.node [v42, v66, v98, v141, v158] (.node [v29, v66, v98, v113, v158] (.node [v28, v66, v98, v113, v141] (.node [v18, v66, v98, v113, v125] .nil .nil) .nil) (.node [v41, v66, v98, v125, v158] (.node [v40, v66, v98, v125, v141] .nil .nil) .nil)) (.node [v58, v66, v113, v141, v158] (.node [v56, v66, v113, v125, v158] (.node [v55, v66, v113, v125, v141] .nil .nil) .nil) (.node [v59, v66, v125, v141, v158] .nil .nil))) (.node [v72, v98, v113, v141, v158] (.node [v66, v98, v113, v155, v170] (.node [v66, v98, v113, v154, v171] (.node [v66, v98, v113, v153, v172] .nil .nil) .nil) (.node [v66, v113, v125, v146, v165] (.node [v66, v98, v130, v141, v168] .nil .nil) .nil)) (.node [v98, v102, v125, v141, v158] (.node [v77, v98, v113, v125, v141] (.node [v75, v98, v113, v125, v158] .nil .nil) .nil) (.node [v113, v117, v125, v141, v158] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4_ok : everyKey (rowOK 3 level3) level4 = true := by decide +kernel
theorem closed4 : Closed 4 level4 := closed_next 3 (by decide) level4 level3 closed3 level4_ok
def level5ll : BinaryTree (List W) := (.node [v16, v66, v98, v113, v125, v158] (.node [v6, v66, v98, v113, v125, v141] (.node [v2, v37, v66, v98, v125, v141] (.node [v0, v76, v98, v113, v125, v141] (.node [v0, v66, v98, v113, v125, v141] (.node [v0, v63, v98, v113, v125, v141] .nil .nil) .nil) (.node [v1, v52, v66, v113, v125, v141] .nil .nil)) (.node [v4, v66, v98, v113, v125, v141] (.node [v3, v25, v66, v98, v113, v141] .nil .nil) (.node [v5, v15, v66, v98, v113, v125] .nil .nil))) (.node [v11, v35, v66, v98, v125, v158] (.node [v9, v73, v98, v113, v125, v158] (.node [v8, v66, v98, v113, v125, v141] (.node [v7, v66, v98, v113, v125, v141] .nil .nil) .nil) (.node [v10, v49, v66, v113, v125, v158] .nil .nil)) (.node [v13, v66, v98, v113, v141, v158] (.node [v12, v22, v66, v98, v113, v158] .nil .nil) (.node [v14, v66, v98, v113, v125, v158] .nil .nil)))) (.node [v30, v66, v98, v113, v125, v141] (.node [v23, v66, v98, v113, v125, v158] (.node [v20, v47, v66, v113, v141, v158] (.node [v19, v70, v98, v113, v141, v158] (.node [v17, v66, v98, v113, v125, v158] .nil .nil) .nil) (.node [v21, v33, v66, v98, v141, v158] .nil .nil)) (.node [v26, v66, v98, v113, v141, v158] (.node [v24, v66, v98, v113, v141, v158] .nil .nil) (.node [v27, v66, v98, v113, v141, v158] .nil .nil))) (.node [v36, v66, v98, v125, v141, v158] (.node [v32, v113, v125, v141, v158, v173] (.node [v31, v45, v66, v125, v141, v158] .nil .nil) (.node [v34, v66, v98, v125, v141, v158] .nil .nil)) (.node [v39, v66, v98, v125, v141, v158] (.node [v38, v79, v98, v125, v141, v158] .nil .nil) (.node [v43, v66, v98, v113, v125, v158] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5ll_ok : everyKey (rowOK 4 level4) level5ll = true := by decide +kernel
def level5lr : BinaryTree (List W) := (.node [v63, v66, v98, v113, v130, v141] (.node [v61, v66, v98, v113, v141, v158] (.node [v53, v78, v113, v125, v141, v158] (.node [v50, v66, v113, v125, v141, v158] (.node [v48, v66, v98, v113, v141, v158] (.node [v46, v98, v125, v141, v158, v174] .nil .nil) .nil) (.node [v51, v66, v113, v125, v141, v158] .nil .nil)) (.node [v57, v66, v98, v113, v125, v141] (.node [v54, v66, v113, v125, v141, v158] .nil .nil) (.node [v60, v98, v113, v131, v141, v158] .nil .nil))) (.node [v63, v66, v80, v113, v125, v141] (.node [v63, v66, v71, v98, v113, v141] (.node [v62, v98, v113, v125, v147, v158] .nil .nil) (.node [v63, v66, v74, v98, v113, v125] .nil .nil)) (.node [v63, v66, v98, v113, v125, v141] (.node [v63, v66, v81, v98, v125, v141] .nil .nil) (.node [v63, v66, v98, v113, v125, v146] .nil .nil)))) (.node [v66, v71, v98, v113, v141, v158] (.node [v65, v66, v98, v113, v125, v141] (.node [v63, v98, v113, v125, v141, v159] (.node [v63, v66, v113, v125, v141, v165] (.node [v63, v66, v98, v125, v141, v168] .nil .nil) .nil) (.node [v64, v66, v98, v113, v125, v141] .nil .nil)) (.node [v66, v68, v98, v113, v125, v158] (.node [v66, v67, v98, v113, v125, v141] .nil .nil) (.node [v66, v69, v98, v113, v125, v141] .nil .nil))) (.node [v66, v82, v119, v125, v141, v158] (.node [v66, v80, v113, v125, v141, v158] (.node [v66, v74, v98, v113, v125, v158] .nil .nil) (.node [v66, v81, v98, v125, v141, v158] .nil .nil)) (.node [v66, v84, v98, v125, v141, v158] (.node [v66, v83, v113, v125, v141, v158] .nil .nil) (.node [v66, v85, v98, v125, v141, v158] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lr_ok : everyKey (rowOK 4 level4) level5lr = true := by decide +kernel
def level5l : BinaryTree (List W) := .node [v44, v66, v98, v113, v125, v141] level5ll level5lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5l_ok : everyKey (rowOK 4 level4) level5l = true := by
  change (_ && everyKey (rowOK 4 level4) level5ll && everyKey (rowOK 4 level4) level5lr) = true
  rw [level5ll_ok, level5lr_ok]
  decide +kernel
def level5rl : BinaryTree (List W) := (.node [v66, v98, v108, v125, v152, v158] (.node [v66, v95, v113, v125, v141, v158] (.node [v66, v91, v113, v125, v149, v158] (.node [v66, v89, v113, v136, v141, v158] (.node [v66, v88, v113, v125, v141, v158] (.node [v66, v87, v113, v125, v141, v158] .nil .nil) .nil) (.node [v66, v90, v98, v113, v141, v158] .nil .nil)) (.node [v66, v93, v113, v125, v141, v158] (.node [v66, v92, v98, v113, v125, v158] .nil .nil) (.node [v66, v94, v113, v125, v141, v158] .nil .nil))) (.node [v66, v98, v104, v137, v141, v158] (.node [v66, v97, v113, v125, v141, v158] (.node [v66, v96, v113, v125, v141, v166] .nil .nil) (.node [v66, v98, v101, v113, v125, v158] .nil .nil)) (.node [v66, v98, v106, v125, v141, v158] (.node [v66, v98, v105, v113, v141, v158] .nil .nil) (.node [v66, v98, v107, v125, v141, v158] .nil .nil)))) (.node [v66, v98, v113, v123, v141, v158] (.node [v66, v98, v113, v115, v141, v158] (.node [v66, v98, v111, v125, v141, v169] (.node [v66, v98, v110, v125, v141, v158] (.node [v66, v98, v109, v113, v125, v158] .nil .nil) .nil) (.node [v66, v98, v112, v125, v141, v158] .nil .nil)) (.node [v66, v98, v113, v121, v141, v158] (.node [v66, v98, v113, v120, v155, v158] .nil .nil) (.node [v66, v98, v113, v122, v141, v171] .nil .nil))) (.node [v66, v98, v113, v125, v138, v172] (.node [v66, v98, v113, v125, v129, v141] (.node [v66, v98, v113, v124, v141, v158] .nil .nil) (.node [v66, v98, v113, v125, v133, v158] .nil .nil)) (.node [v66, v98, v113, v125, v140, v158] (.node [v66, v98, v113, v125, v139, v158] .nil .nil) (.node [v66, v98, v113, v125, v141, v145] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rl_ok : everyKey (rowOK 4 level4) level5rl = true := by decide +kernel
def level5rr : BinaryTree (List W) := (.node [v66, v98, v113, v126, v141, v158] (.node [v66, v98, v113, v125, v141, v170] (.node [v66, v98, v113, v125, v141, v162] (.node [v66, v98, v113, v125, v141, v160] (.node [v66, v98, v113, v125, v141, v158] (.node [v66, v98, v113, v125, v141, v157] .nil .nil) .nil) (.node [v66, v98, v113, v125, v141, v161] .nil .nil)) (.node [v66, v98, v113, v125, v141, v164] (.node [v66, v98, v113, v125, v141, v163] .nil .nil) (.node [v66, v98, v113, v125, v141, v167] .nil .nil))) (.node [v66, v98, v113, v125, v146, v158] (.node [v66, v98, v113, v125, v143, v158] (.node [v66, v98, v113, v125, v142, v158] .nil .nil) (.node [v66, v98, v113, v125, v144, v158] .nil .nil)) (.node [v66, v98, v113, v125, v150, v158] (.node [v66, v98, v113, v125, v148, v158] .nil .nil) (.node [v66, v98, v113, v125, v154, v158] .nil .nil)))) (.node [v66, v98, v118, v125, v141, v158] (.node [v66, v98, v113, v134, v141, v158] (.node [v66, v98, v113, v130, v141, v158] (.node [v66, v98, v113, v128, v141, v158] (.node [v66, v98, v113, v127, v141, v158] .nil .nil) .nil) (.node [v66, v98, v113, v132, v141, v158] .nil .nil)) (.node [v66, v98, v114, v125, v141, v158] (.node [v66, v98, v113, v141, v153, v158] .nil .nil) (.node [v66, v98, v116, v125, v141, v158] .nil .nil))) (.node [v66, v100, v113, v125, v141, v158] (.node [v66, v98, v125, v141, v158, v168] (.node [v66, v98, v125, v141, v151, v158] .nil .nil) (.node [v66, v99, v113, v125, v141, v158] .nil .nil)) (.node [v66, v113, v125, v135, v141, v158] (.node [v66, v103, v113, v125, v141, v158] .nil .nil) (.node [v66, v113, v125, v141, v158, v165] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rr_ok : everyKey (rowOK 4 level4) level5rr = true := by decide +kernel
def level5r : BinaryTree (List W) := .node [v66, v98, v113, v125, v141, v156] level5rl level5rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5r_ok : everyKey (rowOK 4 level4) level5r = true := by
  change (_ && everyKey (rowOK 4 level4) level5rl && everyKey (rowOK 4 level4) level5rr) = true
  rw [level5rl_ok, level5rr_ok]
  decide +kernel
def level5 : BinaryTree (List W) := .node [v66, v86, v98, v125, v141, v158] level5l level5r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5_ok : everyKey (rowOK 4 level4) level5 = true := by
  change (_ && everyKey (rowOK 4 level4) level5l && everyKey (rowOK 4 level4) level5r) = true
  rw [level5l_ok, level5r_ok]
  decide +kernel
theorem closed5 : Closed 5 level5 := closed_next 4 (by decide) level5 level4 closed4 level5_ok
def level6l : BinaryTree (List W) := (.node [v25, v66, v98, v113, v125, v141, v158] (.node [v10, v66, v98, v113, v125, v141, v158] (.node [v2, v66, v98, v113, v125, v141, v158] (.node [v0, v66, v98, v113, v125, v141, v158] (.node [v0, v66, v98, v113, v125, v141] .nil .nil) (.node [v1, v66, v98, v113, v125, v141, v158] .nil .nil)) (.node [v5, v66, v98, v113, v125, v141, v158] (.node [v3, v66, v98, v113, v125, v141, v158] .nil .nil) (.node [v9, v66, v98, v113, v125, v141, v158] .nil .nil))) (.node [v19, v66, v98, v113, v125, v141, v158] (.node [v12, v66, v98, v113, v125, v141, v158] (.node [v11, v66, v98, v113, v125, v141, v158] .nil .nil) (.node [v15, v66, v98, v113, v125, v141, v158] .nil .nil)) (.node [v21, v66, v98, v113, v125, v141, v158] (.node [v20, v66, v98, v113, v125, v141, v158] .nil .nil) (.node [v22, v66, v98, v113, v125, v141, v158] .nil .nil)))) (.node [v46, v66, v98, v113, v125, v141, v158] (.node [v35, v66, v98, v113, v125, v141, v158] (.node [v32, v66, v98, v113, v125, v141, v158] (.node [v31, v66, v98, v113, v125, v141, v158] .nil .nil) (.node [v33, v66, v98, v113, v125, v141, v158] .nil .nil)) (.node [v38, v66, v98, v113, v125, v141, v158] (.node [v37, v66, v98, v113, v125, v141, v158] .nil .nil) (.node [v45, v66, v98, v113, v125, v141, v158] .nil .nil))) (.node [v53, v66, v98, v113, v125, v141, v158] (.node [v49, v66, v98, v113, v125, v141, v158] (.node [v47, v66, v98, v113, v125, v141, v158] .nil .nil) (.node [v52, v66, v98, v113, v125, v141, v158] .nil .nil)) (.node [v62, v66, v98, v113, v125, v141, v158] (.node [v60, v66, v98, v113, v125, v141, v158] .nil .nil) (.node [v63, v66, v98, v113, v125, v141] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6l_ok : everyKey (rowOK 5 level5) level6l = true := by decide +kernel
def level6r : BinaryTree (List W) := (.node [v66, v98, v113, v125, v131, v141, v158] (.node [v66, v91, v98, v113, v125, v141, v158] (.node [v66, v78, v98, v113, v125, v141, v158] (.node [v66, v73, v98, v113, v125, v141, v158] (.node [v66, v70, v98, v113, v125, v141, v158] .nil .nil) (.node [v66, v76, v98, v113, v125, v141, v158] .nil .nil)) (.node [v66, v82, v98, v113, v125, v141, v158] (.node [v66, v79, v98, v113, v125, v141, v158] .nil .nil) (.node [v66, v89, v98, v113, v125, v141, v158] .nil .nil))) (.node [v66, v98, v111, v113, v125, v141, v158] (.node [v66, v98, v104, v113, v125, v141, v158] (.node [v66, v96, v98, v113, v125, v141, v158] .nil .nil) (.node [v66, v98, v108, v113, v125, v141, v158] .nil .nil)) (.node [v66, v98, v113, v120, v125, v141, v158] (.node [v66, v98, v113, v119, v125, v141, v158] .nil .nil) (.node [v66, v98, v113, v122, v125, v141, v158] .nil .nil)))) (.node [v66, v98, v113, v125, v141, v158, v159] (.node [v66, v98, v113, v125, v141, v147, v158] (.node [v66, v98, v113, v125, v137, v141, v158] (.node [v66, v98, v113, v125, v136, v141, v158] .nil .nil) (.node [v66, v98, v113, v125, v138, v141, v158] .nil .nil)) (.node [v66, v98, v113, v125, v141, v152, v158] (.node [v66, v98, v113, v125, v141, v149, v158] .nil .nil) (.node [v66, v98, v113, v125, v141, v155, v158] .nil .nil))) (.node [v66, v98, v113, v125, v141, v158, v172] (.node [v66, v98, v113, v125, v141, v158, v169] (.node [v66, v98, v113, v125, v141, v158, v166] .nil .nil) (.node [v66, v98, v113, v125, v141, v158, v171] .nil .nil)) (.node [v66, v98, v113, v125, v141, v158, v174] (.node [v66, v98, v113, v125, v141, v158, v173] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6r_ok : everyKey (rowOK 5 level5) level6r = true := by decide +kernel
def level6 : BinaryTree (List W) := .node [v63, v66, v98, v113, v125, v141, v158] level6l level6r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6_ok : everyKey (rowOK 5 level5) level6 = true := by
  change (_ && everyKey (rowOK 5 level5) level6l && everyKey (rowOK 5 level5) level6r) = true
  rw [level6l_ok, level6r_ok]
  decide +kernel
theorem closed6 : Closed 6 level6 := closed_next 5 (by decide) level6 level5 closed5 level6_ok
def level7 : BinaryTree (List W) := (.node [v66, v98, v113, v125, v141, v158] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7_ok : everyKey (rowOK 6 level6) level7 = true := by decide +kernel
theorem closed7 : Closed 7 level7 := closed_next 6 (by decide) level7 level6 closed6 level7_ok

theorem lower : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z 7 ins.toFinset :=
  @no_build 7 level7 ins (by decide +kernel) (by decide) closed7 (by decide +kernel)
def witness : List Gate := [⟨.and,[0,4]⟩, ⟨.or,[2,6]⟩, ⟨.and,[1,7]⟩, ⟨.or,[3,4]⟩, ⟨.and,[3,7]⟩, ⟨.or,[5,10]⟩, ⟨.and,[0,11]⟩, ⟨.and,[8,9]⟩, ⟨.or,[12,13]⟩]
theorem upper : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 9 ∧ ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xeaeaeaaaeac8e000 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact ⟨witness,14,by simp [witness],rfl,by decide +kernel⟩
end PEqualNP.Outside.L_meta_15619_aux

open PEqualNP.Outside.L_meta_15619_aux in
theorem PEqualNP.Outside.L_meta_15619 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941264042 * 2 ^ 32 + 3939033088) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941264042 * 2 ^ 32 + 3939033088) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  have code : 3941264042 * 2 ^ 32 + 3939033088 = 0xeaeaeaaaeac8e000 := by decide
  simp only [code] at h ⊢
  obtain ⟨C,legal,size,computes⟩ := h
  obtain ⟨gs,o,mono,bound,ev⟩ := replace 0xeaeaeaaaeac8e000 9 ins (by decide +kernel) sampled rfl lower upper C.gates C.output legal computes
  exact ⟨⟨gs,o⟩,mono,bound.trans size,ev⟩
