import PEqualNP.Defs

-- The live-wire search and circuit compiler are adapted from tacyon52 in L-meta-8639, pull request 12794 under Apache-2.0.
namespace PEqualNP.Outside.L_meta_15101_aux

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

-- The upper and lower halves represent opposite target labels on 40 pairs of assignments.
abbrev W := BitVec 80
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 40 := ((x >>> 40) ^^^ x).setWidth 40
def cuts (ws : List W) : BitVec 40 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 40) ++ (0 : BitVec 40)
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

def differs (i : Fin 40) (w : W) : Prop :=
  w.getLsbD (40+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 40) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 40+i.val < 80 := by omega
  have hi' : i.val < 80 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 40) :
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
  change (cuts ws)[j] = (BitVec.allOnes 40)[j]
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
  · change reachable av (BitVec.allOnes 80 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 80)
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

private def bit (k : Fin 80) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 80) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 80) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#80)[k.val] = false; simp
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
    (row : ∀ j : Fin 80, Nat.testBit T (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
    (width : ins.length = 6) (rejection : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z n ins.toFinset)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 6, if x i then 2^(i : ℕ) else 0)) : n < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ ins, holds ins.toFinset u := fun u hu =>
    .inr (.inr ⟨u,List.mem_toFinset.mpr hu,.inl rfl⟩)
  have evaluate (k : Fin 80) :
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
    (row : ∀ j : Fin 80, Nat.testBit T (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
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

def v0 : W := 0xa4a5548200
def v1 : W := 0xc421188200
def v2 : W := 0xe0241c0200
def v3 : W := 0xe4801c8000
def v4 : W := 0xe4a5400000
def v5 : W := 0xe4a55c8200
def v6 : W := 0x15aeb60000001c7f
def v7 : W := 0x15aeb60000149e7f
def v8 : W := 0x15aeb6a4a5549e7f
def v9 : W := 0x1ae796000018e38e
def v10 : W := 0x1f4bb200001f03f0
def v11 : W := 0x1fed2400001ffc00
def v12 : W := 0x1fefb60000037dff
def v13 : W := 0x1fefb6000017ffff
def v14 : W := 0x1fefb600001bffff
def v15 : W := 0x1fefb600001cffff
def v16 : W := 0x1fefb600001f7fff
def v17 : W := 0x1fefb600001f9fff
def v18 : W := 0x1fefb600001ffdff
def v19 : W := 0x1fefb600001ffe7f
def v20 : W := 0x1fefb6e4a5437dff
def v21 : W := 0x2980029a003980038e
def v22 : W := 0x2e0002d2003e0003f0
def v23 : W := 0x2f8002da003f8003fe
def v24 : W := 0x2fe00049003fe00000
def v25 : W := 0x2fe002db001aa001ff
def v26 : W := 0x2fe002db002540027f
def v27 : W := 0x2fe002db003ba003ff
def v28 : W := 0x2fe002db003dc003ff
def v29 : W := 0x2fe002db003ea003ff
def v30 : W := 0x2fe002db003f4003ff
def v31 : W := 0x2fe002db003fe001ff
def v32 : W := 0x2fe002db003fe003ff
def v33 : W := 0x2fe002dbe49abc81ff
def v34 : W := 0x2fffed6d003ffffc00
def v35 : W := 0x50180a40c070180e00e
def v36 : W := 0x5c000b40407c000fc00
def v37 : W := 0x5c180b40c07c180fc0e
def v38 : W := 0x5c1e0100907c1e00000
def v39 : W := 0x5c1e0b40d0340a07c0f
def v40 : W := 0x5c1e0b40d0481409c0f
def v41 : W := 0x5c1e0b40d0741a0fc0f
def v42 : W := 0x5c1e0b40d0781c0fc0f
def v43 : W := 0x5c1e0b40d07c0a0fc0f
def v44 : W := 0x5c1e0b40d07c140fc0f
def v45 : W := 0x5c1e0b40d07c1e07c0f
def v46 : W := 0x5c1e0b40d07c1e0fc0f
def v47 : W := 0x5c1e0b40de364bc7e0f
def v48 : W := 0x5c1ff5bbb07c1ff03f0
def v49 : W := 0x5ee00b6d607fe00fff0
def v50 : W := 0x5efe0104907ffe00000
def v51 : W := 0x28060508603806070070
def v52 : W := 0x28c005182038c0071c00
def v53 : W := 0x28c605186038c6071c70
def v54 : W := 0x28c660104138c6600000
def v55 : W := 0x28c66518611842231c71
def v56 : W := 0x28c66518612084441c71
def v57 : W := 0x28c66518613846271c71
def v58 : W := 0x28c66518613886471c71
def v59 : W := 0x28c665186138c2271c71
def v60 : W := 0x28c665186138c4471c71
def v61 : W := 0x28c665186138c6631c71
def v62 : W := 0x28c665186138c6671c71
def v63 : W := 0x28c6651861dc633b9e71
def v64 : W := 0x28c67af7d738c678e38e
def v65 : W := 0x28e9851aba38f9871f8e
def v66 : W := 0x28efe0104938ffe00000
def v67 : W := 0x2d0785ac6c3f0787e07e
def v68 : W := 0x2dc7e010493fc7e00000
def v69 : W := 0x52100000005b5aa00000
def v70 : W := 0x52100a41001b5aa36180
def v71 : W := 0x52100a41004318886180
def v72 : W := 0x52100a4100581a0b0180
def v73 : W := 0x52100a41005b400b6000
def v74 : W := 0x52100a41005b5aa36180
def v75 : W := 0x52100a41005b5aab6180
def v76 : W := 0x52100a4100bffff7e380
def v77 : W := 0x521015aeb65b5ab49e7f
def v78 : W := 0x52101ae796431898e38e
def v79 : W := 0x52101f4bb2581a1f03f0
def v80 : W := 0x52101fed245b401ffc00
def v81 : W := 0x52101fefb61b5aa37dff
def v82 : W := 0x523fea43db5b654b627f
def v83 : W := 0x57d1eaf50d5c9b4b9d8f
def v84 : W := 0x7ad66f5961639ccc7df1
def v85 : W := 0x852990a69e842110820e
def v86 : W := 0xa82e150af2a024140270
def v87 : W := 0xadc015bc24a480149c00
def v88 : W := 0xadefe010490000000000
def v89 : W := 0xadefe01049a4a5400000
def v90 : W := 0xadefe01049a4a5548200
def v91 : W := 0xadefe01049a4bfe00000
def v92 : W := 0xadefe01049a7e5e00000
def v93 : W := 0xadefe01049bce7600000
def v94 : W := 0xadefe01049e4a5400000
def v95 : W := 0xadeff5beff0000001c7f
def v96 : W := 0xadeff5beff0000149e7f
def v97 : W := 0xadeff5beff0025401e7f
def v98 : W := 0xadeff5beff0481409c7f
def v99 : W := 0xadeff5beff2084441c7f
def v100 : W := 0xadeff5beff8421109e7f
def v101 : W := 0xadeff5beffa024141e7f
def v102 : W := 0xadeff5beffa480149c7f
def v103 : W := 0xadeff5beffa4a5401c7f
def v104 : W := 0xadeff5beffa4a5549e7f
def v105 : W := 0xadeff5beffe4a5549e7f
def v106 : W := 0xadeff5beffe4a55c9e7f
def v107 : W := 0xd2381a4392c038180380
def v108 : W := 0xd2381ae796c03818e38e
def v109 : W := 0xd2381f4bb2c0381f03f0
def v110 : W := 0xd7101ae504c70018e000
def v111 : W := 0xd7101ae796c70018e38e
def v112 : W := 0xd7101fed24c7001ffc00
def v113 : W := 0xd7381ae796c73818e380
def v114 : W := 0xd739800008c739800000
def v115 : W := 0xd7399ae79e031880618e
def v116 : W := 0xd7399ae79e031898e38e
def v117 : W := 0xd7399ae79e033980638e
def v118 : W := 0xd7399ae79e071980e18e
def v119 : W := 0xd7399ae79e431888618e
def v120 : W := 0xd7399ae79e873990e38e
def v121 : W := 0xd7399ae79ec33898638e
def v122 : W := 0xd7399ae79ec43918838e
def v123 : W := 0xd7399ae79ec71898e18e
def v124 : W := 0xd7399ae79ec72118e20e
def v125 : W := 0xd7399ae79ec73980618e
def v126 : W := 0xd7399ae79ec73998e38e
def v127 : W := 0xd7399ae79ee73d9ce38e
def v128 : W := 0xd7399ae79ee7b99ce38e
def v129 : W := 0xd7399ae79ee7bdd8e38e
def v130 : W := 0xd7399ae79ee7bddce38e
def v131 : W := 0xd73ffae7dfc73ff8e38e
def v132 : W := 0xd7f9faf79fc7f9f8e38e
def v133 : W := 0xfa101f4920f8001f0000
def v134 : W := 0xfa101f4bb2f8001f03f0
def v135 : W := 0xfa101fed24f8001ffc00
def v136 : W := 0xfa381f4bb2f8381f0380
def v137 : W := 0xfa3e000040f83e000000
def v138 : W := 0xfa3e1f4bf2181a0301f0
def v139 : W := 0xfa3e1f4bf2181a1f03f0
def v140 : W := 0xfa3e1f4bf2183e0303f0
def v141 : W := 0xfa3e1f4bf2381e0701f0
def v142 : W := 0xfa3e1f4bf2581a0b01f0
def v143 : W := 0xfa3e1f4bf2b83e1703f0
def v144 : W := 0xfa3e1f4bf2d83a1b03f0
def v145 : W := 0xfa3e1f4bf2e03c1c03f0
def v146 : W := 0xfa3e1f4bf2f81a1f01f0
def v147 : W := 0xfa3e1f4bf2f8241f0270
def v148 : W := 0xfa3e1f4bf2f83e0301f0
def v149 : W := 0xfa3e1f4bf2f83e1f03f0
def v150 : W := 0xfa3e1f4bf2fc3f1f83f0
def v151 : W := 0xfa3e1f4bf2fcbe1f83f0
def v152 : W := 0xfa3e1f4bf2fcbf5f03f0
def v153 : W := 0xfa3e1f4bf2fcbf5f83f0
def v154 : W := 0xfa3fff4bfbf83fff03f0
def v155 : W := 0xfafe7f5bf3f8fe7f03f0
def v156 : W := 0xff101fed24ff001fe000
def v157 : W := 0xff3f9feffeff3f9fe3fe
def v158 : W := 0xffd0001000ffc0000000
def v159 : W := 0xffd01ffd241b40037c00
def v160 : W := 0xffd01ffd241b401ffc00
def v161 : W := 0xffd01ffd241fc003fc00
def v162 : W := 0xffd01ffd243bc0077c00
def v163 : W := 0xffd01ffd245b400b7c00
def v164 : W := 0xffd01ffd24bfc017fc00
def v165 : W := 0xffd01ffd24df401bfc00
def v166 : W := 0xffd01ffd24e7801cfc00
def v167 : W := 0xffd01ffd24fb401f7c00
def v168 : W := 0xffd01ffd24fc801f9c00
def v169 : W := 0xffd01ffd24ffc0037c00
def v170 : W := 0xffd01ffd24ffc01ffc00
def v171 : W := 0xffd01ffd24ffe11ffe00
def v172 : W := 0xffd01ffd24ffe41ffe00
def v173 : W := 0xffd01ffd24ffe55ffc00
def v174 : W := 0xffd01ffd24ffe55ffe00
def v175 : W := 0xffd1fffd2dffc1fffc00
def v176 : W := 0xffd67ffd65ffc67ffc00
def v177 : W := 0xfff99fffbefff99fff8e
def v178 : W := 0xfffe1ffff6fffe1ffff0
def v179 : W := 0xffffe010491b5aa00000
def v180 : W := 0xffffe010491b7fe00000
def v181 : W := 0xffffe010491fdbe00000
def v182 : W := 0xffffe010493bdee00000
def v183 : W := 0xffffe010495b5aa00000
def v184 : W := 0xffffe01049bfffe00000
def v185 : W := 0xffffe01049df7ba00000
def v186 : W := 0xffffe01049e7bdc00000
def v187 : W := 0xffffe01049fb7ea00000
def v188 : W := 0xffffe01049fcbf400000
def v189 : W := 0xffffe01049ffdaa00000
def v190 : W := 0xffffe01049ffe5400000
def v191 : W := 0xffffe01049ffffe00000
def v192 : W := 0xffffe01049fffff48200
def v193 : W := 0xffffe01049fffff88200
def v194 : W := 0xffffe01049fffffc0200
def v195 : W := 0xffffe01049fffffc8000
def v196 : W := 0xffffea51491b5aa36180
def v197 : W := 0xffffea5149ffffe36180
def v198 : W := 0xffffea5149ffffe86180
def v199 : W := 0xffffea5149ffffeb0180
def v200 : W := 0xffffea5149ffffeb6000
def v201 : W := 0xfffff5befffffff49e7f
def v202 : W := 0xfffffa53dbfffff80380
def v203 : W := 0xfffffaf54dfffff8e000
def v204 : W := 0xfffffaf7dfe7bdd8e38e
def v205 : W := 0xfffffaf7dffffff8e38e
def v206 : W := 0xffffff5969ffffff0000
def v207 : W := 0xffffff5bfbfcbf5f03f0
def v208 : W := 0xffffff5bfbffffff03f0
def v209 : W := 0xfffffffd6dffe55ffc00
def v210 : W := 0xfffffffd6dfffffffc00
def v211 : W := 0xffffffffff0318807dff
def v212 : W := 0xffffffffff181a031dff
def v213 : W := 0xffffffffff1b40037c7f
def v214 : W := 0xffffffffff1b5aa37dff
def v215 : W := 0xffffffffffbffff7ffff
def v216 : W := 0xffffffffffdf7bbbffff
def v217 : W := 0xffffffffffe7bddcffff
def v218 : W := 0xfffffffffffb7ebf7fff
def v219 : W := 0xfffffffffffcbf5f9fff
def v220 : W := 0xffffffffffffdabffdff
def v221 : W := 0xffffffffffffe55ffe7f
def v222 : W := 0xffffffffffffffe37dff

def ins : List W := [v214, v104, v126, v149, v170, v191]
theorem sampled : ∀ j : Fin 80, Nat.testBit 0xa8888888a8808000 (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
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
def level4l : BinaryTree (List W) := (.node [v48, v104, v126, v170, v214] (.node [v12, v95, v126, v149, v159] (.node [v7, v95, v126, v138, v170] (.node [v6, v95, v126, v149, v159] (.node [v6, v95, v126, v138, v170] (.node [v6, v95, v115, v149, v170] .nil .nil) .nil) (.node [v7, v95, v115, v149, v170] .nil .nil)) (.node [v12, v95, v115, v149, v170] (.node [v7, v95, v126, v149, v159] .nil .nil) (.node [v12, v95, v126, v138, v170] .nil .nil))) (.node [v34, v104, v126, v149, v214] (.node [v25, v95, v126, v138, v191] (.node [v25, v95, v115, v149, v191] (.node [v20, v104, v126, v149, v170] .nil .nil) .nil) (.node [v33, v104, v126, v149, v191] .nil .nil)) (.node [v39, v95, v126, v159, v191] (.node [v39, v95, v115, v170, v191] .nil .nil) (.node [v47, v104, v126, v170, v191] .nil .nil)))) (.node [v77, v126, v149, v170, v214] (.node [v64, v104, v149, v170, v214] (.node [v55, v95, v149, v159, v191] (.node [v55, v95, v138, v170, v191] (.node [v49, v104, v126, v191, v214] .nil .nil) .nil) (.node [v63, v104, v149, v170, v191] .nil .nil)) (.node [v67, v104, v170, v191, v214] (.node [v65, v104, v149, v191, v214] .nil .nil) (.node [v76, v126, v149, v170, v191] .nil .nil))) (.node [v85, v149, v170, v191, v211] (.node [v83, v126, v170, v191, v214] (.node [v82, v126, v149, v191, v214] (.node [v81, v95, v126, v149, v170] .nil .nil) .nil) (.node [v84, v149, v170, v191, v214] .nil .nil)) (.node [v87, v126, v149, v191, v213] (.node [v86, v126, v170, v191, v212] .nil .nil) (.node [v88, v95, v115, v149, v170] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4l_ok : everyKey (rowOK 3 level3) level4l = true := by decide +kernel
def level4r : BinaryTree (List W) := (.node [v95, v126, v149, v159, v179] (.node [v95, v117, v149, v170, v191] (.node [v95, v115, v138, v170, v191] (.node [v89, v95, v126, v138, v170] (.node [v89, v95, v115, v149, v170] (.node [v88, v95, v126, v149, v159] .nil .nil) .nil) (.node [v89, v95, v126, v149, v159] .nil .nil)) (.node [v95, v115, v149, v170, v179] (.node [v95, v115, v149, v159, v191] .nil .nil) (.node [v95, v115, v149, v170, v191] .nil .nil))) (.node [v95, v126, v138, v170, v191] (.node [v95, v126, v138, v159, v191] (.node [v95, v120, v149, v170, v191] (.node [v95, v118, v149, v170, v191] .nil .nil) .nil) (.node [v95, v126, v138, v170, v179] .nil .nil)) (.node [v95, v126, v141, v170, v191] (.node [v95, v126, v140, v170, v191] .nil .nil) (.node [v95, v126, v143, v170, v191] .nil .nil)))) (.node [v104, v107, v156, v191, v214] (.node [v95, v126, v149, v170, v196] (.node [v95, v126, v149, v162, v191] (.node [v95, v126, v149, v161, v191] (.node [v95, v126, v149, v159, v191] .nil .nil) .nil) (.node [v95, v126, v149, v164, v191] .nil .nil)) (.node [v101, v126, v138, v170, v191] (.node [v100, v115, v149, v170, v191] .nil .nil) (.node [v102, v126, v149, v159, v191] .nil .nil))) (.node [v104, v126, v138, v159, v179] (.node [v104, v115, v138, v170, v179] (.node [v104, v113, v133, v191, v214] (.node [v104, v110, v136, v191, v214] .nil .nil) .nil) (.node [v104, v115, v149, v159, v179] .nil .nil)) (.node [v104, v149, v204, v209, v214] (.node [v104, v126, v207, v209, v214] .nil .nil) (.node [v104, v170, v204, v207, v214] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4r_ok : everyKey (rowOK 3 level3) level4r = true := by decide +kernel
def level4 : BinaryTree (List W) := .node [v88, v95, v126, v138, v170] level4l level4r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4_ok : everyKey (rowOK 3 level3) level4 = true := by
  change (_ && everyKey (rowOK 3 level3) level4l && everyKey (rowOK 3 level3) level4r) = true
  rw [level4l_ok, level4r_ok]
  decide +kernel
theorem closed4 : Closed 4 level4 := closed_next 3 (by decide) level4 level3 closed3 level4_ok
def level5lll : BinaryTree (List W) := (.node [v7, v69, v126, v149, v170, v214] (.node [v3, v25, v104, v126, v149, v191] (.node [v1, v55, v104, v149, v170, v191] (.node [v0, v104, v126, v138, v170, v191] (.node [v0, v104, v115, v149, v170, v191] (.node [v0, v70, v126, v149, v170, v191] .nil .nil) .nil) (.node [v0, v104, v126, v149, v159, v191] .nil .nil)) (.node [v2, v39, v104, v126, v170, v191] (.node [v1, v95, v126, v149, v170, v191] .nil .nil) (.node [v2, v95, v126, v149, v170, v191] .nil .nil))) (.node [v6, v104, v126, v149, v170, v214] (.node [v5, v104, v126, v149, v170, v191] (.node [v4, v12, v104, v126, v149, v170] (.node [v3, v95, v126, v149, v170, v191] .nil .nil) .nil) (.node [v6, v95, v126, v149, v170, v214] .nil .nil)) (.node [v7, v39, v104, v126, v170, v214] (.node [v7, v25, v104, v126, v149, v214] .nil .nil) (.node [v7, v55, v104, v149, v170, v214] .nil .nil)))) (.node [v9, v54, v104, v149, v170, v214] (.node [v7, v104, v126, v138, v170, v214] (.node [v7, v95, v126, v149, v170, v214] (.node [v7, v89, v126, v149, v170, v214] (.node [v7, v70, v126, v149, v170, v214] .nil .nil) .nil) (.node [v7, v104, v115, v149, v170, v214] .nil .nil)) (.node [v7, v104, v126, v149, v170, v214] (.node [v7, v104, v126, v149, v159, v214] .nil .nil) (.node [v8, v104, v126, v149, v170, v214] .nil .nil))) (.node [v12, v39, v104, v126, v170, v214] (.node [v11, v24, v104, v126, v149, v214] (.node [v10, v38, v104, v126, v170, v214] .nil .nil) (.node [v12, v25, v104, v126, v149, v214] .nil .nil)) (.node [v12, v70, v126, v149, v170, v214] (.node [v12, v55, v104, v149, v170, v214] .nil .nil) (.node [v12, v95, v126, v149, v170, v214] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lll_ok : everyKey (rowOK 4 level4) level5lll = true := by decide +kernel
def level5llr : BinaryTree (List W) := (.node [v25, v70, v126, v149, v191, v214] (.node [v17, v104, v126, v149, v170, v214] (.node [v13, v104, v126, v149, v170, v214] (.node [v12, v104, v126, v149, v170, v179] (.node [v12, v104, v126, v149, v159, v214] (.node [v12, v104, v126, v138, v170, v214] .nil .nil) .nil) (.node [v12, v104, v126, v149, v170, v214] .nil .nil)) (.node [v15, v104, v126, v149, v170, v214] (.node [v14, v104, v126, v149, v170, v214] .nil .nil) (.node [v16, v104, v126, v149, v170, v214] .nil .nil))) (.node [v22, v36, v104, v126, v191, v214] (.node [v19, v104, v126, v149, v170, v214] (.node [v18, v104, v126, v149, v170, v214] .nil .nil) (.node [v21, v52, v104, v149, v191, v214] .nil .nil)) (.node [v25, v39, v104, v126, v191, v214] (.node [v23, v104, v126, v149, v191, v214] .nil .nil) (.node [v25, v55, v104, v149, v191, v214] .nil .nil)))) (.node [v27, v104, v126, v149, v191, v214] (.node [v25, v104, v126, v149, v159, v191] (.node [v25, v104, v115, v149, v191, v214] (.node [v25, v95, v126, v149, v191, v214] (.node [v25, v89, v104, v126, v149, v214] .nil .nil) .nil) (.node [v25, v104, v126, v138, v191, v214] .nil .nil)) (.node [v25, v104, v126, v149, v191, v214] (.node [v25, v104, v126, v149, v179, v214] .nil .nil) (.node [v26, v73, v126, v149, v191, v214] .nil .nil))) (.node [v31, v104, v126, v149, v191, v214] (.node [v29, v104, v126, v149, v191, v214] (.node [v28, v104, v126, v149, v191, v214] .nil .nil) (.node [v30, v104, v126, v149, v191, v214] .nil .nil)) (.node [v35, v51, v104, v170, v191, v214] (.node [v32, v104, v126, v149, v191, v214] .nil .nil) (.node [v37, v104, v126, v170, v191, v214] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llr_ok : everyKey (rowOK 4 level4) level5llr = true := by decide +kernel
def level5ll : BinaryTree (List W) := .node [v12, v104, v115, v149, v170, v214] level5lll level5llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5ll_ok : everyKey (rowOK 4 level4) level5ll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lll && everyKey (rowOK 4 level4) level5llr) = true
  rw [level5lll_ok, level5llr_ok]
  decide +kernel
def level5lrl : BinaryTree (List W) := (.node [v53, v104, v149, v170, v191, v214] (.node [v40, v72, v126, v170, v191, v214] (.node [v39, v104, v126, v138, v170, v191] (.node [v39, v95, v126, v170, v191, v214] (.node [v39, v89, v104, v126, v170, v214] (.node [v39, v70, v126, v170, v191, v214] .nil .nil) .nil) (.node [v39, v104, v115, v170, v191, v214] .nil .nil)) (.node [v39, v104, v126, v170, v179, v214] (.node [v39, v104, v126, v159, v191, v214] .nil .nil) (.node [v39, v104, v126, v170, v191, v214] .nil .nil))) (.node [v44, v104, v126, v170, v191, v214] (.node [v42, v104, v126, v170, v191, v214] (.node [v41, v104, v126, v170, v191, v214] .nil .nil) (.node [v43, v104, v126, v170, v191, v214] .nil .nil)) (.node [v46, v104, v126, v170, v191, v214] (.node [v45, v104, v126, v170, v191, v214] .nil .nil) (.node [v50, v104, v126, v149, v170, v214] .nil .nil)))) (.node [v56, v71, v149, v170, v191, v214] (.node [v55, v104, v138, v170, v191, v214] (.node [v55, v95, v149, v170, v191, v214] (.node [v55, v89, v104, v149, v170, v214] (.node [v55, v70, v149, v170, v191, v214] .nil .nil) .nil) (.node [v55, v104, v115, v149, v170, v191] .nil .nil)) (.node [v55, v104, v149, v170, v179, v214] (.node [v55, v104, v149, v159, v191, v214] .nil .nil) (.node [v55, v104, v149, v170, v191, v214] .nil .nil))) (.node [v60, v104, v149, v170, v191, v214] (.node [v58, v104, v149, v170, v191, v214] (.node [v57, v104, v149, v170, v191, v214] .nil .nil) (.node [v59, v104, v149, v170, v191, v214] .nil .nil)) (.node [v62, v104, v149, v170, v191, v214] (.node [v61, v104, v149, v170, v191, v214] .nil .nil) (.node [v66, v104, v126, v149, v170, v214] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrl_ok : everyKey (rowOK 4 level4) level5lrl = true := by decide +kernel
def level5lrr : BinaryTree (List W) := (.node [v80, v104, v126, v149, v191, v214] (.node [v70, v126, v149, v170, v197, v214] (.node [v70, v126, v138, v170, v191, v214] (.node [v70, v95, v126, v149, v170, v191] (.node [v70, v94, v126, v149, v170, v214] (.node [v70, v89, v126, v149, v170, v214] .nil .nil) .nil) (.node [v70, v115, v149, v170, v191, v214] .nil .nil)) (.node [v70, v126, v149, v170, v179, v214] (.node [v70, v126, v149, v159, v191, v214] .nil .nil) (.node [v70, v126, v149, v170, v191, v214] .nil .nil))) (.node [v78, v104, v149, v170, v191, v214] (.node [v75, v126, v149, v170, v191, v214] (.node [v74, v126, v149, v170, v191, v214] .nil .nil) (.node [v78, v89, v104, v149, v170, v214] .nil .nil)) (.node [v79, v104, v126, v170, v191, v214] (.node [v79, v89, v104, v126, v170, v214] .nil .nil) (.node [v80, v89, v104, v126, v149, v214] .nil .nil)))) (.node [v89, v104, v126, v138, v170, v214] (.node [v88, v95, v126, v149, v170, v214] (.node [v86, v126, v170, v191, v214, v219] (.node [v85, v149, v170, v191, v214, v217] (.node [v81, v104, v126, v149, v170, v214] .nil .nil) .nil) (.node [v87, v126, v149, v191, v214, v221] .nil .nil)) (.node [v89, v95, v126, v149, v170, v214] (.node [v88, v104, v126, v149, v170, v214] .nil .nil) (.node [v89, v104, v115, v149, v170, v214] .nil .nil))) (.node [v89, v104, v126, v170, v207, v214] (.node [v89, v104, v126, v149, v170, v214] (.node [v89, v104, v126, v149, v159, v214] .nil .nil) (.node [v89, v104, v126, v149, v209, v214] .nil .nil)) (.node [v89, v126, v149, v170, v201, v214] (.node [v89, v104, v149, v170, v204, v214] .nil .nil) (.node [v90, v104, v126, v149, v170, v214] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrr_ok : everyKey (rowOK 4 level4) level5lrr = true := by decide +kernel
def level5lr : BinaryTree (List W) := .node [v68, v104, v126, v149, v170, v214] level5lrl level5lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lr_ok : everyKey (rowOK 4 level4) level5lr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrl && everyKey (rowOK 4 level4) level5lrr) = true
  rw [level5lrl_ok, level5lrr_ok]
  decide +kernel
def level5l : BinaryTree (List W) := .node [v39, v55, v104, v170, v191, v214] level5ll level5lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5l_ok : everyKey (rowOK 4 level4) level5l = true := by
  change (_ && everyKey (rowOK 4 level4) level5ll && everyKey (rowOK 4 level4) level5lr) = true
  rw [level5ll_ok, level5lr_ok]
  decide +kernel
def level5rll : BinaryTree (List W) := (.node [v95, v126, v149, v170, v191, v214] (.node [v95, v115, v149, v170, v191, v214] (.node [v95, v104, v126, v138, v170, v191] (.node [v94, v104, v126, v149, v170, v214] (.node [v93, v104, v126, v149, v170, v214] (.node [v92, v104, v126, v149, v170, v214] .nil .nil) .nil) (.node [v95, v104, v115, v149, v170, v191] .nil .nil)) (.node [v95, v115, v126, v149, v170, v191] (.node [v95, v104, v126, v149, v159, v191] .nil .nil) (.node [v95, v115, v149, v170, v191] .nil .nil))) (.node [v95, v126, v149, v159, v170, v191] (.node [v95, v126, v138, v170, v191] (.node [v95, v126, v138, v149, v170, v191] .nil .nil) (.node [v95, v126, v138, v170, v191, v214] .nil .nil)) (.node [v95, v126, v149, v159, v191, v214] (.node [v95, v126, v149, v159, v191] .nil .nil) (.node [v95, v126, v149, v170, v179, v214] .nil .nil)))) (.node [v103, v126, v149, v170, v191, v214] (.node [v99, v126, v149, v170, v191, v214] (.node [v97, v126, v149, v170, v191, v214] (.node [v96, v126, v149, v170, v191, v214] (.node [v95, v126, v149, v170, v191, v215] .nil .nil) .nil) (.node [v98, v126, v149, v170, v191, v214] .nil .nil)) (.node [v101, v126, v149, v170, v191, v214] (.node [v100, v126, v149, v170, v191, v214] .nil .nil) (.node [v102, v126, v149, v170, v191, v214] .nil .nil))) (.node [v104, v110, v149, v177, v191, v214] (.node [v104, v108, v149, v170, v191, v214] (.node [v104, v107, v157, v170, v191, v214] .nil .nil) (.node [v104, v109, v126, v170, v191, v214] .nil .nil)) (.node [v104, v112, v126, v149, v191, v214] (.node [v104, v111, v149, v170, v191, v214] .nil .nil) (.node [v104, v113, v149, v170, v191, v214] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rll_ok : everyKey (rowOK 4 level4) level5rll = true := by decide +kernel
def level5rlr : BinaryTree (List W) := (.node [v104, v126, v134, v170, v191, v214] (.node [v104, v119, v149, v170, v191, v214] (.node [v104, v115, v149, v170, v191, v216] (.node [v104, v115, v149, v170, v179, v214] (.node [v104, v115, v149, v159, v191, v214] (.node [v104, v115, v138, v170, v191, v214] .nil .nil) .nil) (.node [v104, v115, v149, v170, v191, v214] .nil .nil)) (.node [v104, v117, v149, v170, v191, v214] (.node [v104, v116, v149, v170, v191, v214] .nil .nil) (.node [v104, v118, v149, v170, v191, v214] .nil .nil))) (.node [v104, v123, v149, v170, v191, v214] (.node [v104, v121, v149, v170, v191, v214] (.node [v104, v120, v149, v170, v191, v214] .nil .nil) (.node [v104, v122, v149, v170, v191, v214] .nil .nil)) (.node [v104, v125, v149, v170, v191, v214] (.node [v104, v124, v149, v170, v191, v214] .nil .nil) (.node [v104, v126, v133, v178, v191, v214] .nil .nil)))) (.node [v104, v126, v140, v170, v191, v214] (.node [v104, v126, v138, v170, v179, v214] (.node [v104, v126, v137, v170, v208, v214] (.node [v104, v126, v136, v170, v191, v214] (.node [v104, v126, v135, v149, v191, v214] .nil .nil) .nil) (.node [v104, v126, v138, v159, v191, v214] .nil .nil)) (.node [v104, v126, v138, v170, v191, v218] (.node [v104, v126, v138, v170, v191, v214] .nil .nil) (.node [v104, v126, v139, v170, v191, v214] .nil .nil))) (.node [v104, v126, v144, v170, v191, v214] (.node [v104, v126, v142, v170, v191, v214] (.node [v104, v126, v141, v170, v191, v214] .nil .nil) (.node [v104, v126, v143, v170, v191, v214] .nil .nil)) (.node [v104, v126, v146, v170, v191, v214] (.node [v104, v126, v145, v170, v191, v214] .nil .nil) (.node [v104, v126, v147, v170, v191, v214] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlr_ok : everyKey (rowOK 4 level4) level5rlr = true := by decide +kernel
def level5rl : BinaryTree (List W) := .node [v104, v114, v149, v170, v205, v214] level5rll level5rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rl_ok : everyKey (rowOK 4 level4) level5rl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rll && everyKey (rowOK 4 level4) level5rlr) = true
  rw [level5rll_ok, level5rlr_ok]
  decide +kernel
def level5rrl : BinaryTree (List W) := (.node [v104, v126, v149, v170, v179, v222] (.node [v104, v126, v149, v163, v191, v214] (.node [v104, v126, v149, v159, v191, v220] (.node [v104, v126, v149, v159, v179, v214] (.node [v104, v126, v149, v158, v210, v214] (.node [v104, v126, v149, v156, v191, v214] .nil .nil) .nil) (.node [v104, v126, v149, v159, v191, v214] .nil .nil)) (.node [v104, v126, v149, v161, v191, v214] (.node [v104, v126, v149, v160, v191, v214] .nil .nil) (.node [v104, v126, v149, v162, v191, v214] .nil .nil))) (.node [v104, v126, v149, v167, v191, v214] (.node [v104, v126, v149, v165, v191, v214] (.node [v104, v126, v149, v164, v191, v214] .nil .nil) (.node [v104, v126, v149, v166, v191, v214] .nil .nil)) (.node [v104, v126, v149, v169, v191, v214] (.node [v104, v126, v149, v168, v191, v214] .nil .nil) (.node [v104, v126, v149, v170, v179, v214] .nil .nil)))) (.node [v104, v126, v149, v170, v188, v214] (.node [v104, v126, v149, v170, v184, v214] (.node [v104, v126, v149, v170, v182, v214] (.node [v104, v126, v149, v170, v181, v214] (.node [v104, v126, v149, v170, v180, v214] .nil .nil) .nil) (.node [v104, v126, v149, v170, v183, v214] .nil .nil)) (.node [v104, v126, v149, v170, v186, v214] (.node [v104, v126, v149, v170, v185, v214] .nil .nil) (.node [v104, v126, v149, v170, v187, v214] .nil .nil))) (.node [v104, v126, v149, v170, v191, v212] (.node [v104, v126, v149, v170, v190, v214] (.node [v104, v126, v149, v170, v189, v214] .nil .nil) (.node [v104, v126, v149, v170, v191, v211] .nil .nil)) (.node [v104, v126, v149, v170, v191, v214] (.node [v104, v126, v149, v170, v191, v213] .nil .nil) (.node [v104, v126, v149, v170, v192, v214] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrl_ok : everyKey (rowOK 4 level4) level5rrl = true := by decide +kernel
def level5rrr : BinaryTree (List W) := (.node [v104, v126, v149, v191, v209, v214] (.node [v104, v126, v149, v170, v203, v214] (.node [v104, v126, v149, v170, v198, v214] (.node [v104, v126, v149, v170, v196, v214] (.node [v104, v126, v149, v170, v195, v214] (.node [v104, v126, v149, v170, v194, v214] .nil .nil) .nil) (.node [v104, v126, v149, v170, v197, v214] .nil .nil)) (.node [v104, v126, v149, v170, v200, v214] (.node [v104, v126, v149, v170, v199, v214] .nil .nil) (.node [v104, v126, v149, v170, v202, v214] .nil .nil))) (.node [v104, v126, v149, v173, v191, v214] (.node [v104, v126, v149, v171, v191, v214] (.node [v104, v126, v149, v170, v206, v214] .nil .nil) (.node [v104, v126, v149, v172, v191, v214] .nil .nil)) (.node [v104, v126, v149, v175, v191, v214] (.node [v104, v126, v149, v174, v191, v214] .nil .nil) (.node [v104, v126, v149, v176, v191, v214] .nil .nil)))) (.node [v104, v128, v149, v170, v191, v214] (.node [v104, v126, v154, v170, v191, v214] (.node [v104, v126, v152, v170, v191, v214] (.node [v104, v126, v151, v170, v191, v214] (.node [v104, v126, v150, v170, v191, v214] .nil .nil) .nil) (.node [v104, v126, v153, v170, v191, v214] .nil .nil)) (.node [v104, v126, v170, v191, v207, v214] (.node [v104, v126, v155, v170, v191, v214] .nil .nil) (.node [v104, v127, v149, v170, v191, v214] .nil .nil))) (.node [v104, v132, v149, v170, v191, v214] (.node [v104, v130, v149, v170, v191, v214] (.node [v104, v129, v149, v170, v191, v214] .nil .nil) (.node [v104, v131, v149, v170, v191, v214] .nil .nil)) (.node [v105, v126, v149, v170, v191, v214] (.node [v104, v149, v170, v191, v204, v214] .nil .nil) (.node [v106, v126, v149, v170, v191, v214] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrr_ok : everyKey (rowOK 4 level4) level5rrr = true := by decide +kernel
def level5rr : BinaryTree (List W) := .node [v104, v126, v149, v170, v193, v214] level5rrl level5rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rr_ok : everyKey (rowOK 4 level4) level5rr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrl && everyKey (rowOK 4 level4) level5rrr) = true
  rw [level5rrl_ok, level5rrr_ok]
  decide +kernel
def level5r : BinaryTree (List W) := .node [v104, v126, v148, v170, v191, v214] level5rl level5rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5r_ok : everyKey (rowOK 4 level4) level5r = true := by
  change (_ && everyKey (rowOK 4 level4) level5rl && everyKey (rowOK 4 level4) level5rr) = true
  rw [level5rl_ok, level5rr_ok]
  decide +kernel
def level5 : BinaryTree (List W) := .node [v91, v104, v126, v149, v170, v214] level5l level5r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5_ok : everyKey (rowOK 4 level4) level5 = true := by
  change (_ && everyKey (rowOK 4 level4) level5l && everyKey (rowOK 4 level4) level5r) = true
  rw [level5l_ok, level5r_ok]
  decide +kernel
theorem closed5 : Closed 5 level5 := closed_next 4 (by decide) level5 level4 closed4 level5_ok
def level6l : BinaryTree (List W) := (.node [v35, v104, v126, v149, v170, v191, v214] (.node [v11, v104, v126, v149, v170, v191, v214] (.node [v4, v104, v126, v149, v170, v191, v214] (.node [v2, v104, v126, v149, v170, v191, v214] (.node [v1, v104, v126, v149, v170, v191, v214] (.node [v0, v104, v126, v149, v170, v191, v214] .nil .nil) .nil) (.node [v3, v104, v126, v149, v170, v191, v214] .nil .nil)) (.node [v9, v104, v126, v149, v170, v191, v214] (.node [v7, v104, v126, v149, v170, v214] (.node [v7, v104, v126, v149, v170, v191, v214] .nil .nil) .nil) (.node [v10, v104, v126, v149, v170, v191, v214] .nil .nil))) (.node [v24, v104, v126, v149, v170, v191, v214] (.node [v21, v104, v126, v149, v170, v191, v214] (.node [v12, v104, v126, v149, v170, v214] (.node [v12, v104, v126, v149, v170, v191, v214] .nil .nil) .nil) (.node [v22, v104, v126, v149, v170, v191, v214] .nil .nil)) (.node [v25, v104, v126, v149, v191, v214] (.node [v25, v104, v126, v149, v170, v191, v214] .nil .nil) (.node [v26, v104, v126, v149, v170, v191, v214] .nil .nil)))) (.node [v55, v104, v126, v149, v170, v191, v214] (.node [v40, v104, v126, v149, v170, v191, v214] (.node [v39, v104, v126, v149, v170, v191, v214] (.node [v38, v104, v126, v149, v170, v191, v214] (.node [v36, v104, v126, v149, v170, v191, v214] .nil .nil) .nil) (.node [v39, v104, v126, v170, v191, v214] .nil .nil)) (.node [v52, v104, v126, v149, v170, v191, v214] (.node [v51, v104, v126, v149, v170, v191, v214] .nil .nil) (.node [v54, v104, v126, v149, v170, v191, v214] .nil .nil))) (.node [v70, v126, v149, v170, v191, v214] (.node [v69, v104, v126, v149, v170, v191, v214] (.node [v56, v104, v126, v149, v170, v191, v214] (.node [v55, v104, v149, v170, v191, v214] .nil .nil) .nil) (.node [v70, v104, v126, v149, v170, v191, v214] .nil .nil)) (.node [v72, v104, v126, v149, v170, v191, v214] (.node [v71, v104, v126, v149, v170, v191, v214] .nil .nil) (.node [v73, v104, v126, v149, v170, v191, v214] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6l_ok : everyKey (rowOK 5 level5) level6l = true := by decide +kernel
def level6r : BinaryTree (List W) := (.node [v104, v126, v149, v159, v170, v191, v214] (.node [v104, v114, v126, v149, v170, v191, v214] (.node [v95, v104, v126, v149, v170, v191, v214] (.node [v89, v104, v126, v149, v170, v191, v214] (.node [v87, v104, v126, v149, v170, v191, v214] (.node [v86, v104, v126, v149, v170, v191, v214] .nil .nil) .nil) (.node [v89, v104, v126, v149, v170, v214] .nil .nil)) (.node [v104, v107, v126, v149, v170, v191, v214] (.node [v95, v126, v149, v170, v191, v214] .nil .nil) (.node [v104, v110, v126, v149, v170, v191, v214] .nil .nil))) (.node [v104, v126, v138, v149, v170, v191, v214] (.node [v104, v126, v133, v149, v170, v191, v214] (.node [v104, v115, v149, v170, v191, v214] (.node [v104, v115, v126, v149, v170, v191, v214] .nil .nil) .nil) (.node [v104, v126, v137, v149, v170, v191, v214] .nil .nil)) (.node [v104, v126, v149, v157, v170, v191, v214] (.node [v104, v126, v138, v170, v191, v214] .nil .nil) (.node [v104, v126, v149, v158, v170, v191, v214] .nil .nil)))) (.node [v104, v126, v149, v170, v191, v210, v214] (.node [v104, v126, v149, v170, v179, v214] (.node [v104, v126, v149, v170, v178, v191, v214] (.node [v104, v126, v149, v170, v177, v191, v214] (.node [v104, v126, v149, v159, v191, v214] .nil .nil) .nil) (.node [v104, v126, v149, v170, v179, v191, v214] .nil .nil)) (.node [v104, v126, v149, v170, v191, v205, v214] (.node [v104, v126, v149, v170, v191, v201, v214] .nil .nil) (.node [v104, v126, v149, v170, v191, v208, v214] .nil .nil))) (.node [v104, v126, v149, v170, v191, v214, v219] (.node [v104, v126, v149, v170, v191, v214, v217] (.node [v104, v126, v149, v170, v191, v214, v216] (.node [v104, v126, v149, v170, v191, v214, v215] .nil .nil) .nil) (.node [v104, v126, v149, v170, v191, v214, v218] .nil .nil)) (.node [v104, v126, v149, v170, v191, v214, v221] (.node [v104, v126, v149, v170, v191, v214, v220] .nil .nil) (.node [v104, v126, v149, v170, v191, v214, v222] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6r_ok : everyKey (rowOK 5 level5) level6r = true := by decide +kernel
def level6 : BinaryTree (List W) := .node [v85, v104, v126, v149, v170, v191, v214] level6l level6r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6_ok : everyKey (rowOK 5 level5) level6 = true := by
  change (_ && everyKey (rowOK 5 level5) level6l && everyKey (rowOK 5 level5) level6r) = true
  rw [level6l_ok, level6r_ok]
  decide +kernel
theorem closed6 : Closed 6 level6 := closed_next 5 (by decide) level6 level5 closed5 level6_ok
def level7 : BinaryTree (List W) := (.node [v104, v126, v149, v170, v191, v214] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7_ok : everyKey (rowOK 6 level6) level7 = true := by decide +kernel
theorem closed7 : Closed 7 level7 := closed_next 6 (by decide) level7 level6 closed6 level7_ok

theorem lower : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z 7 ins.toFinset :=
  @no_build 7 level7 ins (by decide +kernel) (by decide) closed7 (by decide +kernel)
def witness : List Gate := [⟨.or,[1,3]⟩, ⟨.and,[0,6]⟩, ⟨.or,[2,4]⟩, ⟨.and,[3,8]⟩, ⟨.or,[5,9]⟩, ⟨.and,[1,10]⟩, ⟨.and,[2,4]⟩, ⟨.or,[11,12]⟩, ⟨.and,[7,13]⟩]
theorem upper : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 9 ∧ ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xa8888888a8808000 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact ⟨witness,14,by simp [witness],rfl,by decide +kernel⟩
end PEqualNP.Outside.L_meta_15101_aux

open PEqualNP.Outside.L_meta_15101_aux in
theorem PEqualNP.Outside.L_meta_15101 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (2827520136 * 2 ^ 32 + 2826993664) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (2827520136 * 2 ^ 32 + 2826993664) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  have code : 2827520136 * 2 ^ 32 + 2826993664 = 0xa8888888a8808000 := by decide
  simp only [code] at h ⊢
  obtain ⟨C,legal,size,computes⟩ := h
  obtain ⟨gs,o,mono,bound,ev⟩ := replace 0xa8888888a8808000 9 ins (by decide +kernel) sampled rfl lower upper C.gates C.output legal computes
  exact ⟨⟨gs,o⟩,mono,bound.trans size,ev⟩
