import PEqualNP.Defs

-- The live-wire search and circuit compiler are adapted from tacyon52 in L-meta-8639, pull request 12794 under Apache-2.0.
namespace PEqualNP.Outside.L_meta_15621_aux

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

def v0 : W := 0x2d96b32d8000000e39dc7f
def v1 : W := 0x58f338e580000060c1e38e
def v2 : W := 0x71e199ec8000018f0603f0
def v3 : W := 0x7d05bb48000001f007fc00
def v4 : W := 0x7d97bb6d800001fe3ffc7f
def v5 : W := 0x7df62281000001fff80000
def v6 : W := 0x7df6b3ad800001fff9dc7f
def v7 : W := 0x7df7bbed8000006ef9ffff
def v8 : W := 0x7df7bbed8000018f3fdfff
def v9 : W := 0x1678000d53ec000000001dc7f
def v10 : W := 0x2cd000158668003740001e38e
def v11 : W := 0x38e0001997c800c78000603f0
def v12 : W := 0x3e80001dd48000f800007fc00
def v13 : W := 0x3e87d05ff48000f81f007fc00
def v14 : W := 0x3ed0001dd6e800ff40007ff8e
def v15 : W := 0x3ef80004412400ffe00000000
def v16 : W := 0x3ef8001dd7ec003740001ffff
def v17 : W := 0x3ef8001dd7ec00c780007dfff
def v18 : W := 0x3effdf66693400ffffff80000
def v19 : W := 0x2c07829a0037c000000e38007f
def v20 : W := 0x581500f200a780607400c0038e
def v21 : W := 0x701602e000b48180780f0003f0
def v22 : W := 0x7c1002fa008101f0000ff80000
def v23 : W := 0x7c107ffe228101f001fff80000
def v24 : W := 0x7c1602fa00b581f0780ff803f0
def v25 : W := 0x7c178208001241f07e00000000
def v26 : W := 0x7c1782fa00b7c060740ef803ff
def v27 : W := 0x7c1782fa00b7c180780f3803ff
def v28 : W := 0x7c17ff0dbb5a41f07ff007fc00
def v29 : W := 0x7ff802fbddc901ff800ffffc00
def v30 : W := 0x7fff8208441241fffe00000000
def v31 : W := 0x10841081260030c630460c1e00e
def v32 : W := 0x10845089270278000000001c00e
def v33 : W := 0x180600c0466000e03807001fc00
def v34 : W := 0x188610c1666030e638470c1fc0e
def v35 : W := 0x18c000c1e22010e700070f80000
def v36 : W := 0x18c61800844024e738600000000
def v37 : W := 0x18c618c1e66034000000039dc0f
def v38 : W := 0x18c618c1e66034c630460f9fc0f
def v39 : W := 0x18c61f1e9ddeece73878f0603f0
def v40 : W := 0x18f8e0c1fbb7d8e7c7870fe03f0
def v41 : W := 0x1f0760ee466b48f83f87f01fff0
def v42 : W := 0x1fc100efe22810ff0007ff80000
def v43 : W := 0x1fc77820844124ff3fe00000000
def v44 : W := 0x4210223008118318c098f060070
def v45 : W := 0x421062380913c8000000e000070
def v46 : W := 0x4812025048708320c8190061c00
def v47 : W := 0x483e82505df48320f819007fc00
def v48 : W := 0x4a400270c02003390019f380000
def v49 : W := 0x4a502270c8318339c099f3e0070
def v50 : W := 0x4a52282080410739c8a00000000
def v51 : W := 0x4a522a70c87184000000e381c71
def v52 : W := 0x4a522a70c8718718c098f3e1c71
def v53 : W := 0x4a522dafb3cf5f39c8a60c1e38e
def v54 : W := 0x4a6cd270d5a66b393759f39e38e
def v55 : W := 0x4a7ef82084412739ffe00000000
def v56 : W := 0x4d93525f687afb26cf590c61f8e
def v57 : W := 0x529432b12e11b3def0defc7e07e
def v58 : W := 0x581602d04f7080000000001dc00
def v59 : W := 0x583e82d05ff48000f800007fc00
def v60 : W := 0x5ac002f9e22010000000e380000
def v61 : W := 0x5ad63820844127fff8e00000000
def v62 : W := 0x5ad678208441240000000000000
def v63 : W := 0x5ad67820844124e738600000000
def v64 : W := 0x5ad6782084412739c8a00000000
def v65 : W := 0x5ad67af9ef73fc000000e39dc7f
def v66 : W := 0x5afef82084412400ffe00000000
def v67 : W := 0x5fc102ffe228101f0000ff80000
def v68 : W := 0x5fd778208441241f07e00000000
def v69 : W := 0xa0288500108403e0f81f0062000
def v70 : W := 0xa02887d05bb483e0f81f007fc00
def v71 : W := 0xa2e8fd29b0877fe0f81fe3e207f
def v72 : W := 0xa5010506000803ff001f1c00000
def v73 : W := 0xa50107df622813ff001fff80000
def v74 : W := 0xa5177d060d5befff001f1c1dc7f
def v75 : W := 0xa5298000000003ffffe00000000
def v76 : W := 0xa52982d96b32dbffffe0e39dc7f
def v77 : W := 0xa5298506108c00c637460c02380
def v78 : W := 0xa5298506108c0318c7981060380
def v79 : W := 0xa529858f338e58c637460c1e38e
def v80 : W := 0xa529871e199ecb18c798f0603f0
def v81 : W := 0xa529c50e118e480007000000380
def v82 : W := 0xa529c58f338e580007060c1e38e
def v83 : W := 0xa529c71e199ec8000718f0603f0
def v84 : W := 0xa539e506199fcb18c79810603f0
def v85 : W := 0xa539e50e199fc800c78000603f0
def v86 : W := 0xa5a9d50f308e78c637460c0238e
def v87 : W := 0xa5a9d50f318e780607400c0038e
def v88 : W := 0xb02c8580178400c03006001e000
def v89 : W := 0xb02c87d05fb480c0301f007fc00
def v90 : W := 0xb581058f220810c600060c00000
def v91 : W := 0xb58107df622810c6001fff80000
def v92 : W := 0xb5a9c58f338e58c607060c00380
def v93 : W := 0xb5add000040020c637400000000
def v94 : W := 0xb5add58f378e78000700001c38e
def v95 : W := 0xb5add58f378e78c637460c1e38e
def v96 : W := 0xbdafd5cf77ee78e63f470c1ff8e
def v97 : W := 0xbdc105c7e22813ff001f1f80000
def v98 : W := 0xbdc105cfe22810e700070f80000
def v99 : W := 0xbdef9dc7f6ec3718c79813fdf8f
def v100 : W := 0xbdefdd8fb7ce7ce73f660c1e38e
def v101 : W := 0xe038871019948300c0180060000
def v102 : W := 0xe03887d05bb48300c01f007fc00
def v103 : W := 0xe539c71e199ecb00c7180060380
def v104 : W := 0xe701073e000803180018f000000
def v105 : W := 0xe70107ff62281318001fff80000
def v106 : W := 0xe739e02000010318c7800000000
def v107 : W := 0xe739e73e199fc8000700e0003f0
def v108 : W := 0xe739e73e199fcb18c798f0603f0
def v109 : W := 0xe83a875058f483e0f81f0063c00
def v110 : W := 0xe83a875059f48320c8190061c00
def v111 : W := 0xef79e77ed9bfcb39c799f3e03f0
def v112 : W := 0xef7baf76d8fd84c63746ef83ff1
def v113 : W := 0xef7bef3e99dfcf39cfb8f0603f0
def v114 : W := 0xf7bdf7bf3f9ffbdef7defc7e3fe
def v115 : W := 0xf80007d0422003e0001f0000000
def v116 : W := 0xf83887d05bb483e0c01f0060000
def v117 : W := 0xf83e8000044003e0f8000000000
def v118 : W := 0xf83e87d05ff480c03006001fc00
def v119 : W := 0xf83e87d05ff48300c018007dc00
def v120 : W := 0xf83e87d05ff483e0f81f007fc00
def v121 : W := 0xf8be97d17ff4b3e6f85f0c7fc0e
def v122 : W := 0xf8bed7d97ff6fbe0f81f007fc0e
def v123 : W := 0xf8fe9fd0dff4a7e7f87f007fc00
def v124 : W := 0xfa7eaff0dff587f9f8bf007fc00
def v125 : W := 0xfafef820844127e0f8000000000
def v126 : W := 0xfafefff0dff5a7e0f81f007fc00
def v127 : W := 0xfafefff9fff7ffe0f81fe3ffc7f
def v128 : W := 0xfd3f87d65ffc83fff81f1c7fc00
def v129 : W := 0xfd8107df622813e6001f0c00000
def v130 : W := 0xfdbf87df7ffc93e6f81f0c7fc00
def v131 : W := 0xfdbfd7df7ffef8c637460c1ff8e
def v132 : W := 0xfdbfd7df7ffefbe6ff5f0c7ff8e
def v133 : W := 0xff3fe7fe5fffcbf8ff9ff07fff0
def v134 : W := 0xffc10020800003ff00000000000
def v135 : W := 0xffc107ffe22810c60006ef80000
def v136 : W := 0xffc107ffe22813180018f380000
def v137 : W := 0xffc107ffe22813ff001fff80000
def v138 : W := 0xffc71fffe66837ff387fff80000
def v139 : W := 0xffd127ffea3993ffc09fffe0070
def v140 : W := 0xffd167ffeb3bdbff001fff80070
def v141 : W := 0xffd32fffe26917ffc8bfff80000
def v142 : W := 0xffd77820844127ff00000000000
def v143 : W := 0xffd77fffe66937ff001fff80000
def v144 : W := 0xffd77fffef7bffff001fff9dc7f
def v145 : W := 0xffe987fff2ac13fff81fffe2000
def v146 : W := 0xffedd7fff7ae7bff375fff9e38e
def v147 : W := 0xfff987fffbbc93ffc01fffe0000
def v148 : W := 0xfff9e7fffbbfdb18c798f3e03f0
def v149 : W := 0xfff9e7fffbbfdbffc79fffe03f0
def v150 : W := 0xffff87f0dff483fff81f007fc00
def v151 : W := 0xffff87ffe66813fff81fff80000
def v152 : W := 0xffff87fffffc93fff81fffffc00
def v153 : W := 0xfffff820844124c637400000000
def v154 : W := 0xfffff82084412718c7800000000
def v155 : W := 0xfffff820844127ffffe00000000
def v156 : W := 0xfffffaf9ef73ffffffe0e39dc7f
def v157 : W := 0xfffffd2094c527ffffff0062000
def v158 : W := 0xfffffd26844927ffffff1c00000
def v159 : W := 0xfffffd2694cd27ffffe60c02380
def v160 : W := 0xfffffd2694cd27fffff81060380
def v161 : W := 0xfffffd2e95cf6fffffe00000380
def v162 : W := 0xfffffdafa64937ffffe60c00000
def v163 : W := 0xfffffdafb7cf7cc637460c1e38e
def v164 : W := 0xfffffdafb7cf7fffffe60c1e38e
def v165 : W := 0xffffff309dd5a7fffff80060000
def v166 : W := 0xffffff3e9ddfef18c798f0603f0
def v167 : W := 0xffffff3e9ddfeffffff8f0603f0
def v168 : W := 0xfffffff0c66127ffffff0000000
def v169 : W := 0xfffffff0dff5a7ffffff007fc00
def v170 : W := 0xffffffffe66937ffffffff80000
def v171 : W := 0xfffffffffffffcc63746ef9ffff
def v172 : W := 0xffffffffffffff18c798f3fdfff

def ins : List W := [v65, v95, v108, v120, v137, v155]
theorem sampled : ∀ j : Fin 108, Nat.testBit 0xeaeaeaaaeac8e080 (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
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
def level4 : BinaryTree (List W) := (.node [v65, v95, v108, v150, v170] (.node [v41, v65, v95, v137, v155] (.node [v29, v65, v95, v108, v155] (.node [v28, v65, v95, v108, v137] (.node [v18, v65, v95, v108, v120] .nil .nil) .nil) (.node [v40, v65, v95, v120, v155] (.node [v39, v65, v95, v120, v137] .nil .nil) .nil)) (.node [v56, v65, v108, v137, v155] (.node [v54, v65, v108, v120, v155] (.node [v53, v65, v108, v120, v137] .nil .nil) .nil) (.node [v65, v95, v108, v126, v143] (.node [v57, v65, v120, v137, v155] .nil .nil) .nil))) (.node [v71, v95, v108, v137, v155] (.node [v65, v95, v126, v137, v166] (.node [v65, v95, v108, v152, v168] (.node [v65, v95, v108, v151, v169] .nil .nil) .nil) (.node [v65, v120, v137, v163, v166] (.node [v65, v108, v120, v143, v163] .nil .nil) .nil)) (.node [v95, v99, v120, v137, v155] (.node [v76, v95, v108, v120, v137] (.node [v74, v95, v108, v120, v155] .nil .nil) .nil) (.node [v108, v112, v120, v137, v155] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4_ok : everyKey (rowOK 3 level3) level4 = true := by decide +kernel
theorem closed4 : Closed 4 level4 := closed_next 3 (by decide) level4 level3 closed3 level4_ok
def level5ll : BinaryTree (List W) := (.node [v14, v65, v95, v108, v120, v155] (.node [v6, v65, v95, v108, v120, v137] (.node [v2, v36, v65, v95, v120, v137] (.node [v0, v75, v95, v108, v120, v137] (.node [v0, v65, v95, v108, v120, v137] (.node [v0, v62, v95, v108, v120, v137] .nil .nil) .nil) (.node [v1, v50, v65, v108, v120, v137] .nil .nil)) (.node [v4, v65, v95, v108, v120, v137] (.node [v3, v25, v65, v95, v108, v137] .nil .nil) (.node [v5, v15, v65, v95, v108, v120] .nil .nil))) (.node [v10, v48, v65, v108, v120, v155] (.node [v8, v65, v95, v108, v120, v137] (.node [v7, v65, v95, v108, v120, v137] .nil .nil) (.node [v9, v72, v95, v108, v120, v155] .nil .nil)) (.node [v12, v22, v65, v95, v108, v155] (.node [v11, v35, v65, v95, v120, v155] .nil .nil) (.node [v13, v65, v95, v108, v137, v155] .nil .nil)))) (.node [v27, v65, v95, v108, v137, v155] (.node [v21, v33, v65, v95, v137, v155] (.node [v19, v69, v95, v108, v137, v155] (.node [v17, v65, v95, v108, v120, v155] (.node [v16, v65, v95, v108, v120, v155] .nil .nil) .nil) (.node [v20, v46, v65, v108, v137, v155] .nil .nil)) (.node [v24, v65, v95, v108, v137, v155] (.node [v23, v65, v95, v108, v120, v155] .nil .nil) (.node [v26, v65, v95, v108, v137, v155] .nil .nil))) (.node [v34, v65, v95, v120, v137, v155] (.node [v31, v44, v65, v120, v137, v155] (.node [v30, v65, v95, v108, v120, v137] .nil .nil) (.node [v32, v108, v120, v137, v155, v171] .nil .nil)) (.node [v38, v65, v95, v120, v137, v155] (.node [v37, v78, v95, v120, v137, v155] .nil .nil) (.node [v42, v65, v95, v108, v120, v155] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5ll_ok : everyKey (rowOK 4 level4) level5ll = true := by decide +kernel
def level5lr : BinaryTree (List W) := (.node [v62, v65, v95, v108, v126, v137] (.node [v60, v95, v108, v120, v144, v155] (.node [v52, v65, v108, v120, v137, v155] (.node [v49, v65, v108, v120, v137, v155] (.node [v47, v65, v95, v108, v137, v155] (.node [v45, v95, v120, v137, v155, v172] .nil .nil) .nil) (.node [v51, v77, v108, v120, v137, v155] .nil .nil)) (.node [v58, v95, v108, v127, v137, v155] (.node [v55, v65, v95, v108, v120, v137] .nil .nil) (.node [v59, v65, v95, v108, v137, v155] .nil .nil))) (.node [v62, v65, v79, v108, v120, v137] (.node [v62, v65, v70, v95, v108, v137] (.node [v61, v65, v95, v108, v120, v137] .nil .nil) (.node [v62, v65, v73, v95, v108, v120] .nil .nil)) (.node [v62, v65, v95, v108, v120, v137] (.node [v62, v65, v80, v95, v120, v137] .nil .nil) (.node [v62, v65, v95, v108, v120, v143] .nil .nil)))) (.node [v65, v70, v95, v108, v137, v155] (.node [v64, v65, v95, v108, v120, v137] (.node [v62, v95, v108, v120, v137, v156] (.node [v62, v65, v108, v120, v137, v163] (.node [v62, v65, v95, v120, v137, v166] .nil .nil) .nil) (.node [v63, v65, v95, v108, v120, v137] .nil .nil)) (.node [v65, v67, v95, v108, v120, v155] (.node [v65, v66, v95, v108, v120, v137] .nil .nil) (.node [v65, v68, v95, v108, v120, v137] .nil .nil))) (.node [v65, v81, v114, v120, v137, v155] (.node [v65, v79, v108, v120, v137, v155] (.node [v65, v73, v95, v108, v120, v155] .nil .nil) (.node [v65, v80, v95, v120, v137, v155] .nil .nil)) (.node [v65, v83, v95, v120, v137, v155] (.node [v65, v82, v108, v120, v137, v155] .nil .nil) (.node [v65, v84, v95, v120, v137, v155] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lr_ok : everyKey (rowOK 4 level4) level5lr = true := by decide +kernel
def level5l : BinaryTree (List W) := .node [v43, v65, v95, v108, v120, v137] level5ll level5lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5l_ok : everyKey (rowOK 4 level4) level5l = true := by
  change (_ && everyKey (rowOK 4 level4) level5ll && everyKey (rowOK 4 level4) level5lr) = true
  rw [level5ll_ok, level5lr_ok]
  decide +kernel
def level5rl : BinaryTree (List W) := (.node [v65, v95, v106, v120, v137, v167] (.node [v65, v94, v108, v120, v137, v155] (.node [v65, v90, v108, v120, v146, v155] (.node [v65, v88, v108, v132, v137, v155] (.node [v65, v87, v108, v120, v137, v155] (.node [v65, v86, v108, v120, v137, v155] .nil .nil) .nil) (.node [v65, v89, v95, v108, v137, v155] .nil .nil)) (.node [v65, v92, v108, v120, v137, v155] (.node [v65, v91, v95, v108, v120, v155] .nil .nil) (.node [v65, v93, v108, v120, v137, v164] .nil .nil))) (.node [v65, v95, v102, v108, v137, v155] (.node [v65, v95, v98, v108, v120, v155] (.node [v65, v95, v97, v108, v120, v155] .nil .nil) (.node [v65, v95, v101, v133, v137, v155] .nil .nil)) (.node [v65, v95, v104, v120, v149, v155] (.node [v65, v95, v103, v120, v137, v155] .nil .nil) (.node [v65, v95, v105, v108, v120, v155] .nil .nil)))) (.node [v65, v95, v108, v120, v125, v137] (.node [v65, v95, v108, v116, v137, v155] (.node [v65, v95, v108, v110, v137, v155] (.node [v65, v95, v108, v109, v137, v155] (.node [v65, v95, v107, v120, v137, v155] .nil .nil) .nil) (.node [v65, v95, v108, v115, v152, v155] .nil .nil)) (.node [v65, v95, v108, v118, v137, v155] (.node [v65, v95, v108, v117, v137, v169] .nil .nil) (.node [v65, v95, v108, v119, v137, v155] .nil .nil))) (.node [v65, v95, v108, v120, v136, v155] (.node [v65, v95, v108, v120, v134, v170] (.node [v65, v95, v108, v120, v129, v155] .nil .nil) (.node [v65, v95, v108, v120, v135, v155] .nil .nil)) (.node [v65, v95, v108, v120, v137, v153] (.node [v65, v95, v108, v120, v137, v142] .nil .nil) (.node [v65, v95, v108, v120, v137, v154] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rl_ok : everyKey (rowOK 4 level4) level5rl = true := by decide +kernel
def level5rr : BinaryTree (List W) := (.node [v65, v95, v108, v121, v137, v155] (.node [v65, v95, v108, v120, v138, v155] (.node [v65, v95, v108, v120, v137, v161] (.node [v65, v95, v108, v120, v137, v159] (.node [v65, v95, v108, v120, v137, v158] (.node [v65, v95, v108, v120, v137, v157] .nil .nil) .nil) (.node [v65, v95, v108, v120, v137, v160] .nil .nil)) (.node [v65, v95, v108, v120, v137, v165] (.node [v65, v95, v108, v120, v137, v162] .nil .nil) (.node [v65, v95, v108, v120, v137, v168] .nil .nil))) (.node [v65, v95, v108, v120, v143, v155] (.node [v65, v95, v108, v120, v140, v155] (.node [v65, v95, v108, v120, v139, v155] .nil .nil) (.node [v65, v95, v108, v120, v141, v155] .nil .nil)) (.node [v65, v95, v108, v120, v147, v155] (.node [v65, v95, v108, v120, v145, v155] .nil .nil) (.node [v65, v95, v108, v120, v151, v155] .nil .nil)))) (.node [v65, v95, v111, v120, v137, v155] (.node [v65, v95, v108, v126, v137, v155] (.node [v65, v95, v108, v123, v137, v155] (.node [v65, v95, v108, v122, v137, v155] .nil .nil) (.node [v65, v95, v108, v124, v137, v155] .nil .nil)) (.node [v65, v95, v108, v130, v137, v155] (.node [v65, v95, v108, v128, v137, v155] .nil .nil) (.node [v65, v95, v108, v137, v150, v155] .nil .nil))) (.node [v65, v96, v108, v120, v137, v155] (.node [v65, v95, v120, v137, v148, v155] (.node [v65, v95, v113, v120, v137, v155] .nil .nil) (.node [v65, v95, v120, v137, v155, v166] .nil .nil)) (.node [v65, v108, v120, v131, v137, v155] (.node [v65, v100, v108, v120, v137, v155] .nil .nil) (.node [v65, v108, v120, v137, v155, v163] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rr_ok : everyKey (rowOK 4 level4) level5rr = true := by decide +kernel
def level5r : BinaryTree (List W) := .node [v65, v95, v108, v120, v137, v155] level5rl level5rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5r_ok : everyKey (rowOK 4 level4) level5r = true := by
  change (_ && everyKey (rowOK 4 level4) level5rl && everyKey (rowOK 4 level4) level5rr) = true
  rw [level5rl_ok, level5rr_ok]
  decide +kernel
def level5 : BinaryTree (List W) := .node [v65, v85, v95, v120, v137, v155] level5l level5r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5_ok : everyKey (rowOK 4 level4) level5 = true := by
  change (_ && everyKey (rowOK 4 level4) level5l && everyKey (rowOK 4 level4) level5r) = true
  rw [level5l_ok, level5r_ok]
  decide +kernel
theorem closed5 : Closed 5 level5 := closed_next 4 (by decide) level5 level4 closed4 level5_ok
def level6l : BinaryTree (List W) := (.node [v25, v65, v95, v108, v120, v137, v155] (.node [v10, v65, v95, v108, v120, v137, v155] (.node [v2, v65, v95, v108, v120, v137, v155] (.node [v0, v65, v95, v108, v120, v137, v155] (.node [v0, v65, v95, v108, v120, v137] .nil .nil) (.node [v1, v65, v95, v108, v120, v137, v155] .nil .nil)) (.node [v5, v65, v95, v108, v120, v137, v155] (.node [v3, v65, v95, v108, v120, v137, v155] .nil .nil) (.node [v9, v65, v95, v108, v120, v137, v155] .nil .nil))) (.node [v19, v65, v95, v108, v120, v137, v155] (.node [v12, v65, v95, v108, v120, v137, v155] (.node [v11, v65, v95, v108, v120, v137, v155] .nil .nil) (.node [v15, v65, v95, v108, v120, v137, v155] .nil .nil)) (.node [v21, v65, v95, v108, v120, v137, v155] (.node [v20, v65, v95, v108, v120, v137, v155] .nil .nil) (.node [v22, v65, v95, v108, v120, v137, v155] .nil .nil)))) (.node [v45, v65, v95, v108, v120, v137, v155] (.node [v35, v65, v95, v108, v120, v137, v155] (.node [v32, v65, v95, v108, v120, v137, v155] (.node [v31, v65, v95, v108, v120, v137, v155] .nil .nil) (.node [v33, v65, v95, v108, v120, v137, v155] .nil .nil)) (.node [v37, v65, v95, v108, v120, v137, v155] (.node [v36, v65, v95, v108, v120, v137, v155] .nil .nil) (.node [v44, v65, v95, v108, v120, v137, v155] .nil .nil))) (.node [v51, v65, v95, v108, v120, v137, v155] (.node [v48, v65, v95, v108, v120, v137, v155] (.node [v46, v65, v95, v108, v120, v137, v155] .nil .nil) (.node [v50, v65, v95, v108, v120, v137, v155] .nil .nil)) (.node [v60, v65, v95, v108, v120, v137, v155] (.node [v58, v65, v95, v108, v120, v137, v155] .nil .nil) (.node [v62, v65, v95, v108, v120, v137] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6l_ok : everyKey (rowOK 5 level5) level6l = true := by decide +kernel
def level6r : BinaryTree (List W) := (.node [v65, v95, v108, v120, v127, v137, v155] (.node [v65, v90, v95, v108, v120, v137, v155] (.node [v65, v77, v95, v108, v120, v137, v155] (.node [v65, v72, v95, v108, v120, v137, v155] (.node [v65, v69, v95, v108, v120, v137, v155] .nil .nil) (.node [v65, v75, v95, v108, v120, v137, v155] .nil .nil)) (.node [v65, v81, v95, v108, v120, v137, v155] (.node [v65, v78, v95, v108, v120, v137, v155] .nil .nil) (.node [v65, v88, v95, v108, v120, v137, v155] .nil .nil))) (.node [v65, v95, v106, v108, v120, v137, v155] (.node [v65, v95, v101, v108, v120, v137, v155] (.node [v65, v93, v95, v108, v120, v137, v155] .nil .nil) (.node [v65, v95, v104, v108, v120, v137, v155] .nil .nil)) (.node [v65, v95, v108, v115, v120, v137, v155] (.node [v65, v95, v108, v114, v120, v137, v155] .nil .nil) (.node [v65, v95, v108, v117, v120, v137, v155] .nil .nil)))) (.node [v65, v95, v108, v120, v137, v155, v156] (.node [v65, v95, v108, v120, v137, v144, v155] (.node [v65, v95, v108, v120, v133, v137, v155] (.node [v65, v95, v108, v120, v132, v137, v155] .nil .nil) (.node [v65, v95, v108, v120, v134, v137, v155] .nil .nil)) (.node [v65, v95, v108, v120, v137, v149, v155] (.node [v65, v95, v108, v120, v137, v146, v155] .nil .nil) (.node [v65, v95, v108, v120, v137, v152, v155] .nil .nil))) (.node [v65, v95, v108, v120, v137, v155, v170] (.node [v65, v95, v108, v120, v137, v155, v167] (.node [v65, v95, v108, v120, v137, v155, v164] .nil .nil) (.node [v65, v95, v108, v120, v137, v155, v169] .nil .nil)) (.node [v65, v95, v108, v120, v137, v155, v172] (.node [v65, v95, v108, v120, v137, v155, v171] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6r_ok : everyKey (rowOK 5 level5) level6r = true := by decide +kernel
def level6 : BinaryTree (List W) := .node [v62, v65, v95, v108, v120, v137, v155] level6l level6r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6_ok : everyKey (rowOK 5 level5) level6 = true := by
  change (_ && everyKey (rowOK 5 level5) level6l && everyKey (rowOK 5 level5) level6r) = true
  rw [level6l_ok, level6r_ok]
  decide +kernel
theorem closed6 : Closed 6 level6 := closed_next 5 (by decide) level6 level5 closed5 level6_ok
def level7 : BinaryTree (List W) := (.node [v65, v95, v108, v120, v137, v155] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7_ok : everyKey (rowOK 6 level6) level7 = true := by decide +kernel
theorem closed7 : Closed 7 level7 := closed_next 6 (by decide) level7 level6 closed6 level7_ok

theorem lower : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z 7 ins.toFinset :=
  @no_build 7 level7 ins (by decide +kernel) (by decide) closed7 (by decide +kernel)
def witness : List Gate := [⟨.or,[1,3]⟩, ⟨.or,[3,4]⟩, ⟨.and,[1,7]⟩, ⟨.or,[2,4]⟩, ⟨.and,[6,9]⟩, ⟨.or,[5,10]⟩, ⟨.and,[0,11]⟩, ⟨.and,[2,8]⟩, ⟨.or,[12,13]⟩]
theorem upper : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 9 ∧ ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xeaeaeaaaeac8e080 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact ⟨witness,14,by simp [witness],rfl,by decide +kernel⟩
end PEqualNP.Outside.L_meta_15621_aux

open PEqualNP.Outside.L_meta_15621_aux in
theorem PEqualNP.Outside.L_meta_15621 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941264042 * 2 ^ 32 + 3939033216) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941264042 * 2 ^ 32 + 3939033216) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  have code : 3941264042 * 2 ^ 32 + 3939033216 = 0xeaeaeaaaeac8e080 := by decide
  simp only [code] at h ⊢
  obtain ⟨C,legal,size,computes⟩ := h
  obtain ⟨gs,o,mono,bound,ev⟩ := replace 0xeaeaeaaaeac8e080 9 ins (by decide +kernel) sampled rfl lower upper C.gates C.output legal computes
  exact ⟨⟨gs,o⟩,mono,bound.trans size,ev⟩
