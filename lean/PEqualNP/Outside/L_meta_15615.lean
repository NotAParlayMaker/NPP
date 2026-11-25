import PEqualNP.Defs

-- The live-wire search and circuit compiler are adapted from tacyon52 in L-meta-8639, pull request 12794 under Apache-2.0.
namespace PEqualNP.Outside.L_meta_15615_aux

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

def v0 : W := 0x2d9965958000000eef8e3f
def v1 : W := 0x58dc3cf580000060f031ce
def v2 : W := 0x71cc78748000018f03c1f0
def v3 : W := 0x7d117da1000001f003fe00
def v4 : W := 0x7d997db5800001feeffe3f
def v5 : W := 0x7ddd4140000001fffc0000
def v6 : W := 0x7ddd65d5800001ffff8e3f
def v7 : W := 0x7ddd7df58000006effbfff
def v8 : W := 0x7ddd7df58000018fefcfff
def v9 : W := 0x1678000a69fc0000000038e3f
def v10 : W := 0x2cd00003cb7800374000031ce
def v11 : W := 0x38e0000b83c800c780003c1f0
def v12 : W := 0x3e80000bea1000f800003fe00
def v13 : W := 0x3e87d11ffa1000f81f003fe00
def v14 : W := 0x3ed0000beb7800ff40003ffce
def v15 : W := 0x3ee0000bebd800ff80003fff0
def v16 : W := 0x3ef8000820a400ffe00000000
def v17 : W := 0x3ef8000bebfc003740003bfff
def v18 : W := 0x3ef8000bebfc00c780003cfff
def v19 : W := 0x3effdddc34a400ffffffc0000
def v20 : W := 0x2c0782aa001ec000000eec003f
def v21 : W := 0x581500ec005680607400f001ce
def v22 : W := 0x701602cc005c8180780f0001f0
def v23 : W := 0x7c1002ee004001f0000ffc0000
def v24 : W := 0x7c107fff414001f001fffc0000
def v25 : W := 0x7c1502ee005681f0740ffc01ce
def v26 : W := 0x7c178222000a41f07e00000000
def v27 : W := 0x7c1782ee005ec060740efc01ff
def v28 : W := 0x7c1782ee005ec180780fec01ff
def v29 : W := 0x7c17ff337dab41f07ff003fe00
def v30 : W := 0x7ff802eebee101ff800ffffe00
def v31 : W := 0x7fff8222820a41fffe00000000
def v32 : W := 0x10841083004830c630460f0300e
def v33 : W := 0x1084508b8249780000000e0000e
def v34 : W := 0x180600c1107810e038070003e00
def v35 : W := 0x188610c3107830e638470f03e0e
def v36 : W := 0x18c000c3301000e700070fc0000
def v37 : W := 0x18c410c3305830e730470fc300e
def v38 : W := 0x18c61802202024e738600000000
def v39 : W := 0x18c61883206834e738660f0300e
def v40 : W := 0x18c618c33078340000000ec0e0f
def v41 : W := 0x18c618c3307834c630460fc3e0f
def v42 : W := 0x18c61f1ee7a76ce73878f03c1f0
def v43 : W := 0x18f8e0c33b93c8e7c7870ffc1f0
def v44 : W := 0x1f0760edd07dd8f83f87f003ff0
def v45 : W := 0x421022300c008318c098f03c030
def v46 : W := 0x421062388e01c8000000e038030
def v47 : W := 0x481202501c300320c819003ce00
def v48 : W := 0x4a1222701c308338c899f03ce30
def v49 : W := 0x4a400270341003390019f0c0000
def v50 : W := 0x4a52282028208739c8a00000000
def v51 : W := 0x4a522a703c3084000000e0f8e31
def v52 : W := 0x4a522a703c308718c098f0fce31
def v53 : W := 0x4a522dadebefdf39c8a60f031ce
def v54 : W := 0x4a6cd27037db7b393759f0c31ce
def v55 : W := 0x4d93525edc356b26cf590f3cfce
def v56 : W := 0x4fc1027ef414033f0019ffc0000
def v57 : W := 0x4fd378222820a73fcfe00000000
def v58 : W := 0x529432b30c48b3def0deff3f03e
def v59 : W := 0x581602d11e78100000000038e00
def v60 : W := 0x583e82d11ffa1000f800003fe00
def v61 : W := 0x5ac002fbb41000000000eec0000
def v62 : W := 0x5ad638222820a7fff8e00000000
def v63 : W := 0x5ad678222820a40000000000000
def v64 : W := 0x5ad678222820a4e738600000000
def v65 : W := 0x5ad678222820a739c8a00000000
def v66 : W := 0x5ad67afbbe79fc000000eef8e3f
def v67 : W := 0x5afef8222820a400ffe00000000
def v68 : W := 0x5fc102fff414001f0000ffc0000
def v69 : W := 0x5fd778222820a41f07e00000000
def v70 : W := 0xa0288500018203e0f81f0007000
def v71 : W := 0xa02887d117da13e0f81f003fe00
def v72 : W := 0xa2e8fd2aa183efe0f81feec703f
def v73 : W := 0xa5010504400403ff001f1100000
def v74 : W := 0xa50107ddd41403ff001fffc0000
def v75 : W := 0xa5177d044a6dffff001f1138e3f
def v76 : W := 0xa5298000000003ffffe00000000
def v77 : W := 0xa52982d996595bffffe0eef8e3f
def v78 : W := 0xa5298504418600c6374601031c0
def v79 : W := 0xa529850441860318c79810041c0
def v80 : W := 0xa529858dc3cf58c637460f031ce
def v81 : W := 0xa529871cc7874b18c798f03c1f0
def v82 : W := 0xa529c50cc3874800070000001c0
def v83 : W := 0xa529c50cc3874b18c79810041c0
def v84 : W := 0xa529c58dc3cf580007060f031ce
def v85 : W := 0xa529c71cc78748000718f03c1f0
def v86 : W := 0xa52dd50cc3cf7800374000031ce
def v87 : W := 0xa539e50ccb87c800c780003c1f0
def v88 : W := 0xa729e52cc187cb18c798f0041f0
def v89 : W := 0xa729e52cc387c8180780f0001f0
def v90 : W := 0xb02c858103ca10c030060003000
def v91 : W := 0xb02c87d117da10c0301f003fe00
def v92 : W := 0xb52dc58dc3cf5800070000001c0
def v93 : W := 0xb52dc58dc3cf58c0370600031c0
def v94 : W := 0xb581058fc00400c600060f00000
def v95 : W := 0xb58107dfd41400c6001fffc0000
def v96 : W := 0xb5add002000020c637400000000
def v97 : W := 0xb5add58fc3cf780007000e001ce
def v98 : W := 0xb5add58fc3cf78c637460f031ce
def v99 : W := 0xbdedd5cff3df78e737470fc31ce
def v100 : W := 0xbdef9dc771fe3718c7981ec4fcf
def v101 : W := 0xbdefdd8fe3ef7ce73f660f031ce
def v102 : W := 0xe03887100f820300c018003c000
def v103 : W := 0xe03887d11fda1300c01f003fe00
def v104 : W := 0xe539c71ccf874b00c718003c1c0
def v105 : W := 0xe701073cc40403180018f000000
def v106 : W := 0xe70107fdd4140318001fffc0000
def v107 : W := 0xe729c73cc7874b180718f0001c0
def v108 : W := 0xe739e02008008318c7800000000
def v109 : W := 0xe739e52ccb87cb18c78000001c0
def v110 : W := 0xe739e73ccf87c8000700e0381f0
def v111 : W := 0xe739e73ccf87cb18c798f03c1f0
def v112 : W := 0xef3be77cdfb7cb38cf99f03cff0
def v113 : W := 0xef410774741403ff001ff1c0000
def v114 : W := 0xef41077cf41403390019f0c0000
def v115 : W := 0xef79e77cff97cb39c799f0fc1f0
def v116 : W := 0xef7baf747db684c63746e1fbff1
def v117 : W := 0xef7bef3cefa7cf39cfb8f03c1f0
def v118 : W := 0xef7bef7cffb7cf18c798f0fcff1
def v119 : W := 0xf7bdf7bfcfcffbdef7deff3f1fe
def v120 : W := 0xf80007d1141003e0001f0000000
def v121 : W := 0xf82c87d117da13e0301f0003000
def v122 : W := 0xf83e8000082003e0f8000000000
def v123 : W := 0xf83e87d11ffa10c03006003be00
def v124 : W := 0xf83e87d11ffa1300c018003ce00
def v125 : W := 0xf83e87d11ffa13e0f81f003fe00
def v126 : W := 0xf8fe9fd33ffa37e7f87f003fe00
def v127 : W := 0xfa7eaff13ffa97f9f8bf003fe00
def v128 : W := 0xfafef8222820a7e0f8000000000
def v129 : W := 0xfafefff33ffab7e0f81f003fe00
def v130 : W := 0xfafefffbbffbffe0f81feeffe3f
def v131 : W := 0xfd0107d5541403ff001f1100000
def v132 : W := 0xfd3f87d55ffe13fff81f113fe00
def v133 : W := 0xfd8107dfd41403e6001f0f00000
def v134 : W := 0xfdbfd7dfdfff7be6ff5f0f3ffce
def v135 : W := 0xff0107fdd41403f8001ff000000
def v136 : W := 0xff3fe7fddfffdb18c798f03cff0
def v137 : W := 0xff3fe7fddfffdbf8ff9ff03fff0
def v138 : W := 0xffc10022200003ff00000000000
def v139 : W := 0xffc107fff41400c60006efc0000
def v140 : W := 0xffc107fff41403180018fec0000
def v141 : W := 0xffc107fff41403ff001fffc0000
def v142 : W := 0xffc17ffff415efff001fffc003f
def v143 : W := 0xffc517fff45c33ff305fffc300e
def v144 : W := 0xffc557fff65d7bff001fffc000e
def v145 : W := 0xffc71ffff43427ff387fffc0000
def v146 : W := 0xffd32ffffc3487ffc8bfffc0000
def v147 : W := 0xffd778222820a7ff00000000000
def v148 : W := 0xffd77ffffc34a7ff001fffc0000
def v149 : W := 0xffd77ffffe7dffff001ffff8e3f
def v150 : W := 0xffe987fff59603fff81fffc7000
def v151 : W := 0xffed87fff7de13ff301fffc3000
def v152 : W := 0xffedd7fff7df7bff375fffc31ce
def v153 : W := 0xfff9e7ffff97cbffc79ffffc1f0
def v154 : W := 0xffff87f33ffa13fff81f003fe00
def v155 : W := 0xffff87fffc3403fff81fffc0000
def v156 : W := 0xffff87fffffe13fff81fffffe00
def v157 : W := 0xfffff8222820a4c637400000000
def v158 : W := 0xfffff8222820a718c7800000000
def v159 : W := 0xfffff8222820a7ffffe00000000
def v160 : W := 0xfffffafbbe79ffffffe0eef8e3f
def v161 : W := 0xfffffd2229a2a7ffffff0007000
def v162 : W := 0xfffffd266824a7ffffff1100000
def v163 : W := 0xfffffd2669a6a7ffffe601031c0
def v164 : W := 0xfffffd2669a6a7fffff810041c0
def v165 : W := 0xfffffd2eeba7ec00070000001c0
def v166 : W := 0xfffffd2eeba7efffffe000001c0
def v167 : W := 0xfffffda32beab7ffffe60003000
def v168 : W := 0xfffffdafebeffcc637460f031ce
def v169 : W := 0xfffffdafebefffffffe60f031ce
def v170 : W := 0xffffff3eefa7ef18c798f03c1f0
def v171 : W := 0xffffff3eefa7effffff8f03c1f0
def v172 : W := 0xfffffff33c30a7ffffff0000000
def v173 : W := 0xfffffff33ffab7ffffff003fe00
def v174 : W := 0xfffffffffc34a7ffffffffc0000
def v175 : W := 0xfffffffffffffcc63746effbfff
def v176 : W := 0xffffffffffffff18c798fefcfff

def ins : List W := [v66, v98, v111, v125, v141, v159]
theorem sampled : ∀ j : Fin 108, Nat.testBit 0xeaeaeaaaeac0c880 (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
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
def level4 : BinaryTree (List W) := (.node [v66, v82, v125, v151, v159] (.node [v54, v66, v111, v125, v159] (.node [v42, v66, v98, v125, v141] (.node [v29, v66, v98, v111, v141] (.node [v19, v66, v98, v111, v125] .nil .nil) (.node [v30, v66, v98, v111, v159] .nil .nil)) (.node [v44, v66, v98, v141, v159] (.node [v43, v66, v98, v125, v159] .nil .nil) (.node [v53, v66, v111, v125, v141] .nil .nil))) (.node [v66, v82, v125, v141, v167] (.node [v58, v66, v125, v141, v159] (.node [v55, v66, v111, v141, v159] .nil .nil) (.node [v66, v82, v121, v141, v159] .nil .nil)) (.node [v66, v82, v125, v144, v159] (.node [v66, v82, v125, v143, v159] .nil .nil) .nil))) (.node [v66, v111, v129, v141, v168] (.node [v66, v98, v111, v155, v173] (.node [v66, v98, v111, v129, v148] (.node [v66, v92, v125, v141, v159] .nil .nil) (.node [v66, v98, v111, v154, v174] .nil .nil)) (.node [v66, v98, v125, v141, v165] (.node [v66, v98, v111, v156, v172] .nil .nil) .nil)) (.node [v77, v98, v111, v125, v141] (.node [v72, v98, v111, v141, v159] (.node [v66, v125, v141, v168, v170] .nil .nil) (.node [v75, v98, v111, v125, v159] .nil .nil)) (.node [v111, v116, v125, v141, v159] (.node [v98, v100, v125, v141, v159] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4_ok : everyKey (rowOK 3 level3) level4 = true := by decide +kernel
theorem closed4 : Closed 4 level4 := closed_next 3 (by decide) level4 level3 closed3 level4_ok
def level5ll : BinaryTree (List W) := (.node [v13, v66, v98, v111, v141, v159] (.node [v4, v66, v98, v111, v125, v141] (.node [v0, v76, v98, v111, v125, v141] (.node [v0, v66, v82, v98, v125, v141] (.node [v0, v63, v98, v111, v125, v141] (.node [v0, v32, v66, v98, v125, v141] .nil .nil) .nil) (.node [v0, v66, v98, v111, v125, v141] .nil .nil)) (.node [v2, v38, v66, v98, v125, v141] (.node [v1, v66, v82, v125, v141, v159] (.node [v1, v50, v66, v111, v125, v141] .nil .nil) .nil) (.node [v3, v26, v66, v98, v111, v141] .nil .nil))) (.node [v9, v73, v98, v111, v125, v159] (.node [v7, v66, v98, v111, v125, v141] (.node [v6, v66, v98, v111, v125, v141] (.node [v5, v16, v66, v98, v111, v125] .nil .nil) .nil) (.node [v8, v66, v98, v111, v125, v141] .nil .nil)) (.node [v11, v36, v66, v98, v125, v159] (.node [v10, v66, v82, v125, v141, v159] (.node [v10, v49, v66, v111, v125, v159] .nil .nil) .nil) (.node [v12, v23, v66, v98, v111, v159] .nil .nil)))) (.node [v27, v66, v98, v111, v141, v159] (.node [v20, v70, v98, v111, v141, v159] (.node [v17, v66, v98, v111, v125, v159] (.node [v15, v66, v98, v111, v125, v159] (.node [v14, v66, v98, v111, v125, v159] .nil .nil) .nil) (.node [v18, v66, v98, v111, v125, v159] .nil .nil)) (.node [v24, v66, v98, v111, v125, v159] (.node [v22, v34, v66, v98, v141, v159] (.node [v21, v47, v66, v111, v141, v159] .nil .nil) .nil) (.node [v25, v66, v98, v111, v141, v159] .nil .nil))) (.node [v32, v66, v82, v125, v141, v159] (.node [v32, v45, v66, v125, v141, v159] (.node [v31, v66, v98, v111, v125, v141] (.node [v28, v66, v98, v111, v141, v159] .nil .nil) .nil) (.node [v32, v63, v66, v98, v125, v141] .nil .nil)) (.node [v32, v66, v98, v125, v141, v159] (.node [v32, v66, v98, v114, v125, v159] .nil .nil) (.node [v32, v66, v98, v125, v143, v159] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5ll_ok : everyKey (rowOK 4 level4) level5ll = true := by decide +kernel
def level5lr : BinaryTree (List W) := (.node [v63, v66, v71, v98, v111, v141] (.node [v51, v66, v82, v125, v141, v159] (.node [v40, v79, v98, v125, v141, v159] (.node [v37, v66, v98, v125, v141, v159] (.node [v35, v66, v98, v125, v141, v159] (.node [v33, v111, v125, v141, v159, v175] .nil .nil) .nil) (.node [v39, v66, v98, v125, v141, v159] .nil .nil)) (.node [v47, v66, v82, v125, v141, v159] (.node [v46, v98, v125, v141, v159, v176] (.node [v41, v66, v98, v125, v141, v159] .nil .nil) .nil) (.node [v48, v66, v111, v125, v141, v159] .nil .nil))) (.node [v59, v98, v111, v130, v141, v159] (.node [v56, v66, v98, v111, v125, v159] (.node [v52, v66, v111, v125, v141, v159] (.node [v51, v78, v111, v125, v141, v159] .nil .nil) .nil) (.node [v57, v66, v98, v111, v125, v141] .nil .nil)) (.node [v62, v66, v82, v98, v125, v141] (.node [v61, v98, v111, v125, v149, v159] (.node [v60, v66, v98, v111, v141, v159] .nil .nil) .nil) (.node [v62, v66, v98, v111, v125, v141] .nil .nil)))) (.node [v63, v98, v111, v125, v141, v160] (.node [v63, v66, v98, v111, v125, v141] (.node [v63, v66, v81, v98, v125, v141] (.node [v63, v66, v80, v111, v125, v141] (.node [v63, v66, v74, v98, v111, v125] .nil .nil) .nil) (.node [v63, v66, v82, v98, v125, v141] .nil .nil)) (.node [v63, v66, v98, v125, v141, v170] (.node [v63, v66, v98, v111, v129, v141] (.node [v63, v66, v98, v111, v125, v148] .nil .nil) .nil) (.node [v63, v66, v111, v125, v141, v168] .nil .nil))) (.node [v66, v69, v98, v111, v125, v141] (.node [v66, v67, v98, v111, v125, v141] (.node [v65, v66, v98, v111, v125, v141] (.node [v64, v66, v98, v111, v125, v141] .nil .nil) .nil) (.node [v66, v68, v98, v111, v125, v159] .nil .nil)) (.node [v66, v74, v98, v111, v125, v159] (.node [v66, v71, v98, v111, v141, v159] .nil .nil) (.node [v66, v80, v111, v125, v141, v159] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lr_ok : everyKey (rowOK 4 level4) level5lr = true := by decide +kernel
def level5l : BinaryTree (List W) := .node [v33, v66, v82, v125, v141, v159] level5ll level5lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5l_ok : everyKey (rowOK 4 level4) level5l = true := by
  change (_ && everyKey (rowOK 4 level4) level5ll && everyKey (rowOK 4 level4) level5lr) = true
  rw [level5ll_ok, level5lr_ok]
  decide +kernel
def level5rl : BinaryTree (List W) := (.node [v66, v97, v111, v125, v141, v159] (.node [v66, v86, v111, v125, v141, v159] (.node [v66, v82, v125, v141, v152, v159] (.node [v66, v82, v98, v125, v141, v166] (.node [v66, v82, v98, v125, v141, v159] (.node [v66, v82, v90, v125, v141, v159] .nil .nil) .nil) (.node [v66, v82, v119, v125, v141, v159] .nil .nil)) (.node [v66, v84, v111, v125, v141, v159] (.node [v66, v83, v98, v125, v141, v159] (.node [v66, v82, v125, v141, v159, v169] .nil .nil) .nil) (.node [v66, v85, v98, v125, v141, v159] .nil .nil))) (.node [v66, v91, v98, v111, v141, v159] (.node [v66, v89, v98, v125, v141, v159] (.node [v66, v88, v98, v125, v141, v159] (.node [v66, v87, v98, v125, v141, v159] .nil .nil) .nil) (.node [v66, v90, v111, v134, v141, v159] .nil .nil)) (.node [v66, v95, v98, v111, v125, v159] (.node [v66, v94, v111, v125, v152, v159] (.node [v66, v93, v111, v125, v141, v159] .nil .nil) .nil) (.node [v66, v96, v111, v125, v141, v169] .nil .nil)))) (.node [v66, v98, v111, v113, v125, v159] (.node [v66, v98, v106, v111, v125, v159] (.node [v66, v98, v104, v125, v141, v159] (.node [v66, v98, v103, v111, v141, v159] (.node [v66, v98, v102, v137, v141, v159] .nil .nil) .nil) (.node [v66, v98, v105, v125, v153, v159] .nil .nil)) (.node [v66, v98, v109, v125, v141, v159] (.node [v66, v98, v108, v125, v141, v171] (.node [v66, v98, v107, v125, v141, v159] .nil .nil) .nil) (.node [v66, v98, v110, v125, v141, v159] .nil .nil))) (.node [v66, v98, v111, v123, v141, v159] (.node [v66, v98, v111, v121, v141, v159] (.node [v66, v98, v111, v120, v156, v159] (.node [v66, v98, v111, v114, v125, v159] .nil .nil) .nil) (.node [v66, v98, v111, v122, v141, v173] .nil .nil)) (.node [v66, v98, v111, v125, v128, v141] (.node [v66, v98, v111, v124, v141, v159] .nil .nil) (.node [v66, v98, v111, v125, v131, v159] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rl_ok : everyKey (rowOK 4 level4) level5rl = true := by decide +kernel
def level5rr : BinaryTree (List W) := (.node [v66, v98, v111, v125, v146, v159] (.node [v66, v98, v111, v125, v141, v162] (.node [v66, v98, v111, v125, v141, v147] (.node [v66, v98, v111, v125, v139, v159] (.node [v66, v98, v111, v125, v138, v174] (.node [v66, v98, v111, v125, v135, v159] .nil .nil) .nil) (.node [v66, v98, v111, v125, v140, v159] .nil .nil)) (.node [v66, v98, v111, v125, v141, v159] (.node [v66, v98, v111, v125, v141, v158] (.node [v66, v98, v111, v125, v141, v157] .nil .nil) .nil) (.node [v66, v98, v111, v125, v141, v161] .nil .nil))) (.node [v66, v98, v111, v125, v141, v172] (.node [v66, v98, v111, v125, v141, v166] (.node [v66, v98, v111, v125, v141, v164] (.node [v66, v98, v111, v125, v141, v163] .nil .nil) .nil) (.node [v66, v98, v111, v125, v141, v167] .nil .nil)) (.node [v66, v98, v111, v125, v144, v159] (.node [v66, v98, v111, v125, v143, v159] (.node [v66, v98, v111, v125, v142, v159] .nil .nil) .nil) (.node [v66, v98, v111, v125, v145, v159] .nil .nil)))) (.node [v66, v98, v112, v125, v141, v159] (.node [v66, v98, v111, v126, v141, v159] (.node [v66, v98, v111, v125, v151, v159] (.node [v66, v98, v111, v125, v150, v159] (.node [v66, v98, v111, v125, v148, v159] .nil .nil) .nil) (.node [v66, v98, v111, v125, v155, v159] .nil .nil)) (.node [v66, v98, v111, v132, v141, v159] (.node [v66, v98, v111, v129, v141, v159] (.node [v66, v98, v111, v127, v141, v159] .nil .nil) .nil) (.node [v66, v98, v111, v141, v154, v159] .nil .nil))) (.node [v66, v98, v125, v141, v159, v170] (.node [v66, v98, v118, v125, v141, v159] (.node [v66, v98, v117, v125, v141, v159] (.node [v66, v98, v115, v125, v141, v159] .nil .nil) .nil) (.node [v66, v98, v125, v136, v141, v159] .nil .nil)) (.node [v66, v101, v111, v125, v141, v159] (.node [v66, v99, v111, v125, v141, v159] .nil .nil) (.node [v66, v111, v125, v141, v159, v168] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rr_ok : everyKey (rowOK 4 level4) level5rr = true := by decide +kernel
def level5r : BinaryTree (List W) := .node [v66, v98, v111, v125, v133, v159] level5rl level5rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5r_ok : everyKey (rowOK 4 level4) level5r = true := by
  change (_ && everyKey (rowOK 4 level4) level5rl && everyKey (rowOK 4 level4) level5rr) = true
  rw [level5rl_ok, level5rr_ok]
  decide +kernel
def level5 : BinaryTree (List W) := .node [v66, v81, v98, v125, v141, v159] level5l level5r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5_ok : everyKey (rowOK 4 level4) level5 = true := by
  change (_ && everyKey (rowOK 4 level4) level5l && everyKey (rowOK 4 level4) level5r) = true
  rw [level5l_ok, level5r_ok]
  decide +kernel
theorem closed5 : Closed 5 level5 := closed_next 4 (by decide) level5 level4 closed4 level5_ok
def level6l : BinaryTree (List W) := (.node [v32, v66, v98, v111, v125, v141, v159] (.node [v11, v66, v98, v111, v125, v141, v159] (.node [v3, v66, v98, v111, v125, v141, v159] (.node [v1, v66, v98, v111, v125, v141, v159] (.node [v0, v66, v98, v111, v125, v141, v159] (.node [v0, v66, v98, v111, v125, v141] .nil .nil) .nil) (.node [v2, v66, v98, v111, v125, v141, v159] .nil .nil)) (.node [v9, v66, v98, v111, v125, v141, v159] (.node [v5, v66, v98, v111, v125, v141, v159] .nil .nil) (.node [v10, v66, v98, v111, v125, v141, v159] .nil .nil))) (.node [v21, v66, v98, v111, v125, v141, v159] (.node [v16, v66, v98, v111, v125, v141, v159] (.node [v12, v66, v98, v111, v125, v141, v159] .nil .nil) (.node [v20, v66, v98, v111, v125, v141, v159] .nil .nil)) (.node [v23, v66, v98, v111, v125, v141, v159] (.node [v22, v66, v98, v111, v125, v141, v159] .nil .nil) (.node [v26, v66, v98, v111, v125, v141, v159] .nil .nil)))) (.node [v46, v66, v98, v111, v125, v141, v159] (.node [v36, v66, v98, v111, v125, v141, v159] (.node [v33, v66, v98, v111, v125, v141, v159] (.node [v32, v66, v98, v125, v141, v159] .nil .nil) (.node [v34, v66, v98, v111, v125, v141, v159] .nil .nil)) (.node [v40, v66, v98, v111, v125, v141, v159] (.node [v38, v66, v98, v111, v125, v141, v159] .nil .nil) (.node [v45, v66, v98, v111, v125, v141, v159] .nil .nil))) (.node [v51, v66, v98, v111, v125, v141, v159] (.node [v49, v66, v98, v111, v125, v141, v159] (.node [v47, v66, v98, v111, v125, v141, v159] .nil .nil) (.node [v50, v66, v98, v111, v125, v141, v159] .nil .nil)) (.node [v61, v66, v98, v111, v125, v141, v159] (.node [v59, v66, v98, v111, v125, v141, v159] .nil .nil) (.node [v63, v66, v98, v111, v125, v141] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6l_ok : everyKey (rowOK 5 level5) level6l = true := by decide +kernel
def level6r : BinaryTree (List W) := (.node [v66, v98, v111, v122, v125, v141, v159] (.node [v66, v90, v98, v111, v125, v141, v159] (.node [v66, v78, v98, v111, v125, v141, v159] (.node [v66, v73, v98, v111, v125, v141, v159] (.node [v66, v70, v98, v111, v125, v141, v159] .nil .nil) (.node [v66, v76, v98, v111, v125, v141, v159] .nil .nil)) (.node [v66, v82, v98, v111, v125, v141, v159] (.node [v66, v79, v98, v111, v125, v141, v159] .nil .nil) (.node [v66, v82, v98, v125, v141, v159] .nil .nil))) (.node [v66, v98, v105, v111, v125, v141, v159] (.node [v66, v96, v98, v111, v125, v141, v159] (.node [v66, v94, v98, v111, v125, v141, v159] .nil .nil) (.node [v66, v98, v102, v111, v125, v141, v159] .nil .nil)) (.node [v66, v98, v111, v119, v125, v141, v159] (.node [v66, v98, v108, v111, v125, v141, v159] .nil .nil) (.node [v66, v98, v111, v120, v125, v141, v159] .nil .nil)))) (.node [v66, v98, v111, v125, v141, v156, v159] (.node [v66, v98, v111, v125, v138, v141, v159] (.node [v66, v98, v111, v125, v134, v141, v159] (.node [v66, v98, v111, v125, v130, v141, v159] .nil .nil) (.node [v66, v98, v111, v125, v137, v141, v159] .nil .nil)) (.node [v66, v98, v111, v125, v141, v152, v159] (.node [v66, v98, v111, v125, v141, v149, v159] .nil .nil) (.node [v66, v98, v111, v125, v141, v153, v159] .nil .nil))) (.node [v66, v98, v111, v125, v141, v159, v173] (.node [v66, v98, v111, v125, v141, v159, v169] (.node [v66, v98, v111, v125, v141, v159, v160] .nil .nil) (.node [v66, v98, v111, v125, v141, v159, v171] .nil .nil)) (.node [v66, v98, v111, v125, v141, v159, v175] (.node [v66, v98, v111, v125, v141, v159, v174] .nil .nil) (.node [v66, v98, v111, v125, v141, v159, v176] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6r_ok : everyKey (rowOK 5 level5) level6r = true := by decide +kernel
def level6 : BinaryTree (List W) := .node [v63, v66, v98, v111, v125, v141, v159] level6l level6r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6_ok : everyKey (rowOK 5 level5) level6 = true := by
  change (_ && everyKey (rowOK 5 level5) level6l && everyKey (rowOK 5 level5) level6r) = true
  rw [level6l_ok, level6r_ok]
  decide +kernel
theorem closed6 : Closed 6 level6 := closed_next 5 (by decide) level6 level5 closed5 level6_ok
def level7 : BinaryTree (List W) := (.node [v66, v98, v111, v125, v141, v159] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7_ok : everyKey (rowOK 6 level6) level7 = true := by decide +kernel
theorem closed7 : Closed 7 level7 := closed_next 6 (by decide) level7 level6 closed6 level7_ok

theorem lower : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z 7 ins.toFinset :=
  @no_build 7 level7 ins (by decide +kernel) (by decide) closed7 (by decide +kernel)
def witness : List Gate := [⟨.and,[1,2]⟩, ⟨.or,[3,4]⟩, ⟨.and,[6,7]⟩, ⟨.or,[0,8]⟩, ⟨.or,[1,4]⟩, ⟨.and,[3,10]⟩, ⟨.or,[5,11]⟩, ⟨.or,[6,12]⟩, ⟨.and,[9,13]⟩]
theorem upper : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 9 ∧ ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xeaeaeaaaeac0c880 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact ⟨witness,14,by simp [witness],rfl,by decide +kernel⟩
end PEqualNP.Outside.L_meta_15615_aux

open PEqualNP.Outside.L_meta_15615_aux in
theorem PEqualNP.Outside.L_meta_15615 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941264042 * 2 ^ 32 + 3938502784) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941264042 * 2 ^ 32 + 3938502784) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  have code : 3941264042 * 2 ^ 32 + 3938502784 = 0xeaeaeaaaeac0c880 := by decide
  simp only [code] at h ⊢
  obtain ⟨C,legal,size,computes⟩ := h
  obtain ⟨gs,o,mono,bound,ev⟩ := replace 0xeaeaeaaaeac0c880 9 ins (by decide +kernel) sampled rfl lower upper C.gates C.output legal computes
  exact ⟨⟨gs,o⟩,mono,bound.trans size,ev⟩
