import PEqualNP.Defs

-- The live-wire search and circuit compiler are adapted from tacyon52 in L-meta-8639, pull request 12794 under Apache-2.0.
namespace PEqualNP.Outside.L_meta_16721_aux

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

def v0 : W := 0x153c4d9300000001f07e1c
def v1 : W := 0x2b95e4bb4000000e038060
def v2 : W := 0x30b12c2a400001c1cc719b
def v3 : W := 0x35bd6dbb400001c1fc7f9f
def v4 : W := 0x3e28eda0000001f003ff80
def v5 : W := 0x3eb9edaa400001f1cfff9b
def v6 : W := 0x3fbd8900000001fffc0000
def v7 : W := 0xa98000346ec000000000719b
def v8 : W := 0x1570000569700001c00007e1c
def v9 : W := 0x19a000064bb400e6000038060
def v10 : W := 0x1df000076bf400e7c0003fe7c
def v11 : W := 0x1e4000076e0000f800003ff80
def v12 : W := 0x1ed800076eec00f800003ff9b
def v13 : W := 0x1f7000076f7000f9c0003ff9c
def v14 : W := 0x1fe000076fb400fe00003ffe0
def v15 : W := 0x1ff80001244800ffe00000000
def v16 : W := 0x1ff800076e4800ffe0003ff80
def v17 : W := 0x1ffbfbd9b44800ffffffc0000
def v18 : W := 0x80110701c0600000001c07018
def v19 : W := 0x40882091242a40000000000000
def v20 : W := 0x4c0980d3000ec0000001cc001b
def v21 : W := 0x91120114449300000000000000
def v22 : W := 0x98130154001700e01c01f0001c
def v23 : W := 0xd01a0195001b4700600e000060
def v24 : W := 0xd81b01d5001f47e07c0ff0007c
def v25 : W := 0xdc0001d7000007f0000ffc0000
def v26 : W := 0xdc1301d7001707f01c0ffc001c
def v27 : W := 0xdc1b8042000487f07e00000000
def v28 : W := 0xdc1b81d7000487f07e0ffc0000
def v29 : W := 0xdc1bbe6aeda487f07ff003ff80
def v30 : W := 0xdde401d776e007ff800fffff80
def v31 : W := 0x200a070203c60000001c0007180
def v32 : W := 0x20c21d0621844800001c1cc719b
def v33 : W := 0x244a8e0832068c00001c00c0183
def v34 : W := 0x24c0070f30800000001c1cc0000
def v35 : W := 0x24ca9c042104480000000000000
def v36 : W := 0x24ca9e0c3306cc00001c00c0183
def v37 : W := 0x24ca9e0d3206ec00001c1cc019b
def v38 : W := 0x24ca9e0d3346ec0000000000000
def v39 : W := 0x24ca9f0e3386cc00001c1cc719b
def v40 : W := 0x24ca9f0f33c6ec00001c1cc719b
def v41 : W := 0x24ca9f5ff7dffc00001c1fc7f9f
def v42 : W := 0x24dffc0421244800ffe00000000
def v43 : W := 0x2ddbbf1f77cffc00001c1cc719b
def v44 : W := 0x4214414285f8000000000007e00
def v45 : W := 0x4284514681b0400e01c01f07e1c
def v46 : W := 0x4b156050c439100e01c00300e04
def v47 : W := 0x4b156152c5f9100e01c00307e04
def v48 : W := 0x4b156153c4f9300e01c01f07e1c
def v49 : W := 0x4b156153c5f9300000000007e00
def v50 : W := 0x4b800157c090000e00001f00000
def v51 : W := 0x4b956157c4b9100e01c01f00e04
def v52 : W := 0x4b9570040120400e01c00000000
def v53 : W := 0x4b957156c5b9500e01c01f07e1c
def v54 : W := 0x4b957157c5f9700e01c01f07e1c
def v55 : W := 0x4b9ff957c7fffc0e01c01f07f9f
def v56 : W := 0x4f9df35fd7fbf40e01c01f07e1c
def v57 : W := 0x4fd5f95ff5f9fc0e01c01fc7e1f
def v58 : W := 0x6206454281b40380181f0007f80
def v59 : W := 0x62c00546a090038f001f1fc0000
def v60 : W := 0x62c65c0421244b8f19e00000000
def v61 : W := 0x62c65ebd7f6fff8f19e0e038060
def v62 : W := 0x62d9a546a6dbb78fe61f1ff8060
def v63 : W := 0x62dffc0421244b8fffe00000000
def v64 : W := 0x66cedc0421244b8f19e00000000
def v65 : W := 0x66dedf4fb7feec00001c1cc7f9b
def v66 : W := 0x6bd77c0421244b8f19e00000000
def v67 : W := 0x6f07e55bd1b5b7f01e1fe007fe0
def v68 : W := 0x6f5fee58f63f9c0e01dc03c0f87
def v69 : W := 0x6fc7fc0421244bff1fe00000000
def v70 : W := 0x6fdffc042124480e01c00000000
def v71 : W := 0x6fdffd57e5fd780e01c01f07e1c
def v72 : W := 0x6fdfff5ff7fffc0e01dc1fc7f9f
def v73 : W := 0x903802a00e4a0000e0000038000
def v74 : W := 0x942882a81a028470e600e038060
def v75 : W := 0x993120b04c091070e600e038060
def v76 : W := 0x993122b95e4bb470e600e038060
def v77 : W := 0x9d2002b9580000700000e000000
def v78 : W := 0x9d2003fbd8900070001fffc0000
def v79 : W := 0x9d39a00000000070e6000000000
def v80 : W := 0x9d39a2b95e4bb470e600e038060
def v81 : W := 0xb02a06a00a060380f81f0038180
def v82 : W := 0xb42a86a81a0687f0fe1fe0381e0
def v83 : W := 0xb46006a8380003f1001fe0c0000
def v84 : W := 0xb46007fbf89003f1001fffc0000
def v85 : W := 0xb46a8c0020040bf1fe200000000
def v86 : W := 0xb46a8d53e4dd3bf1fe201f07e1c
def v87 : W := 0xb47576a83d6973f101dfe0c7e1c
def v88 : W := 0xb9ab36b54a07738ef9df1f3819c
def v89 : W := 0xb9f33db66d8d5870e61cfcff1fb
def v90 : W := 0xbdfbbebd7f4ffc70e600e038060
def v91 : W := 0xbdfbbfbf7fcffc70e61cfcff1fb
def v92 : W := 0xd23440e08c380380f8030038e00
def v93 : W := 0xd23441e28df80380f803003fe00
def v94 : W := 0xd23443e28efa0380f81f003ff80
def v95 : W := 0xd23c43e28ffa0000e000003fe00
def v96 : W := 0xd6acd3ee9bb2c47ee7c0ff3fe7c
def v97 : W := 0xd6f4d8edbc38ef80f8031cf8e1b
def v98 : W := 0xdb2000f0c81003ff0003e300000
def v99 : W := 0xdb2003fbd89003ff001fffc0000
def v100 : W := 0xdb2a98f0cb56efff0003e30719b
def v101 : W := 0xdb356000002003ffffe00000000
def v102 : W := 0xdb3560b04c2913ffffe0e038060
def v103 : W := 0xdb35630b12e2a7fffffc1cc719b
def v104 : W := 0xdba001f7c89003ff0003ff00000
def v105 : W := 0xdfa003ffd890007e0000ff00000
def v106 : W := 0xdfbdf3ffdffbf47ee7c0ff3fe7c
def v107 : W := 0xf22007e288900380001f0000000
def v108 : W := 0xf22007fbd8900380001fffc0000
def v109 : W := 0xf22647e289b40380181f0000000
def v110 : W := 0xf22647e289b40380181f0007f80
def v111 : W := 0xf22e47e28bb60380f81f003ff80
def v112 : W := 0xf23447e289b00380001f0000000
def v113 : W := 0xf23447e28cb80380f81f0038e00
def v114 : W := 0xf23447e28df80380001f0007e00
def v115 : W := 0xf23645e28dbc0380f81f003ff80
def v116 : W := 0xf23e440001240380f8000000000
def v117 : W := 0xf23e47e289b40380f81f0000000
def v118 : W := 0xf23e47e28ffe0380f81f003ff80
def v119 : W := 0xf23edfe28ffeef80f81f003ff9b
def v120 : W := 0xf23fe7e28fffb780fe1f003ffe0
def v121 : W := 0xf2e007e6a890038f001f1fc0000
def v122 : W := 0xf2fe5c0421244b8ff9e00000000
def v123 : W := 0xf63ec7eb9ffea780f81f003ff80
def v124 : W := 0xf66007eab89003f1001fe0c0000
def v125 : W := 0xf67ecfeabffe8f80f81f00fff83
def v126 : W := 0xf6e007eeb89003ff001fffc0000
def v127 : W := 0xf6e007efb8900380001f1cc0000
def v128 : W := 0xf6eedc0421244bffffe00000000
def v129 : W := 0xf6fedc0421244b80f8000000000
def v130 : W := 0xf6fedfe6affe4b80f81f003ff80
def v131 : W := 0xf6fedfefbffeef80f81f1cfff9b
def v132 : W := 0xfb2007f2c89003ff001fe300000
def v133 : W := 0xfb3f67f3cfff3380f81f003ff80
def v134 : W := 0xfba007f7c890038e001f1f00000
def v135 : W := 0xfbbf77f7cfff738ef9df1f3ff9c
def v136 : W := 0xfbe005f6e89003ff001fffc0000
def v137 : W := 0xfbf77c0421244bffffe00000000
def v138 : W := 0xff2007fbd89003f0001fe000000
def v139 : W := 0xff3fe7fbdfffb7f0fe1fe03ffe0
def v140 : W := 0xffe00404200003ff00000000000
def v141 : W := 0xffe007e6a89003ff001f0000000
def v142 : W := 0xffe007fff89003ff001fffc0000
def v143 : W := 0xffe09ffff890efff001fffc001b
def v144 : W := 0xffe137fff89173ff01dfffc001c
def v145 : W := 0xffe1a7fff891b7ff061fffc0060
def v146 : W := 0xffe1bffff8904bff07ffffc0000
def v147 : W := 0xffe65c0421244bff19e00000000
def v148 : W := 0xffe65ffff9b44bff19ffffc0000
def v149 : W := 0xffe887fffad2a7ff001fffc0000
def v150 : W := 0xffea8ffffa968fff001fffc0183
def v151 : W := 0xffea9ffff9944bff001fffc0000
def v152 : W := 0xffea9ffffbd6efff001fffc719b
def v153 : W := 0xfff127fffcd933ff001fffc0000
def v154 : W := 0xfff577fff9b043ff01dfffc0000
def v155 : W := 0xfff577fffdf973ff01dfffc7e1c
def v156 : W := 0xfff9a7fffedbb7ffe61ffff8060
def v157 : W := 0xfffe47fffffe03fff81ffffff80
def v158 : W := 0xfffffc0421244bffffe00000000
def v159 : W := 0xfffffc04276fffffffe00038060
def v160 : W := 0xfffffc15656d7bffffe00000000
def v161 : W := 0xfffffc1d7125ffffffe0e000060
def v162 : W := 0xfffffcb46d2d5bffffe0e038060
def v163 : W := 0xfffffcf4e9344bffffe3e300000
def v164 : W := 0xfffffd57e5fd7bffffe01f07e1c
def v165 : W := 0xfffffe0d3366efffffe00000000
def v166 : W := 0xfffffea42f6e4bffffe00038000
def v167 : W := 0xfffffeac3b26cfffffe0e038060
def v168 : W := 0xfffffebd79244bffffe0e000000
def v169 : W := 0xfffffebd7f6fffffffe0e038060
def v170 : W := 0xffffff0f33e6effffffc1cc719b
def v171 : W := 0xffffffe6affe4bffffff003ff80
def v172 : W := 0xfffffffff9b44bffffffffc0000

def ins : List W := [v40, v54, v80, v118, v142, v158]
theorem sampled : ∀ j : Fin 108, Nat.testBit 0xfeeaeeeafce0e0e0 (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
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
def level4 : BinaryTree (List W) := (.node [v40, v54, v80, v112, v158] (.node [v40, v54, v61, v118, v142] (.node [v30, v40, v54, v80, v158] (.node [v29, v40, v54, v80, v142] (.node [v17, v40, v54, v80, v118] .nil .nil) .nil) (.node [v40, v54, v60, v80, v109] (.node [v40, v49, v80, v107, v158] .nil .nil) .nil)) (.node [v40, v54, v80, v107, v129] (.node [v40, v54, v67, v142, v158] (.node [v40, v54, v62, v118, v158] .nil .nil) .nil) (.node [v40, v54, v80, v109, v158] .nil .nil))) (.node [v54, v80, v97, v142, v158] (.node [v40, v80, v88, v142, v158] (.node [v40, v80, v87, v118, v158] (.node [v40, v80, v86, v118, v142] .nil .nil) .nil) (.node [v54, v65, v80, v107, v158] (.node [v40, v96, v118, v142, v158] .nil .nil) .nil)) (.node [v54, v89, v118, v142, v158] (.node [v54, v80, v103, v118, v142] (.node [v54, v80, v100, v118, v158] .nil .nil) .nil) (.node [v68, v80, v118, v142, v158] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4_ok : everyKey (rowOK 3 level3) level4 = true := by decide +kernel
theorem closed4 : Closed 4 level4 := closed_next 3 (by decide) level4 level3 closed3 level4_ok
def level5ll : BinaryTree (List W) := (.node [v14, v40, v54, v80, v118, v158] (.node [v9, v40, v54, v59, v118, v158] (.node [v4, v27, v40, v54, v80, v142] (.node [v2, v54, v80, v101, v118, v142] (.node [v1, v40, v54, v60, v118, v142] (.node [v0, v40, v80, v85, v118, v142] .nil .nil) .nil) (.node [v3, v40, v54, v80, v118, v142] .nil .nil)) (.node [v7, v54, v80, v98, v118, v158] (.node [v6, v15, v40, v54, v80, v118] (.node [v5, v40, v54, v80, v118, v142] .nil .nil) .nil) (.node [v8, v40, v80, v83, v118, v158] .nil .nil))) (.node [v11, v40, v54, v80, v118, v158] (.node [v11, v40, v54, v60, v80, v118] (.node [v11, v25, v40, v54, v80, v158] (.node [v10, v40, v54, v80, v118, v158] .nil .nil) .nil) (.node [v11, v40, v54, v80, v107, v158] .nil .nil)) (.node [v12, v40, v54, v80, v118, v158] (.node [v11, v40, v54, v80, v118, v169] .nil .nil) (.node [v13, v40, v54, v80, v118, v158] .nil .nil)))) (.node [v24, v40, v54, v80, v142, v158] (.node [v21, v40, v106, v118, v142, v158] (.node [v19, v54, v91, v118, v142, v158] (.node [v18, v72, v80, v118, v142, v158] (.node [v16, v40, v54, v80, v118, v158] .nil .nil) .nil) (.node [v20, v54, v80, v92, v142, v158] .nil .nil)) (.node [v22, v40, v80, v81, v142, v158] (.node [v22, v40, v54, v80, v107, v158] .nil .nil) (.node [v23, v40, v54, v58, v142, v158] .nil .nil))) (.node [v32, v54, v75, v118, v142, v158] (.node [v28, v40, v54, v80, v142, v158] (.node [v27, v40, v54, v80, v107, v158] (.node [v26, v40, v54, v80, v142, v158] .nil .nil) .nil) (.node [v31, v54, v80, v131, v142, v158] .nil .nil)) (.node [v34, v54, v80, v118, v152, v158] (.node [v33, v46, v80, v118, v142, v158] .nil .nil) (.node [v35, v54, v80, v118, v142, v170] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5ll_ok : everyKey (rowOK 4 level4) level5ll = true := by decide +kernel
def level5lr : BinaryTree (List W) := (.node [v40, v54, v60, v80, v107, v118] (.node [v40, v47, v80, v118, v142, v158] (.node [v40, v42, v54, v80, v118, v142] (.node [v38, v54, v80, v118, v142, v169] (.node [v38, v54, v80, v118, v142, v158] (.node [v37, v54, v80, v118, v142, v158] .nil .nil) .nil) (.node [v39, v54, v80, v118, v142, v158] .nil .nil)) (.node [v40, v44, v80, v135, v142, v158] (.node [v40, v44, v54, v80, v107, v158] .nil .nil) (.node [v40, v45, v74, v118, v142, v158] .nil .nil))) (.node [v40, v52, v80, v118, v142, v164] (.node [v40, v50, v80, v118, v155, v158] (.node [v40, v49, v80, v118, v142, v158] (.node [v40, v48, v80, v118, v142, v158] .nil .nil) .nil) (.node [v40, v51, v80, v118, v142, v158] .nil .nil)) (.node [v40, v54, v58, v80, v107, v158] (.node [v40, v53, v80, v118, v142, v158] .nil .nil) (.node [v40, v54, v60, v78, v80, v118] .nil .nil)))) (.node [v40, v54, v73, v139, v142, v158] (.node [v40, v54, v64, v80, v118, v142] (.node [v40, v54, v60, v118, v142, v169] (.node [v40, v54, v60, v80, v118, v148] (.node [v40, v54, v60, v80, v118, v142] .nil .nil) .nil) (.node [v40, v54, v63, v80, v118, v142] .nil .nil)) (.node [v40, v54, v69, v80, v118, v142] (.node [v40, v54, v66, v80, v118, v142] .nil .nil) (.node [v40, v54, v70, v80, v118, v142] .nil .nil))) (.node [v40, v54, v79, v118, v142, v169] (.node [v40, v54, v77, v118, v156, v158] (.node [v40, v54, v76, v118, v142, v158] (.node [v40, v54, v75, v118, v142, v169] .nil .nil) .nil) (.node [v40, v54, v78, v80, v118, v158] .nil .nil)) (.node [v40, v54, v80, v92, v107, v158] (.node [v40, v54, v80, v84, v118, v158] .nil .nil) (.node [v40, v54, v80, v93, v142, v158] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lr_ok : everyKey (rowOK 4 level4) level5lr = true := by decide +kernel
def level5l : BinaryTree (List W) := .node [v36, v54, v80, v118, v142, v158] level5ll level5lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5l_ok : everyKey (rowOK 4 level4) level5l = true := by
  change (_ && everyKey (rowOK 4 level4) level5ll && everyKey (rowOK 4 level4) level5lr) = true
  rw [level5ll_ok, level5lr_ok]
  decide +kernel
def level5rl : BinaryTree (List W) := (.node [v40, v54, v80, v118, v121, v158] (.node [v40, v54, v80, v107, v157, v158] (.node [v40, v54, v80, v107, v116, v158] (.node [v40, v54, v80, v104, v118, v158] (.node [v40, v54, v80, v99, v118, v158] (.node [v40, v54, v80, v95, v142, v158] .nil .nil) .nil) (.node [v40, v54, v80, v105, v118, v158] .nil .nil)) (.node [v40, v54, v80, v107, v131, v158] (.node [v40, v54, v80, v107, v118, v169] (.node [v40, v54, v80, v107, v118, v158] .nil .nil) .nil) (.node [v40, v54, v80, v107, v139, v158] .nil .nil))) (.node [v40, v54, v80, v114, v142, v158] (.node [v40, v54, v80, v111, v142, v158] (.node [v40, v54, v80, v110, v142, v158] (.node [v40, v54, v80, v108, v118, v158] .nil .nil) .nil) (.node [v40, v54, v80, v113, v142, v158] .nil .nil)) (.node [v40, v54, v80, v116, v142, v171] (.node [v40, v54, v80, v115, v142, v158] .nil .nil) (.node [v40, v54, v80, v117, v142, v158] .nil .nil)))) (.node [v40, v54, v80, v118, v136, v158] (.node [v40, v54, v80, v118, v128, v142] (.node [v40, v54, v80, v118, v126, v158] (.node [v40, v54, v80, v118, v124, v158] (.node [v40, v54, v80, v118, v122, v142] .nil .nil) .nil) (.node [v40, v54, v80, v118, v127, v158] .nil .nil)) (.node [v40, v54, v80, v118, v132, v158] (.node [v40, v54, v80, v118, v129, v142] .nil .nil) (.node [v40, v54, v80, v118, v134, v158] .nil .nil))) (.node [v40, v54, v80, v118, v142, v147] (.node [v40, v54, v80, v118, v140, v172] (.node [v40, v54, v80, v118, v138, v158] (.node [v40, v54, v80, v118, v137, v142] .nil .nil) .nil) (.node [v40, v54, v80, v118, v141, v158] .nil .nil)) (.node [v40, v54, v80, v118, v142, v159] (.node [v40, v54, v80, v118, v142, v158] .nil .nil) (.node [v40, v54, v80, v118, v142, v160] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rl_ok : everyKey (rowOK 4 level4) level5rl = true := by decide +kernel
def level5rr : BinaryTree (List W) := (.node [v40, v54, v80, v119, v142, v158] (.node [v40, v54, v80, v118, v144, v158] (.node [v40, v54, v80, v118, v142, v167] (.node [v40, v54, v80, v118, v142, v165] (.node [v40, v54, v80, v118, v142, v163] (.node [v40, v54, v80, v118, v142, v162] .nil .nil) .nil) (.node [v40, v54, v80, v118, v142, v166] .nil .nil)) (.node [v40, v54, v80, v118, v142, v169] (.node [v40, v54, v80, v118, v142, v168] .nil .nil) (.node [v40, v54, v80, v118, v143, v158] .nil .nil))) (.node [v40, v54, v80, v118, v150, v158] (.node [v40, v54, v80, v118, v148, v158] (.node [v40, v54, v80, v118, v146, v158] (.node [v40, v54, v80, v118, v145, v158] .nil .nil) .nil) (.node [v40, v54, v80, v118, v149, v158] .nil .nil)) (.node [v40, v54, v80, v118, v153, v158] (.node [v40, v54, v80, v118, v151, v158] .nil .nil) (.node [v40, v54, v80, v118, v154, v158] .nil .nil)))) (.node [v40, v56, v80, v118, v142, v158] (.node [v40, v54, v80, v133, v142, v158] (.node [v40, v54, v80, v125, v142, v158] (.node [v40, v54, v80, v123, v142, v158] (.node [v40, v54, v80, v120, v142, v158] .nil .nil) .nil) (.node [v40, v54, v80, v130, v142, v158] .nil .nil)) (.node [v40, v54, v91, v118, v142, v169] (.node [v40, v54, v90, v118, v142, v158] .nil .nil) (.node [v40, v55, v80, v118, v142, v158] .nil .nil))) (.node [v43, v54, v80, v118, v142, v158] (.node [v40, v80, v82, v118, v142, v158] (.node [v40, v71, v80, v118, v142, v158] (.node [v40, v57, v80, v118, v142, v158] .nil .nil) .nil) (.node [v41, v54, v80, v118, v142, v158] .nil .nil)) (.node [v54, v80, v102, v118, v142, v158] (.node [v54, v65, v80, v118, v142, v158] .nil .nil) (.node [v54, v80, v102, v118, v142, v169] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rr_ok : everyKey (rowOK 4 level4) level5rr = true := by decide +kernel
def level5r : BinaryTree (List W) := .node [v40, v54, v80, v118, v142, v161] level5rl level5rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5r_ok : everyKey (rowOK 4 level4) level5r = true := by
  change (_ && everyKey (rowOK 4 level4) level5rl && everyKey (rowOK 4 level4) level5rr) = true
  rw [level5rl_ok, level5rr_ok]
  decide +kernel
def level5 : BinaryTree (List W) := .node [v40, v54, v80, v94, v142, v158] level5l level5r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5_ok : everyKey (rowOK 4 level4) level5 = true := by
  change (_ && everyKey (rowOK 4 level4) level5l && everyKey (rowOK 4 level4) level5r) = true
  rw [level5l_ok, level5r_ok]
  decide +kernel
theorem closed5 : Closed 5 level5 := closed_next 4 (by decide) level5 level4 closed4 level5_ok
def level6l : BinaryTree (List W) := (.node [v23, v40, v54, v80, v118, v142, v158] (.node [v11, v40, v54, v80, v118, v142, v158] (.node [v6, v40, v54, v80, v118, v142, v158] (.node [v2, v40, v54, v80, v118, v142, v158] (.node [v1, v40, v54, v80, v118, v142, v158] (.node [v0, v40, v54, v80, v118, v142, v158] .nil .nil) .nil) (.node [v4, v40, v54, v80, v118, v142, v158] .nil .nil)) (.node [v8, v40, v54, v80, v118, v142, v158] (.node [v7, v40, v54, v80, v118, v142, v158] .nil .nil) (.node [v9, v40, v54, v80, v118, v142, v158] .nil .nil))) (.node [v19, v40, v54, v80, v118, v142, v158] (.node [v15, v40, v54, v80, v118, v142, v158] (.node [v11, v40, v54, v80, v118, v158] .nil .nil) (.node [v18, v40, v54, v80, v118, v142, v158] .nil .nil)) (.node [v21, v40, v54, v80, v118, v142, v158] (.node [v20, v40, v54, v80, v118, v142, v158] .nil .nil) (.node [v22, v40, v54, v80, v118, v142, v158] .nil .nil)))) (.node [v40, v44, v54, v80, v118, v142, v158] (.node [v32, v40, v54, v80, v118, v142, v158] (.node [v27, v40, v54, v80, v118, v142, v158] (.node [v25, v40, v54, v80, v118, v142, v158] .nil .nil) (.node [v31, v40, v54, v80, v118, v142, v158] .nil .nil)) (.node [v34, v40, v54, v80, v118, v142, v158] (.node [v33, v40, v54, v80, v118, v142, v158] .nil .nil) (.node [v35, v40, v54, v80, v118, v142, v158] .nil .nil))) (.node [v40, v52, v54, v80, v118, v142, v158] (.node [v40, v46, v54, v80, v118, v142, v158] (.node [v40, v45, v54, v80, v118, v142, v158] .nil .nil) (.node [v40, v50, v54, v80, v118, v142, v158] .nil .nil)) (.node [v40, v54, v59, v80, v118, v142, v158] (.node [v40, v54, v58, v80, v118, v142, v158] .nil .nil) (.node [v40, v54, v60, v80, v118, v142] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6l_ok : everyKey (rowOK 5 level5) level6l = true := by decide +kernel
def level6r : BinaryTree (List W) := (.node [v40, v54, v80, v107, v118, v158] (.node [v40, v54, v80, v83, v118, v142, v158] (.node [v40, v54, v75, v80, v118, v142, v158] (.node [v40, v54, v73, v80, v118, v142, v158] (.node [v40, v54, v72, v80, v118, v142, v158] .nil .nil) (.node [v40, v54, v74, v80, v118, v142, v158] .nil .nil)) (.node [v40, v54, v79, v80, v118, v142, v158] (.node [v40, v54, v77, v80, v118, v142, v158] .nil .nil) (.node [v40, v54, v80, v81, v118, v142, v158] .nil .nil))) (.node [v40, v54, v80, v98, v118, v142, v158] (.node [v40, v54, v80, v91, v118, v142, v158] (.node [v40, v54, v80, v85, v118, v142, v158] .nil .nil) (.node [v40, v54, v80, v92, v118, v142, v158] .nil .nil)) (.node [v40, v54, v80, v106, v118, v142, v158] (.node [v40, v54, v80, v101, v118, v142, v158] .nil .nil) (.node [v40, v54, v80, v107, v118, v142, v158] .nil .nil)))) (.node [v40, v54, v80, v118, v142, v156, v158] (.node [v40, v54, v80, v118, v139, v142, v158] (.node [v40, v54, v80, v118, v131, v142, v158] (.node [v40, v54, v80, v116, v118, v142, v158] .nil .nil) (.node [v40, v54, v80, v118, v135, v142, v158] .nil .nil)) (.node [v40, v54, v80, v118, v142, v152, v158] (.node [v40, v54, v80, v118, v140, v142, v158] .nil .nil) (.node [v40, v54, v80, v118, v142, v155, v158] .nil .nil))) (.node [v40, v54, v80, v118, v142, v158, v170] (.node [v40, v54, v80, v118, v142, v158, v164] (.node [v40, v54, v80, v118, v142, v157, v158] .nil .nil) (.node [v40, v54, v80, v118, v142, v158, v169] .nil .nil)) (.node [v40, v54, v80, v118, v142, v158, v172] (.node [v40, v54, v80, v118, v142, v158, v171] .nil .nil) (.node [v40, v54, v80, v118, v142, v169] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6r_ok : everyKey (rowOK 5 level5) level6r = true := by decide +kernel
def level6 : BinaryTree (List W) := .node [v40, v54, v60, v80, v118, v142, v158] level6l level6r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6_ok : everyKey (rowOK 5 level5) level6 = true := by
  change (_ && everyKey (rowOK 5 level5) level6l && everyKey (rowOK 5 level5) level6r) = true
  rw [level6l_ok, level6r_ok]
  decide +kernel
theorem closed6 : Closed 6 level6 := closed_next 5 (by decide) level6 level5 closed5 level6_ok
def level7 : BinaryTree (List W) := (.node [v40, v54, v80, v118, v142, v158] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7_ok : everyKey (rowOK 6 level6) level7 = true := by decide +kernel
theorem closed7 : Closed 7 level7 := closed_next 6 (by decide) level7 level6 closed6 level7_ok

theorem lower : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z 7 ins.toFinset :=
  @no_build 7 level7 ins (by decide +kernel) (by decide) closed7 (by decide +kernel)
def witness : List Gate := [⟨.or,[0,1]⟩, ⟨.or,[0,3]⟩, ⟨.or,[1,2]⟩, ⟨.and,[4,8]⟩, ⟨.and,[3,9]⟩, ⟨.and,[5,7]⟩, ⟨.or,[2,11]⟩, ⟨.and,[6,12]⟩, ⟨.or,[10,13]⟩]
theorem upper : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 9 ∧ ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xfeeaeeeafce0e0e0 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact ⟨witness,14,by simp [witness],rfl,by decide +kernel⟩
end PEqualNP.Outside.L_meta_16721_aux

open PEqualNP.Outside.L_meta_16721_aux in
theorem PEqualNP.Outside.L_meta_16721 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4242596064) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4242596064) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  have code : 4276809450 * 2 ^ 32 + 4242596064 = 0xfeeaeeeafce0e0e0 := by decide
  simp only [code] at h ⊢
  obtain ⟨C,legal,size,computes⟩ := h
  obtain ⟨gs,o,mono,bound,ev⟩ := replace 0xfeeaeeeafce0e0e0 9 ins (by decide +kernel) sampled rfl lower upper C.gates C.output legal computes
  exact ⟨⟨gs,o⟩,mono,bound.trans size,ev⟩
