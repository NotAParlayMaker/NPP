import PEqualNP.Defs

-- The live-wire search and circuit compiler are adapted from tacyon52 in L-meta-8639, pull request 12794 under Apache-2.0.
namespace PEqualNP.Outside.L_meta_15353_aux

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

def v0 : W := 0xad660000000001cff
def v1 : W := 0x16726000000000631e
def v2 : W := 0x14012a000000034031e
def v3 : W := 0x1e01ab00000000000ff
def v4 : W := 0x84240c000000184601e
def v5 : W := 0x94252e000000000001e
def v6 : W := 0xc6340d0000000001c1f
def v7 : W := 0x2debdef0000000001cff
def v8 : W := 0x5b5672e0000001b4631e
def v9 : W := 0x739cbe200000063983e0
def v10 : W := 0x7bdefee0000007bde3fe
def v11 : W := 0x7e1fe440000007c1fc00
def v12 : W := 0x7f5ff6e0000007f5ff1e
def v13 : W := 0x7fe10890000007fe0000
def v14 : W := 0x7febdef0000007fe1cff
def v15 : W := 0x7ff77af0000007fe631e
def v16 : W := 0x7ffffef0000001b47fff
def v17 : W := 0x7ffffef0000006399fff
def v18 : W := 0x7ffffef0000007c1fcff
def v19 : W := 0x26800001000007f8000000
def v20 : W := 0x4828000010000f838000000
def v21 : W := 0x1108000ad6600039d8001cff
def v22 : W := 0x15ae800001000039d8000000
def v23 : W := 0x15ae800ad7600039d8001cff
def v24 : W := 0x2ce68000010000c620000000
def v25 : W := 0x2ce68016736000c62000631e
def v26 : W := 0x396c001cb6200307c00183e0
def v27 : W := 0x3dc8001ee44003f80001fc00
def v28 : W := 0x3dee8000010003fff8000000
def v29 : W := 0x3dee800ad76003fff8001cff
def v30 : W := 0x3dee801cb72003fff80183e0
def v31 : W := 0x3dee801ee54003fff801fc00
def v32 : W := 0x3dee801ef76000fff8007fff
def v33 : W := 0x3dee801ef760033fd8019fff
def v34 : W := 0x3dee801ef76003f9d801fcff
def v35 : W := 0x3deeffe1099003fffffe0000
def v36 : W := 0xc003800001000c0038000000
def v37 : W := 0x2802680000100680620000000
def v38 : W := 0x28026814013a068062034031e
def v39 : W := 0x3003401801a207007c03803e0
def v40 : W := 0x3003401c01aa07007c03c03fe
def v41 : W := 0x3003401e01ab07007c03803ff
def v42 : W := 0x3803681c01ba07807e03c03fe
def v43 : W := 0x3c01101e008907c00003e0000
def v44 : W := 0x3c037800001000001d8000000
def v45 : W := 0x3c037800001007c07f8000000
def v46 : W := 0x3c03781801b207c07f83803e0
def v47 : W := 0x3c03781e009907c07f83e0000
def v48 : W := 0x3c03781e01bb00001d80000ff
def v49 : W := 0x3c03781e01bb06807f83403ff
def v50 : W := 0x3c03781e01bb07007d83803ff
def v51 : W := 0x3c037fe1fe5407c07ffc1fc00
def v52 : W := 0x3fdd901feecd07ff8003ffc00
def v53 : W := 0x3fdff800001007ffff8000000
def v54 : W := 0x1084828000010308c020000000
def v55 : W := 0x108482884241c308c02184601e
def v56 : W := 0x1284a680000100000000000000
def v57 : W := 0x1284a6894253e000000000001e
def v58 : W := 0x1806800c03404380f801c07c00
def v59 : W := 0x1806800c4340c380f801c47c1e
def v60 : W := 0x1806800c6340d380f801c07c1f
def v61 : W := 0x1886828c4341c388f821c47c1e
def v62 : W := 0x18c2010c6100938c0001c60000
def v63 : W := 0x18c68380000100003818000000
def v64 : W := 0x18c683800001038cf838000000
def v65 : W := 0x18c6838c0341438cf839c07c00
def v66 : W := 0x18c6838c6101938cf839c60000
def v67 : W := 0x18c6838c6341d0003818001c1f
def v68 : W := 0x18c6838c6341d308f839847c1f
def v69 : W := 0x18c6838c6341d380f819c07c1f
def v70 : W := 0x18c683f39cbf238cf83e3983e0
def v71 : W := 0x18fb6d0c7db6b38f07c1c783e0
def v72 : W := 0x18ffef800001038ffff8000000
def v73 : W := 0x1b06b40d835a63f0ffc1f87fe0
def v74 : W := 0x1bc2110de10893fc0001fe0000
def v75 : W := 0x1bc6b780000103fcfff8000000
def v76 : W := 0x1bc6b78d835b63fcfff9f87fe0
def v77 : W := 0x41111820888c0c1301c60980e0
def v78 : W := 0x43113c21889e200001c00000e0
def v79 : W := 0x43113c2debdef00001c0001cff
def v80 : W := 0x4813082409840c833806419c00
def v81 : W := 0x49421124a1081c9400064a0000
def v82 : W := 0x4942117fe1089c940007fe0000
def v83 : W := 0x4953190000000c9739d8000000
def v84 : W := 0x49531924a98c100039d8001ce1
def v85 : W := 0x49531924a98c1c1339de099ce1
def v86 : W := 0x49531924a98c1c8339de419ce1
def v87 : W := 0x4953192debdef00039d8001cff
def v88 : W := 0x4953195b5672ec9739d9b4631e
def v89 : W := 0x496ef7a4b77b7c94c6264a631e
def v90 : W := 0x497fff8000010c97fff8000000
def v91 : W := 0x4a932ea54997aceb3e26759f1e
def v92 : W := 0x4bc21125e1089cfc00067e0000
def v93 : W := 0x4bd33f8000010cff3ff8000000
def v94 : W := 0x51959aa8cacdcf1bc1e78de0fe
def v95 : W := 0x5817882c0bc440003800001c00
def v96 : W := 0x5817882debdef0003800001cff
def v97 : W := 0x59c2112ce1089f9c0007ce0000
def v98 : W := 0x59d79b8000010f9ff9f8000000
def v99 : W := 0x5bc2112de10890000000000000
def v100 : W := 0x5bc2112de108907c00003e0000
def v101 : W := 0x5bc2112de108938c0001c60000
def v102 : W := 0x5bc2112de1089c9400064a0000
def v103 : W := 0x5bc2112debdef0000000001cff
def v104 : W := 0x5bc2117fe10890000007fe0000
def v105 : W := 0x5bc6b7ade10990000000000000
def v106 : W := 0x5bd7bf800001000039d8000000
def v107 : W := 0x5bd7bf800001007c3ff8000000
def v108 : W := 0x5bd7bf800001038cf9f8000000
def v109 : W := 0x5bd7bf8000010c9739d8000000
def v110 : W := 0x5bd7bfa1889f200039d80000e0
def v111 : W := 0x5bd7bfa4a98d100039d8001ce1
def v112 : W := 0x5bd7bfac0bc5400039d8001c00
def v113 : W := 0x5bd7bfade109900039d8000000
def v114 : W := 0x5bd7bfadebdff00039d8001cff
def v115 : W := 0x5bffff8000010003fff8000000
def v116 : W := 0xa400005200000ffc0007fe0000
def v117 : W := 0xa415aed20ad76ffc39dffe1cff
def v118 : W := 0xa428400000000fffc620000000
def v119 : W := 0xa428402debdeffffc620001cff
def v120 : W := 0xa428405214200368c621b46300
def v121 : W := 0xa428405214200c730606398300
def v122 : W := 0xa428405214200f83c007c1e000
def v123 : W := 0xa428405b5672e368c621b4631e
def v124 : W := 0xa42ce6d216736368c621b4631e
def v125 : W := 0xa4396c521cb62c7307c63983e0
def v126 : W := 0xa43dc8521ee44f83f807c1fc00
def v127 : W := 0xa43dee8000010ffffff8000000
def v128 : W := 0xa6286453143220600600300300
def v129 : W := 0xa628645b5672e0600601b4631e
def v130 : W := 0xa62ce6d316736060c62030631e
def v131 : W := 0xa6396c531cb6206307c03183e0
def v132 : W := 0xa7e8778000010fffc7f8000000
def v133 : W := 0xa7e877d3f43bbf83c1dfc1e0ff
def v134 : W := 0xb42cc05a16604300c001806000
def v135 : W := 0xb42cc05b5672e300c001b4631e
def v136 : W := 0xb42ce6da16736300c62180631e
def v137 : W := 0xb43dc85a1ee44303f80181fc00
def v138 : W := 0xb680005b400083680001b40000
def v139 : W := 0xb680005b5672e3680001b4631e
def v140 : W := 0xb6ace68000010368c620000000
def v141 : W := 0xb6ace68000010fffc620000000
def v142 : W := 0xb6ace6d214210368c621b46300
def v143 : W := 0xb6ace6d314332368c620300300
def v144 : W := 0xb6ace6da16614368c621806000
def v145 : W := 0xb6ace6db16736368c621b06300
def v146 : W := 0xb6ace6db40018368c621b40000
def v147 : W := 0xb6ace6db5673e060060030031e
def v148 : W := 0xb6ace6db5673e300c00180601e
def v149 : W := 0xb6ace6db5673e368c621b4631e
def v150 : W := 0xb6bdee800001036bfff8000000
def v151 : W := 0xb7ecf7800001037cc7f8000000
def v152 : W := 0xb7ecf7dbf67bf37cc621be631e
def v153 : W := 0xbceec38000010ffffe38000000
def v154 : W := 0xbceec3de7761dc733e1e399f1f
def v155 : W := 0xbeeee780000103ecfe38000000
def v156 : W := 0xbeeee7df7773f3ecc621f6631e
def v157 : W := 0xe43948721ca40c030006018000
def v158 : W := 0xe43948739cbe2c0300063983e0
def v159 : W := 0xe439487e1fe44c030007c1fc00
def v160 : W := 0xe4396c721cb62c0307c60183e0
def v161 : W := 0xe43dc8721ee44c03f80601fc00
def v162 : W := 0xe6396c731cb62c630606318300
def v163 : W := 0xe700107380080c700006380000
def v164 : W := 0xe7397c0000000c7307c0000000
def v165 : W := 0xe7397c739cbe206007c03003e0
def v166 : W := 0xe7397c739cbe2c0301c60180e0
def v167 : W := 0xe7397c739cbe2c7307c63983e0
def v168 : W := 0xe7397c7bdefeec7307c7bde3fe
def v169 : W := 0xe7397c7ffffefc7307c6399fff
def v170 : W := 0xe7397ef39cbf2c7307fe3983e0
def v171 : W := 0xe73dfe8000010c73fff8000000
def v172 : W := 0xe73dfef39cbf2c73fffe3983e0
def v173 : W := 0xe7b97ef39cbf2c7b07e63983e0
def v174 : W := 0xe7f97d73fcbebc7f07c63f83e0
def v175 : W := 0xe7f97f8000010c7f07f8000000
def v176 : W := 0xe7f97ff39cbf2c7307de3983e0
def v177 : W := 0xe7f97ff39cbf2c7f07fe3983e0
def v178 : W := 0xe7f97ff3fcbfbc7f07fe3f83e0
def v179 : W := 0xed7b5976bdac1368fff9b47fe1
def v180 : W := 0xef7b7d77bdbe3cf707c67b83e0
def v181 : W := 0xf43dc87a1ee44f03c00781e000
def v182 : W := 0xf7bdfe8000010f7bc7e0000000
def v183 : W := 0xf7bdfef39cbf2c7307c63983e0
def v184 : W := 0xf7bdfef39cbf2f7bc7e63983e0
def v185 : W := 0xf7bdfefbdeffef7bc7e7bde3fe
def v186 : W := 0xfc02007e01000f800007c00000
def v187 : W := 0xfc3fc80000000f83f800000000
def v188 : W := 0xfc3fc87e1fe44300f801807c00
def v189 : W := 0xfc3fc87e1fe44c033806019c00
def v190 : W := 0xfc3fc87e1fe44f83f807c1fc00
def v191 : W := 0xfc3fc87f5ff6ef83f807f5ff1e
def v192 : W := 0xfc3fc87ffffeff83f807c1fcff
def v193 : W := 0xfc3fcafe1fe54f83f83fc1fc00
def v194 : W := 0xfc3fee8000010f83fff8000000
def v195 : W := 0xfc3feefe1fe54f83ffffc1fc00
def v196 : W := 0xfcbfcafe1fe54f8bf827c1fc00
def v197 : W := 0xfcffc97e7fe4df8ff807c7fc00
def v198 : W := 0xfcffcb8000010f8ff838000000
def v199 : W := 0xfcffcbfe1fe54f83f81fc1fc00
def v200 : W := 0xfcffcbfe1fe54f8ff83fc1fc00
def v201 : W := 0xfcffcbfe7fe5df8ff83fc7fc00
def v202 : W := 0xfd7fd97ebfec5f97f807cbfc00
def v203 : W := 0xfebfee8000010febfe20000000
def v204 : W := 0xfebfeefe1fe54f83f807c1fc00
def v205 : W := 0xfebfeefe1fe54febfe27c1fc00
def v206 : W := 0xfebfeeff5ff7efebfe27f5ff1e
def v207 : W := 0xff3ffc7f9ffe6ff3ffc7f9ffe0
def v208 : W := 0xffc2110000000ffc0000000000
def v209 : W := 0xffc2112de1089ffc0000000000
def v210 : W := 0xffc2117fe10893680001b40000
def v211 : W := 0xffc2117fe1089c700006380000
def v212 : W := 0xffc2117fe1089f800007c00000
def v213 : W := 0xffc2117fe1089ffc0007fe0000
def v214 : W := 0xffc2117febdefffc0007fe1cff
def v215 : W := 0xffc2117ff77afffc0007fe631e
def v216 : W := 0xffc2378000010ffc07f8000000
def v217 : W := 0xffc237ffe1099ffc0627fe0000
def v218 : W := 0xffc237ffe1099ffc07fffe0000
def v219 : W := 0xffc6938000010ffcf838000000
def v220 : W := 0xffc693ffe1099ffcc027fe0000
def v221 : W := 0xffc693ffe1099ffcf83ffe0000
def v222 : W := 0xffc6b7ffe1099ffc0007fe0000
def v223 : W := 0xffd7bf8000010ffc39d8000000
def v224 : W := 0xffd7bfffe1099ffc39dffe0000
def v225 : W := 0xffd7bfffebdffffc39dffe1cff
def v226 : W := 0xffea517fe1089fffc627fe0000
def v227 : W := 0xffea517ff5289ffcc627fe6300
def v228 : W := 0xffea517ff5289fff0607ff8300
def v229 : W := 0xffea517ff5289fffc007ffe000
def v230 : W := 0xffea757ff53abffc0607fe0300
def v231 : W := 0xffeed17ff768dffcc007fe6000
def v232 : W := 0xffeef78000010ffcc620000000
def v233 : W := 0xffeef7ade1099368c620000000
def v234 : W := 0xffeef7ffe1099ffcc627fe0000
def v235 : W := 0xffeef7ffe1099fffc627fe0000
def v236 : W := 0xffeef7fff5299ffcc627fe6300
def v237 : W := 0xffeef7fff53bbffcc627fe0300
def v238 : W := 0xffeef7fff769dffcc627fe6000
def v239 : W := 0xffeef7fff77bf368c621b4631e
def v240 : W := 0xffeef7fff77bfffcc627fe631e
def v241 : W := 0xfffb597ffdac9fff0007ff8000
def v242 : W := 0xfffb7d7ffdbebc7307c63983e0
def v243 : W := 0xfffb7d7ffdbebfff07c7ff83e0
def v244 : W := 0xffffd97fffecdf83f807c1fc00
def v245 : W := 0xffffd97fffecdffff807fffc00
def v246 : W := 0xffffff8000010368fff8000000
def v247 : W := 0xffffff8000010c733fd8000000
def v248 : W := 0xffffff8000010f83f9d8000000
def v249 : W := 0xffffff8000010ffffff8000000
def v250 : W := 0xffffff801cb72ffffff80183e0
def v251 : W := 0xffffff801ee54ffffff801fc00
def v252 : W := 0xffffff81801b2ffffff83803e0
def v253 : W := 0xffffff81e0099ffffff83e0000
def v254 : W := 0xffffff8c03414ffffff9c07c00
def v255 : W := 0xffffff8c61019ffffff9c60000
def v256 : W := 0xffffffa0888d0ffffffe0980e0
def v257 : W := 0xffffffa1889f2ffffff80000e0
def v258 : W := 0xffffffa409850ffffffe419c00
def v259 : W := 0xffffffa4a1091ffffffe4a0000
def v260 : W := 0xffffffa4a98d1ffffff8001ce1
def v261 : W := 0xffffffac0bc54ffffff8001c00
def v262 : W := 0xffffffade1099ffffff8000000
def v263 : W := 0xffffffadebdffffffff8001cff
def v264 : W := 0xffffffd200010ffffffffe0000
def v265 : W := 0xffffffd214210ffffff9b46300
def v266 : W := 0xffffffd214210ffffffe398300
def v267 : W := 0xffffffd214210fffffffc1e000
def v268 : W := 0xffffffd314332ffffff8300300
def v269 : W := 0xffffffda16614ffffff9806000
def v270 : W := 0xffffffdb40018ffffff9b40000
def v271 : W := 0xffffffdb5673effffff9b4631e
def v272 : W := 0xfffffff21ca50ffffffe018000
def v273 : W := 0xfffffff380090ffffffe380000
def v274 : W := 0xfffffff39cbf2c733fde3983e0
def v275 : W := 0xfffffff39cbf2ffffffe3983e0
def v276 : W := 0xfffffffe01010fffffffc00000
def v277 : W := 0xfffffffe1fe54f83f9dfc1fc00
def v278 : W := 0xfffffffe1fe54fffffffc1fc00
def v279 : W := 0xffffffff9fff6ffffffff9ffe0
def v280 : W := 0xffffffffe1099ffffffffe0000
def v281 : W := 0xfffffffffdbfbfffffffff83e0
def v282 : W := 0xffffffffffeddffffffffffc00
def v283 : W := 0xfffffffffffff368fff9b47fff
def v284 : W := 0xfffffffffffffc733fde399fff
def v285 : W := 0xffffffffffffff83f9dfc1fcff

def ins : List W := [v114, v149, v167, v190, v213, v249]
theorem sampled : ∀ j : Fin 104, Nat.testBit 0xeaaae888eaaae880 (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
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
def level3 : BinaryTree (List W) := (.node [v114, v145, v157, v213] (.node [v76, v114, v149, v213] .nil .nil) .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level3_ok : everyKey (rowOK 2 level2) level3 = true := by decide +kernel
theorem closed3 : Closed 3 level3 := closed_next 2 (by decide) level3 level2 closed2 level3_ok
def level4l : BinaryTree (List W) := (.node [v71, v114, v149, v190, v249] (.node [v40, v114, v149, v167, v213] (.node [v23, v114, v149, v167, v200] (.node [v23, v103, v149, v167, v190] (.node [v21, v114, v149, v167, v190] .nil .nil) (.node [v23, v113, v149, v167, v190] .nil .nil)) (.node [v35, v114, v149, v167, v190] (.node [v23, v114, v149, v177, v190] .nil .nil) (.node [v39, v65, v114, v149, v213] .nil .nil))) (.node [v52, v114, v149, v167, v249] (.node [v46, v58, v114, v149, v213] (.node [v41, v114, v149, v167, v213] .nil .nil) (.node [v51, v114, v149, v167, v213] .nil .nil)) (.node [v60, v114, v149, v190, v213] (.node [v59, v114, v149, v190, v213] .nil .nil) (.node [v70, v114, v149, v190, v213] .nil .nil)))) (.node [v105, v114, v149, v167, v190] (.node [v91, v114, v167, v213, v249] (.node [v88, v114, v167, v190, v213] (.node [v73, v114, v149, v213, v249] .nil .nil) (.node [v89, v114, v167, v190, v249] .nil .nil)) (.node [v99, v114, v149, v167, v200] (.node [v94, v114, v190, v213, v249] .nil .nil) (.node [v99, v114, v149, v177, v190] .nil .nil))) (.node [v114, v149, v158, v213, v278] (.node [v114, v146, v167, v190, v240] (.node [v114, v145, v167, v190, v213] .nil .nil) (.node [v114, v149, v157, v213, v279] .nil .nil)) (.node [v114, v149, v167, v190, v217] (.node [v114, v149, v159, v213, v275] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4l_ok : everyKey (rowOK 3 level3) level4l = true := by decide +kernel
def level4r : BinaryTree (List W) := (.node [v114, v149, v173, v190, v213] (.node [v114, v149, v167, v193, v213] (.node [v114, v149, v167, v190, v235] (.node [v114, v149, v167, v190, v233] (.node [v114, v149, v167, v190, v222] .nil .nil) (.node [v114, v149, v167, v190, v234] .nil .nil)) (.node [v114, v149, v167, v190, v237] (.node [v114, v149, v167, v190, v236] .nil .nil) (.node [v114, v149, v167, v190, v238] .nil .nil))) (.node [v114, v149, v167, v201, v213] (.node [v114, v149, v167, v199, v213] (.node [v114, v149, v167, v196, v213] .nil .nil) (.node [v114, v149, v167, v200, v213] .nil .nil)) (.node [v114, v149, v170, v190, v213] (.node [v114, v149, v167, v204, v213] .nil .nil) .nil))) (.node [v114, v167, v239, v244, v249] (.node [v114, v149, v183, v190, v213] (.node [v114, v149, v177, v190, v213] (.node [v114, v149, v176, v190, v213] .nil .nil) (.node [v114, v149, v178, v190, v213] .nil .nil)) (.node [v114, v167, v190, v239, v262] (.node [v114, v149, v242, v244, v249] .nil .nil) (.node [v114, v167, v190, v239, v280] .nil .nil))) (.node [v133, v149, v167, v213, v249] (.node [v117, v149, v167, v190, v249] (.node [v114, v190, v239, v242, v249] .nil .nil) (.node [v119, v149, v167, v190, v213] .nil .nil)) (.node [v167, v179, v190, v213, v249] (.node [v149, v154, v190, v213, v249] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4r_ok : everyKey (rowOK 3 level3) level4r = true := by decide +kernel
def level4 : BinaryTree (List W) := .node [v114, v149, v167, v190, v220] level4l level4r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4_ok : everyKey (rowOK 3 level3) level4 = true := by
  change (_ && everyKey (rowOK 3 level3) level4l && everyKey (rowOK 3 level3) level4r) = true
  rw [level4l_ok, level4r_ok]
  decide +kernel
theorem closed4 : Closed 4 level4 := closed_next 3 (by decide) level4 level3 closed3 level4_ok
def level5lll : BinaryTree (List W) := (.node [v8, v114, v149, v167, v190, v213] (.node [v7, v23, v114, v149, v167, v190] (.node [v3, v114, v149, v167, v190, v213] (.node [v1, v114, v149, v167, v190, v213] (.node [v0, v114, v149, v167, v190, v213] (.node [v0, v23, v114, v149, v167, v190] .nil .nil) .nil) (.node [v2, v114, v149, v167, v190, v213] .nil .nil)) (.node [v5, v114, v149, v167, v190, v213] (.node [v4, v114, v149, v167, v190, v213] .nil .nil) (.node [v6, v114, v149, v167, v190, v213] .nil .nil))) (.node [v8, v23, v114, v149, v167, v190] (.node [v7, v114, v149, v167, v190, v213] (.node [v7, v106, v149, v167, v190, v213] (.node [v7, v99, v114, v149, v167, v190] .nil .nil) .nil) (.node [v7, v118, v149, v167, v190, v213] .nil .nil)) (.node [v8, v99, v114, v149, v167, v190] (.node [v8, v83, v114, v167, v190, v213] .nil .nil) (.node [v8, v114, v140, v167, v190, v213] .nil .nil)))) (.node [v17, v114, v149, v167, v190, v213] (.node [v13, v28, v114, v149, v167, v190] (.node [v11, v45, v114, v149, v167, v213] (.node [v10, v114, v149, v167, v190, v213] (.node [v9, v64, v114, v149, v190, v213] .nil .nil) .nil) (.node [v12, v114, v149, v167, v190, v213] .nil .nil)) (.node [v15, v114, v149, v167, v190, v213] (.node [v14, v114, v149, v167, v190, v213] .nil .nil) (.node [v16, v114, v149, v167, v190, v213] .nil .nil))) (.node [v22, v23, v114, v149, v167, v190] (.node [v19, v114, v149, v167, v190, v213] (.node [v18, v114, v149, v167, v190, v213] .nil .nil) (.node [v20, v114, v149, v167, v190, v213] .nil .nil)) (.node [v23, v28, v114, v149, v167, v190] (.node [v22, v114, v149, v167, v190, v213] .nil .nil) (.node [v23, v45, v114, v149, v167, v190] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lll_ok : everyKey (rowOK 4 level4) level5lll = true := by decide +kernel
def level5llr : BinaryTree (List W) := (.node [v31, v114, v149, v167, v190, v213] (.node [v24, v114, v149, v167, v190, v213] (.node [v23, v114, v149, v167, v190, v275] (.node [v23, v114, v140, v149, v167, v190] (.node [v23, v106, v114, v149, v167, v190] (.node [v23, v99, v149, v167, v190, v249] .nil .nil) .nil) (.node [v23, v114, v149, v167, v190, v249] .nil .nil)) (.node [v23, v114, v149, v167, v190, v280] (.node [v23, v114, v149, v167, v190, v278] .nil .nil) (.node [v23, v116, v149, v167, v190, v249] .nil .nil))) (.node [v28, v114, v149, v167, v190, v213] (.node [v27, v43, v114, v149, v167, v249] (.node [v26, v62, v114, v149, v190, v249] (.node [v25, v81, v114, v167, v190, v249] .nil .nil) .nil) (.node [v28, v99, v114, v149, v167, v190] .nil .nil)) (.node [v29, v114, v149, v167, v190, v249] (.node [v28, v114, v149, v167, v190, v280] .nil .nil) (.node [v30, v114, v149, v167, v190, v213] .nil .nil)))) (.node [v42, v114, v149, v167, v213, v249] (.node [v37, v114, v149, v167, v190, v213] (.node [v34, v114, v149, v167, v190, v249] (.node [v33, v114, v149, v167, v190, v249] (.node [v32, v114, v149, v167, v190, v249] .nil .nil) .nil) (.node [v36, v114, v149, v167, v190, v213] .nil .nil)) (.node [v39, v58, v114, v149, v213, v249] (.node [v38, v80, v114, v167, v213, v249] .nil .nil) (.node [v39, v114, v149, v167, v213, v278] .nil .nil))) (.node [v45, v114, v149, v167, v190, v213] (.node [v45, v99, v114, v149, v167, v190] (.node [v44, v114, v149, v167, v190, v213] .nil .nil) (.node [v45, v114, v149, v158, v190, v213] .nil .nil)) (.node [v45, v114, v149, v177, v190, v213] (.node [v45, v114, v149, v167, v213, v278] .nil .nil) (.node [v46, v114, v149, v167, v190, v213] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llr_ok : everyKey (rowOK 4 level4) level5llr = true := by decide +kernel
def level5ll : BinaryTree (List W) := .node [v23, v64, v114, v149, v167, v190] level5lll level5llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5ll_ok : everyKey (rowOK 4 level4) level5ll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lll && everyKey (rowOK 4 level4) level5llr) = true
  rw [level5lll_ok, level5llr_ok]
  decide +kernel
def level5lrl : BinaryTree (List W) := (.node [v66, v114, v149, v167, v190, v213] (.node [v58, v114, v149, v190, v213, v275] (.node [v54, v114, v149, v167, v190, v213] (.node [v50, v114, v149, v167, v213, v249] (.node [v49, v114, v149, v167, v213, v249] (.node [v48, v122, v149, v167, v213, v249] .nil .nil) .nil) (.node [v53, v114, v149, v167, v190, v213] .nil .nil)) (.node [v56, v114, v149, v167, v190, v213] (.node [v55, v77, v114, v190, v213, v249] .nil .nil) (.node [v57, v167, v190, v213, v249, v283] .nil .nil))) (.node [v64, v114, v149, v167, v190, v213] (.node [v64, v99, v114, v149, v167, v190] (.node [v63, v114, v149, v167, v190, v213] (.node [v61, v114, v149, v190, v213, v249] .nil .nil) .nil) (.node [v64, v114, v149, v159, v167, v213] .nil .nil)) (.node [v64, v114, v149, v190, v213, v275] (.node [v64, v114, v149, v167, v200, v213] .nil .nil) (.node [v65, v114, v149, v167, v190, v213] .nil .nil)))) (.node [v81, v114, v149, v167, v190, v280] (.node [v74, v114, v149, v167, v190, v249] (.node [v69, v114, v149, v190, v213, v249] (.node [v68, v114, v149, v190, v213, v249] (.node [v67, v121, v149, v190, v213, v249] .nil .nil) .nil) (.node [v72, v114, v149, v167, v190, v213] .nil .nil)) (.node [v78, v149, v190, v213, v249, v284] (.node [v75, v114, v149, v167, v190, v213] .nil .nil) (.node [v79, v114, v149, v167, v190, v213] .nil .nil))) (.node [v85, v114, v167, v190, v213, v249] (.node [v82, v114, v149, v167, v190, v249] (.node [v82, v114, v140, v149, v167, v190] .nil .nil) (.node [v84, v120, v167, v190, v213, v249] .nil .nil)) (.node [v87, v114, v149, v167, v190, v213] (.node [v86, v114, v167, v190, v213, v249] .nil .nil) (.node [v90, v114, v149, v167, v190, v213] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrl_ok : everyKey (rowOK 4 level4) level5lrl = true := by decide +kernel
def level5lrr : BinaryTree (List W) := (.node [v99, v114, v149, v167, v244, v249] (.node [v99, v114, v126, v149, v167, v249] (.node [v98, v114, v149, v167, v190, v213] (.node [v96, v114, v149, v167, v190, v213] (.node [v95, v149, v167, v213, v249, v285] (.node [v93, v114, v149, v167, v190, v213] .nil .nil) .nil) (.node [v97, v114, v149, v167, v190, v249] .nil .nil)) (.node [v99, v114, v124, v167, v190, v249] (.node [v99, v106, v114, v149, v167, v190] .nil .nil) (.node [v99, v114, v125, v149, v190, v249] .nil .nil))) (.node [v99, v114, v149, v167, v190, v262] (.node [v99, v114, v140, v149, v167, v190] (.node [v99, v114, v127, v149, v167, v190] .nil .nil) (.node [v99, v114, v149, v167, v190, v249] .nil .nil)) (.node [v99, v114, v149, v167, v190, v278] (.node [v99, v114, v149, v167, v190, v275] .nil .nil) (.node [v99, v114, v149, v167, v190, v280] .nil .nil)))) (.node [v106, v114, v149, v167, v190, v213] (.node [v101, v114, v149, v167, v190, v249] (.node [v99, v149, v167, v190, v225, v249] (.node [v99, v114, v167, v190, v239, v249] (.node [v99, v114, v149, v190, v242, v249] .nil .nil) .nil) (.node [v100, v114, v149, v167, v190, v249] .nil .nil)) (.node [v103, v114, v149, v167, v190, v213] (.node [v102, v114, v149, v167, v190, v249] .nil .nil) (.node [v104, v114, v149, v167, v190, v249] .nil .nil))) (.node [v109, v114, v149, v167, v190, v213] (.node [v107, v114, v149, v167, v190, v213] (.node [v106, v149, v167, v190, v213, v263] .nil .nil) (.node [v108, v114, v149, v167, v190, v213] .nil .nil)) (.node [v111, v114, v149, v167, v190, v213] (.node [v110, v114, v149, v167, v190, v213] .nil .nil) (.node [v112, v114, v149, v167, v190, v213] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrr_ok : everyKey (rowOK 4 level4) level5lrr = true := by decide +kernel
def level5lr : BinaryTree (List W) := .node [v92, v114, v149, v167, v190, v249] level5lrl level5lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lr_ok : everyKey (rowOK 4 level4) level5lr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrl && everyKey (rowOK 4 level4) level5lrr) = true
  rw [level5lrl_ok, level5lrr_ok]
  decide +kernel
def level5l : BinaryTree (List W) := .node [v47, v114, v149, v167, v190, v213] level5ll level5lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5l_ok : everyKey (rowOK 4 level4) level5l = true := by
  change (_ && everyKey (rowOK 4 level4) level5ll && everyKey (rowOK 4 level4) level5lr) = true
  rw [level5ll_ok, level5lr_ok]
  decide +kernel
def level5rll : BinaryTree (List W) := (.node [v114, v140, v149, v167, v190, v213] (.node [v114, v130, v167, v190, v213, v249] (.node [v114, v126, v149, v167, v213, v249] (.node [v114, v124, v167, v190, v213, v249] (.node [v114, v123, v149, v167, v190, v213] (.node [v114, v115, v149, v167, v190, v213] .nil .nil) .nil) (.node [v114, v125, v149, v190, v213, v249] .nil .nil)) (.node [v114, v128, v185, v190, v213, v249] (.node [v114, v127, v149, v167, v190, v213] .nil .nil) (.node [v114, v129, v149, v167, v190, v213] .nil .nil))) (.node [v114, v136, v167, v190, v213, v249] (.node [v114, v134, v167, v206, v213, v249] (.node [v114, v132, v149, v167, v190, v213] (.node [v114, v131, v149, v190, v213, v249] .nil .nil) .nil) (.node [v114, v135, v149, v167, v190, v213] .nil .nil)) (.node [v114, v138, v167, v190, v240, v249] (.node [v114, v137, v149, v167, v213, v249] .nil .nil) (.node [v114, v139, v149, v167, v190, v213] .nil .nil)))) (.node [v114, v148, v167, v190, v213, v249] (.node [v114, v143, v149, v167, v190, v213] (.node [v114, v141, v149, v167, v190, v213] (.node [v114, v140, v167, v190, v213, v271] (.node [v114, v140, v149, v167, v190, v234] .nil .nil) .nil) (.node [v114, v142, v149, v167, v190, v213] .nil .nil)) (.node [v114, v146, v149, v167, v190, v213] (.node [v114, v144, v149, v167, v190, v213] .nil .nil) (.node [v114, v147, v167, v190, v213, v249] .nil .nil))) (.node [v114, v149, v155, v167, v190, v213] (.node [v114, v149, v151, v167, v190, v213] (.node [v114, v149, v150, v167, v190, v213] .nil .nil) (.node [v114, v149, v153, v167, v190, v213] .nil .nil)) (.node [v114, v149, v157, v190, v213, v275] (.node [v114, v149, v157, v167, v213, v278] .nil .nil) (.node [v114, v149, v157, v207, v213, v249] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rll_ok : everyKey (rowOK 4 level4) level5rll = true := by decide +kernel
def level5rlr : BinaryTree (List W) := (.node [v114, v149, v167, v184, v190, v213] (.node [v114, v149, v167, v168, v190, v213] (.node [v114, v149, v163, v190, v243, v249] (.node [v114, v149, v161, v167, v213, v249] (.node [v114, v149, v160, v190, v213, v249] (.node [v114, v149, v159, v167, v213, v249] .nil .nil) .nil) (.node [v114, v149, v162, v190, v213, v249] .nil .nil)) (.node [v114, v149, v165, v190, v213, v249] (.node [v114, v149, v164, v190, v213, v275] .nil .nil) (.node [v114, v149, v166, v190, v213, v249] .nil .nil))) (.node [v114, v149, v167, v175, v190, v213] (.node [v114, v149, v167, v171, v190, v213] (.node [v114, v149, v167, v169, v190, v213] .nil .nil) (.node [v114, v149, v167, v172, v190, v213] .nil .nil)) (.node [v114, v149, v167, v181, v213, v249] (.node [v114, v149, v167, v177, v190, v213] .nil .nil) (.node [v114, v149, v167, v182, v190, v213] .nil .nil)))) (.node [v114, v149, v167, v190, v198, v213] (.node [v114, v149, v167, v190, v191, v213] (.node [v114, v149, v167, v188, v213, v249] (.node [v114, v149, v167, v187, v213, v278] (.node [v114, v149, v167, v186, v245, v249] .nil .nil) .nil) (.node [v114, v149, v167, v189, v213, v249] .nil .nil)) (.node [v114, v149, v167, v190, v194, v213] (.node [v114, v149, v167, v190, v192, v213] .nil .nil) (.node [v114, v149, v167, v190, v195, v213] .nil .nil))) (.node [v114, v149, v167, v190, v208, v280] (.node [v114, v149, v167, v190, v203, v213] (.node [v114, v149, v167, v190, v200, v213] .nil .nil) (.node [v114, v149, v167, v190, v205, v213] .nil .nil)) (.node [v114, v149, v167, v190, v210, v249] (.node [v114, v149, v167, v190, v209, v249] .nil .nil) (.node [v114, v149, v167, v190, v211, v249] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlr_ok : everyKey (rowOK 4 level4) level5rlr = true := by decide +kernel
def level5rl : BinaryTree (List W) := .node [v114, v149, v158, v190, v213, v249] level5rll level5rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rl_ok : everyKey (rowOK 4 level4) level5rl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rll && everyKey (rowOK 4 level4) level5rlr) = true
  rw [level5rll_ok, level5rlr_ok]
  decide +kernel
def level5rrl : BinaryTree (List W) := (.node [v114, v149, v167, v190, v213, v253] (.node [v114, v149, v167, v190, v213, v232] (.node [v114, v149, v167, v190, v213, v219] (.node [v114, v149, v167, v190, v213, v216] (.node [v114, v149, v167, v190, v213, v215] (.node [v114, v149, v167, v190, v213, v214] .nil .nil) .nil) (.node [v114, v149, v167, v190, v213, v218] .nil .nil)) (.node [v114, v149, v167, v190, v213, v223] (.node [v114, v149, v167, v190, v213, v221] .nil .nil) (.node [v114, v149, v167, v190, v213, v224] .nil .nil))) (.node [v114, v149, v167, v190, v213, v249] (.node [v114, v149, v167, v190, v213, v247] (.node [v114, v149, v167, v190, v213, v246] (.node [v114, v149, v167, v190, v213, v234] .nil .nil) .nil) (.node [v114, v149, v167, v190, v213, v248] .nil .nil)) (.node [v114, v149, v167, v190, v213, v251] (.node [v114, v149, v167, v190, v213, v250] .nil .nil) (.node [v114, v149, v167, v190, v213, v252] .nil .nil)))) (.node [v114, v149, v167, v190, v213, v262] (.node [v114, v149, v167, v190, v213, v258] (.node [v114, v149, v167, v190, v213, v256] (.node [v114, v149, v167, v190, v213, v255] (.node [v114, v149, v167, v190, v213, v254] .nil .nil) .nil) (.node [v114, v149, v167, v190, v213, v257] .nil .nil)) (.node [v114, v149, v167, v190, v213, v260] (.node [v114, v149, v167, v190, v213, v259] .nil .nil) (.node [v114, v149, v167, v190, v213, v261] .nil .nil))) (.node [v114, v149, v167, v190, v213, v267] (.node [v114, v149, v167, v190, v213, v265] (.node [v114, v149, v167, v190, v213, v264] .nil .nil) (.node [v114, v149, v167, v190, v213, v266] .nil .nil)) (.node [v114, v149, v167, v190, v213, v269] (.node [v114, v149, v167, v190, v213, v268] .nil .nil) (.node [v114, v149, v167, v190, v213, v270] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrl_ok : everyKey (rowOK 4 level4) level5rrl = true := by decide +kernel
def level5rrr : BinaryTree (List W) := (.node [v114, v149, v167, v190, v234] (.node [v114, v149, v167, v190, v213, v281] (.node [v114, v149, v167, v190, v213, v277] (.node [v114, v149, v167, v190, v213, v275] (.node [v114, v149, v167, v190, v213, v274] (.node [v114, v149, v167, v190, v213, v273] .nil .nil) .nil) (.node [v114, v149, v167, v190, v213, v276] .nil .nil)) (.node [v114, v149, v167, v190, v213, v279] (.node [v114, v149, v167, v190, v213, v278] .nil .nil) (.node [v114, v149, v167, v190, v213, v280] .nil .nil))) (.node [v114, v149, v167, v190, v228, v249] (.node [v114, v149, v167, v190, v226, v249] (.node [v114, v149, v167, v190, v213, v282] .nil .nil) (.node [v114, v149, v167, v190, v227, v249] .nil .nil)) (.node [v114, v149, v167, v190, v230, v249] (.node [v114, v149, v167, v190, v229, v249] .nil .nil) (.node [v114, v149, v167, v190, v231, v249] .nil .nil)))) (.node [v114, v149, v174, v190, v213, v249] (.node [v114, v149, v167, v200, v213] (.node [v114, v149, v167, v190, v241, v249] (.node [v114, v149, v167, v190, v240, v280] (.node [v114, v149, v167, v190, v234, v249] .nil .nil) .nil) (.node [v114, v149, v167, v197, v213, v249] .nil .nil)) (.node [v114, v149, v167, v202, v213, v249] (.node [v114, v149, v167, v200, v213, v249] .nil .nil) (.node [v114, v149, v167, v213, v244, v249] .nil .nil))) (.node [v114, v149, v190, v213, v242, v249] (.node [v114, v149, v177, v190, v213, v249] (.node [v114, v149, v177, v190, v213] .nil .nil) (.node [v114, v149, v180, v190, v213, v249] .nil .nil)) (.node [v114, v156, v167, v190, v213, v249] (.node [v114, v152, v167, v190, v213, v249] .nil .nil) (.node [v114, v167, v190, v213, v239, v249] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrr_ok : everyKey (rowOK 4 level4) level5rrr = true := by decide +kernel
def level5rr : BinaryTree (List W) := .node [v114, v149, v167, v190, v213, v272] level5rrl level5rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rr_ok : everyKey (rowOK 4 level4) level5rr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrl && everyKey (rowOK 4 level4) level5rrr) = true
  rw [level5rrl_ok, level5rrr_ok]
  decide +kernel
def level5r : BinaryTree (List W) := .node [v114, v149, v167, v190, v212, v249] level5rl level5rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5r_ok : everyKey (rowOK 4 level4) level5r = true := by
  change (_ && everyKey (rowOK 4 level4) level5rl && everyKey (rowOK 4 level4) level5rr) = true
  rw [level5rl_ok, level5rr_ok]
  decide +kernel
def level5 : BinaryTree (List W) := .node [v113, v114, v149, v167, v190, v213] level5l level5r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5_ok : everyKey (rowOK 4 level4) level5 = true := by
  change (_ && everyKey (rowOK 4 level4) level5l && everyKey (rowOK 4 level4) level5r) = true
  rw [level5l_ok, level5r_ok]
  decide +kernel
theorem closed5 : Closed 5 level5 := closed_next 4 (by decide) level5 level4 closed4 level5_ok
def level6l : BinaryTree (List W) := (.node [v45, v114, v149, v167, v190, v213, v249] (.node [v25, v114, v149, v167, v190, v213, v249] (.node [v9, v114, v149, v167, v190, v213, v249] (.node [v8, v114, v149, v167, v190, v213] (.node [v7, v114, v149, v167, v190, v213, v249] (.node [v7, v114, v149, v167, v190, v213] .nil .nil) .nil) (.node [v8, v114, v149, v167, v190, v213, v249] .nil .nil)) (.node [v23, v114, v149, v167, v190, v213, v249] (.node [v13, v114, v149, v167, v190, v213, v249] (.node [v11, v114, v149, v167, v190, v213, v249] .nil .nil) .nil) (.node [v23, v114, v149, v167, v190, v249] .nil .nil))) (.node [v38, v114, v149, v167, v190, v213, v249] (.node [v28, v114, v149, v167, v190, v213] (.node [v27, v114, v149, v167, v190, v213, v249] (.node [v26, v114, v149, v167, v190, v213, v249] .nil .nil) .nil) (.node [v28, v114, v149, v167, v190, v213, v249] .nil .nil)) (.node [v43, v114, v149, v167, v190, v213, v249] (.node [v39, v114, v149, v167, v190, v213, v249] .nil .nil) (.node [v45, v114, v149, v167, v190, v213] .nil .nil)))) (.node [v77, v114, v149, v167, v190, v213, v249] (.node [v62, v114, v149, v167, v190, v213, v249] (.node [v57, v114, v149, v167, v190, v213, v249] (.node [v55, v114, v149, v167, v190, v213, v249] (.node [v48, v114, v149, v167, v190, v213, v249] .nil .nil) .nil) (.node [v58, v114, v149, v167, v190, v213, v249] .nil .nil)) (.node [v64, v114, v149, v167, v190, v213, v249] (.node [v64, v114, v149, v167, v190, v213] .nil .nil) (.node [v67, v114, v149, v167, v190, v213, v249] .nil .nil))) (.node [v84, v114, v149, v167, v190, v213, v249] (.node [v81, v114, v149, v167, v190, v213, v249] (.node [v80, v114, v149, v167, v190, v213, v249] (.node [v78, v114, v149, v167, v190, v213, v249] .nil .nil) .nil) (.node [v83, v114, v149, v167, v190, v213, v249] .nil .nil)) (.node [v99, v114, v149, v167, v190, v213, v249] (.node [v95, v114, v149, v167, v190, v213, v249] .nil .nil) (.node [v99, v114, v149, v167, v190, v249] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6l_ok : everyKey (rowOK 5 level5) level6l = true := by decide +kernel
def level6r : BinaryTree (List W) := (.node [v114, v149, v167, v190, v206, v213, v249] (.node [v114, v138, v149, v167, v190, v213, v249] (.node [v114, v121, v149, v167, v190, v213, v249] (.node [v114, v118, v149, v167, v190, v213, v249] (.node [v114, v116, v149, v167, v190, v213, v249] (.node [v106, v114, v149, v167, v190, v213, v249] .nil .nil) .nil) (.node [v114, v120, v149, v167, v190, v213, v249] .nil .nil)) (.node [v114, v128, v149, v167, v190, v213, v249] (.node [v114, v122, v149, v167, v190, v213, v249] .nil .nil) (.node [v114, v134, v149, v167, v190, v213, v249] .nil .nil))) (.node [v114, v149, v164, v167, v190, v213, v249] (.node [v114, v149, v157, v167, v190, v213, v249] (.node [v114, v140, v149, v167, v190, v213, v249] (.node [v114, v140, v149, v167, v190, v213] .nil .nil) .nil) (.node [v114, v149, v163, v167, v190, v213, v249] .nil .nil)) (.node [v114, v149, v167, v186, v190, v213, v249] (.node [v114, v149, v167, v185, v190, v213, v249] .nil .nil) (.node [v114, v149, v167, v187, v190, v213, v249] .nil .nil)))) (.node [v114, v149, v167, v190, v213, v249, v275] (.node [v114, v149, v167, v190, v213, v243, v249] (.node [v114, v149, v167, v190, v213, v225, v249] (.node [v114, v149, v167, v190, v208, v213, v249] (.node [v114, v149, v167, v190, v207, v213, v249] .nil .nil) .nil) (.node [v114, v149, v167, v190, v213, v240, v249] .nil .nil)) (.node [v114, v149, v167, v190, v213, v249, v263] (.node [v114, v149, v167, v190, v213, v245, v249] .nil .nil) (.node [v114, v149, v167, v190, v213, v249, v271] .nil .nil))) (.node [v114, v149, v167, v190, v213, v249, v285] (.node [v114, v149, v167, v190, v213, v249, v283] (.node [v114, v149, v167, v190, v213, v249, v280] (.node [v114, v149, v167, v190, v213, v249, v278] .nil .nil) .nil) (.node [v114, v149, v167, v190, v213, v249, v284] .nil .nil)) (.node [v114, v149, v167, v190, v213, v278] (.node [v114, v149, v167, v190, v213, v275] .nil .nil) (.node [v114, v149, v167, v190, v213, v280] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6r_ok : everyKey (rowOK 5 level5) level6r = true := by decide +kernel
def level6 : BinaryTree (List W) := .node [v106, v114, v149, v167, v190, v213] level6l level6r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6_ok : everyKey (rowOK 5 level5) level6 = true := by
  change (_ && everyKey (rowOK 5 level5) level6l && everyKey (rowOK 5 level5) level6r) = true
  rw [level6l_ok, level6r_ok]
  decide +kernel
theorem closed6 : Closed 6 level6 := closed_next 5 (by decide) level6 level5 closed5 level6_ok
def level7 : BinaryTree (List W) := (.node [v114, v149, v167, v190, v213, v249] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7_ok : everyKey (rowOK 6 level6) level7 = true := by decide +kernel
theorem closed7 : Closed 7 level7 := closed_next 6 (by decide) level7 level6 closed6 level7_ok

theorem lower : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z 7 ins.toFinset :=
  @no_build 7 level7 ins (by decide +kernel) (by decide) closed7 (by decide +kernel)
def witness : List Gate := [⟨.or,[2,3]⟩, ⟨.and,[2,3]⟩, ⟨.or,[0,7]⟩, ⟨.and,[1,8]⟩, ⟨.or,[4,7]⟩, ⟨.and,[0,10]⟩, ⟨.or,[5,6]⟩, ⟨.and,[9,12]⟩, ⟨.or,[11,13]⟩]
theorem upper : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 9 ∧ ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xeaaae888eaaae880 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact ⟨witness,14,by simp [witness],rfl,by decide +kernel⟩
end PEqualNP.Outside.L_meta_15353_aux

open PEqualNP.Outside.L_meta_15353_aux in
theorem PEqualNP.Outside.L_meta_15353 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3937069192 * 2 ^ 32 + 3937069184) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3937069192 * 2 ^ 32 + 3937069184) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  have code : 3937069192 * 2 ^ 32 + 3937069184 = 0xeaaae888eaaae880 := by decide
  simp only [code] at h ⊢
  obtain ⟨C,legal,size,computes⟩ := h
  obtain ⟨gs,o,mono,bound,ev⟩ := replace 0xeaaae888eaaae880 9 ins (by decide +kernel) sampled rfl lower upper C.gates C.output legal computes
  exact ⟨⟨gs,o⟩,mono,bound.trans size,ev⟩
