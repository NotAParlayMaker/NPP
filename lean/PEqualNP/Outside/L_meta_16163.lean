import PEqualNP.Defs

-- The live-wire search and circuit compiler are adapted from tacyon52 in L-meta-8639, pull request 12794 under Apache-2.0.
namespace PEqualNP.Outside.L_meta_16163_aux

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

-- The upper and lower halves represent opposite target labels on 48 pairs of assignments.
abbrev W := BitVec 96
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 48 := ((x >>> 48) ^^^ x).setWidth 48
def cuts (ws : List W) : BitVec 48 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 48) ++ (0 : BitVec 48)
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

def differs (i : Fin 48) (w : W) : Prop :=
  w.getLsbD (48+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 48) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 48+i.val < 96 := by omega
  have hi' : i.val < 96 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 48) :
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
  change (cuts ws)[j] = (BitVec.allOnes 48)[j]
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
  · change reachable av (BitVec.allOnes 96 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 96)
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

private def bit (k : Fin 96) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 96) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 96) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#96)[k.val] = false; simp
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
    (row : ∀ j : Fin 96, Nat.testBit T (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
    (width : ins.length = 6) (rejection : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z n ins.toFinset)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 6, if x i then 2^(i : ℕ) else 0)) : n < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ ins, holds ins.toFinset u := fun u hu =>
    .inr (.inr ⟨u,List.mem_toFinset.mpr hu,.inl rfl⟩)
  have evaluate (k : Fin 96) :
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
    (row : ∀ j : Fin 96, Nat.testBit T (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
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

def wa : W := 0x0
def wb : W := 0x318c11820810
def wc : W := 0x380e01c00c00
def wd : W := 0x398e11c20c10
def we : W := 0x39c001c30000
def wf : W := 0x39cc11c30810
def wg : W := 0x39ce01c30c00
def wh : W := 0x39ce18000000
def wi : W := 0x39ce19820810
def wj : W := 0x39ce19c00c00
def wk : W := 0x39ce19c30000
def wl : W := 0xc63026041000
def wm : W := 0xc83206401400
def wn : W := 0xce4006450000
def wo : W := 0xce7228000000
def wp : W := 0x2a3100000000ea10
def wq : W := 0x326000000000f3e0
def wr : W := 0x3c4200000000fc00
def ws : W := 0x3e730000000001ef
def wt : W := 0xa02310000003a0210
def wu : W := 0xc02a00000003c03e0
def wv : W := 0xf00840000003f0000
def ww : W := 0xf02b50000000001ef
def wx : W := 0x820811000001820810
def wy : W := 0x820811318c11820810
def wz : W := 0x8a2a31000000000000
def wA : W := 0xc00c02000001c00c00
def wB : W := 0xc30004000001c30000
def wC : W := 0xc30c1700000000000f
def wD : W := 0x20410c00000060411e0
def wE : W := 0x20c32e00000000001e0
def wF : W := 0x2401442000006401400
def wG : W := 0x2450084000006450000
def wH : W := 0x24514c60000000001ef
def wI : W := 0x2c03c42000000000000
def wJ : W := 0x2cf0084000000000000
def wK : W := 0x2cf3ef70000000001ef
def wL : W := 0x5104000000001baea10
def wM : W := 0x51040000000063cf200
def wN : W := 0x5104000000007c0fc00
def wO : W := 0x5104000000007ff0000
def wP : W := 0x518622000000038e200
def wQ : W := 0x590680000000180e800
def wR : W := 0x59a4000000001ba0000
def wS : W := 0x59a6a3100000038e200
def wT : W := 0x59a6a31000001baea10
def wU : W := 0x59a7e73000001baebff
def wV : W := 0x59f6ab5000001baebff
def wW : W := 0x710704000000600f000
def wX : W := 0x71c40800000063c0000
def wY : W := 0x71c72e00000063cf3e0
def wZ : W := 0x71c7ef30000063cf3ef
def w0 : W := 0x71f72f50000063cf3ef
def w1 : W := 0x75554c6000001baebff
def w2 : W := 0x75d76e600000038e3ef
def w3 : W := 0x75d76e60000063cf3ef
def w4 : W := 0x79e7af1000007befbf0
def w5 : W := 0x7d04000000007c00000
def w6 : W := 0x7d07c42000007c0fc00
def w7 : W := 0x7da7e73000007fafe10
def w8 : W := 0x7dc7ee2000007fcffe0
def w9 : W := 0x7df4084000007ff0000
def waa : W := 0x7df6ab5000007ffea10
def wab : W := 0x7df72e4000007fff3e0
def wac : W := 0x7df7cc6000007fffc00
def wad : W := 0x7df7ef700000038e3ef
def wae : W := 0x7df7ef7000001baebff
def waf : W := 0x7df7ef70000063cf3ef
def wag : W := 0x7df7ef7000007befbff
def wah : W := 0x7df7ef7000007c0fdef
def wai : W := 0x7df7ef7000007faffff
def waj : W := 0x7df7ef7000007fcffef
def wak : W := 0x7df7ef7000007ff01ef
def wal : W := 0x7df7ef7000007ffebff
def wam : W := 0x7df7ef7000007fff3ef
def wan : W := 0x7df7ef7000007fffdef
def wao : W := 0x7df7ef739ce1e3cf3ef
def wap : W := 0x40082220000000000000
def waq : W := 0x500002310001d0000210
def war : W := 0x600003200001e00003e0
def was : W := 0x780001080001f8000000
def wat : W := 0x780003390000000001ef
def wau : W := 0x410000811000c10000810
def wav : W := 0x410000811318c11820810
def waw : W := 0x450002a31000000000000
def wax : W := 0x600000c02000e00000c00
def way : W := 0x618000008000e18000000
def waz : W := 0x618000c1b00000000000f
def waA : W := 0x10200011400030200011e0
def waB : W := 0x10600033600000000001e0
def waC : W := 0x1200001442003200001400
def waD : W := 0x1228000108003228000000
def waE : W := 0x122800154a0000000001ef
def waF : W := 0x1600003c42000000000000
def waG : W := 0x1678000108000000000000
def waH : W := 0x1678003f7b0000000001ef
def waI : W := 0x167acf3fff0000000001ef
def waJ : W := 0x2880008000000dd000ea10
def waK : W := 0x28800080000031e000f200
def waL : W := 0x2880008000003e0000fc00
def waM : W := 0x2880008000003ff8000000
def waN : W := 0x2887d0fc42003e07c0fc00
def waO : W := 0x28c000a2200001c000e200
def waP : W := 0x2c8000a800000c0000e800
def waQ : W := 0x2c87d0fc42000c07c0fc00
def waR : W := 0x2cd0008000000dd0000000
def waS : W := 0x2cd000aa310001c000e200
def waT : W := 0x2cd000aa31000dd000ea10
def waU : W := 0x2cd000be73000dd000ebff
def waV : W := 0x2cd59aea31000dd1baea10
def waW : W := 0x2cf800ab39000dd000ebff
def waX : W := 0x388000b04000300000f000
def waY : W := 0x3887d0fc42003007c0fc00
def waZ : W := 0x38e00081000031e0000000
def wa0 : W := 0x38e000b3600031e000f3e0
def wa1 : W := 0x38e000bf730031e000f3ef
def wa2 : W := 0x38e71cf3e00031e63cf3e0
def wa3 : W := 0x38f800b3790031e000f3ef
def wa4 : W := 0x3aa800954a000dd000ebff
def wa5 : W := 0x3ae800b76a0001c000e3ef
def wa6 : W := 0x3ae800b76a0031e000f3ef
def wa7 : W := 0x3cf000bb71003df000fbf0
def wa8 : W := 0x3e80008000003e00000000
def wa9 : W := 0x3e8000bc42003e0000fc00
def wba : W := 0x3e8510fc42003e07c0fc00
def wbb : W := 0x3e8590fc42003e0180fc00
def wbc : W := 0x3e8710fc42003e0600fc00
def wbd : W := 0x3e87d0fc42003e07c0fc00
def wbe : W := 0x3ed000be73003fd000fe10
def wbf : W := 0x3ee000bf62003fe000ffe0
def wbg : W := 0x3ef8008108003ff8000000
def wbh : W := 0x3ef800ab39003ff800ea10
def wbi : W := 0x3ef800b368003ff800f3e0
def wbj : W := 0x3ef800bd4a003ff800fc00
def wbk : W := 0x3ef800bf7b0001c000e3ef
def wbl : W := 0x3ef800bf7b000dd000ebff
def wbm : W := 0x3ef800bf7b0031e000f3ef
def wbn : W := 0x3ef800bf7b003df000fbff
def wbo : W := 0x3ef800bf7b003e0000fdef
def wbp : W := 0x3ef800bf7b003fd000ffff
def wbq : W := 0x3ef800bf7b003fe000ffef
def wbr : W := 0x3ef800bf7b003ff80001ef
def wbs : W := 0x3ef800bf7b003ff800ebff
def wbt : W := 0x3ef800bf7b003ff800f3ef
def wbu : W := 0x3ef800bf7b003ff800fdef
def wbv : W := 0x3ef800bf7b39f1e1c3f3ef
def wbw : W := 0x3effdfc18c003fffff0000
def wbx : W := 0x8010020011018010020010
def wby : W := 0x8010020011318c11820810
def wbz : W := 0x80500a0231000000000000
def wbA : W := 0xc00003000401c000030000
def wbB : W := 0xc01800000801c018000000
def wbC : W := 0xc01803001d00000000000f
def wbD : W := 0x200200401800600200401e0
def wbE : W := 0x200600c03a00000000001e0
def wbF : W := 0x24000050084064000050000
def wbG : W := 0x24028000108064028000000
def wbH : W := 0x2402805018c0000000001ef
def wbI : W := 0x2c0000f0084000000000000
def wbJ : W := 0x2c078000108000000000000
def wbK : W := 0x2c0780f03bd0000000001ef
def wbL : W := 0x2c07acf3fff0000000001ef
def wbM : W := 0x2d6780f3fff0000000001ef
def wbN : W := 0x501002000000181d03a0210
def wbO : W := 0x501002000000601e03c0200
def wbP : W := 0x5010020000007c0003f0000
def wbQ : W := 0x5010020000007c1f8000000
def wbR : W := 0x50107ff408407c007ff0000
def wbS : W := 0x501402802200001c0380200
def wbT : W := 0x53ff820810807fff8000000
def wbU : W := 0x581002a00000180003a0000
def wbV : W := 0x58107ff4084018007ff0000
def wbW : W := 0x581502000000181d0000000
def wbX : W := 0x581502a02310001c0380200
def wbY : W := 0x581502a02310181d03a0210
def wbZ : W := 0x581502f02b50181d03a03ff
def wb0 : W := 0x58155ba6a310181d1baea10
def wb1 : W := 0x581782a03390181d03a03ff
def wb2 : W := 0x5add02aaa31018dd03aea10
def wb3 : W := 0x5bff820810801bff8000000
def wb4 : W := 0x701002c00800600003c0000
def wb5 : W := 0x70107ff4084060007ff0000
def wb6 : W := 0x701602001000601e0000000
def wb7 : W := 0x701602c03a00601e03c03e0
def wb8 : W := 0x701602f03b50601e03c03ef
def wb9 : W := 0x701673c73e00601e63cf3e0
def wca : W := 0x701782c03b90601e03c03ef
def wcb : W := 0x739e02cb3e00631e03cf3e0
def wcc : W := 0x73ff8208108063ff8000000
def wcd : W := 0x7412825018c0181d03a03ff
def wce : W := 0x741682d03ac0001c03803ef
def wcf : W := 0x741682d03ac0601e03c03ef
def wcg : W := 0x781702e03b10781f03e03f0
def wch : W := 0x7c10020000007c000000000
def wci : W := 0x7c1002f008407c0003f0000
def wcj : W := 0x7c1053f408407c007ff0000
def wck : W := 0x7c105bf408407c001bf0000
def wcl : W := 0x7c1073f408407c0063f0000
def wcm : W := 0x7c107ff408407c007ff0000
def wcn : W := 0x7c1502f02b507c1d03f0210
def wco : W := 0x7c1602f03a407c1e03f03e0
def wcp : W := 0x7c17820010807c1f8000000
def wcq : W := 0x7c1782a033907c1f83a0210
def wcr : W := 0x7c1782c03a807c1f83c03e0
def wcs : W := 0x7c1782f018c07c1f83f0000
def wct : W := 0x7c1782f03bd0001c03803ef
def wcu : W := 0x7c1782f03bd0181d03a03ff
def wcv : W := 0x7c1782f03bd0601e03c03ef
def wcw : W := 0x7c1782f03bd0781f03e03ff
def wcx : W := 0x7c1782f03bd07c0003f01ef
def wcy : W := 0x7c1782f03bd07c1d03f03ff
def wcz : W := 0x7c1782f03bd07c1e03f03ef
def wcA : W := 0x7c1782f03bd07c1f80001ef
def wcB : W := 0x7c1782f03bd07c1f83a03ff
def wcC : W := 0x7c1782f03bd07c1f83c03ef
def wcD : W := 0x7c1782f03bd07c1f83f01ef
def wcE : W := 0x7c1782f03bd3e0fe1fc0fef
def wcF : W := 0x7c17ff07d4a07c1ffc0fc00
def wcG : W := 0x7e9f820810807fff8000000
def wcH : W := 0x7edf820810807cdf8000000
def wcI : W := 0x7f9f820810807f1f8000000
def wcJ : W := 0x7ff802fbcc607fe003ffc00
def wcK : W := 0x7fff820810807fff8000000
def wcL : W := 0x80200400402080200400400
def wcM : W := 0x84000410004084000410000
def wcN : W := 0x84208000008084208000000
def wcO : W := 0x8420841040e00000000000f
def wcP : W := 0x8420841040e318c1182081f
def wcQ : W := 0x100400800800300c01800800
def wcR : W := 0x100400800800318c11820810
def wcS : W := 0x100400802800000000000000
def wcT : W := 0x108000820000318001820000
def wcU : W := 0x108000820000318c11820810
def wcV : W := 0x1080008a0000000000000000
def wcW : W := 0x108400820800318c01820800
def wcX : W := 0x108410000000318c10000000
def wcY : W := 0x108410000000318c11820810
def wcZ : W := 0x108410800800318c11800800
def wc0 : W := 0x108410820000318c11820000
def wc1 : W := 0x108410820811000000000000
def wc2 : W := 0x108410820811318c11820810
def wc3 : W := 0x108410820811398e11c20c10
def wc4 : W := 0x10841082081139cc11c30810
def wc5 : W := 0x10841082081139ce19820810
def wc6 : W := 0x108410822811318c11820810
def wc7 : W := 0x108410822a31318c1182ea10
def wc8 : W := 0x1084108a0811318c11820810
def wc9 : W := 0x1084108a0a31318c11ba0a10
def wda : W := 0x1084108a2a31318c11820810
def wdb : W := 0x108410c20c13318c11c20c10
def wdc : W := 0x108410c30815318c11c30810
def wdd : W := 0x108410c30c17318c1182081f
def wde : W := 0x108412cf3ef7318c118209ff
def wdf : W := 0x1084159a6a31318c11baea10
def wdg : W := 0x108450000000000000000000
def wdh : W := 0x108450820811318c11820810
def wdi : W := 0x108450820a31318dd1820a10
def wdj : W := 0x108450822a31318c11820810
def wdk : W := 0x1084508a0a31318c11820810
def wdl : W := 0x1084508a2a31000000000000
def wdm : W := 0x1084508a2a31318c11820810
def wdn : W := 0x1084508a2a31f7bc37861810
def wdo : W := 0x108452cf3ef70000000001ef
def wdp : W := 0x1084559a6a31000001baea10
def wdq : W := 0x108610820c13318e11820c10
def wdr : W := 0x108618820819318e19820810
def wds : W := 0x108618820c1b318c1182081f
def wdt : W := 0x109678823f7b318c118209ff
def wdu : W := 0x1096788a3f7b0000000001ef
def wdv : W := 0x10acd082aa31318dd182ea10
def wdw : W := 0x10acd08aaa31000dd000ea10
def wdx : W := 0x10c41083081531cc11830810
def wdy : W := 0x10c41882081931cc19820810
def wdz : W := 0x10c41883081d318c1182081f
def wdA : W := 0x12c4788f0bbd318c118209ff
def wdB : W := 0x12c4788f2bbd0000000001ef
def wdC : W := 0x158550aa0a31318dd1ba0a10
def wdD : W := 0x158550aa2a310181d03a0210
def wdE : W := 0x180000c00000380001c00000
def wdF : W := 0x180600000000380e00000000
def wdG : W := 0x180600c00c02000000000000
def wdH : W := 0x180600c00c02380e01c00c00
def wdI : W := 0x180600c00c02398e11c20c10
def wdJ : W := 0x180600c00c0239ce01c30c00
def wdK : W := 0x180600c00c0239ce19c00c00
def wdL : W := 0x180607d07c42380e07c0fc00
def wdM : W := 0x183e80c0bc42383e01c0fc00
def wdN : W := 0x183e87d0fc42383e07c0fc00
def wdO : W := 0x188410c20811398c11c20810
def wdP : W := 0x188600c20c02398e01c20c00
def wdQ : W := 0x188610820811398e11820810
def wdR : W := 0x188610c00c02398e11c00c00
def wdS : W := 0x188610c20c13318c11820810
def wdT : W := 0x188610c20c13398e11c20c10
def wdU : W := 0x18c00000000039c000000000
def wdV : W := 0x18c000c30004000000000000
def wdW : W := 0x18c000c3000439c001c30000
def wdX : W := 0x18c000c3000439cc11c30810
def wdY : W := 0x18c000c3000439ce01c30c00
def wdZ : W := 0x18c000c3000439ce19c30000
def wd0 : W := 0x18c007df408439c007ff0000
def wd1 : W := 0x18c400c3080439cc01c30800
def wd2 : W := 0x18c41082081139cc11820810
def wd3 : W := 0x18c410c3000439cc11c30000
def wd4 : W := 0x18c410c30815318c11820810
def wd5 : W := 0x18c410c3081539cc11c30810
def wd6 : W := 0x18c600c00c0239ce01c00c00
def wd7 : W := 0x18c600c3000439ce01c30000
def wd8 : W := 0x18c600c30c0639ce01c30c00
def wd9 : W := 0x18c610c30c1739ce11c30c10
def wea : W := 0x18c618000008000000000000
def web : W := 0x18c61800000839ce18000000
def wec : W := 0x18c61800000839ce19820810
def wed : W := 0x18c61800000839ce19c00c00
def wee : W := 0x18c61800000839ce19c30000
def wef : W := 0x18c61880080839ce19800800
def weg : W := 0x18c61882000839ce19820000
def weh : W := 0x18c618820819318c11820810
def wei : W := 0x18c61882081939ce19820810
def wej : W := 0x18c618c0000839ce19c00000
def wek : W := 0x18c618c00c0a39ce19c00c00
def wel : W := 0x18c618c20c1b39ce19c20c10
def wem : W := 0x18c618c3000c39ce19c30000
def wen : W := 0x18c618c3081d39ce19c30810
def weo : W := 0x18c618c30c0e39ce19c30c00
def wep : W := 0x18c618c30c1f00000000000f
def weq : W := 0x18c618c30c1f318c1182081f
def wer : W := 0x18c618c30c1f380e01c00c0f
def wes : W := 0x18c618c30c1f398e11c20c1f
def wet : W := 0x18c618c30c1f39c001c3000f
def weu : W := 0x18c618c30c1f39cc11c3081f
def wev : W := 0x18c618c30c1f39ce01c30c0f
def wew : W := 0x18c618c30c1f39ce1800000f
def wex : W := 0x18c618c30c1f39ce1982081f
def wey : W := 0x18c618c30c1f39ce19c00c0f
def wez : W := 0x18c618c30c1f39ce19c3000f
def weA : W := 0x18c61acf3eff0000000001ef
def weB : W := 0x18c61f1c72e839ce1e3cf3e0
def weC : W := 0x18c658cb2e3f00000000000f
def weD : W := 0x18d678c33f7f0000000001ef
def weE : W := 0x18f8e0c3b36439f1e1c3f3e0
def weF : W := 0x18fef800810839fff8000000
def weG : W := 0x18feffdfc18c39ffffff0000
def weH : W := 0x1ac678cf0fbf0000000001ef
def weI : W := 0x1f0760ec0fa23e0fe1fc0fe0
def weJ : W := 0x1fc100ef00843fc001ff0000
def weK : W := 0x1fc107ff40843fc007ff0000
def weL : W := 0x1fc7782001083fcff8000000
def weM : W := 0x1fc77ff07d4a3fcfffc0fc00
def weN : W := 0x1fff80efbcc63ffe01fffc00
def weO : W := 0x1ffff82081083ffff8000000
def weP : W := 0x401002001040c03006001000
def weQ : W := 0x401002003040000000000000
def weR : W := 0x420002040080c60006040000
def weS : W := 0x4200020c0080000000000000
def weT : W := 0x421020000100c63020000000
def weU : W := 0x4210220411c00000000001e0
def weV : W := 0x4210220411c0c630260411e0
def weW : W := 0x4210224515c6c630260411ef
def weX : W := 0x4210271c73e0c630263cf3e0
def weY : W := 0x421060000100000000000000
def weZ : W := 0x4210620c33e00000000001e0
def we0 : W := 0x4210620c33e0c630260411e0
def we1 : W := 0x421062cf3ff70000000001ef
def we2 : W := 0x4210671c73e00000063cf3e0
def we3 : W := 0x42122a0415cac630260411ef
def we4 : W := 0x42167a0c3ffb0000000001ef
def we5 : W := 0x4238e204b3e0c631e604f3e0
def we6 : W := 0x4238e20cb3e00031e000f3e0
def we7 : W := 0x42502a0511ccc630260411ef
def we8 : W := 0x42d07a0f33fd0000000001ef
def we9 : W := 0x4711622c13e0c631e63c13e0
def wfa : W := 0x4711622c33e00601e03c03e0
def wfb : W := 0x480002400000c80006400000
def wfc : W := 0x481200000000c83200000000
def wfd : W := 0x481202401442000000000000
def wfe : W := 0x481202401442c83206401400
def wff : W := 0x481202401442f83e07c01c00
def wfg : W := 0x481207d07c42c83207c0fc00
def wfh : W := 0x483e8240bc42c83e0640fc00
def wfi : W := 0x483e87d0fc42c83e07c0fc00
def wfj : W := 0x4a12224415c2ce32264415e0
def wfk : W := 0x4a4000000000ce4000000000
def wfl : W := 0x4a4002450084000000000000
def wfm : W := 0x4a4002450084ce4006450000
def wfn : W := 0x4a4002450084ffc007c70000
def wfo : W := 0x4a4007df4084ce4007ff0000
def wfp : W := 0x4a50224511c4ce70264511e0
def wfq : W := 0x4a52024514c6ce7206451400
def wfr : W := 0x4a5228000108000000000000
def wfs : W := 0x4a5228000108ce7228000000
def wft : W := 0x4a5228000108fffe38000000
def wfu : W := 0x4a522a0411c8ce722e0411e0
def wfv : W := 0x4a522a40154ace722e401400
def wfw : W := 0x4a522a45018cce722e450000
def wfx : W := 0x4a522a4515ce0000000001ef
def wfy : W := 0x4a522a4515ce318c118209ff
def wfz : W := 0x4a522a4515cec630260411ef
def wfA : W := 0x4a522a4515cec832064015ef
def wfB : W := 0x4a522a4515cece32264415ef
def wfC : W := 0x4a522a4515cece40064501ef
def wfD : W := 0x4a522a4515cece70264511ef
def wfE : W := 0x4a522a4515cece72064515ef
def wfF : W := 0x4a522a4515cece72280001ef
def wfG : W := 0x4a522a4515cece722e0411ef
def wfH : W := 0x4a522a4515cece722e4015ef
def wfI : W := 0x4a522a4515cece722e4501ef
def wfJ : W := 0x4a522a4515cef7bc378619ff
def wfK : W := 0x4a522acf3fff0000000001ef
def wfL : W := 0x4a522d9a6b39ce7229baea10
def wfM : W := 0x4a522d9a6b39fffe3838e200
def wfN : W := 0x4a526a4d37ee0000000001ef
def wfO : W := 0x4a526a4d37ee318c118209ff
def wfP : W := 0x4a567a453fff0000000001ef
def wfQ : W := 0x4a6cd245aab5ce4dd645ea10
def wfR : W := 0x4a6cd245aab5ffc1c7c7e200
def wfS : W := 0x4a7ef8008108ce7ff8000000
def wfT : W := 0x4a7effdfc18cce7fffff0000
def wfU : W := 0x4ad27a4f17ff0000000001ef
def wfV : W := 0x4d93526a1673c9b3d67a1610
def wfW : W := 0x4d93526a1673f83fc7f81e00
def wfX : W := 0x4fc1026f0084cfc0067f0000
def wfY : W := 0x4fc107ff4084cfc007ff0000
def wfZ : W := 0x4fd378200108cff3f8000000
def wf0 : W := 0x4fd37ff07d4acff3ffc0fc00
def wf1 : W := 0x4fff826fbcc6cffe067ffc00
def wf2 : W := 0x4ffff8208108cffff8000000
def wf3 : W := 0x5294328619d1f7bc378619f0
def wf4 : W := 0x5294728e3bf10000000001e0
def wf5 : W := 0x5294728e3bf1318c118209f0
def wf6 : W := 0x580002c00000000000000000
def wf7 : W := 0x581600000000000000000000
def wf8 : W := 0x581602c01c42f83e07c01c00
def wf9 : W := 0x581602c03c42000000000000
def wga : W := 0x581602c03c42380e01c00c00
def wgb : W := 0x581602c03c42c83206401400
def wgc : W := 0x581602cf3ef70000000001ef
def wgd : W := 0x581607d07c42000007c0fc00
def wge : W := 0x58167ac03f7b0000000001ef
def wgf : W := 0x583e82c0bc42003e0000fc00
def wgg : W := 0x583e87d0fc42003e07c0fc00
def wgh : W := 0x589612c21c53f9be17c21c10
def wgi : W := 0x589612c23c53318c11820810
def wgj : W := 0x589652ca3e73000000000000
def wgk : W := 0x589652ca3e73398e11c20c10
def wgl : W := 0x58d61ac33c5f00000000000f
def wgm : W := 0x5a1662cc3fe20000000001e0
def wgn : W := 0x5a562ac53dce0000000001ef
def wgo : W := 0x5a9632c61dd3ffbe37c61df0
def wgp : W := 0x5ac000000000000000000000
def wgq : W := 0x5ac002c70084ffc007c70000
def wgr : W := 0x5ac002cf0084000000000000
def wgs : W := 0x5ac002cf008439c001c30000
def wgt : W := 0x5ac002cf0084ce4006450000
def wgu : W := 0x5ac002cf3ef70000000001ef
def wgv : W := 0x5ac007df4084000007ff0000
def wgw : W := 0x5ac07acf03bd0000000001ef
def wgx : W := 0x5ac412c70895ffcc17c70810
def wgy : W := 0x5ac412cf0895318c11820810
def wgz : W := 0x5ac452cf2ab5000000000000
def wgA : W := 0x5ac452cf2ab539cc11c30810
def wgB : W := 0x5ac61acf0c9f00000000000f
def wgC : W := 0x5ad062cf33e40000000001e0
def wgD : W := 0x5ad22acf15ce0000000001ef
def wgE : W := 0x5ad432c719d5fffc37c719f0
def wgF : W := 0x5ad602c71cc6fffe07c71c00
def wgG : W := 0x5ad602cf3cc6000000000000
def wgH : W := 0x5ad602cf3cc639ce01c30c00
def wgI : W := 0x5ad638000108fffe38000000
def wgJ : W := 0x5ad638820919fffe39820810
def wgK : W := 0x5ad63a8619d9fffe3f8619f0
def wgL : W := 0x5ad63ac01d4afffe3fc01c00
def wgM : W := 0x5ad63ac7018cfffe3fc70000
def wgN : W := 0x5ad63ac71ddf0000000001ef
def wgO : W := 0x5ad63ac71ddf318c118209ff
def wgP : W := 0x5ad63d186328fffe3838e200
def wgQ : W := 0x5ad63d9a6b39fffe39baea10
def wgR : W := 0x5ad678000108000000000000
def wgS : W := 0x5ad67800010839ce18000000
def wgT : W := 0x5ad678000108ce7228000000
def wgU : W := 0x5ad678003f7b0000000001ef
def wgV : W := 0x5ad6780f03bd0000000001ef
def wgW : W := 0x5ad678820919318c11820810
def wgX : W := 0x5ad6788a2b39000000000000
def wgY : W := 0x5ad6788a2b3939ce19820810
def wgZ : W := 0x5ad678c30d1f00000000000f
def wg0 : W := 0x5ad67a0c33e80000000001e0
def wg1 : W := 0x5ad67a4515ce0000000001ef
def wg2 : W := 0x5ad67ac03d4a000000000000
def wg3 : W := 0x5ad67ac03d4a39ce19c00c00
def wg4 : W := 0x5ad67acf018c000000000000
def wg5 : W := 0x5ad67acf018c39ce19c30000
def wg6 : W := 0x5ad67acf3fff0000000001ef
def wg7 : W := 0x5ad67acf3fff318c118209ff
def wg8 : W := 0x5ad67acf3fff380e01c00def
def wg9 : W := 0x5ad67acf3fff398e11c20dff
def wha : W := 0x5ad67acf3fff39c001c301ef
def whb : W := 0x5ad67acf3fff39cc11c309ff
def whc : W := 0x5ad67acf3fff39ce01c30def
def whd : W := 0x5ad67acf3fff39ce180001ef
def whe : W := 0x5ad67acf3fff39ce198209ff
def whf : W := 0x5ad67acf3fff39ce19c00def
def whg : W := 0x5ad67acf3fff39ce19c301ef
def whh : W := 0x5ad67acf3fffc630260411ef
def whi : W := 0x5ad67acf3fffc832064015ef
def whj : W := 0x5ad67acf3fffce40064501ef
def whk : W := 0x5ad67acf3fffce72280001ef
def whl : W := 0x5ad67d10410839ce1e3cf200
def whm : W := 0x5ad67d9a6b39000001baea10
def whn : W := 0x5ad67d9a6b39ce7229baea10
def who : W := 0x5ad67fdf7fff000001baebff
def whp : W := 0x5ad67fdf7fff0000063cf3ef
def whq : W := 0x5ad67fdf7fff000007c0fdef
def whr : W := 0x5ad67fdf7fff000007ff01ef
def whs : W := 0x5ae882cf808439f1e1c3f200
def wht : W := 0x5ae8c2c7a2a4ffc1c7c7e200
def whu : W := 0x5aecd2c7aab5ffcdd7c7ea10
def whv : W := 0x5aecd2cfaab5000dd000ea10
def whw : W := 0x5aecd2cfaab5ce4dd645ea10
def whx : W := 0x5afef8008108003ff8000000
def why : W := 0x5afefacfbfff000dd000ebff
def whz : W := 0x5afefacfbfff0031e000f3ef
def whA : W := 0x5afefacfbfff003e0000fdef
def whB : W := 0x5afefacfbfff003ff80001ef
def whC : W := 0x5afeffdfc18c003fffff0000
def whD : W := 0x5d1702e03c423e0fe1fc0e00
def whE : W := 0x5d1742e81e62f83fc7f81e00
def whF : W := 0x5d9752ea1e73f9bfd7fa1e10
def whG : W := 0x5d9752ea3e730181d03a0210
def whH : W := 0x5d9752ea3e73c9b3d67a1610
def whI : W := 0x5fc102ef008407c0003f0000
def whJ : W := 0x5fc107ff408407c007ff0000
def whK : W := 0x5fd77820010807c1f8000000
def whL : W := 0x5fd77aef3fff0181d03a03ff
def whM : W := 0x5fd77aef3fff0601e03c03ef
def whN : W := 0x5fd77aef3fff07c0003f01ef
def whO : W := 0x5fd77aef3fff07c1f80001ef
def whP : W := 0x5fd77ff07d4a07c1ffc0fc00
def whQ : W := 0x5fff82efbcc607fe003ffc00
def whR : W := 0x5ffff820810807fff8000000
def whS : W := 0xa00005104000f80007c00000
def whT : W := 0xa02880008000f83e00000000
def whU : W := 0xa0288510c000300c0180e800
def whV : W := 0xa0288510c000c0300600f000
def whW : W := 0xa0288510c000f83e07c0fc00
def whX : W := 0xa0288510e00000000000e000
def whY : W := 0xa0288510fc42f83e07c0fc00
def whZ : W := 0xa0288750d442f83e07c0fc00
def wh0 : W := 0xa02887d0fc42000007c0fc00
def wh1 : W := 0xa02887d0fc42300c07c0fc00
def wh2 : W := 0xa02887d0fc42c03007c0fc00
def wh3 : W := 0xa02887d0fc42f83e07c0fc00
def wh4 : W := 0xa03a8510d442f83e07c0fc00
def wh5 : W := 0xa03e8510fc42003e0000fc00
def wh6 : W := 0xa03e8510fc42303e0180fc00
def wh7 : W := 0xa03e8510fc42c03e0600fc00
def wh8 : W := 0xa03e8510fc42f83e07c0fc00
def wh9 : W := 0xa03e87d0fc42f83e07c0fc00
def wia : W := 0xa2e8fd1fc3bdf83e07c0fdef
def wib : W := 0xa50100200000ffc000000000
def wic : W := 0xa50105304000318001ba0000
def wid : W := 0xa50105304000c600063c0000
def wie : W := 0xa50105304000ffc007ff0000
def wif : W := 0xa50105384000000000380000
def wig : W := 0xa501053f4084ffc007ff0000
def wih : W := 0xa50107754084ffc007ff0000
def wii : W := 0xa50107ff4084000007ff0000
def wij : W := 0xa50107ff4084318007ff0000
def wik : W := 0xa50107ff4084c60007ff0000
def wil : W := 0xa50107ff4084ffc007ff0000
def wim : W := 0xa5177d307f7bffc007ff01ef
def win : W := 0xa52980208000318dd0000000
def wio : W := 0xa52980208000c631e0000000
def wip : W := 0xa52980208000fffff8000000
def wiq : W := 0xa52982efbef7fffff80001ef
def wir : W := 0xa5298530c0000001c038e200
def wis : W := 0xa5298530c0000001c63cf200
def wit : W := 0xa5298530c0000031e038f200
def wiu : W := 0xa5298530c0000601e03ce200
def wiv : W := 0xa5298530c000318dd1baea10
def wiw : W := 0xa5298530c000c031c638f200
def wix : W := 0xa5298530c000c601c63ce200
def wiy : W := 0xa5298530c000c630063cf000
def wiz : W := 0xa5298530c000c631e038e200
def wiA : W := 0xa5298530c000c631e600f000
def wiB : W := 0xa5298530c000c631e63c0000
def wiC : W := 0xa5298530c000c631e63cf200
def wiD : W := 0xa5298530c000ce33e67cf600
def wiE : W := 0xa5298530c000ce71e67df200
def wiF : W := 0xa5298530c000ce73ee3cf200
def wiG : W := 0xa5298530c000f7bdf7befa10
def wiH : W := 0xa5298530c000f9bfd7fafe10
def wiI : W := 0xa5298530c000fe3fe7fcfe00
def wiJ : W := 0xa5298530c000ffcdd7ffea10
def wiK : W := 0xa5298530c000fff1e7fff200
def wiL : W := 0xa5298530c000fffe07fffc00
def wiM : W := 0xa5298530c000fffff9baea10
def wiN : W := 0xa5298530c000fffffe3cf200
def wiO : W := 0xa5298530c000ffffffc0fc00
def wiP : W := 0xa5298530c000ffffffff0000
def wiQ : W := 0xa5298530e0000001c038e200
def wiR : W := 0xa5298530e000c631e63cf200
def wiS : W := 0xa5298530ea310001c038ea10
def wiT : W := 0xa5298530ea31318dd1baea10
def wiU : W := 0xa5298530f260c631e63cf3e0
def wiV : W := 0xa5298538c0000001c038e200
def wiW : W := 0xa5298538c000c631e63cf200
def wiX : W := 0xa5298538e00000000038e000
def wiY : W := 0xa5298538e2200001c038e200
def wiZ : W := 0xa5298538e220c631e63cf200
def wi0 : W := 0xa529853ac2310001c03ae210
def wi1 : W := 0xa529853ac231318dd1baea10
def wi2 : W := 0xa529853cc2a0c631e63cf3e0
def wi3 : W := 0xa52985baea310001c038e200
def wi4 : W := 0xa52985baea310001c1baea10
def wi5 : W := 0xa52985baea31318dd1baea10
def wi6 : W := 0xa5298730f040c631e63cf200
def wi7 : W := 0xa5298734d0c0c631e63cf3e0
def wi8 : W := 0xa529873cc080c631e63cf200
def wi9 : W := 0xa529873cf2e00001c63cf3e0
def wja : W := 0xa529873cf2e0c631e63cf3e0
def wjb : W := 0xa52987fffef7c631e63cf3ef
def wjc : W := 0xa529c02080000001c0000000
def wjd : W := 0xa529c530c0000001c038e200
def wje : W := 0xa529c530c000c631e63cf200
def wjf : W := 0xa529c530e0000001c000e000
def wjg : W := 0xa529c530e2200001c038e200
def wjh : W := 0xa529c530e220c631e63cf200
def wji : W := 0xa529c538c0000001c0380000
def wjj : W := 0xa529c538c2200001c038e200
def wjk : W := 0xa529c538c220c631e63cf200
def wjl : W := 0xa529c538e2200001c038e200
def wjm : W := 0xa529c538e2200001c63cf200
def wjn : W := 0xa529c538e2200031e038f200
def wjo : W := 0xa529c538e2200601e03ce200
def wjp : W := 0xa529c538e220318dd1baea10
def wjq : W := 0xa529c538e220c031c638f200
def wjr : W := 0xa529c538e220c601c63ce200
def wjs : W := 0xa529c538e220c631e038e200
def wjt : W := 0xa529c538e220c631e63cf200
def wju : W := 0xa529c538e2310001c038e210
def wjv : W := 0xa529c538ea310001c038e200
def wjw : W := 0xa529c538ea310001c038ea10
def wjx : W := 0xa529c538f2600001c038f3e0
def wjy : W := 0xa529c53ae2310001c038e200
def wjz : W := 0xa529c53ae2310001c03ae210
def wjA : W := 0xa529c53aea310001c03aea10
def wjB : W := 0xa529c53ce2a00001c03ce3e0
def wjC : W := 0xa529c5baea310001c038e200
def wjD : W := 0xa529c5baea310001c038ea10
def wjE : W := 0xa529c5baea310001c03ae210
def wjF : W := 0xa529c5baea310001c1baea10
def wjG : W := 0xa529c5baea31318dd1baea10
def wjH : W := 0xa529c738f2600001c638f200
def wjI : W := 0xa529c73ce2a00001c63ce200
def wjJ : W := 0xa529c73cf2e00001c038e3e0
def wjK : W := 0xa529c73cf2e00001c63cf3e0
def wjL : W := 0xa529c73cf2e0c631e63cf3e0
def wjM : W := 0xa529c7fffef70001c038e3ef
def wjN : W := 0xa529d530c2310001d038e210
def wjO : W := 0xa529d530c231318dd1baea10
def wjP : W := 0xa529d538e2310001c038e200
def wjQ : W := 0xa529d538e2310001d038e210
def wjR : W := 0xa529d538ea310001d038ea10
def wjS : W := 0xa529d53ae2310001d03ae210
def wjT : W := 0xa529e530c320c631e63cf3e0
def wjU : W := 0xa529e538e3200001e038e3e0
def wjV : W := 0xa529f8208108fffff8000000
def wjW : W := 0xa52dd530ea310001c038e200
def wjX : W := 0xa52dd530ea31000dd038ea10
def wjY : W := 0xa52dd530ea31318dd1baea10
def wjZ : W := 0xa52dd538ea310001c038e200
def wj0 : W := 0xa52dd538ea310001c038ea10
def wj1 : W := 0xa52dd538ea310001d038e210
def wj2 : W := 0xa52dd538ea31000dd038ea10
def wj3 : W := 0xa52dd538ea31318dd1baea10
def wj4 : W := 0xa52dd5baea310001c038e200
def wj5 : W := 0xa52dd5baea31000dd1baea10
def wj6 : W := 0xa52dd5baea31318dd1baea10
def wj7 : W := 0xa5398530f040c631e63cf200
def wj8 : W := 0xa539a530d140c631e63cf3e0
def wj9 : W := 0xa539c538f2600031c038f200
def wka : W := 0xa539e530c100c631e63cf200
def wkb : W := 0xa539e530f3600031e038f3e0
def wkc : W := 0xa539e530f360c631e63cf3e0
def wkd : W := 0xa539e538e3200031e038e200
def wke : W := 0xa539e538f3600001c038e3e0
def wkf : W := 0xa539e538f3600031e038f3e0
def wkg : W := 0xa539e538f360c631e63cf3e0
def wkh : W := 0xa539e73cf3e00031e63cf3e0
def wki : W := 0xa539e73cf3e0c631e63cf3e0
def wkj : W := 0xa53ba8208108fffff8000000
def wkk : W := 0xa53ff8208108003ff8000000
def wkl : W := 0xa53ff820810831bff8000000
def wkm : W := 0xa53ff8208108c63ff8000000
def wkn : W := 0xa53ff8208108fffff8000000
def wko : W := 0xa53ffd30ff7bc631e63cf3ef
def wkp : W := 0xa53ffd38ff7b0001c038e3ef
def wkq : W := 0xa5a9d53ac2310001c038e200
def wkr : W := 0xa5a9d53ac2310181d03ae210
def wks : W := 0xa5a9d53ac231318dd1baea10
def wkt : W := 0xa5a9d53ae2310001c038e200
def wku : W := 0xa5a9d53ae2310001c03ae210
def wkv : W := 0xa5a9d53ae2310001d038e210
def wkw : W := 0xa5a9d53ae2310181d03ae210
def wkx : W := 0xa5a9d53ae231318dd1baea10
def wky : W := 0xa5a9d5baea310001c038e200
def wkz : W := 0xa5a9d5baea310181d1baea10
def wkA : W := 0xa5a9d5baea31318dd1baea10
def wkB : W := 0xa5add53aea310001c038e200
def wkC : W := 0xa5add53aea31018dd03aea10
def wkD : W := 0xa5add53aea31318dd1baea10
def wkE : W := 0xa729853cc080c631e63cf200
def wkF : W := 0xa729a534c180c631e63cf3e0
def wkG : W := 0xa729c53ce2a00601c03ce200
def wkH : W := 0xa729e530c100c631e63cf200
def wkI : W := 0xa729e538e3200601e038e200
def wkJ : W := 0xa729e53cc3a00601e03ce3e0
def wkK : W := 0xa729e53cc3a0c631e63cf3e0
def wkL : W := 0xa729e53ce3a00001c038e3e0
def wkM : W := 0xa729e53ce3a00601e03ce3e0
def wkN : W := 0xa729e53ce3a0c631e63cf3e0
def wkO : W := 0xa729e73cf3e00601e63cf3e0
def wkP : W := 0xa729e73cf3e0c631e63cf3e0
def wkQ : W := 0xa739e53cf3e00631e03cf3e0
def wkR : W := 0xa739e53cf3e0c631e63cf3e0
def wkS : W := 0xa74105354084ffc007ff0000
def wkT : W := 0xa769a8208108fffff8000000
def wkU : W := 0xa7c1053f408407c0003f0000
def wkV : W := 0xa7c1053f408437c001bf0000
def wkW : W := 0xa7c1053f4084c7c0063f0000
def wkX : W := 0xa7c1053f4084ffc007ff0000
def wkY : W := 0xa7c107ff4084ffc007ff0000
def wkZ : W := 0xa7e9f820810807c1f8000000
def wk0 : W := 0xa7e9f820810837cdf8000000
def wk1 : W := 0xa7e9f8208108c7f1f8000000
def wk2 : W := 0xa7e9f8208108fffff8000000
def wk3 : W := 0xa7e9fd3fc3bdc631e63cf3ef
def wk4 : W := 0xa7e9fd3fe3bd0001c038e3ef
def wk5 : W := 0xa7fff8208108fffff8000000
def wk6 : W := 0xad6bcd79e62e0001c038e20f
def wk7 : W := 0xb00005904000300001800000
def wk8 : W := 0xb02c80008000300c00000000
def wk9 : W := 0xb02c8590e80000000000e000
def wla : W := 0xb02c8590e800300c0180e800
def wlb : W := 0xb02c8590e800f83e07c0fc00
def wlc : W := 0xb02c8590fc42300c0180fc00
def wld : W := 0xb02c859aea31300c01baea10
def wle : W := 0xb02c87d0fc42000007c0fc00
def wlf : W := 0xb02c87d0fc42300c0180e800
def wlg : W := 0xb02c87d0fc42300c07c0fc00
def wlh : W := 0xb02c87d0fc42f83e07c0fc00
def wli : W := 0xb02cd590ea31300dd180ea10
def wlj : W := 0xb03e8590fc42003e0000fc00
def wlk : W := 0xb03e8590fc42300c0180e800
def wll : W := 0xb03e8590fc42303e0180fc00
def wlm : W := 0xb03e8590fc42f83e07c0fc00
def wln : W := 0xb03e87d0fc42303e07c0fc00
def wlo : W := 0xb0ac9592e811318c1182e810
def wlp : W := 0xb0acd59aea31300c0180e800
def wlq : W := 0xb2ecfd9febbd300c0180e9ef
def wlr : W := 0xb52d85b0e800318dd1baea10
def wls : W := 0xb52d85baea31318dd1baea10
def wlt : W := 0xb52dc5b8ea200001c038e200
def wlu : W := 0xb52dc5b8ea20300dc1b8ea00
def wlv : W := 0xb52dc5baea310001c038e200
def wlw : W := 0xb52dc5baea31300dc1baea10
def wlx : W := 0xb52dd5b0ea31318dd1baea10
def wly : W := 0xb52dd5b8ea310001c038e200
def wlz : W := 0xb52dd5b8ea31300dd1b8ea10
def wlA : W := 0xb58100200000318000000000
def wlB : W := 0xb58105ba4000000000380000
def wlC : W := 0xb58105ba4000318001ba0000
def wlD : W := 0xb58105ba4000ffc007ff0000
def wlE : W := 0xb58105ba6a31318001baea10
def wlF : W := 0xb58105bf4084318001bf0000
def wlG : W := 0xb58107ff4084000007ff0000
def wlH : W := 0xb58107ff4084318001ba0000
def wlI : W := 0xb58107ff4084318007ff0000
def wlJ : W := 0xb58107ff4084ffc007ff0000
def wlK : W := 0xb58155ba42313181d1ba0210
def wlL : W := 0xb58515ba4811318c11ba0810
def wlM : W := 0xb58555ba6a31318001ba0000
def wlN : W := 0xb5977dba7f7b318001ba01ef
def wlO : W := 0xb5a985bac000318dd1baea10
def wlP : W := 0xb5a985baea31318dd1baea10
def wlQ : W := 0xb5a9c5bae2200001c038e200
def wlR : W := 0xb5a9c5bae2203181c1bae200
def wlS : W := 0xb5a9c5baea310001c038e200
def wlT : W := 0xb5a9c5baea313181c1baea10
def wlU : W := 0xb5a9d5bac231318dd1baea10
def wlV : W := 0xb5a9d5bae2310001c038e200
def wlW : W := 0xb5a9d5bae2313181d1bae210
def wlX : W := 0xb5ad85bae800318c01bae800
def wlY : W := 0xb5ad85baea31318c01baea10
def wlZ : W := 0xb5ad95b2c811318dd1baea10
def wl0 : W := 0xb5ad95baea31318dd1baea10
def wl1 : W := 0xb5add02080000001c0000000
def wl2 : W := 0xb5add0208000318dd0000000
def wl3 : W := 0xb5add0208000fffff8000000
def wl4 : W := 0xb5add020aa31318dd000ea10
def wl5 : W := 0xb5add02a8231318dd03a0210
def wl6 : W := 0xb5add0a28811318dd1820810
def wl7 : W := 0xb5add0aaaa31318dd0000000
def wl8 : W := 0xb5add2efbef7318dd00001ef
def wl9 : W := 0xb5add530c000318dd1baea10
def wma : W := 0xb5add530ea31318dd1baea10
def wmb : W := 0xb5add538e2200001c038e200
def wmc : W := 0xb5add538e220318dd038e200
def wmd : W := 0xb5add538ea310001c038e200
def wme : W := 0xb5add538ea31318dd038ea10
def wmf : W := 0xb5add53ac231318dd1baea10
def wmg : W := 0xb5add53ae2310001c038e200
def wmh : W := 0xb5add53ae231318dd03ae210
def wmi : W := 0xb5add5b0e800318dd180e800
def wmj : W := 0xb5add5b0ea31318dd180ea10
def wmk : W := 0xb5add5b2ea31318dd1baea10
def wml : W := 0xb5add5bac000318dd1ba0000
def wmm : W := 0xb5add5bac231318dd1ba0210
def wmn : W := 0xb5add5baca31318dd1baea10
def wmo : W := 0xb5add5baea3100000038e000
def wmp : W := 0xb5add5baea310001c000e000
def wmq : W := 0xb5add5baea310001c0380000
def wmr : W := 0xb5add5baea310001c038e200
def wms : W := 0xb5add5baea310001c038ea10
def wmt : W := 0xb5add5baea310001c03ae210
def wmu : W := 0xb5add5baea310001c1baea10
def wmv : W := 0xb5add5baea310001d038e210
def wmw : W := 0xb5add5baea31000dd038ea10
def wmx : W := 0xb5add5baea310181d03ae210
def wmy : W := 0xb5add5baea31300dc1b8ea00
def wmz : W := 0xb5add5baea313181c1bae200
def wmA : W := 0xb5add5baea31318c01bae800
def wmB : W := 0xb5add5baea31318dd038e200
def wmC : W := 0xb5add5baea31318dd180e800
def wmD : W := 0xb5add5baea31318dd1ba0000
def wmE : W := 0xb5add5baea31318dd1baea10
def wmF : W := 0xb5add5baea31398fd1faee10
def wmG : W := 0xb5add5baea3139cdd1fbea10
def wmH : W := 0xb5add5baea3139cfd9baea10
def wmI : W := 0xb5add5baea31c631e63cf200
def wmJ : W := 0xb5add5baea31f7bdf7befa10
def wmK : W := 0xb5add5baea31f9bfd7fafe10
def wmL : W := 0xb5add5baea31ffcdd7ffea10
def wmM : W := 0xb5add5baea31fffff9baea10
def wmN : W := 0xb5add5bafe73318dd1bafe10
def wmO : W := 0xb5add5bfeab5318dd1bfea10
def wmP : W := 0xb5add5faee33318dd1faee10
def wmQ : W := 0xb5add5fbea35318dd1fbea10
def wmR : W := 0xb5add7befaf1318dd7befbf0
def wmS : W := 0xb5add7fafe73318dd1baea10
def wmT : W := 0xb5add7fafe73318dd7fafe10
def wmU : W := 0xb5add7ffeab5318dd1baea10
def wmV : W := 0xb5add7ffeab5318dd7ffea10
def wmW : W := 0xb5add7fffef70001c63cf3ef
def wmX : W := 0xb5add7fffef7318dd1baebff
def wmY : W := 0xb5adf8208108318df8000000
def wmZ : W := 0xb5adfdbaeb39318df9baea10
def wm0 : W := 0xb5afd5baee33318fd1baee10
def wm1 : W := 0xb5afddbaea39318fd9baea10
def wm2 : W := 0xb5bdf5bafb7131bdf1bafbf0
def wm3 : W := 0xb5bfd5bafe73318dd1baea10
def wm4 : W := 0xb5bfd5bafe7331bfd1bafe10
def wm5 : W := 0xb5bff8208108003ff8000000
def wm6 : W := 0xb5bff8208108318dd0000000
def wm7 : W := 0xb5bff820810831bff8000000
def wm8 : W := 0xb5bff8208108fffff8000000
def wm9 : W := 0xb5bffdbaeb39318dd1baea10
def wna : W := 0xb5bffdbaeb3931bff9baea10
def wnb : W := 0xb5bffdbaff7b0031e038f3ef
def wnc : W := 0xb5bffdbaff7b318dd1baebff
def wnd : W := 0xb5edd5bbea3531cdd1bbea10
def wne : W := 0xb5edddbaea3931cdd9baea10
def wnf : W := 0xb7adf5beebb1378df1beebf0
def wng : W := 0xb7c105bf408407c0003f0000
def wnh : W := 0xb7c105bf4084318001ba0000
def wni : W := 0xb7c105bf408437c001bf0000
def wnj : W := 0xb7c105bf4084ffc007ff0000
def wnk : W := 0xb7c107ff408437c007ff0000
def wnl : W := 0xb7edd5bfeab5318dd1baea10
def wnm : W := 0xb7edd5bfeab537cdd1bfea10
def wnn : W := 0xb7edf820810807c1f8000000
def wno : W := 0xb7edf8208108318dd0000000
def wnp : W := 0xb7edf820810837cdf8000000
def wnq : W := 0xb7edf8208108fffff8000000
def wnr : W := 0xb7edfdbaeb39318dd1baea10
def wns : W := 0xb7edfdbaeb3937cdf9baea10
def wnt : W := 0xb7edfdbfebbd0601e03ce3ef
def wnu : W := 0xb7edfdbfebbd318dd1baebff
def wnv : W := 0xb7fff820810837fff8000000
def wnw : W := 0xb82e85d0cc02f83e07c0fc00
def wnx : W := 0xb82e85d0ec02380e01c0ec00
def wny : W := 0xb82e87d0fc42380e07c0fc00
def wnz : W := 0xb82e87d0fc42f83e07c0fc00
def wnA : W := 0xb83e85d0fc42383e01c0fc00
def wnB : W := 0xb83e85d0fc42f83e07c0fc00
def wnC : W := 0xbdadd5faea31398dd1faea10
def wnD : W := 0xbdafd5baea31398fd1baea10
def wnE : W := 0xbdafd5faee330001c038e200
def wnF : W := 0xbdafd5faee33318dd1baea10
def wnG : W := 0xbdafd5faee33398fd1faee10
def wnH : W := 0xbdc105f34004ffc007ff0000
def wnI : W := 0xbdc105fb400439c001fb0000
def wnJ : W := 0xbdc107ff408439c007ff0000
def wnK : W := 0xbdc107ff4084ffc007ff0000
def wnL : W := 0xbdedd5baea3139cdd1baea10
def wnM : W := 0xbdedd5fbea350001c038e200
def wnN : W := 0xbdedd5fbea35318dd1baea10
def wnO : W := 0xbdedd5fbea3539cdd1fbea10
def wnP : W := 0xbdef98208008fffff8000000
def wnQ : W := 0xbdef9df3cc1fc631e63cf20f
def wnR : W := 0xbdefd5fbee3739cfd1fbee10
def wnS : W := 0xbdefd820800839cfd8000000
def wnT : W := 0xbdefddbaea390001c038e200
def wnU : W := 0xbdefddbaea39318dd1baea10
def wnV : W := 0xbdefddbaea3939cfd9baea10
def wnW : W := 0xbdefddfaee3b39cfd9faee10
def wnX : W := 0xbdefddfbea3d39cfd9fbea10
def wnY : W := 0xbdefddfbee3f0001c038e20f
def wnZ : W := 0xbdefddfbee3f318dd1baea1f
def wn0 : W := 0xbdfff820810839fff8000000
def wn1 : W := 0xbdfff8208108fffff8000000
def wn2 : W := 0xbfc105ff40843fc001ff0000
def wn3 : W := 0xbfc105ff4084ffc007ff0000
def wn4 : W := 0xbfeff82081083fcff8000000
def wn5 : W := 0xbfeff8208108fffff8000000
def wn6 : W := 0xe00007104000c00006000000
def wn7 : W := 0xe03880008000c03000000000
def wn8 : W := 0xe0388710f040c0300600f000
def wn9 : W := 0xe0388710f040f83e07c0fc00
def woa : W := 0xe0388710fc42c0300600fc00
def wob : W := 0xe038871cf2e0c030063cf3e0
def woc : W := 0xe0388750f442c0300640f400
def wod : W := 0xe03887d0fc42c0300600f000
def woe : W := 0xe03887d0fc42c03007c0fc00
def wof : W := 0xe03887d0fc42f83e07c0fc00
def wog : W := 0xe038e710f360c031e600f3e0
def woh : W := 0xe03a8710f442c0320600f400
def woi : W := 0xe03e8710fc42c0300600f000
def woj : W := 0xe03e8710fc42c03e0600fc00
def wok : W := 0xe03e8710fc42f83e07c0fc00
def wol : W := 0xe03e87d0fc42c03e07c0fc00
def wom : W := 0xe238a714f1c0c6302604f1e0
def won : W := 0xe238e71cf3e0c0300600f1e0
def woo : W := 0xe5298730c000c631e63cf200
def wop : W := 0xe529c738e220c001c638e200
def woq : W := 0xe5398530c000c631e63cf200
def wor : W := 0xe5398730d040c631e63cf200
def wos : W := 0xe5398730f040c031c638f200
def wot : W := 0xe5398730f040c630063cf000
def wou : W := 0xe5398730f040c631e600f000
def wov : W := 0xe5398730f040c631e63cf200
def wow : W := 0xe5398738f040c0300638f000
def wox : W := 0xe539873cf2e0c631e63cf3e0
def woy : W := 0xe539c538e220c031c038e200
def woz : W := 0xe539c730f040c031c600f000
def woA : W := 0xe539c738f2600001c038e200
def woB : W := 0xe539c738f260c031c638f200
def woC : W := 0xe539c738f260c631e63cf200
def woD : W := 0xe539c73cf2e0c031c63cf3e0
def woE : W := 0xe539e730f360c631e63cf3e0
def woF : W := 0xe539e738f360c031e638f3e0
def woG : W := 0xe70100200000c60000000000
def woH : W := 0xe701073c4080c600063c0000
def woI : W := 0xe701073c4080ffc007ff0000
def woJ : W := 0xe701073c72e0c600063cf3e0
def woK : W := 0xe701073f4084c600063f0000
def woL : W := 0xe701077d4084c600067d0000
def woM : W := 0xe70107ff4084c600063c0000
def woN : W := 0xe70107ff4084c60007ff0000
def woO : W := 0xe70107ff4084ffc007ff0000
def woP : W := 0xe701673c43a0c601e63c03e0
def woQ : W := 0xe711273c51c0c630263c11e0
def woR : W := 0xe711673c73e0c600063c01e0
def woS : W := 0xe7298530c000c631e63cf200
def woT : W := 0xe7298734c080c631e63cf200
def woU : W := 0xe729873cc080c601c63ce200
def woV : W := 0xe729873cc080c630063cf000
def woW : W := 0xe729873cc080c631e63c0000
def woX : W := 0xe729873cc080c631e63cf200
def woY : W := 0xe729873ce080c600063ce000
def woZ : W := 0xe729873cf2e0c631e63cf3e0
def wo0 : W := 0xe729c538e220c601c038e200
def wo1 : W := 0xe729c73cc080c601c63c0000
def wo2 : W := 0xe729c73ce2a00001c038e200
def wo3 : W := 0xe729c73ce2a0c601c63ce200
def wo4 : W := 0xe729c73ce2a0c631e63cf200
def wo5 : W := 0xe729c73cf2e0c601c63cf3e0
def wo6 : W := 0xe729e73cc3a0c631e63cf3e0
def wo7 : W := 0xe729e73ce3a0c601e63ce3e0
def wo8 : W := 0xe7398730f040c6300600f000
def wo9 : W := 0xe7398730fc42c6300600fc00
def wpa : W := 0xe739873cc080c630063c0000
def wpb : W := 0xe739873cf0c0c630063cf000
def wpc : W := 0xe739873cf0c0c631e63cf200
def wpd : W := 0xe739873cf2e0c630063cf3e0
def wpe : W := 0xe739873fc084c630063f0000
def wpf : W := 0xe739873ffcc6c630063ffc00
def wpg : W := 0xe739a530c100c631e63cf200
def wph : W := 0xe739a734d1c00001c038e3e0
def wpi : W := 0xe739a734d1c0c631e63cf3e0
def wpj : W := 0xe739a734f1c0c631e63cf3e0
def wpk : W := 0xe739a73cd1c0c631e63cf3e0
def wpl : W := 0xe739a73cf1c0c630263cf1e0
def wpm : W := 0xe739a73cf3e0c631e63cf3e0
def wpn : W := 0xe739c73cf2e0c631c63cf200
def wpo : W := 0xe739e0208100c631e0000000
def wpp : W := 0xe739e0208100fffff8000000
def wpq : W := 0xe739e020b360c631e000f3e0
def wpr : W := 0xe739e02c83a0c631e03c03e0
def wps : W := 0xe739e22491c0c631e60411e0
def wpt : W := 0xe739e22cb3e0c631e00001e0
def wpu : W := 0xe739e530c100c631e038e200
def wpv : W := 0xe739e530c100c631e600f000
def wpw : W := 0xe739e530c100c631e63c0000
def wpx : W := 0xe739e530c100c631e63cf200
def wpy : W := 0xe739e530e100c631e000e000
def wpz : W := 0xe739e530f360c631e63cf3e0
def wpA : W := 0xe739e538c100c631e0380000
def wpB : W := 0xe739e538e3200001c038e200
def wpC : W := 0xe739e538e320c631e038e200
def wpD : W := 0xe739e538e320c631e63cf200
def wpE : W := 0xe739e538f360c631e038f3e0
def wpF : W := 0xe739e53cc3a0c631e63cf3e0
def wpG : W := 0xe739e53ce3a0c631e03ce3e0
def wpH : W := 0xe739e730c100c631e6000000
def wpI : W := 0xe739e730f140c631e600f000
def wpJ : W := 0xe739e730f140c631e63cf200
def wpK : W := 0xe739e730f360c631e600f3e0
def wpL : W := 0xe739e734d1c0c631e63cf3e0
def wpM : W := 0xe739e734f1c0c631e604f1e0
def wpN : W := 0xe739e734f3e0c631e63cf3e0
def wpO : W := 0xe739e738f360c631e638f200
def wpP : W := 0xe739e73cc180c631e63c0000
def wpQ : W := 0xe739e73cc180c631e63cf200
def wpR : W := 0xe739e73cc3a0c631e63c03e0
def wpS : W := 0xe739e73cd1c0c631e63c11e0
def wpT : W := 0xe739e73cd3e0c631e63cf3e0
def wpU : W := 0xe739e73ce3a0c631e63ce200
def wpV : W := 0xe739e73cf1c0c631e63cf000
def wpW : W := 0xe739e73cf3e00001c038e3e0
def wpX : W := 0xe739e73cf3e00001c63cf3e0
def wpY : W := 0xe739e73cf3e00031e038f3e0
def wpZ : W := 0xe739e73cf3e00601e03ce3e0
def wp0 : W := 0xe739e73cf3e0c031c638f3e0
def wp1 : W := 0xe739e73cf3e0c601c63ce3e0
def wp2 : W := 0xe739e73cf3e0c630063cf1e0
def wp3 : W := 0xe739e73cf3e0c631e038e3e0
def wp4 : W := 0xe739e73cf3e0c631e600f1e0
def wp5 : W := 0xe739e73cf3e0c631e63c01e0
def wp6 : W := 0xe739e73cf3e0c631e63cf3e0
def wp7 : W := 0xe739e73cf3e0ce33e67cf7e0
def wp8 : W := 0xe739e73cf3e0ce71e67df3e0
def wp9 : W := 0xe739e73cf3e0ce73ee3cf3e0
def wqa : W := 0xe739e73cf3e0f7bdf7befbf0
def wqb : W := 0xe739e73cf3e0fe3fe7fcffe0
def wqc : W := 0xe739e73cf3e0fff1e7fff3e0
def wqd : W := 0xe739e73cf3e0fffffe3cf3e0
def wqe : W := 0xe739e73cfbf1c631e63cfbf0
def wqf : W := 0xe739e73cffe2c631e63cffe0
def wqg : W := 0xe739e73cfff3c631e63cf3ef
def wqh : W := 0xe739e73ef3f1c631e63ef3f0
def wqi : W := 0xe739e73ff3e4c631e63ff3e0
def wqj : W := 0xe739e73ff3f5c631e63cf3ef
def wqk : W := 0xe739e77cf7e2c631e67cf7e0
def wql : W := 0xe739e77df3e4c631e67df3e0
def wqm : W := 0xe739e77df7e6c631e63cf3ef
def wqn : W := 0xe739e7befbf1c631e63cf3e0
def wqo : W := 0xe739e7befbf1c631e7befbf0
def wqp : W := 0xe739e7fcffe2c631e63cf3e0
def wqq : W := 0xe739e7fcffe2c631e7fcffe0
def wqr : W := 0xe739e7fff3e4c631e63cf3e0
def wqs : W := 0xe739e7fff3e4c631e7fff3e0
def wqt : W := 0xe739e7fffff7c631e63cf3ef
def wqu : W := 0xe739f73cf3f1c631f63cf3f0
def wqv : W := 0xe739f8208108c631f8000000
def wqw : W := 0xe739ff30c108c631fe000000
def wqx : W := 0xe739ff30fd4ac631fe00fc00
def wqy : W := 0xe739ff3cf3e8c631fe3cf3e0
def wqz : W := 0xe739ff3cf3f9c631e63cf3ef
def wqA : W := 0xe739ff3fc18cc631fe3f0000
def wqB : W := 0xe73be73cf7e2c633e63cf7e0
def wqC : W := 0xe73be8208108c633e8000000
def wqD : W := 0xe73bef3cf3e8c633ee3cf3e0
def wqE : W := 0xe73bef3cf7eac631e63cf3ef
def wqF : W := 0xe73df73cfbf1c631e63cf3e0
def wqG : W := 0xe73df73cfbf1c63df63cfbf0
def wqH : W := 0xe73fe73cffe2c631e63cf3e0
def wqI : W := 0xe73fe73cffe2c63fe63cffe0
def wqJ : W := 0xe73ff8208108c631e0000000
def wqK : W := 0xe73ff8208108c63ff8000000
def wqL : W := 0xe73ff8208108fffff8000000
def wqM : W := 0xe73fff3cf3e8c631e63cf3e0
def wqN : W := 0xe73fff3cf3e8c63ffe3cf3e0
def wqO : W := 0xe73fff3cfffbc631e63cf3ef
def wqP : W := 0xe73fffffffffc631e63cf3ef
def wqQ : W := 0xe741073d4084c640063d0000
def wqR : W := 0xe779e73df3e4c671e63df3e0
def wqS : W := 0xe779e8208108c671e8000000
def wqT : W := 0xe779ef3cf3e8c671ee3cf3e0
def wqU : W := 0xe779ef3df3ecc631e63cf3ef
def wqV : W := 0xe7b9f73ef3f1c631e63cf3e0
def wqW : W := 0xe7b9f73ef3f1c7b1f63ef3f0
def wqX : W := 0xe7c1073f4084c600063c0000
def wqY : W := 0xe7c1073f4084c7c0063f0000
def wqZ : W := 0xe7c1073f4084ffc007ff0000
def wq0 : W := 0xe7c107ff4084c7c007ff0000
def wq1 : W := 0xe7f9e73ff3e4c631e63cf3e0
def wq2 : W := 0xe7f9e73ff3e4c7f1e63ff3e0
def wq3 : W := 0xe7f9f8208108c631e0000000
def wq4 : W := 0xe7f9f8208108c7f1f8000000
def wq5 : W := 0xe7f9f8208108fffff8000000
def wq6 : W := 0xe7f9ff3cf3e8c631e63cf3e0
def wq7 : W := 0xe7f9ff3cf3e8c7f1fe3cf3e0
def wq8 : W := 0xe7f9ff3ff3fdc631e63cf3ef
def wq9 : W := 0xe7f9ffffffffc631e63cf3ef
def wra : W := 0xe7fff8208108c7fff8000000
def wrb : W := 0xe7ffff3fffffc631e63cf3ef
def wrc : W := 0xe83a8750d442300c0180e800
def wrd : W := 0xe83a8750d442c8320640f400
def wre : W := 0xe83a8750d442f83e07c0fc00
def wrf : W := 0xe83a8750f442c0300600f000
def wrg : W := 0xe83a8750f442c8320640f400
def wrh : W := 0xe83a8750f442f83e07c0fc00
def wri : W := 0xe83a87d0fc42c83207c0fc00
def wrj : W := 0xe83a87d0fc42f83e07c0fc00
def wrk : W := 0xe83e8750fc42c83e0640fc00
def wrl : W := 0xe83e8750fc42f83e07c0fc00
def wrm : W := 0xe8ba9752f453c9b21642f410
def wrn : W := 0xed3b8770d442ce33e67cf600
def wro : W := 0xed3bc778f662c833c678f600
def wrp : W := 0xef39e77cf3e0ce31e67cf3e0
def wrq : W := 0xef3be73cf3e0ce33e63cf3e0
def wrr : W := 0xef3be77cf7e2c631e63cf3e0
def wrs : W := 0xef3be77cf7e2ce33e67cf7e0
def wrt : W := 0xef4107754084318001ba0000
def wru : W := 0xef4107754084ce40067d0000
def wrv : W := 0xef4107754084ffc007ff0000
def wrw : W := 0xef41077d4084c600063c0000
def wrx : W := 0xef41077d4084ce40067d0000
def wry : W := 0xef41077d4084ffc007ff0000
def wrz : W := 0xef4107ff4084ce4007ff0000
def wrA : W := 0xef4107ff4084ffc007ff0000
def wrB : W := 0xef45177d4895ce4c167d0810
def wrC : W := 0xef698775c084ce71e67df200
def wrD : W := 0xef69c77de2a4ce41c67de200
def wrE : W := 0xef79e73cf3e0ce71e63cf3e0
def wrF : W := 0xef79e77df3e4c631e63cf3e0
def wrG : W := 0xef79e77df3e4ce71e67df3e0
def wrH : W := 0xef7b8770f442ce720640f400
def wrI : W := 0xef7b877dc084ce72067d0000
def wrJ : W := 0xef7b877df4c6ce72067df400
def wrK : W := 0xef7ba8208108318dd0000000
def wrL : W := 0xef7ba8208108ce73e8000000
def wrM : W := 0xef7ba8208108fffff8000000
def wrN : W := 0xef7bad30c108ce73ee3cf200
def wrO : W := 0xef7baf75d5ce0001c038e3ef
def wrP : W := 0xef7baf75d5ce318dd1baebff
def wrQ : W := 0xef7baf75d5cec631e63cf3ef
def wrR : W := 0xef7be77df7e6ce73e67df7e0
def wrS : W := 0xef7be8208108c631e0000000
def wrT : W := 0xef7be8208108ce73e8000000
def wrU : W := 0xef7be8208108fffff8000000
def wrV : W := 0xef7be8a28919ce73e9820810
def wrW : W := 0xef7bed38e328ce73e838e200
def wrX : W := 0xef7bef3cf3e8c631e63cf3e0
def wrY : W := 0xef7bef3cf3e8ce73ee3cf3e0
def wrZ : W := 0xef7bef70c108ce73ee400000
def wr0 : W := 0xef7bef70f54ace73ee40f400
def wr1 : W := 0xef7bef7cf7eace73ee7cf7e0
def wr2 : W := 0xef7bef7dc18cce73ee7d0000
def wr3 : W := 0xef7bef7df3ecce73ee7df3e0
def wr4 : W := 0xef7bef7df7ee0001c038e3ef
def wr5 : W := 0xef7bef7df7eec631e63cf3ef
def wr6 : W := 0xef7bef7df7eece33e67cf7ef
def wr7 : W := 0xef7bef7df7eece71e67df3ef
def wr8 : W := 0xef7bef7df7eece73ee3cf3ef
def wr9 : W := 0xef7befffffffc631e63cf3ef
def wsa : W := 0xef7ff8208108ce7ff8000000
def wsb : W := 0xef7ff8208108fffff8000000
def wsc : W := 0xef7fff7dffffc631e63cf3ef
def wsd : W := 0xefc1077f4084cfc0067f0000
def wse : W := 0xefc1077f4084ffc007ff0000
def wsf : W := 0xeffbf8208108cff3f8000000
def wsg : W := 0xeffbf8208108fffff8000000
def wsh : W := 0xeffbff7ff7ffc631e63cf3ef
def wsi : W := 0xf03c8790f840f03c0780f800
def wsj : W := 0xf03c87d0fc42f03c07c0fc00
def wsk : W := 0xf03e8790fc42f03e0780fc00
def wsl : W := 0xf5bdd7bafa71318dd1baea10
def wsm : W := 0xf5bdd7bafa71f1bdd7bafa10
def wsn : W := 0xf73de7bcfbe0c631e63cf3e0
def wso : W := 0xf73de7bcfbe0f63de7bcfbe0
def wsp : W := 0xf78107be4080f78007be0000
def wsq : W := 0xf78107ff4084f78007ff0000
def wsr : W := 0xf7add7beeab1318dd1baea10
def wss : W := 0xf7add7beeab1f78dd7beea10
def wst : W := 0xf7b9e7bef3e0c631e63cf3e0
def wsu : W := 0xf7b9e7bef3e0f7b1e7bef3e0
def wsv : W := 0xf7bdf0208100f7bdf0000000
def wsw : W := 0xf7bdf5baeb31318dd1baea10
def wsx : W := 0xf7bdf5baeb31f7bdf1baea10
def wsy : W := 0xf7bdf73cf3e0c631e63cf3e0
def wsz : W := 0xf7bdf73cf3e0f7bdf63cf3e0
def wsA : W := 0xf7bdf7befbf1318dd1baebf0
def wsB : W := 0xf7bdf7befbf1c631e63cf3e0
def wsC : W := 0xf7bdf7befbf1f7bdf7befbf0
def wsD : W := 0xf7bdf7fffff7c631e63cf3ef
def wsE : W := 0xf7bff8208108f7bff8000000
def wsF : W := 0xf7bfffbefffbc631e63cf3ef
def wsG : W := 0xf7c107bf4084f7c007bf0000
def wsH : W := 0xf7fdf8208108f7fdf8000000
def wsI : W := 0xf7fdffbffbfdc631e63cf3ef
def wsJ : W := 0xf80000000000f80000000000
def wsK : W := 0xf80007d04000f80007c00000
def wsL : W := 0xf80007d07c42f80007c0fc00
def wsM : W := 0xf80007df4084f80007ff0000
def wsN : W := 0xf80607d04c02f80e07c00c00
def wsO : W := 0xf81207d05442f83207c01400
def wsP : W := 0xf81607d07c42f80007c00000
def wsQ : W := 0xf82887d0c000f83e07c0fc00
def wsR : W := 0xf82887d0fc42f83e07c0fc00
def wsS : W := 0xf82c87d0e800f80c07c0e800
def wsT : W := 0xf82c87d0fc42f80c07c0fc00
def wsU : W := 0xf83887d0f040f83007c0f000
def wsV : W := 0xf83887d0fc42f83007c0fc00
def wsW : W := 0xf83a87d0d442f83e07c0fc00
def wsX : W := 0xf83a87d0f442f83207c0f400
def wsY : W := 0xf83e80008000f83e00000000
def wsZ : W := 0xf83e8000bc42f83e0000fc00
def ws0 : W := 0xf83e80c08c02f83e01c00c00
def ws1 : W := 0xf83e82409442f83e06401400
def ws2 : W := 0xf83e82c0bc42f83e00000000
def ws3 : W := 0xf83e8510c000f83e07c0fc00
def ws4 : W := 0xf83e8510fc42f83e07c0fc00
def ws5 : W := 0xf83e8590e800f83e0180e800
def ws6 : W := 0xf83e8590fc42f83e0180fc00
def ws7 : W := 0xf83e8710f040f83e0600f000
def ws8 : W := 0xf83e8710fc42f83e0600fc00
def ws9 : W := 0xf83e8750d442f83e07c0fc00
def wta : W := 0xf83e8750f442f83e0640f400
def wtb : W := 0xf83e87d0c000f83e07c00000
def wtc : W := 0xf83e87d0d442f83e07c01400
def wtd : W := 0xf83e87d0dc42f83e07c0fc00
def wte : W := 0xf83e87d0fc4200000000e000
def wtf : W := 0xf83e87d0fc42300c0180e800
def wtg : W := 0xf83e87d0fc42300c07c0fc00
def wth : W := 0xf83e87d0fc42303e0180fc00
def wti : W := 0xf83e87d0fc42380e01c0ec00
def wtj : W := 0xf83e87d0fc42c0300600f000
def wtk : W := 0xf83e87d0fc42c03007c0fc00
def wtl : W := 0xf83e87d0fc42c03e0600fc00
def wtm : W := 0xf83e87d0fc42c8320640f400
def wtn : W := 0xf83e87d0fc42f03c0780f800
def wto : W := 0xf83e87d0fc42f80c07c0e800
def wtp : W := 0xf83e87d0fc42f83007c0f000
def wtq : W := 0xf83e87d0fc42f83e0180e800
def wtr : W := 0xf83e87d0fc42f83e0600f000
def wts : W := 0xf83e87d0fc42f83e07c00000
def wtt : W := 0xf83e87d0fc42f83e07c0fc00
def wtu : W := 0xf83e87d0fc42f9be17c2fc10
def wtv : W := 0xf83e87d0fc42f9fe07c3fc00
def wtw : W := 0xf83e87d0fc42f9fe1fc0fc00
def wtx : W := 0xf83e87d0fc42fe3e27c4fc00
def wty : W := 0xf83e87d0fc42fe7e07c5fc00
def wtz : W := 0xf83e87d0fc42fe7e2fc0fc00
def wtA : W := 0xf83e87d0fe73f83e07c0fe10
def wtB : W := 0xf83e87d2fc53f83e07c2fc10
def wtC : W := 0xf83e87d3fc46f83e07c3fc00
def wtD : W := 0xf83e87d5fcc6f83e07c5fc00
def wtE : W := 0xf83e87dafe73f83e07c0fc00
def wtF : W := 0xf83e87dafe73f83e07fafe10
def wtG : W := 0xf83e87dcfee2f83e07fcffe0
def wtH : W := 0xf83e87dffcc6f83e07c0fc00
def wtI : W := 0xf83e87dffcc6f83e07fffc00
def wtJ : W := 0xf83e87dffef7f83e07c0fdef
def wtK : W := 0xf83e97d0fc53f83e17c0fc10
def wtL : W := 0xf83e9fd0fc4af83e1fc0fc00
def wtM : W := 0xf83eafd0fd4af83e2fc0fc00
def wtN : W := 0xf83ec7d8fe62f83e07c0fc00
def wtO : W := 0xf83ed7d0fe73f83e07c0fc00
def wtP : W := 0xf83ed7d0fe73f83fd7c0fe10
def wtQ : W := 0xf83ee7d0ff62f83fe7c0ffe0
def wtR : W := 0xf83ef8008108f83ff8000000
def wtS : W := 0xf83effd0fd4af83e07c0fc00
def wtT : W := 0xf83effd0fd4af83fffc0fc00
def wtU : W := 0xf83effd0ff7bf83e07c0fdef
def wtV : W := 0xf83effdfc18cf83fffff0000
def wtW : W := 0xf87e87d1fc46f87e07c1fc00
def wtX : W := 0xf87e8fd0fc4af87e0fc0fc00
def wtY : W := 0xf8be87d2fc42f9be07c2fc00
def wtZ : W := 0xf8be87dafc42f83e07c0fc00
def wt0 : W := 0xf8be97d0fc42f9be17c0fc00
def wt1 : W := 0xf8be97d2fc53f83e07c0fc00
def wt2 : W := 0xf8be97d2fc53f9be17c2fc10
def wt3 : W := 0xf8bed7d0fc42f83e07c0fc00
def wt4 : W := 0xf8bed7dafe73f83e07c0fc00
def wt5 : W := 0xf8bed7dafe73f9be17c2fc10
def wt6 : W := 0xf8c007d34004f9c007c30000
def wt7 : W := 0xf8fe87d0fc42f9fe07c0fc00
def wt8 : W := 0xf8fe87d3fc46f83e07c0fc00
def wt9 : W := 0xf8fe87d3fc46f9fe07c3fc00
def wua : W := 0xf8fe97d3fc57f9fe17c3fc10
def wub : W := 0xf8fe98008008f9fe18000000
def wuc : W := 0xf8fe9fd0fc4af83e07c0fc00
def wud : W := 0xf8fe9fd0fc4af9fe1fc0fc00
def wue : W := 0xf8fe9fd2fc5bf9fe1fc2fc10
def wuf : W := 0xf8fe9fd3fc4ef9fe1fc3fc00
def wug : W := 0xf8fe9fd3fc5ff83e07c0fc0f
def wuh : W := 0xfa3e87d4fcc2fe3e07c4fc00
def wui : W := 0xfa3e87dcfcc2f83e07c0fc00
def wuj : W := 0xfa3ea7d0fd42fe3e27c0fc00
def wuk : W := 0xfa3ea7d4fdc2fe3e27c4fde0
def wul : W := 0xfa3ee7d0fd42f83e07c0fc00
def wum : W := 0xfa3ee7dcffe2f83e07c0fde0
def wun : W := 0xfa4007d54084fe4007c50000
def wuo : W := 0xfa7e87d0fc42fe7e07c0fc00
def wup : W := 0xfa7e87d5fcc6f83e07c0fc00
def wuq : W := 0xfa7e87d5fcc6fe7e07c5fc00
def wur : W := 0xfa7e87d5fcc6fffe07c7fc00
def wus : W := 0xfa7ea8008108fe7e28000000
def wut : W := 0xfa7eafd0fd4af83e07c0fc00
def wuu : W := 0xfa7eafd0fd4afe7e2fc0fc00
def wuv : W := 0xfa7eafd0fd4afffe3fc0fc00
def wuw : W := 0xfa7eafd5fdcef83e07c0fdef
def wux : W := 0xfa7eafd5fdcefe7e2fc5fc00
def wuy : W := 0xfac007df4084f80007c00000
def wuz : W := 0xfad67fdf7ffff80007c001ef
def wuA : W := 0xfafe87d0fc42f83e07c0fc00
def wuB : W := 0xfafe87d7fcc6fffe07c7fc00
def wuC : W := 0xfafe87dffcc6f83e07c0fc00
def wuD : W := 0xfafe87dffcc6f9fe07c3fc00
def wuE : W := 0xfafe87dffcc6fe7e07c5fc00
def wuF : W := 0xfafe97d7fcd7fffe17c7fc10
def wuG : W := 0xfafebfd0fd4afffe3fc0fc00
def wuH : W := 0xfafebfd2fd5bfffe3fc2fc10
def wuI : W := 0xfafed7dffef7f83e07c0fc00
def wuJ : W := 0xfafef8008108f83e00000000
def wuK : W := 0xfafefacfbffff83e000001ef
def wuL : W := 0xfafeffd0fd4af83e07c0fc00
def wuM : W := 0xfafeffd0fd4af9fe1fc0fc00
def wuN : W := 0xfafeffd0fd4afe7e2fc0fc00
def wuO : W := 0xfafeffdaff7bf83e07c0fc00
def wuP : W := 0xfafeffdffdcef83e07c0fc00
def wuQ : W := 0xfafeffdfffff300c0180e9ef
def wuR : W := 0xfafeffdfffffc0300600f1ef
def wuS : W := 0xfafeffdffffff83e07c0fdef
def wuT : W := 0xfd0107f04000ffc007ff0000
def wuU : W := 0xfd0107ff4084ffc007ff0000
def wuV : W := 0xfd3f80208000fffff8000000
def wuW : W := 0xfd3f87f0fc42c631e63cf200
def wuX : W := 0xfd3f87f0fc42f9bfd7fafe10
def wuY : W := 0xfd3f87f0fc42fe3fe7fcfe00
def wuZ : W := 0xfd3f87f0fc42fffe07c0fc00
def wu0 : W := 0xfd3f87f0fc42fffe07fffc00
def wu1 : W := 0xfd3f87f0fc42ffffffc0fc00
def wu2 : W := 0xfd3fc7f8fe620001c038e200
def wu3 : W := 0xfd3fc7f8fe62f83fc7f8fe00
def wu4 : W := 0xfd3ff8208108fffff8000000
def wu5 : W := 0xfd8107fa4000f98007fa0000
def wu6 : W := 0xfd8107ff4084f98007ff0000
def wu7 : W := 0xfdadd7faea31318dd1baea10
def wu8 : W := 0xfdadd7faea31f98dd7faea10
def wu9 : W := 0xfdbf87f0fc42f9be07c0fc00
def wva : W := 0xfdbf87fafc42f9be07fafc00
def wvb : W := 0xfdbfd0208000f9bfd0000000
def wvc : W := 0xfdbfd5baea31318dd1baea10
def wvd : W := 0xfdbfd5baea31f9bfd1baea10
def wve : W := 0xfdbfd7f0fc42f9bfd7c0fc00
def wvf : W := 0xfdbfd7fafe730001c038e200
def wvg : W := 0xfdbfd7fafe73318dd1baea10
def wvh : W := 0xfdbfd7fafe73398fd1faee10
def wvi : W := 0xfdbfd7fafe73c031c638f200
def wvj : W := 0xfdbfd7fafe73f83fc7f8fe00
def wvk : W := 0xfdbfd7fafe73f9bfd7fafe10
def wvl : W := 0xfdbff8208108f9bff8000000
def wvm : W := 0xff0107fc4080fe0007fc0000
def wvn : W := 0xff0107ff4084fe0007ff0000
def wvo : W := 0xff39e7fcf3e0c631e63cf3e0
def wvp : W := 0xff39e7fcf3e0fe31e7fcf3e0
def wvq : W := 0xff3f87f0fc42fe3e07c0fc00
def wvr : W := 0xff3f87fcfcc2fe3e07fcfc00
def wvs : W := 0xff3fe0208100fe3fe0000000
def wvt : W := 0xff3fe73cf3e0c631e63cf3e0
def wvu : W := 0xff3fe73cf3e0fe3fe63cf3e0
def wvv : W := 0xff3fe7f0fd42fe3fe7c0fc00
def wvw : W := 0xff3fe7fcffe2c631e63cf3e0
def wvx : W := 0xff3fe7fcffe2ce33e67cf7e0
def wvy : W := 0xff3fe7fcffe2fe3fe7fcffe0
def wvz : W := 0xff3fe7fffff7c631e63cf3ef
def wvA : W := 0xff3ff8208108fe3ff8000000
def wvB : W := 0xff3ffffcfffbc631e63cf3ef
def wvC : W := 0xff4107f54084ffc007ff0000
def wvD : W := 0xff4107fd4084fe4007fd0000
def wvE : W := 0xff7fa8208108fffff8000000
def wvF : W := 0xff7fe8208108fe7fe8000000
def wvG : W := 0xff7feffdffeec631e63cf3ef
def wvH : W := 0xffbff7fefff3c631e63cf3e0
def wvI : W := 0xffbff7fefff3ffbff7fefff0
def wvJ : W := 0xffc100200000ffc000000000
def wvK : W := 0xffc1002f0084ffc0003f0000
def wvL : W := 0xffc100e30004ffc001c30000
def wvM : W := 0xffc102650084ffc006450000
def wvN : W := 0xffc102ef0084ffc000000000
def wvO : W := 0xffc105304000ffc007ff0000
def wvP : W := 0xffc1053f4084ffc007ff0000
def wvQ : W := 0xffc105ba4000ffc001ba0000
def wvR : W := 0xffc105bf4084ffc001bf0000
def wvS : W := 0xffc1073c4080ffc0063c0000
def wvT : W := 0xffc1073f4084ffc0063f0000
def wvU : W := 0xffc107754084ffc007ff0000
def wvV : W := 0xffc1077d4084ffc0067d0000
def wvW : W := 0xffc107f04000ffc007c00000
def wvX : W := 0xffc107f54084ffc007c50000
def wvY : W := 0xffc107f74084ffc007ff0000
def wvZ : W := 0xffc107ff4084000000380000
def wv0 : W := 0xffc107ff4084318001ba0000
def wv1 : W := 0xffc107ff4084318007ff0000
def wv2 : W := 0xffc107ff408437c001bf0000
def wv3 : W := 0xffc107ff408439c001fb0000
def wv4 : W := 0xffc107ff4084c600063c0000
def wv5 : W := 0xffc107ff4084c60007ff0000
def wv6 : W := 0xffc107ff4084c7c0063f0000
def wv7 : W := 0xffc107ff4084ce40067d0000
def wv8 : W := 0xffc107ff4084f78007be0000
def wv9 : W := 0xffc107ff4084f98007fa0000
def wwa : W := 0xffc107ff4084fe0007fc0000
def wwb : W := 0xffc107ff4084ffc001ba0000
def wwc : W := 0xffc107ff4084ffc0063c0000
def wwd : W := 0xffc107ff4084ffc007c00000
def wwe : W := 0xffc107ff4084ffc007ff0000
def wwf : W := 0xffc107ff4084ffcc17ff0810
def wwg : W := 0xffc107ff4084ffce07ff0c00
def wwh : W := 0xffc107ff4084ffce1fff0000
def wwi : W := 0xffc107ff4084fff027ff1000
def wwj : W := 0xffc107ff4084fff207ff1400
def wwk : W := 0xffc107ff4084fff22fff0000
def wwl : W := 0xffc107ff42b5ffc007ff0210
def wwm : W := 0xffc107ff4895ffc007ff0810
def wwn : W := 0xffc107ff4c86ffc007ff0c00
def wwo : W := 0xffc107ff54c6ffc007ff1400
def wwp : W := 0xffc107ff6ab5ffc007ff0000
def wwq : W := 0xffc107ff6ab5ffc007ffea10
def wwr : W := 0xffc107ff72e4ffc007fff3e0
def wws : W := 0xffc107ff7cc6ffc007ff0000
def wwt : W := 0xffc107ff7cc6ffc007fffc00
def wwu : W := 0xffc107ff7ef7ffc007ff01ef
def wwv : W := 0xffc117ff4095ffc017ff0010
def www : W := 0xffc11fff408cffc01fff0000
def wwx : W := 0xffc12fff418cffc02fff0000
def wwy : W := 0xffc147ff62a4ffc007ff0000
def wwz : W := 0xffc157ff42b5ffc007ff0000
def wwA : W := 0xffc157ff42b5ffc1d7ff0210
def wwB : W := 0xffc167ff43a4ffc1e7ff03e0
def wwC : W := 0xffc178200108ffc1f8000000
def wwD : W := 0xffc17ff07d4affc1ffc0fc00
def wwE : W := 0xffc17fff418cffc007ff0000
def wwF : W := 0xffc17fff418cffc1ffff0000
def wwG : W := 0xffc17fff43bdffc007ff01ef
def wwH : W := 0xffc307ff4486ffc207ff0400
def wwI : W := 0xffc30fff408cffc20fff0000
def wwJ : W := 0xffc507ff4884ffcc07ff0800
def wwK : W := 0xffc507ff6884ffc007ff0000
def wwL : W := 0xffc517ff4084ffcc17ff0000
def wwM : W := 0xffc517ff4895ffc007ff0000
def wwN : W := 0xffc517ff4895ffcc17ff0810
def wwO : W := 0xffc557ff4084ffc007ff0000
def wwP : W := 0xffc557ff6ab5ffc007ff0000
def wwQ : W := 0xffc557ff6ab5ffcc17ff0810
def wwR : W := 0xffc707ff4084ffce07ff0000
def wwS : W := 0xffc707ff4c86ffc007ff0000
def wwT : W := 0xffc707ff4c86ffce07ff0c00
def wwU : W := 0xffc717ff4c97ffce17ff0c10
def wwV : W := 0xffc718200008ffce18000000
def wwW : W := 0xffc71fff408cffc007ff0000
def wwX : W := 0xffc71fff408cffce1fff0000
def wwY : W := 0xffc71fff489dffce1fff0810
def wwZ : W := 0xffc71fff4c8effce1fff0c00
def ww0 : W := 0xffc71fff4c9fffc007ff000f
def ww1 : W := 0xffd107ff50c4fff007ff1000
def ww2 : W := 0xffd107ff70c4ffc007ff0000
def ww3 : W := 0xffd127ff4184fff027ff0000
def ww4 : W := 0xffd127ff51c4fff027ff11e0
def ww5 : W := 0xffd167ff4184ffc007ff0000
def ww6 : W := 0xffd167ff73e4ffc007ff01e0
def ww7 : W := 0xffd307ff4084fff207ff0000
def ww8 : W := 0xffd307ff54c6ffc007ff0000
def ww9 : W := 0xffd307ff54c6fff207ff1400
def wxa : W := 0xffd307ff54c6fffe07ff1c00
def wxb : W := 0xffd328200108fff228000000
def wxc : W := 0xffd32fff418cffc007ff0000
def wxd : W := 0xffd32fff418cfff22fff0000
def wxe : W := 0xffd32fff418cfffe3fff0000
def wxf : W := 0xffd32fff55ceffc007ff01ef
def wxg : W := 0xffd32fff55cefff22fff1400
def wxh : W := 0xffd707ff4084ffc007ff0000
def wxi : W := 0xffd707ff5cc6fffe07ff1c00
def wxj : W := 0xffd707ff7cc6ffc007ff0000
def wxk : W := 0xffd707ff7cc6ffce07ff0c00
def wxl : W := 0xffd707ff7cc6fff207ff1400
def wxm : W := 0xffd717ff5cd7fffe17ff1c10
def wxn : W := 0xffd73fff418cfffe3fff0000
def wxo : W := 0xffd73fff499dfffe3fff0810
def wxp : W := 0xffd757ff7ef7ffc007ff0000
def wxq : W := 0xffd778200108ffc000000000
def wxr : W := 0xffd77aef3fffffc0000001ef
def wxs : W := 0xffd77fff418cffc007ff0000
def wxt : W := 0xffd77fff418cffce1fff0000
def wxu : W := 0xffd77fff418cfff22fff0000
def wxv : W := 0xffd77fff6bbdffc007ff0000
def wxw : W := 0xffd77fff7dceffc007ff0000
def wxx : W := 0xffd77fff7fff318001ba01ef
def wxy : W := 0xffd77fff7fffc600063c01ef
def wxz : W := 0xffd77fff7fffffc007ff01ef
def wxA : W := 0xffe980208000fffff8000000
def wxB : W := 0xffe987ffc084c631e63cf200
def wxC : W := 0xffe987ffc084ffcdd7ffea10
def wxD : W := 0xffe987ffc084fff1e7fff200
def wxE : W := 0xffe987ffc084fffe07ff0000
def wxF : W := 0xffe987ffc084fffe07fffc00
def wxG : W := 0xffe987ffc084ffffffff0000
def wxH : W := 0xffe9c7ffe2a40001c038e200
def wxI : W := 0xffe9c7ffe2a4ffc1c7ffe200
def wxJ : W := 0xffe9f8208108fffff8000000
def wxK : W := 0xffed87ffc084ffcc07ff0000
def wxL : W := 0xffed87ffe884ffcc07ffe800
def wxM : W := 0xffedd0208000ffcdd0000000
def wxN : W := 0xffedd5baea31318dd1baea10
def wxO : W := 0xffedd5baea31ffcdd1baea10
def wxP : W := 0xffedd7ffc084ffcdd7ff0000
def wxQ : W := 0xffedd7ffeab50001c038e200
def wxR : W := 0xffedd7ffeab5318dd1baea10
def wxS : W := 0xffedd7ffeab539cdd1fbea10
def wxT : W := 0xffedd7ffeab5c601c63ce200
def wxU : W := 0xffedd7ffeab5ffc1c7ffe200
def wxV : W := 0xffedd7ffeab5ffcdd7ffea10
def wxW : W := 0xffedf8208108ffcdf8000000
def wxX : W := 0xfff987ffc084fff007ff0000
def wxY : W := 0xfff987fff0c4fff007fff000
def wxZ : W := 0xfff9e0208100fff1e0000000
def wx0 : W := 0xfff9e73cf3e0c631e63cf3e0
def wx1 : W := 0xfff9e73cf3e0fff1e63cf3e0
def wx2 : W := 0xfff9e7ffc184fff1e7ff0000
def wx3 : W := 0xfff9e7fff3e4c631e63cf3e0
def wx4 : W := 0xfff9e7fff3e4ce71e67df3e0
def wx5 : W := 0xfff9e7fff3e4fff1e7fff3e0
def wx6 : W := 0xfff9e7fffff7c631e63cf3ef
def wx7 : W := 0xfff9f8208108fff1f8000000
def wx8 : W := 0xfff9fffff3fdc631e63cf3ef
def wx9 : W := 0xfffba8208108fffff8000000
def wya : W := 0xfffbe8208108fff3e8000000
def wyb : W := 0xfffbeffff7eec631e63cf3ef
def wyc : W := 0xfffdf7fffbf5c631e63cf3e0
def wyd : W := 0xfffdf7fffbf5fffdf7fffbf0
def wye : W := 0xffff80208000fffe00000000
def wyf : W := 0xffff802fbcc6fffe003ffc00
def wyg : W := 0xffff87f0fc42c6300600f000
def wyh : W := 0xffff87f0fc42fffe07c0fc00
def wyi : W := 0xffff87f3fc46fffe07c3fc00
def wyj : W := 0xffff87f5fcc6fffe07c5fc00
def wyk : W := 0xffff87ffc084c630063c0000
def wyl : W := 0xffff87ffc084fffe07ff0000
def wym : W := 0xffff87ffcc86fffe07ff0c00
def wyn : W := 0xffff87ffd4c6fffe07ff1400
def wyo : W := 0xffff87fffcc6c630063cf000
def wyp : W := 0xffff87fffcc6fffe07c0fc00
def wyq : W := 0xffff87fffcc6fffe07ff0000
def wyr : W := 0xffff87fffcc6fffe07fffc00
def wys : W := 0xffff9ff0fc4afffe1fc0fc00
def wyt : W := 0xffff9fffc08cfffe1fff0000
def wyu : W := 0xffffa8208108fffe28000000
def wyv : W := 0xffffaff0fd4afffe2fc0fc00
def wyw : W := 0xffffafffc18cfffe2fff0000
def wyx : W := 0xffffb8208108fffff8000000
def wyy : W := 0xffffbff7dddf0001c038e3ef
def wyz : W := 0xffffd7fffef7318dd1baea10
def wyA : W := 0xffffd7fffef7ffffd7fffe10
def wyB : W := 0xffffe7ffffe6c631e63cf3e0
def wyC : W := 0xffffe7ffffe6ffffe7ffffe0
def wyD : W := 0xfffff82081080001c0000000
def wyE : W := 0xfffff8208108318dd0000000
def wyF : W := 0xfffff820810831bff8000000
def wyG : W := 0xfffff820810837cdf8000000
def wyH : W := 0xfffff820810839cfd8000000
def wyI : W := 0xfffff8208108c631e0000000
def wyJ : W := 0xfffff8208108c63ff8000000
def wyK : W := 0xfffff8208108c7f1f8000000
def wyL : W := 0xfffff8208108ce73e8000000
def wyM : W := 0xfffff8208108f7bdf0000000
def wyN : W := 0xfffff8208108f9bfd0000000
def wyO : W := 0xfffff8208108fe3fe0000000
def wyP : W := 0xfffff8208108ffcdd0000000
def wyQ : W := 0xfffff8208108fff1e0000000
def wyR : W := 0xfffff8208108fffe00000000
def wyS : W := 0xfffff8208108fffff8000000
def wyT : W := 0xfffff8208108fffff9820810
def wyU : W := 0xfffff8208108fffff9c00c00
def wyV : W := 0xfffff8208108fffff9c30000
def wyW : W := 0xfffff8208108fffffe041000
def wyX : W := 0xfffff8208108fffffe401400
def wyY : W := 0xfffff8208108fffffe450000
def wyZ : W := 0xfffff8208339fffff8000210
def wy0 : W := 0xfffff8208919fffff8000810
def wy1 : W := 0xfffff8208d0afffff8000c00
def wy2 : W := 0xfffff820954afffff8001400
def wy3 : W := 0xfffff820ab39fffff8000000
def wy4 : W := 0xfffff820ab39fffff800ea10
def wy5 : W := 0xfffff820b368fffff800f3e0
def wy6 : W := 0xfffff820bd4afffff8000000
def wy7 : W := 0xfffff820bd4afffff800fc00
def wy8 : W := 0xfffff820bf7bfffff80001ef
def wy9 : W := 0xfffff8228119fffff8020010
def wza : W := 0xfffff823810cfffff8030000
def wzb : W := 0xfffff825818cfffff8050000
def wzc : W := 0xfffff828a328fffff8000000
def wzd : W := 0xfffff82a8339fffff8000000
def wze : W := 0xfffff82a8339fffff83a0210
def wzf : W := 0xfffff82c83a8fffff83c03e0
def wzg : W := 0xfffff82f818cfffff8000000
def wzh : W := 0xfffff82f818cfffff83f0000
def wzi : W := 0xfffff82f83bdfffff80001ef
def wzj : W := 0xfffff860850afffff8400400
def wzk : W := 0xfffff861810cfffff8410000
def wzl : W := 0xfffff8a08908fffff9800800
def wzm : W := 0xfffff8a0a908fffff8000000
def wzn : W := 0xfffff8a28108fffff9820000
def wzo : W := 0xfffff8a28919fffff8000000
def wzp : W := 0xfffff8a28919fffff9820810
def wzq : W := 0xfffff8aa8108fffff8000000
def wzr : W := 0xfffff8aaab39fffff8000000
def wzs : W := 0xfffff8aaab39fffff9820810
def wzt : W := 0xfffff8e08108fffff9c00000
def wzu : W := 0xfffff8e08d0afffff8000000
def wzv : W := 0xfffff8e08d0afffff9c00c00
def wzw : W := 0xfffff8e28d1bfffff9c20c10
def wzx : W := 0xfffff8e3810cfffff8000000
def wzy : W := 0xfffff8e3810cfffff9c30000
def wzz : W := 0xfffff8e3891dfffff9c30810
def wzA : W := 0xfffff8e38d0efffff9c30c00
def wzB : W := 0xfffff8e38d1ffffff800000f
def wzC : W := 0xfffffa209148fffffe001000
def wzD : W := 0xfffffa20b148fffff8000000
def wzE : W := 0xfffffa248188fffffe040000
def wzF : W := 0xfffffa2491c8fffffe0411e0
def wzG : W := 0xfffffa2c8188fffff8000000
def wzH : W := 0xfffffa2cb3e8fffff80001e0
def wzI : W := 0xfffffa608108fffffe400000
def wzJ : W := 0xfffffa60954afffff8000000
def wzK : W := 0xfffffa60954afffffe401400
def wzL : W := 0xfffffa60954affffffc01c00
def wzM : W := 0xfffffa65818cfffff8000000
def wzN : W := 0xfffffa65818cfffffe450000
def wzO : W := 0xfffffa65818cffffffc70000
def wzP : W := 0xfffffa6595cefffff80001ef
def wzQ : W := 0xfffffa6595cefffffe451400
def wzR : W := 0xfffffae08108fffff8000000
def wzS : W := 0xfffffae09d4affffffc01c00
def wzT : W := 0xfffffae0bd4afffff8000000
def wzU : W := 0xfffffae0bd4afffff9c00c00
def wzV : W := 0xfffffae0bd4afffffe401400
def wzW : W := 0xfffffae29d5bffffffc21c10
def wzX : W := 0xfffffae7818cffffffc70000
def wzY : W := 0xfffffae7899dffffffc70810
def wzZ : W := 0xfffffaeabf7bfffff8000000
def wz0 : W := 0xfffffaef818cfffff8000000
def wz1 : W := 0xfffffaef818cfffff9c30000
def wz2 : W := 0xfffffaef818cfffffe450000
def wz3 : W := 0xfffffaefabbdfffff8000000
def wz4 : W := 0xfffffaefbdcefffff8000000
def wz5 : W := 0xfffffaefbfff318dd00001ef
def wz6 : W := 0xfffffaefbfffc631e00001ef
def wz7 : W := 0xfffffaefbffffffff80001ef
def wz8 : W := 0xfffffd30c108c631e63cf200
def wz9 : W := 0xfffffd30c108fffff9baea10
def wAa : W := 0xfffffd30c108fffffe3cf200
def wAb : W := 0xfffffd30c108ffffffc00000
def wAc : W := 0xfffffd30c108ffffffc0fc00
def wAd : W := 0xfffffd30c108ffffffff0000
def wAe : W := 0xfffffd38e3280001c038e200
def wAf : W := 0xfffffd38e328fffff838e200
def wAg : W := 0xfffffdb0c108fffff9800000
def wAh : W := 0xfffffdb0e908fffff980e800
def wAi : W := 0xfffffdbac108fffff9ba0000
def wAj : W := 0xfffffdbaeb390001c038e200
def wAk : W := 0xfffffdbaeb39318dd1baea10
def wAl : W := 0xfffffdbaeb3939cfd9baea10
def wAm : W := 0xfffffdbaeb39c631e038e200
def wAn : W := 0xfffffdbaeb39fffff838e200
def wAo : W := 0xfffffdbaeb39fffff9baea10
def wAp : W := 0xffffff30c108fffffe000000
def wAq : W := 0xffffff30f148fffffe00f000
def wAr : W := 0xffffff3cc188fffffe3c0000
def wAs : W := 0xffffff3cf3e8c631e63cf3e0
def wAt : W := 0xffffff3cf3e8ce73ee3cf3e0
def wAu : W := 0xffffff3cf3e8fffffe3cf3e0
def wAv : W := 0xffffff3cfffbc631e63cf3ef
def wAw : W := 0xffffff3ff3fdc631e63cf3ef
def wAx : W := 0xffffff7df7eec631e63cf3ef
def wAy : W := 0xffffffbefbf9c631e63cf3e0
def wAz : W := 0xffffffbefbf9ffffffbefbf0
def wAA : W := 0xfffffff0c108c631e6000000
def wAB : W := 0xfffffff0c108ffffffc00000
def wAC : W := 0xfffffff0cd0affffffc00c00
def wAD : W := 0xfffffff0d54affffffc01400
def wAE : W := 0xfffffff0fd4ac631e600f000
def wAF : W := 0xfffffff0fd4afffe07c0fc00
def wAG : W := 0xfffffff0fd4affffffc00000
def wAH : W := 0xfffffff0fd4affffffc0fc00
def wAI : W := 0xfffffff3c10cffffffc30000
def wAJ : W := 0xfffffff5c18cffffffc50000
def wAK : W := 0xfffffffaff7b318dd1baea10
def wAL : W := 0xfffffffaff7bfffffffafe10
def wAM : W := 0xfffffffcffeac631e63cf3e0
def wAN : W := 0xfffffffcffeafffffffcffe0
def wAO : W := 0xffffffffc18cc631e63c0000
def wAP : W := 0xffffffffc18cfffe07ff0000
def wAQ : W := 0xffffffffc18cffffffc00000
def wAR : W := 0xffffffffc18cffffffff0000
def wAS : W := 0xffffffffebbd318dd1baea10
def wAT : W := 0xffffffffebbdffffffffea10
def wAU : W := 0xfffffffff3ecc631e63cf3e0
def wAV : W := 0xfffffffff3ecfffffffff3e0
def wAW : W := 0xfffffffffdcefffffffffc00
def wAX : W := 0xffffffffffff0001c038e3ef
def wAY : W := 0xffffffffffff0001c63cf3ef
def wAZ : W := 0xffffffffffff0031e038f3ef
def wA0 : W := 0xffffffffffff0601e03ce3ef
def wA1 : W := 0xffffffffffff318dd1baebff
def wA2 : W := 0xffffffffffffc031c638f3ef
def wA3 : W := 0xffffffffffffc601c63ce3ef
def wA4 : W := 0xffffffffffffc630063cf1ef
def wA5 : W := 0xffffffffffffc631e038e3ef
def wA6 : W := 0xffffffffffffc631e600f1ef
def wA7 : W := 0xffffffffffffc631e63c01ef
def wA8 : W := 0xffffffffffffc631e63cf3ef
def wA9 : W := 0xffffffffffffce33e67cf7ef
def wBa : W := 0xffffffffffffce71e67df3ef
def wBb : W := 0xffffffffffffce73ee3cf3ef
def wBc : W := 0xfffffffffffff7bdf7befbff
def wBd : W := 0xfffffffffffff9bfd7faffff
def wBe : W := 0xfffffffffffffe3fe7fcffef
def wBf : W := 0xffffffffffffffcdd7ffebff
def wBg : W := 0xfffffffffffffff1e7fff3ef
def wBh : W := 0xfffffffffffffffe07fffdef
def wBi : W := 0xfffffffffffffffff9baebff
def wBj : W := 0xfffffffffffffffffe3cf3ef
def wBk : W := 0xffffffffffffffffffc0fdef
def wBl : W := 0xffffffffffffffffffff01ef

def ins : List W := [wg6,wmE,wp6,wtt,wwe,wyS]
theorem sampled : ∀ j : Fin 96, Nat.testBit 0xeaeaeaaaeaaaaa88 (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
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
def level3 : BinaryTree (List W) := (.node [wg6,wmE,wqx,wyl] (.node [wg6,wjA,wyr,wAB] (.node [wcJ,wg6,wmr,wyS] (.node [wcF,wg6,wjz,wwe] (.node [wbw,wg6,wmr,wtt] (.node [wbw,wg6,wjw,wtt] .nil .nil) .nil) (.node [wcJ,wg6,wjQ,wyS] (.node [wcF,wg6,wmr,wwe] .nil .nil) .nil)) (.node [wfW,wg6,wwe,wyS] (.node [wfR,wg6,wtt,wyS] (.node [wfM,wg6,wtt,wwe] .nil .nil) .nil) (.node [wg6,wjz,wyl,wAH] (.node [wg6,wjw,wyh,wAR] .nil .nil) .nil))) (.node [wg6,wmr,wyr,wAB] (.node [wg6,wjS,wyh,wAR] (.node [wg6,wjR,wyl,wAH] (.node [wg6,wjQ,wyr,wAB] .nil .nil) .nil) (.node [wg6,wmr,wyl,wAH] (.node [wg6,wmr,wyh,wAR] .nil .nil) .nil)) (.node [wg6,wmE,wpf,wAB] (.node [wg6,wmE,wpe,wAH] (.node [wg6,wmE,wo9,wAR] .nil .nil) .nil) (.node [wg6,wmE,wqw,wyr] .nil .nil)))) (.node [wg6,wmE,wyo,wAB] (.node [wg6,wmE,wr0,wyl] (.node [wg6,wmE,wrI,wAH] (.node [wg6,wmE,wrH,wAR] (.node [wg6,wmE,wqA,wyh] .nil .nil) .nil) (.node [wg6,wmE,wrZ,wyr] (.node [wg6,wmE,wrJ,wAB] .nil .nil) .nil)) (.node [wg6,wmE,wyh,wAO] (.node [wg6,wmE,wyg,wAR] (.node [wg6,wmE,wr2,wyh] .nil .nil) .nil) (.node [wg6,wmE,wyl,wAE] (.node [wg6,wmE,wyk,wAH] .nil .nil) .nil))) (.node [wiq,wjC,wtt,wwe] (.node [wia,wmr,wwe,wyS] (.node [wia,wkt,wwe,wyS] (.node [wg6,wmE,wyr,wAA] .nil .nil) .nil) (.node [wim,wmr,wtt,wyS] (.node [wim,wjZ,wtt,wyS] .nil .nil) .nil)) (.node [wt4,wwe,wzr,wAX] (.node [wtt,wwP,wzr,wAX] (.node [wiq,wmr,wtt,wwe] .nil .nil) .nil) (.node [wt4,wwP,wyS,wAX] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level3_ok : everyKey (rowOK 2 level2) level3 = true := by decide +kernel
theorem closed3 : Closed 3 level3 := closed_next 2 (by decide) level3 level2 closed2 level3_ok
def level4lllll : BinaryTree (List W) := (.node [wT,wg6,wjl,wuL,wwe] (.node [wT,wgL,wg6,wtt,wwe] (.node [wP,wgJ,wg6,wtt,wwe] (.node [wK,wip,wjC,wtt,wwe] (.node [wb,wrP,wtt,wwe,wyS] .nil .nil) (.node [wK,wip,wmr,wtt,wwe] .nil .nil)) (.node [wT,wgJ,wg6,wtt,wwe] (.node [wS,wft,wg6,wtt,wwe] .nil .nil) .nil)) (.node [wT,wg6,wjl,wtt,wxs] (.node [wT,wg6,wjl,wtt,wxd] (.node [wT,wgM,wg6,wtt,wwe] .nil .nil) (.node [wT,wg6,wjl,wtt,wxn] .nil .nil)) (.node [wT,wg6,wjl,wuG,wwe] (.node [wT,wg6,wjl,wuu,wwe] .nil .nil) .nil))) (.node [wY,wg6,wjF,wud,wwe] (.node [wT,wg6,wmW,wtt,wwe] (.node [wT,wg6,wjK,wuu,wwe] (.node [wT,wg6,wjK,wtt,wxd] .nil .nil) (.node [wT,wg6,wjM,wtt,wwe] .nil .nil)) (.node [wY,wg6,wjF,wtt,wwX] (.node [wT,wg6,wtt,wwe,wAe] .nil .nil) .nil)) (.node [w1,wp6,wrP,wtt,wwe] (.node [w0,wg6,wkt,wtt,wwe] (.node [wZ,wg6,wjZ,wtt,wwe] .nil .nil) .nil) (.node [w3,wg6,wjl,wtt,wwe] (.node [w2,wg6,wjl,wtt,wwe] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lllll_ok : everyKey (rowOK 3 level3) level4lllll = true := by decide +kernel
def level4llllr : BinaryTree (List W) := (.node [waf,wg6,wmu,wtt,wwe] (.node [waf,wcv,wg6,wmr,wwe] (.node [wae,wg6,wmr,wtt,wwe] (.node [wad,wdl,wtt,wwe,wAX] (.node [w9,wbg,wg6,wmr,wtt] .nil .nil) (.node [wad,wg6,wmr,wtt,wwe] .nil .nil)) (.node [waf,wbm,wg6,wmr,wtt] (.node [wae,wp6,wrP,wtt,wwe] .nil .nil) .nil)) (.node [waf,wg6,wmr,wtj,wwe] (.node [waf,wg6,wjF,wtt,wwe] (.node [waf,wg6,wjC,wtt,wwe] .nil .nil) .nil) (.node [waf,wg6,wmr,wtt,wwe] (.node [waf,wg6,wmr,wtt,wv4] .nil .nil) .nil))) (.node [waH,wie,wjZ,wtt,wyS] (.node [waj,wg6,wmr,wtt,wwe] (.node [waf,wmE,wnQ,wtt,wwe] (.node [waf,wg6,wmE,wtj,wv4] .nil .nil) (.node [wag,wg6,wmr,wtt,wwe] .nil .nil)) (.node [wao,wg6,wmE,wtt,wwe] (.node [wam,wg6,wmr,wtt,wwe] .nil .nil) .nil)) (.node [waS,wfn,wg6,wtt,wyS] (.node [waO,wgx,wg6,wtt,wyS] (.node [waH,wie,wmr,wtt,wyS] .nil .nil) .nil) (.node [waT,wgF,wg6,wtt,wyS] (.node [waT,wgx,wg6,wtt,wyS] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llllr_ok : everyKey (rowOK 3 level3) level4llllr = true := by decide +kernel
def level4llll : BinaryTree (List W) := .node [w6,wcp,wg6,wmr,wwe] level4lllll level4llllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llll_ok : everyKey (rowOK 3 level3) level4llll = true := by
  change (_ && everyKey (rowOK 3 level3) level4lllll && everyKey (rowOK 3 level3) level4llllr) = true
  rw [level4lllll_ok, level4llllr_ok]
  decide +kernel
def level4lllrl : BinaryTree (List W) := (.node [wa0,wg6,wj2,wtt,wzy] (.node [waT,wg6,wkf,wtt,wzN] (.node [waT,wg6,wjl,wuq,wyS] (.node [waT,wg6,wjl,wtt,wzX] (.node [waT,wg6,wjl,wtt,wzN] .nil .nil) (.node [waT,wg6,wjl,wtt,wz0] .nil .nil)) (.node [waT,wg6,wjl,wuC,wyS] (.node [waT,wg6,wjl,wuB,wyS] .nil .nil) .nil)) (.node [waT,wg6,wnb,wtt,wyS] (.node [waT,wg6,wkp,wtt,wyS] (.node [waT,wg6,wkf,wuq,wyS] .nil .nil) .nil) (.node [waV,wg6,wjl,wtt,wAR] (.node [waT,wg6,wtt,wxH,wyS] .nil .nil) .nil))) (.node [wa9,wci,wg6,wmr,wyS] (.node [wa4,wp6,wrP,wtt,wyS] (.node [wa1,wg6,wjC,wtt,wyS] (.node [wa0,wg6,wj2,wt9,wyS] .nil .nil) (.node [wa3,wg6,wkt,wtt,wyS] .nil .nil)) (.node [wa6,wg6,wjl,wtt,wyS] (.node [wa5,wg6,wjl,wtt,wyS] .nil .nil) .nil)) (.node [wbk,wdl,wtt,wyS,wAX] (.node [wbd,wg6,wmr,wwe,wyS] (.node [wbd,wbw,wg6,wmE,wp6] .nil .nil) .nil) (.node [wbl,wg6,wmr,wtt,wyS] (.node [wbk,wg6,wmr,wtt,wyS] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lllrl_ok : everyKey (rowOK 3 level3) level4lllrl = true := by decide +kernel
def level4lllrr : BinaryTree (List W) := (.node [wbv,wg6,wmE,wtt,wyS] (.node [wbm,wg6,wmw,wtt,wyS] (.node [wbm,wg6,wmr,wtj,wyS] (.node [wbm,wg6,wjZ,wtt,wyS] (.node [wbm,wcv,wg6,wmr,wyS] .nil .nil) (.node [wbm,wg6,wj2,wtt,wyS] .nil .nil)) (.node [wbm,wg6,wmr,wtt,wyS] (.node [wbm,wg6,wmr,wtt,wyI] .nil .nil) .nil)) (.node [wbn,wg6,wmr,wtt,wyS] (.node [wbm,wmE,wnQ,wtt,wyS] (.node [wbm,wg6,wmE,wtj,wyI] .nil .nil) .nil) (.node [wbt,wg6,wmr,wtt,wyS] (.node [wbq,wg6,wmr,wtt,wyS] .nil .nil) .nil))) (.node [wbw,wg6,wmE,wp6,wyh] (.node [wbw,wg6,wjl,wmE,wtt] (.node [wbw,wem,wg6,wmE,wtt] (.node [wbw,wc2,wg6,wmE,wtt] .nil .nil) (.node [wbw,wg6,wiC,wmE,wtt] .nil .nil)) (.node [wbw,wg6,wmE,wp6,wtt] (.node [wbw,wg6,wmE,wpP,wtt] .nil .nil) .nil)) (.node [wbK,whW,wmr,wwe,wyS] (.node [wbK,whW,wkt,wwe,wyS] (.node [wbw,wg6,wmE,wtt,wA8] .nil .nil) .nil) (.node [wbX,wff,wg6,wwe,wyS] (.node [wbS,wgh,wg6,wwe,wyS] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lllrr_ok : everyKey (rowOK 3 level3) level4lllrr = true := by decide +kernel
def level4lllr : BinaryTree (List W) := .node [wbl,wp6,wrP,wtt,wyS] level4lllrl level4lllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lllr_ok : everyKey (rowOK 3 level3) level4lllr = true := by
  change (_ && everyKey (rowOK 3 level3) level4lllrl && everyKey (rowOK 3 level3) level4lllrr) = true
  rw [level4lllrl_ok, level4lllrr_ok]
  decide +kernel
def level4lll : BinaryTree (List W) := .node [waT,wgM,wg6,wtt,wyS] level4llll level4lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lll_ok : everyKey (rowOK 3 level3) level4lll = true := by
  change (_ && everyKey (rowOK 3 level3) level4llll && everyKey (rowOK 3 level3) level4lllr) = true
  rw [level4llll_ok, level4lllr_ok]
  decide +kernel
def level4llrll : BinaryTree (List W) := (.node [wb0,wg6,wjl,wwe,wAH] (.node [wbY,wg6,wjl,wxi,wyS] (.node [wbY,wg6,wjl,wwe,wzS] (.node [wbY,wgL,wg6,wwe,wyS] (.node [wbY,wgF,wg6,wwe,wyS] .nil .nil) (.node [wbY,wg6,wjl,wwe,wzK] .nil .nil)) (.node [wbY,wg6,wjl,ww9,wyS] (.node [wbY,wg6,wjl,wwe,wzT] .nil .nil) .nil)) (.node [wbY,wg6,wk4,wwe,wyS] (.node [wbY,wg6,wkM,wwe,wzK] (.node [wbY,wg6,wjl,wxj,wyS] .nil .nil) (.node [wbY,wg6,wkM,ww9,wyS] .nil .nil)) (.node [wbY,wg6,wu2,wwe,wyS] (.node [wbY,wg6,wnt,wwe,wyS] .nil .nil) .nil))) (.node [wce,wg6,wjl,wwe,wyS] (.node [wb8,wg6,wjC,wwe,wyS] (.node [wb7,wg6,wkw,wwe,wzv] (.node [wb2,wg6,wjl,wyr,wyS] .nil .nil) (.node [wb7,wg6,wkw,wwT,wyS] .nil .nil)) (.node [wcd,wp6,wrP,wwe,wyS] (.node [wca,wg6,wjZ,wwe,wyS] .nil .nil) .nil)) (.node [wcm,wg6,wmr,wtt,wyS] (.node [wcm,wcF,wg6,wmE,wp6] (.node [wcf,wg6,wjl,wwe,wyS] .nil .nil) .nil) (.node [wct,wg6,wmr,wwe,wyS] (.node [wct,wdl,wwe,wyS,wAX] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llrll_ok : everyKey (rowOK 3 level3) level4llrll = true := by decide +kernel
def level4llrlr : BinaryTree (List W) := (.node [wcE,wg6,wmE,wwe,wyS] (.node [wcv,wg6,wmx,wwe,wyS] (.node [wcv,wg6,wmr,wv4,wyS] (.node [wcv,wg6,wkt,wwe,wyS] (.node [wcu,wp6,wrP,wwe,wyS] .nil .nil) (.node [wcv,wg6,wkw,wwe,wyS] .nil .nil)) (.node [wcv,wg6,wmr,wwe,wyS] (.node [wcv,wg6,wmr,wwe,wyI] .nil .nil) .nil)) (.node [wcw,wg6,wmr,wwe,wyS] (.node [wcv,wmE,wnQ,wwe,wyS] (.node [wcv,wg6,wmE,wv4,wyI] .nil .nil) .nil) (.node [wcC,wg6,wmr,wwe,wyS] (.node [wcz,wg6,wmr,wwe,wyS] .nil .nil) .nil))) (.node [wcF,wg6,wmE,wp6,wyl] (.node [wcF,wg6,wjl,wmE,wwe] (.node [wcF,wek,wg6,wmE,wwe] (.node [wcF,wc2,wg6,wmE,wwe] .nil .nil) (.node [wcF,wg6,wiC,wmE,wwe] .nil .nil)) (.node [wcF,wg6,wmE,wp6,wwe] (.node [wcF,wg6,wmE,wpI,wwe] .nil .nil) .nil)) (.node [wcJ,wc2,wg6,wmE,wyS] (.node [wcJ,wcK,wg6,wmE,wp6] (.node [wcF,wg6,wmE,wwe,wA8] .nil .nil) .nil) (.node [wcJ,wg6,wiC,wmE,wyS] (.node [wcJ,wd8,wg6,wmE,wyS] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llrlr_ok : everyKey (rowOK 3 level3) level4llrlr = true := by decide +kernel
def level4llrl : BinaryTree (List W) := .node [wcu,wg6,wmr,wwe,wyS] level4llrll level4llrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llrl_ok : everyKey (rowOK 3 level3) level4llrl = true := by
  change (_ && everyKey (rowOK 3 level3) level4llrll && everyKey (rowOK 3 level3) level4llrlr) = true
  rw [level4llrll_ok, level4llrlr_ok]
  decide +kernel
def level4llrrl : BinaryTree (List W) := (.node [wc2,wia,wmE,wwe,wyS] (.node [wc2,wfL,wg6,wtt,wwe] (.node [wcJ,wg6,wmE,wyS,wA8] (.node [wcJ,wg6,wmE,wp6,wyS] (.node [wcJ,wg6,wmE,wpb,wyS] .nil .nil) (.node [wcJ,wg6,wmE,wp6,wAB] .nil .nil)) (.node [wcP,wrP,wtt,wwe,wyS] (.node [wcK,wg6,wmr,wtt,wwe] .nil .nil) .nil)) (.node [wc2,wg6,wmE,wyh,wAR] (.node [wc2,wfV,wg6,wwe,wyS] (.node [wc2,wfQ,wg6,wtt,wyS] .nil .nil) .nil) (.node [wc2,wg6,wmE,wyr,wAB] (.node [wc2,wg6,wmE,wyl,wAH] .nil .nil) .nil))) (.node [wdl,wrO,wtt,wwe,wyS] (.node [wdl,wre,wwe,wyS,wAX] (.node [wc2,wiq,wmE,wtt,wwe] (.node [wc2,wim,wmE,wtt,wyS] .nil .nil) (.node [wc2,wrP,wtt,wwe,wyS] .nil .nil)) (.node [wdl,wrM,wtt,wwe,wAX] (.node [wdl,wrv,wtt,wyS,wAX] .nil .nil) .nil)) (.node [wdl,wtt,wvZ,wyS,wAX] (.node [wdl,wte,wwe,wyS,wAX] (.node [wdl,wr4,wtt,wwe,wyS] .nil .nil) .nil) (.node [wdl,wtt,wwe,wyS,wAX] (.node [wdl,wtt,wwe,wyD,wAX] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llrrl_ok : everyKey (rowOK 3 level3) level4llrrl = true := by decide +kernel
def level4llrrr : BinaryTree (List W) := (.node [wem,wg6,wmE,wyh,wAR] (.node [wd6,wg6,wmE,wyh,wAR] (.node [wdn,wg6,wtt,wwe,wyS] (.node [wdl,wt4,wwe,wyS,wAX] (.node [wdl,wtt,wwP,wyS,wAX] .nil .nil) (.node [wdm,wtt,wwe,wyS,wAX] .nil .nil)) (.node [wd5,wfQ,wg6,wtt,wyS] (.node [wdT,wfV,wg6,wwe,wyS] .nil .nil) .nil)) (.node [wei,wfL,wg6,wtt,wwe] (.node [wd8,wg6,wmE,wyr,wAB] (.node [wd7,wg6,wmE,wyl,wAH] .nil .nil) .nil) (.node [wek,wg6,wmE,wyl,wAH] (.node [wej,wg6,wmE,wyr,wAB] .nil .nil) .nil))) (.node [weB,wg6,wmE,wud,wwe] (.node [weB,wg6,wmE,woN,wtt] (.node [weB,wg6,wjF,wtt,wwe] (.node [weq,wrP,wtt,wwe,wyS] .nil .nil) (.node [weB,wg6,wmE,woe,wwe] .nil .nil)) (.node [weB,wg6,wmE,wtt,wwX] (.node [weB,wg6,wmE,wtt,wwe] .nil .nil) .nil)) (.node [weE,wg6,wmE,woj,wyS] (.node [weE,wg6,wj2,wtt,wyS] (.node [weB,wg6,wnV,wtt,wwe] .nil .nil) .nil) (.node [weE,wg6,wmE,wtt,wyS] (.node [weE,wg6,wmE,wqK,wtt] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llrrr_ok : everyKey (rowOK 3 level3) level4llrrr = true := by decide +kernel
def level4llrr : BinaryTree (List W) := .node [wdl,wtt,wwe,wzr,wAX] level4llrrl level4llrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llrr_ok : everyKey (rowOK 3 level3) level4llrr = true := by
  change (_ && everyKey (rowOK 3 level3) level4llrrl && everyKey (rowOK 3 level3) level4llrrr) = true
  rw [level4llrrl_ok, level4llrrr_ok]
  decide +kernel
def level4llr : BinaryTree (List W) := .node [wcJ,wg6,wjl,wmE,wyS] level4llrl level4llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llr_ok : everyKey (rowOK 3 level3) level4llr = true := by
  change (_ && everyKey (rowOK 3 level3) level4llrl && everyKey (rowOK 3 level3) level4llrr) = true
  rw [level4llrl_ok, level4llrr_ok]
  decide +kernel
def level4ll : BinaryTree (List W) := .node [wbY,wgh,wg6,wwe,wyS] level4lll level4llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4ll_ok : everyKey (rowOK 3 level3) level4ll = true := by
  change (_ && everyKey (rowOK 3 level3) level4lll && everyKey (rowOK 3 level3) level4llr) = true
  rw [level4lll_ok, level4llr_ok]
  decide +kernel
def level4lrlll : BinaryTree (List W) := (.node [wfz,wg6,wtj,wv4,wyS] (.node [weI,wg6,wmE,wwe,wyS] (.node [weI,wg6,wkw,wwe,wyS] (.node [weE,wg6,wnO,wtt,wyS] (.node [weE,wg6,wmE,wt9,wyS] .nil .nil) (.node [weG,wg6,wmE,wp6,wtt] .nil .nil)) (.node [weI,wg6,wmE,wq4,wwe] (.node [weI,wg6,wmE,wqY,wyS] .nil .nil) .nil)) (.node [weM,wg6,wmE,wp6,wwe] (.node [weI,wg6,wmE,wwT,wyS] (.node [weI,wg6,wmE,wwe,wzv] .nil .nil) (.node [weI,wg6,wnG,wwe,wyS] .nil .nil)) (.node [wfy,wiv,wtt,wwe,wyS] (.node [weN,wg6,wmE,wp6,wyS] .nil .nil) .nil))) (.node [wfL,wg6,wjK,wtt,wwe] (.node [wfJ,wg6,wtt,wwe,wyS] (.node [wfz,wg6,wtt,wv4,wyI] (.node [wfz,wg6,wtj,wwe,wyI] .nil .nil) (.node [wfz,wnQ,wtt,wwe,wyS] .nil .nil)) (.node [wfL,wg6,wjl,wtt,wwe] (.node [wfL,wg6,wiC,wtt,wwe] .nil .nil) .nil)) (.node [wfL,wg6,wpC,wtt,wwe] (.node [wfL,wg6,wlI,wp6,wtt] (.node [wfL,wg6,wlg,wp6,wwe] .nil .nil) .nil) (.node [wfL,wg6,wp6,wtt,wxd] (.node [wfL,wg6,wp6,wtt,wwe] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrlll_ok : everyKey (rowOK 3 level3) level4lrlll = true := by decide +kernel
def level4lrllr : BinaryTree (List W) := (.node [wfQ,wg6,wp6,wuq,wyS] (.node [wfQ,wg6,wkf,wtt,wyS] (.node [wfO,wmE,wtt,wwe,wyS] (.node [wfL,wg6,wtt,wwe,wA8] (.node [wfL,wg6,wrY,wtt,wwe] .nil .nil) (.node [wfN,wmr,wtt,wwe,wyS] .nil .nil)) (.node [wfQ,wg6,wjl,wtt,wyS] (.node [wfQ,wg6,wiC,wtt,wyS] .nil .nil) .nil)) (.node [wfQ,wg6,wo3,wtt,wyS] (.node [wfQ,wg6,wm7,wp6,wtt] (.node [wfQ,wg6,wll,wp6,wyS] .nil .nil) .nil) (.node [wfQ,wg6,wp6,wtt,wzN] (.node [wfQ,wg6,wp6,wtt,wyS] .nil .nil) .nil))) (.node [wfV,wg6,wni,wp6,wyS] (.node [wfV,wg6,wiC,wwe,wyS] (.node [wfQ,wg6,wtt,wyS,wA8] (.node [wfQ,wg6,wrG,wtt,wyS] .nil .nil) (.node [wfT,wg6,wmE,wp6,wtt] .nil .nil)) (.node [wfV,wg6,wkM,wwe,wyS] (.node [wfV,wg6,wjl,wwe,wyS] .nil .nil) .nil)) (.node [wfV,wg6,wp6,wwe,wyS] (.node [wfV,wg6,woB,wwe,wyS] (.node [wfV,wg6,wnp,wp6,wwe] .nil .nil) .nil) (.node [wfV,wg6,wp6,ww9,wyS] (.node [wfV,wg6,wp6,wwe,wzK] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrllr_ok : everyKey (rowOK 3 level3) level4lrllr = true := by decide +kernel
def level4lrll : BinaryTree (List W) := .node [wfL,wg6,wp6,wuu,wwe] level4lrlll level4lrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrll_ok : everyKey (rowOK 3 level3) level4lrll = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrlll && everyKey (rowOK 3 level3) level4lrllr) = true
  rw [level4lrlll_ok, level4lrllr_ok]
  decide +kernel
def level4lrlrl : BinaryTree (List W) := (.node [wgj,wtt,wwe,wyS,wAX] (.node [wf3,wg6,wtt,wwe,wyS] (.node [wf3,wg6,wrg,wwe,wyS] (.node [wf0,wg6,wmE,wp6,wwe] (.node [wfV,wg6,wwe,wyS,wA8] .nil .nil) (.node [wf1,wg6,wmE,wp6,wyS] .nil .nil)) (.node [wf3,wg6,wrT,wtt,wwe] (.node [wf3,wg6,wrx,wtt,wyS] .nil .nil) .nil)) (.node [wf3,wg6,wt2,wwe,wyS] (.node [wf3,wg6,wtt,wwN,wyS] (.node [wf3,wg6,wtt,wwe,wzp] .nil .nil) .nil) (.node [wgj,wjl,wuS,wwe,wyS] (.node [wf9,wmr,wuS,wwe,wyS] .nil .nil) .nil))) (.node [wgP,wg6,wmE,wtt,wwe] (.node [wgz,wtt,wwe,wyS,wAX] (.node [wgr,wmr,wtt,wxz,wyS] (.node [wgo,wg6,wtt,wwe,wyS] .nil .nil) (.node [wgz,wjl,wtt,wxz,wyS] .nil .nil)) (.node [wgK,wg6,wtt,wwe,wyS] (.node [wgE,wg6,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wgR,wmr,wtt,wwe,wz7] (.node [wgQ,wg6,wp6,wtt,wwe] (.node [wgQ,wg6,wjl,wtt,wwe] .nil .nil) .nil) (.node [wgX,wtt,wwe,wyS,wAX] (.node [wgX,wjl,wtt,wwe,wz7] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrlrl_ok : everyKey (rowOK 3 level3) level4lrlrl = true := by decide +kernel
def level4lrlrr : BinaryTree (List W) := (.node [wg6,whF,wp6,wwe,wyS] (.node [wg6,whv,wjl,wtt,wyS] (.node [wg6,wht,wmE,wtt,wyS] (.node [wg6,whn,wp6,wtt,wwe] (.node [wg6,whm,wjl,wtt,wwe] .nil .nil) (.node [wg6,whs,wmE,wtt,wyS] .nil .nil)) (.node [wg6,whu,wp6,wtt,wyS] (.node [wg6,whu,wjl,wtt,wyS] .nil .nil) .nil)) (.node [wg6,whD,wmE,wwe,wyS] (.node [wg6,whC,wmE,wp6,wtt] (.node [wg6,whw,wp6,wtt,wyS] .nil .nil) .nil) (.node [wg6,whF,wjl,wwe,wyS] (.node [wg6,whE,wmE,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wil,wmr,wtt,wyS] (.node [wg6,whQ,wmE,wp6,wyS] (.node [wg6,whH,wp6,wwe,wyS] (.node [wg6,whG,wjl,wwe,wyS] .nil .nil) (.node [wg6,whP,wmE,wp6,wwe] .nil .nil)) (.node [wg6,wh8,wmr,wwe,wyS] (.node [wg6,wh3,wmr,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wir,wtt,wwP,wyS] (.node [wg6,wir,wtt,wwe,wzs] (.node [wg6,wir,wtt,wwe,wzr] .nil .nil) .nil) (.node [wg6,wir,wt4,wwe,wyS] (.node [wg6,wir,wtt,wwQ,wyS] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrlrr_ok : everyKey (rowOK 3 level3) level4lrlrr = true := by decide +kernel
def level4lrlr : BinaryTree (List W) := .node [wg6,whl,wmE,wtt,wwe] level4lrlrl level4lrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrlr_ok : everyKey (rowOK 3 level3) level4lrlr = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrlrl && everyKey (rowOK 3 level3) level4lrlrr) = true
  rw [level4lrlrl_ok, level4lrlrr_ok]
  decide +kernel
def level4lrl : BinaryTree (List W) := .node [wfV,wg6,wrs,wwe,wyS] level4lrll level4lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrl_ok : everyKey (rowOK 3 level3) level4lrl = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrll && everyKey (rowOK 3 level3) level4lrlr) = true
  rw [level4lrll_ok, level4lrlr_ok]
  decide +kernel
def level4lrrll : BinaryTree (List W) := (.node [wg6,wjl,wrv,wtt,wzr] (.node [wg6,wjl,wmE,wyh,wAR] (.node [wg6,wiS,wtt,wwe,wyS] (.node [wg6,wiC,wmE,wyl,wAH] (.node [wg6,wiC,wmE,wyh,wAR] .nil .nil) (.node [wg6,wiC,wmE,wyr,wAB] .nil .nil)) (.node [wg6,wi3,wtt,wwe,wyS] (.node [wg6,wi0,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wjl,wre,wwP,wyS] (.node [wg6,wjl,wmE,wyr,wAB] (.node [wg6,wjl,wmE,wyl,wAH] .nil .nil) (.node [wg6,wjl,wre,wwe,wzr] .nil .nil)) (.node [wg6,wjl,wrg,wwN,wyS] (.node [wg6,wjl,wrg,wwe,wzp] .nil .nil) .nil))) (.node [wg6,wjl,wrT,wt2,wwe] (.node [wg6,wjl,wrM,wtt,wwP] (.node [wg6,wjl,wrx,wtt,wzp] (.node [wg6,wjl,wrv,wt4,wyS] .nil .nil) (.node [wg6,wjl,wrx,wt2,wyS] .nil .nil)) (.node [wg6,wjl,wrT,wtt,wwN] (.node [wg6,wjl,wrM,wt4,wwe] .nil .nil) .nil)) (.node [wg6,wjl,wtt,wwe,wy3] (.node [wg6,wjl,wtt,wwe,wy0] (.node [wg6,wjl,wtt,wwe,wyZ] .nil .nil) .nil) (.node [wg6,wjl,wtt,wwe,wzd] (.node [wg6,wjl,wtt,wwe,wy9] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrrll_ok : everyKey (rowOK 3 level3) level4lrrll = true := by decide +kernel
def level4lrrlr : BinaryTree (List W) := (.node [wg6,wjl,wtt,wwv,wyS] (.node [wg6,wjl,wtt,wwe,wzY] (.node [wg6,wjl,wtt,wwe,wzw] (.node [wg6,wjl,wtt,wwe,wzr] (.node [wg6,wjl,wtt,wwe,wzp] .nil .nil) (.node [wg6,wjl,wtt,wwe,wzs] .nil .nil)) (.node [wg6,wjl,wtt,wwe,wzW] (.node [wg6,wjl,wtt,wwe,wzz] .nil .nil) .nil)) (.node [wg6,wjl,wtt,wwl,wyS] (.node [wg6,wjl,wtt,wwe,wz3] (.node [wg6,wjl,wtt,wwe,wzZ] .nil .nil) .nil) (.node [wg6,wjl,wtt,wwp,wyS] (.node [wg6,wjl,wtt,wwm,wyS] .nil .nil) .nil))) (.node [wg6,wjl,wtt,wwQ,wyS] (.node [wg6,wjl,wtt,wwN,wzp] (.node [wg6,wjl,wtt,wwM,wyS] (.node [wg6,wjl,wtt,wwz,wyS] .nil .nil) (.node [wg6,wjl,wtt,wwN,wyS] .nil .nil)) (.node [wg6,wjl,wtt,wwP,wzr] (.node [wg6,wjl,wtt,wwP,wyS] .nil .nil) .nil)) (.node [wg6,wjl,wtt,wxm,wyS] (.node [wg6,wjl,wtt,wwY,wyS] (.node [wg6,wjl,wtt,wwU,wyS] .nil .nil) .nil) (.node [wg6,wjl,wtt,wxp,wyS] (.node [wg6,wjl,wtt,wxo,wyS] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrrlr_ok : everyKey (rowOK 3 level3) level4lrrlr = true := by decide +kernel
def level4lrrl : BinaryTree (List W) := .node [wg6,wjl,wtt,wwe,wzo] level4lrrll level4lrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrrl_ok : everyKey (rowOK 3 level3) level4lrrl = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrrll && everyKey (rowOK 3 level3) level4lrrlr) = true
  rw [level4lrrll_ok, level4lrrlr_ok]
  decide +kernel
def level4lrrrl : BinaryTree (List W) := (.node [wg6,wjl,wt5,wwe,wyS] (.node [wg6,wjl,wt2,wwe,wyS] (.node [wg6,wjl,wtK,wwe,wyS] (.node [wg6,wjl,wtB,wwe,wyS] (.node [wg6,wjl,wtA,wwe,wyS] .nil .nil) (.node [wg6,wjl,wtE,wwe,wyS] .nil .nil)) (.node [wg6,wjl,wt1,wwe,wyS] (.node [wg6,wjl,wtO,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wjl,wt4,wwe,wyS] (.node [wg6,wjl,wt2,wwN,wyS] (.node [wg6,wjl,wt2,wwe,wzp] .nil .nil) .nil) (.node [wg6,wjl,wt4,wwP,wyS] (.node [wg6,wjl,wt4,wwe,wzr] .nil .nil) .nil))) (.node [wg6,wju,wtt,wwe,wyS] (.node [wg6,wjl,wuH,wwe,wyS] (.node [wg6,wjl,wue,wwe,wyS] (.node [wg6,wjl,wua,wwe,wyS] .nil .nil) (.node [wg6,wjl,wuF,wwe,wyS] .nil .nil)) (.node [wg6,wjl,wuO,wwe,wyS] (.node [wg6,wjl,wuI,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wjw,wtt,wvJ,wAR] (.node [wg6,wjw,woa,wwe,wyS] (.node [wg6,wjv,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wjw,wtt,wwe,wzy] (.node [wg6,wjw,wtt,wwe,wyS] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrrrl_ok : everyKey (rowOK 3 level3) level4lrrrl = true := by decide +kernel
def level4lrrrr : BinaryTree (List W) := (.node [wg6,wjC,wtt,wwe,wyS] (.node [wg6,wjz,wtt,wwZ,wyS] (.node [wg6,wjz,wsY,wwe,wAH] (.node [wg6,wjy,wtt,wwe,wyS] (.node [wg6,wjw,wuf,wwe,wyS] .nil .nil) (.node [wg6,wjz,woK,wtt,wyS] .nil .nil)) (.node [wg6,wjz,wtt,wwe,wzv] (.node [wg6,wjz,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wjA,wtt,wwe,wAB] (.node [wg6,wjA,wtt,wwe,wyS] (.node [wg6,wjz,wud,wwe,wyS] .nil .nil) .nil) (.node [wg6,wjC,woM,wtt,wyS] (.node [wg6,wjC,wod,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wjF,wta,wwe,wyS] (.node [wg6,wjF,wqY,wtt,wyS] (.node [wg6,wjE,wtt,wwe,wyS] (.node [wg6,wjD,wtt,wwe,wyS] .nil .nil) (.node [wg6,wjF,woj,wwe,wyS] .nil .nil)) (.node [wg6,wjF,wrx,wtt,wyS] (.node [wg6,wjF,wrg,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wjF,wtt,wv4,wyS] (.node [wg6,wjF,wtt,wvV,wyS] (.node [wg6,wjF,wtj,wwe,wyS] .nil .nil) .nil) (.node [wg6,wjF,wtt,wwe,wzv] (.node [wg6,wjF,wtt,wwe,wzp] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrrrr_ok : everyKey (rowOK 3 level3) level4lrrrr = true := by decide +kernel
def level4lrrr : BinaryTree (List W) := .node [wg6,wjw,wtt,wwX,wyS] level4lrrrl level4lrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrrr_ok : everyKey (rowOK 3 level3) level4lrrr = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrrrl && everyKey (rowOK 3 level3) level4lrrrr) = true
  rw [level4lrrrl_ok, level4lrrrr_ok]
  decide +kernel
def level4lrr : BinaryTree (List W) := .node [wg6,wjl,wtt,wxv,wyS] level4lrrl level4lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrr_ok : everyKey (rowOK 3 level3) level4lrr = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrrl && everyKey (rowOK 3 level3) level4lrrr) = true
  rw [level4lrrl_ok, level4lrrr_ok]
  decide +kernel
def level4lr : BinaryTree (List W) := .node [wg6,wir,wt5,wwe,wyS] level4lrl level4lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lr_ok : everyKey (rowOK 3 level3) level4lr = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrl && everyKey (rowOK 3 level3) level4lrr) = true
  rw [level4lrl_ok, level4lrr_ok]
  decide +kernel
def level4l : BinaryTree (List W) := .node [weE,wg6,wmE,wtt,wzy] level4ll level4lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4l_ok : everyKey (rowOK 3 level3) level4l = true := by
  change (_ && everyKey (rowOK 3 level3) level4ll && everyKey (rowOK 3 level3) level4lr) = true
  rw [level4ll_ok, level4lr_ok]
  decide +kernel
def level4rllll : BinaryTree (List W) := (.node [wg6,wjZ,woi,wwe,wyS] (.node [wg6,wjQ,wtt,wwT,wyS] (.node [wg6,wjQ,wsK,wyr,wyS] (.node [wg6,wjP,wtt,wwe,wyS] (.node [wg6,wjN,wtt,wwe,wyS] .nil .nil) (.node [wg6,wjQ,wqv,wtt,wwe] .nil .nil)) (.node [wg6,wjQ,wtt,wwe,wzA] (.node [wg6,wjQ,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wjS,wtt,wwe,wyS] (.node [wg6,wjR,wtt,wwe,wyS] (.node [wg6,wjQ,wt9,wwe,wyS] .nil .nil) (.node [wg6,wjR,wtt,wyl,wyS] .nil .nil)) (.node [wg6,wjW,wtt,wwe,wyS] (.node [wg6,wjS,wwe,wyh,wyS] .nil .nil) .nil))) (.node [wg6,wj2,wrg,wwe,wyS] (.node [wg6,wj1,wtt,wwe,wyS] (.node [wg6,wjZ,wtt,wwe,wyS] (.node [wg6,wjZ,wqJ,wtt,wwe] .nil .nil) (.node [wg6,wj0,wtt,wwe,wyS] .nil .nil)) (.node [wg6,wj2,wq4,wtt,wwe] (.node [wg6,wj2,woe,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wj2,wtj,wwe,wyS] (.node [wg6,wj2,wsX,wwe,wyS] (.node [wg6,wj2,wrT,wtt,wwe] .nil .nil) .nil) (.node [wg6,wj2,wtt,wwe,wyI] (.node [wg6,wj2,wtt,wwe,wya] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rllll_ok : everyKey (rowOK 3 level3) level4rllll = true := by decide +kernel
def level4rlllr : BinaryTree (List W) := (.node [wg6,wkw,wrx,wtt,wyS] (.node [wg6,wkt,wq3,wtt,wwe] (.node [wg6,wkn,wmr,wtt,wwe] (.node [wg6,wj2,wtt,wwX,wyS] (.node [wg6,wj2,wtt,wwT,wyS] .nil .nil) (.node [wg6,wj4,wtt,wwe,wyS] .nil .nil)) (.node [wg6,wkt,wqX,wtt,wyS] (.node [wg6,wkq,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wkv,wtt,wwe,wyS] (.node [wg6,wku,wtt,wwe,wyS] (.node [wg6,wkt,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wkw,wqK,wtt,wwe] (.node [wg6,wkw,woN,wtt,wyS] .nil .nil) .nil))) (.node [wg6,wkw,wt9,wwe,wyS] (.node [wg6,wkw,wtt,wv4,wyS] (.node [wg6,wkw,wtt,wvD,wyS] (.node [wg6,wkw,wrT,wtt,wwe] .nil .nil) (.node [wg6,wkw,wtt,wvF,wwe] .nil .nil)) (.node [wg6,wkw,wt2,wwe,wyS] (.node [wg6,wkw,wtt,wwe,wyI] .nil .nil) .nil)) (.node [wg6,wkB,wtt,wwe,wyS] (.node [wg6,wky,wtt,wwe,wyS] (.node [wg6,wkw,wud,wwe,wyS] .nil .nil) .nil) (.node [wg6,wk2,wmr,wtt,wwe] (.node [wg6,wkX,wmr,wtt,wyS] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlllr_ok : everyKey (rowOK 3 level3) level4rlllr = true := by decide +kernel
def level4rlll : BinaryTree (List W) := .node [wg6,wj2,wtt,wwN,wyS] level4rllll level4rlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlll_ok : everyKey (rowOK 3 level3) level4rlll = true := by
  change (_ && everyKey (rowOK 3 level3) level4rllll && everyKey (rowOK 3 level3) level4rlllr) = true
  rw [level4rllll_ok, level4rlllr_ok]
  decide +kernel
def level4rllrl : BinaryTree (List W) := (.node [wg6,wlS,wtt,wwe,wyS] (.node [wg6,wlv,wtt,wwe,wyS] (.node [wg6,wlg,wmr,wwe,wyS] (.node [wg6,wla,wvi,wwe,wyS] (.node [wg6,wk9,wvj,wwe,wyS] .nil .nil) (.node [wg6,wle,wmr,wwe,wyS] .nil .nil)) (.node [wg6,wll,wmr,wwe,wyS] (.node [wg6,wlj,wmr,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wlC,wtt,wxT,wyS] (.node [wg6,wlB,wtt,wxU,wyS] (.node [wg6,wly,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wlI,wmr,wtt,wyS] (.node [wg6,wlG,wmr,wtt,wyS] .nil .nil) .nil))) (.node [wg6,wmp,wtt,wwe,wyS] (.node [wg6,wmd,wtt,wwe,wyS] (.node [wg6,wl1,wtt,wwe,wAn] (.node [wg6,wlV,wtt,wwe,wyS] .nil .nil) (.node [wg6,wl2,wtt,wwe,wAm] .nil .nil)) (.node [wg6,wmo,wtt,wwe,wyS] (.node [wg6,wmg,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmr,wm7,wtt,wwe] (.node [wg6,wmr,wm5,wtt,wwe] (.node [wg6,wmq,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmr,wni,wtt,wyS] (.node [wg6,wmr,wng,wtt,wyS] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rllrl_ok : everyKey (rowOK 3 level3) level4rllrl = true := by decide +kernel
def level4rllrr : BinaryTree (List W) := (.node [wg6,wmr,wry,wtt,wyS] (.node [wg6,wmr,wq4,wtt,wwe] (.node [wg6,wmr,woN,wtt,wyS] (.node [wg6,wmr,woe,wwe,wyS] (.node [wg6,wmr,wnp,wtt,wwe] .nil .nil) (.node [wg6,wmr,woj,wwe,wyS] .nil .nil)) (.node [wg6,wmr,wqY,wtt,wyS] (.node [wg6,wmr,wqK,wtt,wwe] .nil .nil) .nil)) (.node [wg6,wmr,wrh,wwe,wyS] (.node [wg6,wmr,wrg,wwe,wyS] (.node [wg6,wmr,wre,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmr,wrx,wtt,wyS] (.node [wg6,wmr,wrv,wtt,wyS] .nil .nil) .nil))) (.node [wg6,wmr,wtf,wwe,wyS] (.node [wg6,wmr,wsK,wyr,wyS] (.node [wg6,wmr,wrT,wtt,wwe] (.node [wg6,wmr,wrM,wtt,wwe] .nil .nil) (.node [wg6,wmr,wrU,wtt,wwe] .nil .nil)) (.node [wg6,wmr,wte,wwe,wyS] (.node [wg6,wmr,wsY,wwe,wAH] .nil .nil) .nil)) (.node [wg6,wmr,wtj,wwe,wyS] (.node [wg6,wmr,wtj,wwe,wyI] (.node [wg6,wmr,wtj,wv4,wyS] .nil .nil) .nil) (.node [wg6,wmr,wtl,wwe,wyS] (.node [wg6,wmr,wtk,wwe,wyS] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rllrr_ok : everyKey (rowOK 3 level3) level4rllrr = true := by decide +kernel
def level4rllr : BinaryTree (List W) := .node [wg6,wmr,wnn,wtt,wwe] level4rllrl level4rllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rllr_ok : everyKey (rowOK 3 level3) level4rllr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rllrl && everyKey (rowOK 3 level3) level4rllrr) = true
  rw [level4rllrl_ok, level4rllrr_ok]
  decide +kernel
def level4rll : BinaryTree (List W) := .node [wg6,wk6,wtt,wwe,wyS] level4rlll level4rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rll_ok : everyKey (rowOK 3 level3) level4rll = true := by
  change (_ && everyKey (rowOK 3 level3) level4rlll && everyKey (rowOK 3 level3) level4rllr) = true
  rw [level4rlll_ok, level4rllr_ok]
  decide +kernel
def level4rlrll : BinaryTree (List W) := (.node [wg6,wmr,wtt,wwc,wyS] (.node [wg6,wmr,wtt,wv4,wyI] (.node [wg6,wmr,wtt,wvJ,wAR] (.node [wg6,wmr,wtp,wwe,wyS] (.node [wg6,wmr,wtn,wwe,wyS] .nil .nil) (.node [wg6,wmr,wtr,wwe,wyS] .nil .nil)) (.node [wg6,wmr,wtt,wv0,wyS] (.node [wg6,wmr,wtt,wvZ,wyS] .nil .nil) .nil)) (.node [wg6,wmr,wtt,wv7,wyS] (.node [wg6,wmr,wtt,wv5,wyS] (.node [wg6,wmr,wtt,wv4,wyS] .nil .nil) (.node [wg6,wmr,wtt,wv6,wyS] .nil .nil)) (.node [wg6,wmr,wtt,wwa,wyS] (.node [wg6,wmr,wtt,wv8,wyS] .nil .nil) .nil))) (.node [wg6,wmr,wtt,wwe,wyM] (.node [wg6,wmr,wtt,wwe,wyJ] (.node [wg6,wmr,wtt,wwe,wyE] (.node [wg6,wmr,wtt,wwe,wyD] .nil .nil) (.node [wg6,wmr,wtt,wwe,wyI] .nil .nil)) (.node [wg6,wmr,wtt,wwe,wyL] (.node [wg6,wmr,wtt,wwe,wyK] .nil .nil) .nil)) (.node [wg6,wmr,wtt,wwe,wyS] (.node [wg6,wmr,wtt,wwe,wyQ] (.node [wg6,wmr,wtt,wwe,wyO] .nil .nil) .nil) (.node [wg6,wmr,wtt,wwe,wyU] (.node [wg6,wmr,wtt,wwe,wyT] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlrll_ok : everyKey (rowOK 3 level3) level4rlrll = true := by decide +kernel
def level4rlrlr : BinaryTree (List W) := (.node [wg6,wmr,wtt,wwf,wyS] (.node [wg6,wmr,wtt,wwe,wzL] (.node [wg6,wmr,wtt,wwe,wzv] (.node [wg6,wmr,wtt,wwe,wzp] (.node [wg6,wmr,wtt,wwe,wzo] .nil .nil) (.node [wg6,wmr,wtt,wwe,wzr] .nil .nil)) (.node [wg6,wmr,wtt,wwe,wzK] (.node [wg6,wmr,wtt,wwe,wzy] .nil .nil) .nil)) (.node [wg6,wmr,wtt,wwe,wzT] (.node [wg6,wmr,wtt,wwe,wzO] (.node [wg6,wmr,wtt,wwe,wzN] .nil .nil) .nil) (.node [wg6,wmr,wtt,wwe,wAB] (.node [wg6,wmr,wtt,wwe,wz0] .nil .nil) .nil))) (.node [wg6,wmr,wtt,wwX,wyS] (.node [wg6,wmr,wtt,wwN,wyS] (.node [wg6,wmr,wtt,wwh,wyS] (.node [wg6,wmr,wtt,wwg,wyS] .nil .nil) (.node [wg6,wmr,wtt,wwM,wyS] .nil .nil)) (.node [wg6,wmr,wtt,wwT,wyS] (.node [wg6,wmr,wtt,wwP,wyS] .nil .nil) .nil)) (.node [wg6,wmr,wtt,wxd,wyS] (.node [wg6,wmr,wtt,wxa,wyS] (.node [wg6,wmr,wtt,ww9,wyS] .nil .nil) .nil) (.node [wg6,wmr,wtt,wxj,wyS] (.node [wg6,wmr,wtt,wxe,wyS] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlrlr_ok : everyKey (rowOK 3 level3) level4rlrlr = true := by decide +kernel
def level4rlrl : BinaryTree (List W) := .node [wg6,wmr,wtt,wwe,wyV] level4rlrll level4rlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlrl_ok : everyKey (rowOK 3 level3) level4rlrl = true := by
  change (_ && everyKey (rowOK 3 level3) level4rlrll && everyKey (rowOK 3 level3) level4rlrlr) = true
  rw [level4rlrll_ok, level4rlrlr_ok]
  decide +kernel
def level4rlrrl : BinaryTree (List W) := (.node [wg6,wmr,wuv,wwe,wyS] (.node [wg6,wmr,wt4,wwe,wyS] (.node [wg6,wmr,wtw,wwe,wyS] (.node [wg6,wmr,wtu,wwe,wyS] (.node [wg6,wmr,wtt,wyl,wyS] .nil .nil) (.node [wg6,wmr,wtv,wwe,wyS] .nil .nil)) (.node [wg6,wmr,wt2,wwe,wyS] (.node [wg6,wmr,wt1,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmr,wuq,wwe,wyS] (.node [wg6,wmr,wud,wwe,wyS] (.node [wg6,wmr,wt9,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmr,wuu,wwe,wyS] (.node [wg6,wmr,wur,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wmu,wtt,wv4,wyS] (.node [wg6,wms,wtt,wwe,wyS] (.node [wg6,wmr,wuL,wwe,wyS] (.node [wg6,wmr,wuC,wwe,wyS] .nil .nil) (.node [wg6,wmr,wwe,wyh,wyS] .nil .nil)) (.node [wg6,wmu,wtj,wwe,wyS] (.node [wg6,wmt,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmw,wtt,wwe,wyI] (.node [wg6,wmw,wtj,wwe,wyS] (.node [wg6,wmv,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmx,wtt,wwe,wyI] (.node [wg6,wmx,wtt,wv4,wyS] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlrrl_ok : everyKey (rowOK 3 level3) level4rlrrl = true := by decide +kernel
def level4rlrrr : BinaryTree (List W) := (.node [wg6,wmE,wo8,wtt,wAR] (.node [wg6,wmE,woh,wqC,wwe] (.node [wg6,wmE,wod,woM,wyS] (.node [wg6,wmB,wtt,wwe,wyI] (.node [wg6,wmz,wtt,wv4,wyS] .nil .nil) (.node [wg6,wmE,woc,woL,wyS] .nil .nil)) (.node [wg6,wmE,woe,wv4,wyS] (.node [wg6,wmE,woe,wrx,wyS] .nil .nil) .nil)) (.node [wg6,wmE,woj,wwe,wyI] (.node [wg6,wmE,woj,wrT,wwe] (.node [wg6,wmE,woi,wqJ,wwe] .nil .nil) .nil) (.node [wg6,wmE,woN,wtj,wyS] (.node [wg6,wmE,woN,wrg,wyS] .nil .nil) .nil))) (.node [wg6,wmE,wpH,wyr,wAB] (.node [wg6,wmE,wpb,wyr,wAB] (.node [wg6,wmE,wpa,wwe,wAH] (.node [wg6,wmE,wo8,wyh,wAR] .nil .nil) (.node [wg6,wmE,wpa,wyl,wAH] .nil .nil)) (.node [wg6,wmE,wpH,wyr,wyS] (.node [wg6,wmE,wpb,wAH,wAR] .nil .nil) .nil)) (.node [wg6,wmE,wpP,wyh,wAR] (.node [wg6,wmE,wpI,wyr,wAR] (.node [wg6,wmE,wpI,wyl,wAH] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wtV] (.node [wg6,wmE,wpP,wyr,wAH] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlrrr_ok : everyKey (rowOK 3 level3) level4rlrrr = true := by decide +kernel
def level4rlrr : BinaryTree (List W) := .node [wg6,wmy,wtj,wwe,wyS] level4rlrrl level4rlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlrr_ok : everyKey (rowOK 3 level3) level4rlrr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rlrrl && everyKey (rowOK 3 level3) level4rlrrr) = true
  rw [level4rlrrl_ok, level4rlrrr_ok]
  decide +kernel
def level4rlr : BinaryTree (List W) := .node [wg6,wmr,wtt,wxs,wyS] level4rlrl level4rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlr_ok : everyKey (rowOK 3 level3) level4rlr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rlrl && everyKey (rowOK 3 level3) level4rlrr) = true
  rw [level4rlrl_ok, level4rlrr_ok]
  decide +kernel
def level4rl : BinaryTree (List W) := .node [wg6,wmr,wtm,wwe,wyS] level4rll level4rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rl_ok : everyKey (rowOK 3 level3) level4rl = true := by
  change (_ && everyKey (rowOK 3 level3) level4rll && everyKey (rowOK 3 level3) level4rlr) = true
  rw [level4rll_ok, level4rlr_ok]
  decide +kernel
def level4rrlll : BinaryTree (List W) := (.node [wg6,wmE,wp6,wyp,wAR] (.node [wg6,wmE,wp6,wyf,wyS] (.node [wg6,wmE,wp6,wxE,wAH] (.node [wg6,wmE,wp6,wvq,wAR] (.node [wg6,wmE,wp6,wu9,wAR] .nil .nil) (.node [wg6,wmE,wp6,wwe,wwD] .nil .nil)) (.node [wg6,wmE,wp6,wxX,wAH] (.node [wg6,wmE,wp6,wxK,wAH] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wyl,wAH] (.node [wg6,wmE,wp6,wyi,wAR] (.node [wg6,wmE,wp6,wyh,wAR] .nil .nil) (.node [wg6,wmE,wp6,wyj,wAR] .nil .nil)) (.node [wg6,wmE,wp6,wyn,wAH] (.node [wg6,wmE,wp6,wym,wAH] .nil .nil) .nil))) (.node [wg6,wmE,wp6,wyr,wAD] (.node [wg6,wmE,wp6,wyr,wAp] (.node [wg6,wmE,wp6,wyr,wAb] (.node [wg6,wmE,wp6,wyq,wAH] .nil .nil) (.node [wg6,wmE,wp6,wyr,wAg] .nil .nil)) (.node [wg6,wmE,wp6,wyr,wAC] (.node [wg6,wmE,wp6,wyr,wAB] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wyr,wAJ] (.node [wg6,wmE,wp6,wyr,wAI] (.node [wg6,wmE,wp6,wyr,wAG] .nil .nil) .nil) (.node [wg6,wmE,wp6,wys,wAR] (.node [wg6,wmE,wp6,wyr,wAQ] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrlll_ok : everyKey (rowOK 3 level3) level4rrlll = true := by decide +kernel
def level4rrllr : BinaryTree (List W) := (.node [wg6,wmE,wrd,wru,wyS] (.node [wg6,wmE,wqQ,wqS,wtt] (.node [wg6,wmE,wp6,wAH,wAP] (.node [wg6,wmE,wp6,wyw,wAH] (.node [wg6,wmE,wp6,wyv,wAR] .nil .nil) (.node [wg6,wmE,wp6,wAF,wAR] .nil .nil)) (.node [wg6,wmE,wqK,wtj,wwe] (.node [wg6,wmE,wqK,wrg,wwe] .nil .nil) .nil)) (.node [wg6,wmE,wqY,wtt,wyI] (.node [wg6,wmE,wqY,wrT,wtt] (.node [wg6,wmE,wqX,wq3,wtt] .nil .nil) .nil) (.node [wg6,wmE,wq4,wtt,wv4] (.node [wg6,wmE,wq4,wrx,wtt] .nil .nil) .nil))) (.node [wg6,wmE,wrg,wrz,wyS] (.node [wg6,wmE,wrg,wrx,wrT] (.node [wg6,wmE,wrf,wrw,wyS] (.node [wg6,wmE,wrd,wrL,wwe] .nil .nil) (.node [wg6,wmE,wrf,wrS,wwe] .nil .nil)) (.node [wg6,wmE,wrg,wrx,wzp] (.node [wg6,wmE,wrg,wrx,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wrg,wsa,wwe] (.node [wg6,wmE,wrg,wrT,wwN] (.node [wg6,wmE,wrg,wrT,wwe] .nil .nil) .nil) (.node [wg6,wmE,wrg,wvF,wwe] (.node [wg6,wmE,wrg,wvD,wyS] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrllr_ok : everyKey (rowOK 3 level3) level4rrllr = true := by decide +kernel
def level4rrll : BinaryTree (List W) := .node [wg6,wmE,wp6,wyt,wAH] level4rrlll level4rrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrll_ok : everyKey (rowOK 3 level3) level4rrll = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrlll && everyKey (rowOK 3 level3) level4rrllr) = true
  rw [level4rrlll_ok, level4rrllr_ok]
  decide +kernel
def level4rrlrl : BinaryTree (List W) := (.node [wg6,wmE,wrx,wtj,wyS] (.node [wg6,wmE,wru,wrL,wtt] (.node [wg6,wmE,wri,wrx,wyS] (.node [wg6,wmE,wrg,wwe,wyI] (.node [wg6,wmE,wrg,wv7,wyS] .nil .nil) (.node [wg6,wmE,wrg,wwe,wyL] .nil .nil)) (.node [wg6,wmE,wrm,wwe,wyS] (.node [wg6,wmE,wrk,wrT,wwe] .nil .nil) .nil)) (.node [wg6,wmE,wrx,wrT,wt2] (.node [wg6,wmE,wrx,wrT,wtt] (.node [wg6,wmE,wrw,wrS,wtt] .nil .nil) .nil) (.node [wg6,wmE,wrx,wsX,wyS] (.node [wg6,wmE,wrx,wsf,wtt] .nil .nil) .nil))) (.node [wg6,wmE,wrI,wtt,wyS] (.node [wg6,wmE,wrx,wtt,wyL] (.node [wg6,wmE,wrx,wtt,wya] (.node [wg6,wmE,wrx,wtm,wyS] .nil .nil) (.node [wg6,wmE,wrx,wtt,wyI] .nil .nil)) (.node [wg6,wmE,wrH,wwe,wyS] (.node [wg6,wmE,wrB,wtt,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wrT,wta,wwe] (.node [wg6,wmE,wrT,wsd,wtt] (.node [wg6,wmE,wrJ,wsK,wyS] .nil .nil) .nil) (.node [wg6,wmE,wrT,wtm,wwe] (.node [wg6,wmE,wrT,wtj,wwe] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrlrl_ok : everyKey (rowOK 3 level3) level4rrlrl = true := by decide +kernel
def level4rrlrr : BinaryTree (List W) := (.node [wg6,wmE,wtj,wv5,wyS] (.node [wg6,wmE,wsK,wyo,wyS] (.node [wg6,wmE,wrZ,wtt,wwe] (.node [wg6,wmE,wrT,wtt,wv7] (.node [wg6,wmE,wrT,wtt,wv4] .nil .nil) (.node [wg6,wmE,wrV,wtt,wwe] .nil .nil)) (.node [wg6,wmE,wr2,wtt,wvJ] (.node [wg6,wmE,wr0,wsY,wwe] .nil .nil) .nil)) (.node [wg6,wmE,wte,wwe,wyD] (.node [wg6,wmE,wte,wvZ,wyS] (.node [wg6,wmE,wsY,wwe,wAE] .nil .nil) .nil) (.node [wg6,wmE,wtj,wv4,wyS] (.node [wg6,wmE,wtj,wv4,wyI] .nil .nil) .nil))) (.node [wg6,wmE,wtk,wv4,wyS] (.node [wg6,wmE,wtj,wwe,wyJ] (.node [wg6,wmE,wtj,wwa,wyS] (.node [wg6,wmE,wtj,wv7,wyS] .nil .nil) (.node [wg6,wmE,wtj,wwe,wyI] .nil .nil)) (.node [wg6,wmE,wtj,wwe,wyO] (.node [wg6,wmE,wtj,wwe,wyL] .nil .nil) .nil)) (.node [wg6,wmE,wtm,wv7,wyS] (.node [wg6,wmE,wtm,wv4,wyS] (.node [wg6,wmE,wtl,wwe,wyI] .nil .nil) .nil) (.node [wg6,wmE,wtm,wwe,wyL] (.node [wg6,wmE,wtm,wwe,wyI] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrlrr_ok : everyKey (rowOK 3 level3) level4rrlrr = true := by decide +kernel
def level4rrlr : BinaryTree (List W) := .node [wg6,wmE,wrT,wtt,wvV] level4rrlrl level4rrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrlr_ok : everyKey (rowOK 3 level3) level4rrlr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrlrl && everyKey (rowOK 3 level3) level4rrlrr) = true
  rw [level4rrlrl_ok, level4rrlrr_ok]
  decide +kernel
def level4rrl : BinaryTree (List W) := .node [wg6,wmE,wrg,wv4,wyS] level4rrll level4rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrl_ok : everyKey (rowOK 3 level3) level4rrl = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrll && everyKey (rowOK 3 level3) level4rrlr) = true
  rw [level4rrll_ok, level4rrlr_ok]
  decide +kernel
def level4rrrll : BinaryTree (List W) := (.node [wg6,wmE,wwe,wyg,wyS] (.node [wg6,wmE,wtt,wv4,wyQ] (.node [wg6,wmE,wtt,wv4,wyI] (.node [wg6,wmE,wtt,wvJ,wAO] (.node [wg6,wmE,wtr,wwe,wyI] .nil .nil) (.node [wg6,wmE,wtt,wvZ,wyD] .nil .nil)) (.node [wg6,wmE,wtt,wv4,wyL] (.node [wg6,wmE,wtt,wv4,wyK] .nil .nil) .nil)) (.node [wg6,wmE,wtt,wwc,wyI] (.node [wg6,wmE,wtt,wv7,wyI] (.node [wg6,wmE,wtt,wv6,wyI] .nil .nil) (.node [wg6,wmE,wtt,wv7,wyL] .nil .nil)) (.node [wg6,wmE,wtt,wyk,wyS] (.node [wg6,wmE,wtt,wwe,wAA] .nil .nil) .nil))) (.node [wg6,wpW,wtt,wwe,wzr] (.node [wg6,wnE,wtt,wwe,wyS] (.node [wg6,wmE,wyl,wAH,wA8] (.node [wg6,wmE,wyh,wAR,wA8] .nil .nil) (.node [wg6,wmE,wyr,wAB,wA8] .nil .nil)) (.node [wg6,wnT,wtt,wwe,wyS] (.node [wg6,wnM,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wrO,wtt,wwe,wyS] (.node [wg6,wpW,wt4,wwe,wyS] (.node [wg6,wpW,wtt,wwP,wyS] .nil .nil) .nil) (.node [wg6,wtt,wwe,wxQ,wyS] (.node [wg6,wtt,wvf,wwe,wyS] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrrll_ok : everyKey (rowOK 3 level3) level4rrrll = true := by decide +kernel
def level4rrrlr : BinaryTree (List W) := (.node [wia,wmE,wov,wwe,wyS] (.node [wia,wiC,wmE,wwe,wyS] (.node [wg7,wmr,wtt,wwe,wyS] (.node [wg6,wtt,wwP,wyS,wAX] (.node [wg6,wtt,wwe,wzr,wAX] .nil .nil) (.node [wg6,wt4,wwe,wyS,wAX] .nil .nil)) (.node [wh8,wim,wmE,wp6,wyS] (.node [wh3,wiq,wmE,wp6,wwe] .nil .nil) .nil)) (.node [wia,wkK,wmE,wwe,wyS] (.node [wia,wks,wp6,wwe,wyS] (.node [wia,wjl,wmE,wwe,wyS] .nil .nil) .nil) (.node [wia,wk2,wmE,wp6,wwe] (.node [wia,wkX,wmE,wp6,wyS] .nil .nil) .nil))) (.node [wia,wp6,wvg,wwe,wyS] (.node [wia,wmE,wq8,wwe,wyS] (.node [wia,wmE,wp6,wwe,wzT] (.node [wia,wmE,wp6,wwe,wyS] .nil .nil) (.node [wia,wmE,wp6,wxj,wyS] .nil .nil)) (.node [wia,wmE,wwe,wyS,wA8] (.node [wia,wmE,wvw,wwe,wyS] .nil .nil) .nil)) (.node [wim,wjl,wmE,wtt,wyS] (.node [wim,wiC,wmE,wtt,wyS] (.node [wil,wiq,wmE,wp6,wtt] .nil .nil) .nil) (.node [wim,wkc,wmE,wtt,wyS] (.node [wim,wjY,wp6,wtt,wyS] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrrlr_ok : everyKey (rowOK 3 level3) level4rrrlr = true := by decide +kernel
def level4rrrl : BinaryTree (List W) := .node [wg6,wtt,wwe,wyS,wAj] level4rrrll level4rrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrrl_ok : everyKey (rowOK 3 level3) level4rrrl = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrrll && everyKey (rowOK 3 level3) level4rrrlr) = true
  rw [level4rrrll_ok, level4rrrlr_ok]
  decide +kernel
def level4rrrrl : BinaryTree (List W) := (.node [wiq,wmE,wpx,wtt,wwe] (.node [wim,wmE,wtt,wyS,wA8] (.node [wim,wmE,wp6,wuC,wyS] (.node [wim,wmE,wp6,wtt,wyS] (.node [wim,wmE,woX,wtt,wyS] .nil .nil) (.node [wim,wmE,wp6,wtt,wz0] .nil .nil)) (.node [wim,wmE,wtt,wx3,wyS] (.node [wim,wmE,wqO,wtt,wyS] .nil .nil) .nil)) (.node [wiq,wi5,wp6,wtt,wwe] (.node [wiq,wiC,wmE,wtt,wwe] (.node [wim,wp6,wtt,wxR,wyS] .nil .nil) .nil) (.node [wiq,wjl,wmE,wtt,wwe] (.node [wiq,wja,wmE,wtt,wwe] .nil .nil) .nil))) (.node [wiq,wp6,wtt,wwe,wAk] (.node [wiq,wmE,wqt,wtt,wwe] (.node [wiq,wmE,wp6,wtt,wxs] (.node [wiq,wmE,wp6,wtt,wwe] .nil .nil) (.node [wiq,wmE,wp6,wuL,wwe] .nil .nil)) (.node [wiq,wmE,wtt,wwe,wA8] (.node [wiq,wmE,wtt,wwe,wAs] .nil .nil) .nil)) (.node [wiC,wrP,wtt,wwe,wyS] (.node [wiv,wrO,wtt,wwe,wyS] (.node [wir,wrP,wtt,wwe,wyS] .nil .nil) .nil) (.node [wjt,wrP,wtt,wwe,wyS] (.node [wjl,wrP,wtt,wwe,wyS] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrrrl_ok : everyKey (rowOK 3 level3) level4rrrrl = true := by decide +kernel
def level4rrrrr : BinaryTree (List W) := (.node [wp6,wrK,wrP,wtt,wwe] (.node [wpi,wrP,wtt,wwe,wyS] (.node [wmE,wnQ,wtt,wwe,wyS] (.node [wmE,wnQ,wtt,wv4,wyS] (.node [wmE,wnQ,wtj,wwe,wyS] .nil .nil) (.node [wmE,wnQ,wtt,wwe,wyI] .nil .nil)) (.node [wph,wrP,wtt,wwe,wyS] (.node [wmE,wtt,wwe,wyy,wyS] .nil .nil) .nil)) (.node [wp6,wre,wrP,wwe,wyS] (.node [wp6,wrc,wrP,wwe,wyS] (.node [wpW,wrP,wtt,wwe,wyS] .nil .nil) .nil) (.node [wp6,wrv,wrP,wtt,wyS] (.node [wp6,wrt,wrP,wtt,wyS] .nil .nil) .nil))) (.node [wp6,wrP,wtt,wwP,wyS] (.node [wp6,wrP,wtt,wwe,wyE] (.node [wp6,wrP,wtf,wwe,wyS] (.node [wp6,wrM,wrP,wtt,wwe] .nil .nil) (.node [wp6,wrP,wtt,wv0,wyS] .nil .nil)) (.node [wp6,wrP,wtt,wwe,wzr] (.node [wp6,wrP,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wrP,wr5,wtt,wwe,wyS] (.node [wrO,wtt,wwe,wyS,wAX] (.node [wp6,wrP,wt4,wwe,wyS] .nil .nil) .nil) (.node [wrP,wtt,wwe,wyS,wA8] (.node [wrP,wsB,wtt,wwe,wyS] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrrrr_ok : everyKey (rowOK 3 level3) level4rrrrr = true := by decide +kernel
def level4rrrr : BinaryTree (List W) := .node [wmr,wnQ,wtt,wwe,wyS] level4rrrrl level4rrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrrr_ok : everyKey (rowOK 3 level3) level4rrrr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrrrl && everyKey (rowOK 3 level3) level4rrrrr) = true
  rw [level4rrrrl_ok, level4rrrrr_ok]
  decide +kernel
def level4rrr : BinaryTree (List W) := .node [wim,wkn,wmE,wp6,wtt] level4rrrl level4rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrr_ok : everyKey (rowOK 3 level3) level4rrr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrrl && everyKey (rowOK 3 level3) level4rrrr) = true
  rw [level4rrrl_ok, level4rrrr_ok]
  decide +kernel
def level4rr : BinaryTree (List W) := .node [wg6,wmE,wtp,wv4,wyS] level4rrl level4rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rr_ok : everyKey (rowOK 3 level3) level4rr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrl && everyKey (rowOK 3 level3) level4rrr) = true
  rw [level4rrl_ok, level4rrr_ok]
  decide +kernel
def level4r : BinaryTree (List W) := .node [wg6,wmE,wp6,wuZ,wAR] level4rl level4rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4r_ok : everyKey (rowOK 3 level3) level4r = true := by
  change (_ && everyKey (rowOK 3 level3) level4rl && everyKey (rowOK 3 level3) level4rr) = true
  rw [level4rl_ok, level4rr_ok]
  decide +kernel
def level4 : BinaryTree (List W) := .node [wg6,wjF,wtt,wwe,wzy] level4l level4r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4_ok : everyKey (rowOK 3 level3) level4 = true := by
  change (_ && everyKey (rowOK 3 level3) level4l && everyKey (rowOK 3 level3) level4r) = true
  rw [level4l_ok, level4r_ok]
  decide +kernel
theorem closed4 : Closed 4 level4 := closed_next 3 (by decide) level4 level3 closed3 level4_ok
def level5llllll : BinaryTree (List W) := (.node [wb,wg7,wmE,wtt,wwe,wyS] (.node [wb,wg6,wmE,wtm,wwe,wyS] (.node [wb,wfN,wmE,wtt,wwe,wyS] (.node [wb,wcv,wg6,wmE,wwe,wyS] (.node [wb,waf,wg6,wmE,wtt,wwe] (.node [wa,wg6,wmr,wtt,wwe,wyS] .nil .nil) (.node [wb,wbm,wg6,wmE,wtt,wyS] .nil .nil)) (.node [wb,wfz,wg6,wtt,wwe,wyS] (.node [wb,wfx,wiv,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wb,wg6,wmE,wrx,wtt,wyS] (.node [wb,wg6,wmE,wrg,wwe,wyS] (.node [wb,wg6,wmr,wtt,wwe,wyS] .nil .nil) .nil) (.node [wb,wg6,wmE,wtj,wwe,wyS] (.node [wb,wg6,wmE,wrT,wtt,wwe] .nil .nil) .nil))) (.node [wb,wg6,wmE,wtt,wwe,wyT] (.node [wb,wg6,wmE,wtt,wwe,wyI] (.node [wb,wg6,wmE,wtt,wv7,wyS] (.node [wb,wg6,wmE,wtt,wv4,wyS] .nil .nil) .nil) (.node [wb,wg6,wmE,wtt,wwe,wyS] (.node [wb,wg6,wmE,wtt,wwe,wyL] .nil .nil) .nil)) (.node [wb,wg6,wmE,wtt,wwN,wyS] (.node [wb,wg6,wmE,wtt,wwf,wyS] (.node [wb,wg6,wmE,wtt,wwe,wzp] .nil .nil) .nil) (.node [wb,wg6,wmE,wt2,wwe,wyS] (.node [wb,wg6,wmE,wtu,wwe,wyS] .nil .nil) .nil)))) (.node [wh,wg6,wmr,wtt,wwe,wyS] (.node [we,wg6,wmr,wtt,wwe,wyS] (.node [wc,wg6,wmE,wtt,wwe,wyI] (.node [wc,wg6,wmr,wtt,wwe,wyS] (.node [wc,wcv,wg6,wmE,wwe,wyS] .nil .nil) (.node [wc,wg6,wmE,wtt,wv4,wyS] .nil .nil)) (.node [we,wbm,wg6,wmE,wtt,wyS] (.node [wd,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wf,wg6,wmE,wtt,wwe,wyS] (.node [we,wg6,wmE,wtt,wwe,wyI] (.node [we,wg6,wmE,wtj,wwe,wyS] .nil .nil) .nil) (.node [wh,waf,wg6,wmE,wtt,wwe] (.node [wg,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wl,wdm,wg6,wtt,wwe,wyS] (.node [wi,wg6,wmE,wtt,wwe,wyS] (.node [wh,wg6,wmE,wtt,wv4,wyS] (.node [wh,wg6,wmE,wtj,wwe,wyS] .nil .nil) .nil) (.node [wk,wg6,wmE,wtt,wwe,wyS] (.node [wj,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wx,wg6,wjl,wtt,wwe,wyS] (.node [wt,wg6,wjl,wtt,wwe,wyS] (.node [wp,wg6,wjl,wtt,wwe,wyS] .nil .nil) .nil) (.node [wx,wg6,wmE,wrT,wtt,wwe] (.node [wx,wg6,wjF,wtt,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llllll_ok : everyKey (rowOK 4 level4) level5llllll = true := by decide +kernel
def level5lllllr : BinaryTree (List W) := (.node [wT,wfs,wg6,wjl,wtt,wwe] (.node [wK,wip,wmE,wp6,wtt,wwe] (.node [wK,wg6,wmr,wtt,wwe,wyS] (.node [wK,wT,wg6,wjl,wtt,wwe] (.node [wz,wg6,wjl,wtt,wwe,wyS] (.node [wy,wg6,wmE,wtt,wwe,wyS] .nil .nil) (.node [wH,wg6,wjl,wtt,wwe,wyS] .nil .nil)) (.node [wK,wg6,wjC,wtt,wwe,wyS] (.node [wK,wc2,wip,wmE,wtt,wwe] .nil .nil) .nil)) (.node [wK,wip,wiC,wmE,wtt,wwe] (.node [wK,whp,wmE,wp6,wtt,wwe] (.node [wK,who,wmE,wp6,wtt,wwe] .nil .nil) .nil) (.node [wK,wip,wmE,wpx,wtt,wwe] (.node [wK,wip,wjl,wmE,wtt,wwe] .nil .nil) .nil))) (.node [wP,wg6,wjl,wtt,wwe,wAo] (.node [wK,wiq,wmE,wp6,wtt,wwe] (.node [wK,wip,wmE,wtt,wwe,wA8] (.node [wK,wip,wmE,wqt,wtt,wwe] .nil .nil) .nil) (.node [wP,wgI,wg6,wmE,wtt,wwe] (.node [wM,wgS,wg6,wmE,wtt,wwe] .nil .nil) .nil)) (.node [wT,wcp,wg6,wjl,wtt,wwe] (.node [wT,wbg,wg6,wjl,wtt,wwe] (.node [wS,wg6,wmr,wtt,wwe,wyS] .nil .nil) .nil) (.node [wT,wfs,wg6,wiC,wtt,wwe] (.node [wT,wc2,wfs,wg6,wtt,wwe] .nil .nil) .nil)))) (.node [wT,wgI,wg6,wjl,wtt,wwe] (.node [wT,wfs,wg6,wp6,wuu,wwe] (.node [wT,wfs,wg6,wlI,wp6,wtt] (.node [wT,wfs,wg6,wlg,wp6,wwe] (.node [wT,wfs,wg6,wjK,wtt,wwe] .nil .nil) .nil) (.node [wT,wfs,wg6,wp6,wtt,wxd] (.node [wT,wfs,wg6,wp6,wtt,wwe] .nil .nil) .nil)) (.node [wT,wfv,wg6,wp6,wtt,wwe] (.node [wT,wfs,wg6,wtt,wwe,wA8] (.node [wT,wfs,wg6,wrY,wtt,wwe] .nil .nil) .nil) (.node [wT,wfL,wg6,wp6,wtt,wwe] (.node [wT,wfw,wg6,wp6,wtt,wwe] .nil .nil) .nil))) (.node [wT,wg6,wjl,wtt,wwe,wAf] (.node [wT,wgT,wg6,wp6,wtt,wwe] (.node [wT,wgR,wg6,wjl,wtt,wwe] (.node [wT,wgI,wg6,wp6,wtt,wwe] .nil .nil) .nil) (.node [wT,wg6,wjl,wtt,wwe,wyS] (.node [wT,wg6,wir,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wT,wg6,wjl,wtt,wwe,wAR] (.node [wT,wg6,wjl,wtt,wwe,wAH] (.node [wT,wg6,wjl,wtt,wwe,wAo] .nil .nil) .nil) (.node [wT,wg6,wmr,wtt,wwe,wyS] (.node [wT,wg6,wjK,wtt,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllllr_ok : everyKey (rowOK 4 level4) level5lllllr = true := by decide +kernel
def level5lllll : BinaryTree (List W) := .node [wy,wg6,wi5,wtt,wwe,wyS] level5llllll level5lllllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllll_ok : everyKey (rowOK 4 level4) level5lllll = true := by
  change (_ && everyKey (rowOK 4 level4) level5llllll && everyKey (rowOK 4 level4) level5lllllr) = true
  rw [level5llllll_ok, level5lllllr_ok]
  decide +kernel
def level5llllrl : BinaryTree (List W) := (.node [wY,wg6,wjF,wtt,wwe,wyS] (.node [wY,web,wg6,wmE,woN,wtt] (.node [wT,wg6,wp6,wtt,wwe,wAk] (.node [wT,wg6,wmX,wp6,wtt,wwe] (.node [wT,wg6,wmE,wp6,wuu,wwe] (.node [wT,wg6,wmE,wp6,wtt,wxs] .nil .nil) (.node [wT,wg6,wmE,wp6,wuL,wwe] .nil .nil)) (.node [wT,wg6,wp6,wtt,wwe,wyE] (.node [wT,wg6,wpW,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wV,wg6,wmE,wp6,wtt,wwe] (.node [wU,wg6,wmE,wp6,wtt,wwe] (.node [wT,wg6,wtt,wwe,wyS,wAX] .nil .nil) .nil) (.node [wY,web,wg6,wmE,woe,wwe] (.node [wY,web,wg6,wjF,wtt,wwe] .nil .nil) .nil))) (.node [wY,wek,wg6,wmE,wtt,wwe] (.node [wY,web,wg6,wmE,wud,wwe] (.node [wY,web,wg6,wmE,wtt,wwX] (.node [wY,web,wg6,wmE,wtt,wwe] .nil .nil) .nil) (.node [wY,wei,wg6,wmE,wtt,wwe] (.node [wY,web,wg6,wnV,wtt,wwe] .nil .nil) .nil)) (.node [wY,wgI,wg6,wmE,wtt,wwe] (.node [wY,weB,wg6,wmE,wtt,wwe] (.node [wY,wem,wg6,wmE,wtt,wwe] .nil .nil) .nil) (.node [wY,wg6,wjl,wtt,wwe,wAo] (.node [wY,wgS,wg6,wmE,wtt,wwe] .nil .nil) .nil)))) (.node [wY,wg6,wmE,wtt,wwe,wAs] (.node [wY,wg6,wmE,wp6,wuu,wwe] (.node [wY,wg6,wmE,wp6,wtt,wxd] (.node [wY,wg6,wmE,wp6,wtt,wwX] (.node [wY,wg6,wmr,wtt,wwe,wyS] .nil .nil) .nil) (.node [wY,wg6,wmE,wp6,wud,wwe] (.node [wY,wg6,wmE,wp6,wtt,wxs] .nil .nil) .nil)) (.node [wY,wg6,wmE,wrT,wtt,wwe] (.node [wY,wg6,wmE,wqt,wtt,wwe] (.node [wY,wg6,wmE,wp6,wuL,wwe] .nil .nil) .nil) (.node [wY,wg6,wmE,wtt,wwe,wyI] (.node [wY,wg6,wmE,wrY,wtt,wwe] .nil .nil) .nil))) (.node [w0,wg6,wmE,wq8,wtt,wwe] (.node [wZ,wg6,wmE,wp6,wtt,wwe] (.node [wY,wg6,wp6,wtt,wwe,wAk] (.node [wY,wg6,wnV,wp6,wtt,wwe] .nil .nil) .nil) (.node [w0,wg6,wmE,wp6,wtt,wwe] (.node [wZ,wg6,wmE,wqO,wtt,wwe] .nil .nil) .nil)) (.node [w4,wg6,wjl,wtt,wwe,wyS] (.node [w3,wg6,wmE,wr5,wtt,wwe] (.node [w3,wg6,wmE,wp6,wtt,wwe] .nil .nil) .nil) (.node [w6,wbY,wg6,wjl,wwe,wyS] (.node [w5,wg6,wmE,wp6,wyr,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llllrl_ok : everyKey (rowOK 4 level4) level5llllrl = true := by decide +kernel
def level5llllrr : BinaryTree (List W) := (.node [w9,wg6,wmE,wpb,wtt,wyS] (.node [w7,wg6,wjl,wtt,wwe,wyS] (.node [w6,wfZ,wg6,wmE,wp6,wwe] (.node [w6,wcp,wg6,wmE,wwe,wA8] (.node [w6,wcp,wg6,wjl,wmE,wwe] (.node [w6,wcp,wg6,wiC,wmE,wwe] .nil .nil) (.node [w6,wcp,wg6,wmE,wp6,wwe] .nil .nil)) (.node [w6,weL,wg6,wmE,wp6,wwe] (.node [w6,wcF,wg6,wmE,wp6,wwe] .nil .nil) .nil)) (.node [w6,wg6,wmE,wpb,wwe,wyS] (.node [w6,wg6,wmr,wtt,wwe,wyS] (.node [w6,wg6,whK,wmE,wp6,wwe] .nil .nil) .nil) (.node [w6,wg6,wmE,wp6,wyl,wyS] (.node [w6,wg6,wmE,wp6,wwe,wwC] .nil .nil) .nil))) (.node [w9,wbg,wg6,wmE,wtt,wA8] (.node [w9,wbg,wg6,wiC,wmE,wtt] (.node [w9,wbg,wc2,wg6,wmE,wtt] (.node [w9,waT,wg6,wjl,wtt,wyS] .nil .nil) .nil) (.node [w9,wbg,wg6,wmE,wp6,wtt] (.node [w9,wbg,wg6,wjl,wmE,wtt] .nil .nil) .nil)) (.node [w9,wfS,wg6,wmE,wp6,wtt] (.node [w9,weF,wg6,wmE,wp6,wtt] (.node [w9,wbw,wg6,wmE,wp6,wtt] .nil .nil) .nil) (.node [w9,wg6,wmr,wtt,wwe,wyS] (.node [w9,wg6,whx,wmE,wp6,wtt] .nil .nil) .nil)))) (.node [wae,wg6,wiC,wmE,wtt,wwe] (.node [wad,wg6,wmE,wtt,wwe,wAX] (.node [waa,wg6,wjl,wtt,wwe,wyS] (.node [w9,wg6,wmE,wp6,wyh,wyS] (.node [w9,wg6,wmE,wp6,wtt,wtR] .nil .nil) .nil) (.node [wad,wg6,wmE,wp6,wtt,wwe] (.node [wad,wg6,wjl,wmE,wtt,wwe] .nil .nil) .nil)) (.node [wae,wc2,wg6,wmE,wtt,wwe] (.node [wae,wcu,wg6,wmE,wp6,wwe] (.node [wae,wbl,wg6,wmE,wp6,wtt] .nil .nil) .nil) (.node [wae,weq,wg6,wmE,wtt,wwe] (.node [wae,wdl,wp6,wtt,wwe,wA1] .nil .nil) .nil))) (.node [wae,wg6,wmE,wtt,wwe,wA8] (.node [wae,wg6,wmE,wp6,wtf,wwe] (.node [wae,wg6,wmE,wpW,wtt,wwe] (.node [wae,wg6,wjl,wmE,wtt,wwe] .nil .nil) .nil) (.node [wae,wg6,wmE,wp6,wtt,wwe] (.node [wae,wg6,wmE,wp6,wtt,wv0] .nil .nil) .nil)) (.node [waf,wcv,wg6,wmE,wp6,wwe] (.node [waf,wbm,wg6,wmE,wtt,wA8] (.node [waf,wbm,wg6,wmE,wp6,wtt] .nil .nil) .nil) (.node [waf,wc2,wg6,wmE,wtt,wwe] (.node [waf,wcv,wg6,wmE,wwe,wA8] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llllrr_ok : everyKey (rowOK 4 level4) level5llllrr = true := by decide +kernel
def level5llllr : BinaryTree (List W) := .node [w6,wcp,wc2,wg6,wmE,wwe] level5llllrl level5llllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llllr_ok : everyKey (rowOK 4 level4) level5llllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llllrl && everyKey (rowOK 4 level4) level5llllrr) = true
  rw [level5llllrl_ok, level5llllrr_ok]
  decide +kernel
def level5llll : BinaryTree (List W) := .node [wT,wg6,wmE,wp6,wtt,wxd] level5lllll level5llllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llll_ok : everyKey (rowOK 4 level4) level5llll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lllll && everyKey (rowOK 4 level4) level5llllr) = true
  rw [level5lllll_ok, level5llllr_ok]
  decide +kernel
def level5lllrll : BinaryTree (List W) := (.node [waj,wg6,wmE,wtt,wwe,wA8] (.node [waf,wg6,wmE,wp6,wtt,wv4] (.node [waf,wg6,wmr,wp6,wtt,wwe] (.node [waf,wg6,wiC,wmE,wtt,wwe] (.node [waf,wfz,wg6,wp6,wtt,wwe] (.node [waf,weZ,wmE,wtt,wwe,wA8] .nil .nil) (.node [waf,wfz,wg6,wtt,wwe,wA8] .nil .nil)) (.node [waf,wg6,wmr,wmE,wtt,wwe] (.node [waf,wg6,wjl,wmE,wtt,wwe] .nil .nil) .nil)) (.node [waf,wg6,wmr,wtt,wwe,wA8] (.node [waf,wg6,wmr,wtt,wwe,wyS] (.node [waf,wg6,wmr,wtt,wwe] .nil .nil) .nil) (.node [waf,wg6,wmE,wp6,wtj,wwe] (.node [waf,wg6,wmE,wpo,wtt,wwe] .nil .nil) .nil))) (.node [waf,wg6,wmE,wtt,wwe,wA8] (.node [waf,wg6,wmE,wtj,wwe,wA8] (.node [waf,wg6,wmE,wqt,wtt,wwe] (.node [waf,wg6,wmE,wp6,wtt,wwe] .nil .nil) .nil) (.node [waf,wg6,wmE,wtt,wwe,wyI] (.node [waf,wg6,wmE,wtt,wv4,wA8] .nil .nil) .nil)) (.node [wag,wg6,wmE,wtt,wwe,wA8] (.node [wag,wg6,wmE,wp6,wtt,wwe] (.node [waf,wiC,wmE,wtt,wwe,wA8] .nil .nil) .nil) (.node [waj,wg6,wmE,wp6,wtt,wwe] (.node [wai,wg6,wmE,wp6,wtt,wwe] .nil .nil) .nil)))) (.node [waE,wg6,wjl,wtt,wwe,wyS] (.node [wau,wg6,wjl,wtt,wwe,wyS] (.node [wan,wg6,wmE,wp6,wtt,wwe] (.node [wam,wg6,wmE,wp6,wtt,wwe] (.node [wal,wg6,wmE,wp6,wtt,wwe] .nil .nil) (.node [wam,wg6,wmE,wtt,wwe,wA8] .nil .nil)) (.node [waq,wg6,wjl,wtt,wwe,wyS] (.node [wap,wmE,wtt,wwe,wyS,wAX] .nil .nil) .nil)) (.node [wav,wg6,wjY,wtt,wwe,wyS] (.node [wau,wg6,wmE,wrx,wtt,wyS] (.node [wau,wg6,wj2,wtt,wwe,wyS] .nil .nil) .nil) (.node [waw,wg6,wjl,wtt,wwe,wyS] (.node [wav,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil))) (.node [waH,whz,wmE,wp6,wtt,wyS] (.node [waH,wg6,wjZ,wtt,wwe,wyS] (.node [waH,wc2,wie,wmE,wtt,wyS] (.node [waH,waT,wg6,wjl,wtt,wyS] .nil .nil) .nil) (.node [waH,why,wmE,wp6,wtt,wyS] (.node [waH,wg6,wmr,wtt,wwe,wyS] .nil .nil) .nil)) (.node [waH,wie,wmE,woX,wtt,wyS] (.node [waH,wie,wjl,wmE,wtt,wyS] (.node [waH,wie,wiC,wmE,wtt,wyS] .nil .nil) .nil) (.node [waH,wie,wmE,wqO,wtt,wyS] (.node [waH,wie,wmE,wp6,wtt,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrll_ok : everyKey (rowOK 4 level4) level5lllrll = true := by decide +kernel
def level5lllrlr : BinaryTree (List W) := (.node [waT,wgr,wg6,wjl,wtt,wyS] (.node [waT,wfm,wg6,wll,wp6,wyS] (.node [waS,wg6,wmr,wtt,wwe,wyS] (.node [waO,wgq,wg6,wmE,wtt,wyS] (.node [waK,wgs,wg6,wmE,wtt,wyS] (.node [waH,wim,wmE,wp6,wtt,wyS] .nil .nil) (.node [waN,wg6,wmE,wp6,wwe,wyS] .nil .nil)) (.node [waQ,wg6,wmE,wp6,wwe,wyS] (.node [waO,wg6,wjl,wtt,wxV,wyS] .nil .nil) .nil)) (.node [waT,wfm,wg6,wiC,wtt,wyS] (.node [waT,wc2,wfm,wg6,wtt,wyS] (.node [waT,wci,wg6,wjl,wtt,wyS] .nil .nil) .nil) (.node [waT,wfm,wg6,wkf,wtt,wyS] (.node [waT,wfm,wg6,wjl,wtt,wyS] .nil .nil) .nil))) (.node [waT,wfm,wg6,wtt,wyS,wA8] (.node [waT,wfm,wg6,wp6,wtt,wzN] (.node [waT,wfm,wg6,wp6,wtt,wyS] (.node [waT,wfm,wg6,wm7,wp6,wtt] .nil .nil) .nil) (.node [waT,wfm,wg6,wrG,wtt,wyS] (.node [waT,wfm,wg6,wp6,wuq,wyS] .nil .nil) .nil)) (.node [waT,wfQ,wg6,wp6,wtt,wyS] (.node [waT,wfw,wg6,wp6,wtt,wyS] (.node [waT,wfq,wg6,wp6,wtt,wyS] .nil .nil) .nil) (.node [waT,wgq,wg6,wp6,wtt,wyS] (.node [waT,wgq,wg6,wjl,wtt,wyS] .nil .nil) .nil)))) (.node [waT,wg6,wmE,wp6,wuq,wyS] (.node [waT,wg6,wjl,wtt,wyr,wyS] (.node [waT,wg6,wjl,wtt,wwe,wyS] (.node [waT,wg6,wir,wtt,wwe,wyS] (.node [waT,wgt,wg6,wp6,wtt,wyS] .nil .nil) .nil) (.node [waT,wg6,wjl,wtt,wxV,wyS] (.node [waT,wg6,wjl,wtt,wxI,wyS] .nil .nil) .nil)) (.node [waT,wg6,wmr,wtt,wwe,wyS] (.node [waT,wg6,wkf,wtt,wwe,wyS] (.node [waT,wg6,wjl,wtt,wyS,wAR] .nil .nil) .nil) (.node [waT,wg6,wmE,wp6,wtt,wz0] (.node [waT,wg6,wmE,wp6,wtt,wzN] .nil .nil) .nil))) (.node [waT,wg6,wtt,wwe,wyS,wAX] (.node [waT,wg6,wpW,wtt,wwe,wyS] (.node [waT,wg6,wnc,wp6,wtt,wyS] (.node [waT,wg6,wmE,wp6,wuC,wyS] .nil .nil) .nil) (.node [waT,wg6,wp6,wtt,wxR,wyS] (.node [waT,wg6,wp6,wtt,wv0,wyS] .nil .nil) .nil)) (.node [waV,wg6,wmE,wp6,wtt,wAR] (.node [waV,wg6,wjl,wtt,wwe,wyS] (.node [waU,wg6,wmE,wp6,wtt,wyS] .nil .nil) .nil) (.node [waY,wg6,wmE,wp6,wwe,wyS] (.node [waW,wg6,wmE,wp6,wtt,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrlr_ok : everyKey (rowOK 4 level4) level5lllrlr = true := by decide +kernel
def level5lllrl : BinaryTree (List W) := .node [waH,wie,wmE,wtt,wyS,wA8] level5lllrll level5lllrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrl_ok : everyKey (rowOK 4 level4) level5lllrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lllrll && everyKey (rowOK 4 level4) level5lllrlr) = true
  rw [level5lllrll_ok, level5lllrlr_ok]
  decide +kernel
def level5lllrrl : BinaryTree (List W) := (.node [wa0,wg6,wmE,wtt,wv4,wyS] (.node [wa0,wg6,wjl,wtt,wxV,wyS] (.node [wa0,wd5,wg6,wmE,wtt,wyS] (.node [wa0,wdW,wg6,wmE,wtt,wzy] (.node [wa0,wdW,wg6,wmE,wqK,wtt] (.node [wa0,wdW,wg6,wmE,woj,wyS] .nil .nil) (.node [wa0,wdW,wg6,wmE,wtt,wyS] .nil .nil)) (.node [wa0,wdW,wg6,wnO,wtt,wyS] (.node [wa0,wdW,wg6,wmE,wt9,wyS] .nil .nil) .nil)) (.node [wa0,weE,wg6,wmE,wtt,wyS] (.node [wa0,wem,wg6,wmE,wtt,wyS] (.node [wa0,wd8,wg6,wmE,wtt,wyS] .nil .nil) .nil) (.node [wa0,wgs,wg6,wmE,wtt,wyS] (.node [wa0,wgq,wg6,wmE,wtt,wyS] .nil .nil) .nil))) (.node [wa0,wg6,wmE,wp6,wt9,wyS] (.node [wa0,wg6,wmE,wp6,wtt,wzy] (.node [wa0,wg6,wmr,wtt,wwe,wyS] (.node [wa0,wg6,wj2,wtt,wwe,wyS] .nil .nil) .nil) (.node [wa0,wg6,wmE,wp6,wtt,wz0] (.node [wa0,wg6,wmE,wp6,wtt,wzN] .nil .nil) .nil)) (.node [wa0,wg6,wmE,wqO,wtt,wyS] (.node [wa0,wg6,wmE,wp6,wuC,wyS] (.node [wa0,wg6,wmE,wp6,wuq,wyS] .nil .nil) .nil) (.node [wa0,wg6,wmE,wrG,wtt,wyS] (.node [wa0,wg6,wmE,wrx,wtt,wyS] .nil .nil) .nil)))) (.node [wa8,wg6,wmE,wp6,wwe,wAH] (.node [wa2,wg6,wmE,wp6,wtt,wAR] (.node [wa0,wg6,wp6,wtt,wxR,wyS] (.node [wa0,wg6,wnO,wp6,wtt,wyS] (.node [wa0,wg6,wmE,wtt,wx3,wyS] .nil .nil) .nil) (.node [wa1,wg6,wmE,wqt,wtt,wyS] (.node [wa1,wg6,wmE,wp6,wtt,wyS] .nil .nil) .nil)) (.node [wa6,wg6,wmE,wp6,wtt,wyS] (.node [wa3,wg6,wmE,wq8,wtt,wyS] (.node [wa3,wg6,wmE,wp6,wtt,wyS] .nil .nil) .nil) (.node [wa7,wg6,wjl,wtt,wwe,wyS] (.node [wa6,wg6,wmE,wr5,wtt,wyS] .nil .nil) .nil))) (.node [wa9,wci,wg6,wmE,wyS,wA8] (.node [wa9,wci,wg6,wiC,wmE,wyS] (.node [wa9,wci,wc2,wg6,wmE,wyS] (.node [wa9,wbY,wg6,wjl,wwe,wyS] .nil .nil) .nil) (.node [wa9,wci,wg6,wmE,wp6,wyS] (.node [wa9,wci,wg6,wjl,wmE,wyS] .nil .nil) .nil)) (.node [wa9,wfX,wg6,wmE,wp6,wyS] (.node [wa9,weJ,wg6,wmE,wp6,wyS] (.node [wa9,wcJ,wg6,wmE,wp6,wyS] .nil .nil) .nil) (.node [wa9,wg6,wmr,wtt,wwe,wyS] (.node [wa9,wg6,whI,wmE,wp6,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrrl_ok : everyKey (rowOK 4 level4) level5lllrrl = true := by decide +kernel
def level5lllrrr : BinaryTree (List W) := (.node [wbl,wcu,wg6,wmE,wp6,wyS] (.node [wbg,wbw,wg6,wmE,wp6,wtt] (.node [wbd,wg6,wiC,wmE,wwe,wyS] (.node [wbb,wg6,wmE,wp6,wwe,wyS] (.node [wa9,wg6,wmE,wp6,wwe,wAB] (.node [wa9,wg6,wmE,wp6,wvK,wyS] .nil .nil) (.node [wba,wg6,wmE,wp6,wwe,wyS] .nil .nil)) (.node [wbd,wc2,wg6,wmE,wwe,wyS] (.node [wbc,wg6,wmE,wp6,wwe,wyS] .nil .nil) .nil)) (.node [wbd,wg6,wmE,wp6,wwe,wyS] (.node [wbd,wg6,wmE,wp6,wvJ,wAR] (.node [wbd,wg6,wjl,wmE,wwe,wyS] .nil .nil) .nil) (.node [wbe,wg6,wjl,wtt,wwe,wyS] (.node [wbd,wg6,wmE,wwe,wyS,wA8] .nil .nil) .nil))) (.node [wbg,wg6,wmE,wp6,wsM,wtt] (.node [wbg,wgv,wg6,wmE,wp6,wtt] (.node [wbg,wfo,wg6,wmE,wp6,wtt] (.node [wbg,wd0,wg6,wmE,wp6,wtt] .nil .nil) .nil) (.node [wbg,wg6,wmE,wpI,wtt,wwe] (.node [wbg,wg6,wmr,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wbk,wg6,wjl,wmE,wtt,wyS] (.node [wbh,wg6,wjl,wtt,wwe,wyS] (.node [wbg,wg6,wmE,wp6,wwe,wyh] .nil .nil) .nil) (.node [wbk,wg6,wmE,wtt,wyS,wAX] (.node [wbk,wg6,wmE,wp6,wtt,wyS] .nil .nil) .nil)))) (.node [wbm,wcv,wg6,wmE,wyS,wA8] (.node [wbl,wg6,wmE,wpW,wtt,wyS] (.node [wbl,weq,wg6,wmE,wtt,wyS] (.node [wbl,wdl,wp6,wtt,wyS,wA1] (.node [wbl,wc2,wg6,wmE,wtt,wyS] .nil .nil) .nil) (.node [wbl,wg6,wjl,wmE,wtt,wyS] (.node [wbl,wg6,wiC,wmE,wtt,wyS] .nil .nil) .nil)) (.node [wbl,wg6,wmE,wp6,wtt,wyS] (.node [wbl,wg6,wmE,wp6,wtt,wyE] (.node [wbl,wg6,wmE,wp6,wtf,wyS] .nil .nil) .nil) (.node [wbm,wcv,wg6,wmE,wp6,wyS] (.node [wbl,wg6,wmE,wtt,wyS,wA8] .nil .nil) .nil))) (.node [wbm,wg6,wiC,wmE,wtt,wyS] (.node [wbm,weZ,wmE,wtt,wyS,wA8] (.node [wbm,wdW,wg6,wmE,wtt,wyS] (.node [wbm,wc2,wg6,wmE,wtt,wyS] .nil .nil) .nil) (.node [wbm,wfz,wg6,wtt,wyS,wA8] (.node [wbm,wfz,wg6,wp6,wtt,wyS] .nil .nil) .nil)) (.node [wbm,wg6,wmr,wp6,wtt,wyS] (.node [wbm,wg6,wmr,wmE,wtt,wyS] (.node [wbm,wg6,wjl,wmE,wtt,wyS] .nil .nil) .nil) (.node [wbm,wg6,wmr,wtt,wyS] (.node [wbm,wg6,wmr,wtt,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrrr_ok : everyKey (rowOK 4 level4) level5lllrrr = true := by decide +kernel
def level5lllrr : BinaryTree (List W) := .node [wa9,wg6,wmE,wpI,wwe,wyS] level5lllrrl level5lllrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrr_ok : everyKey (rowOK 4 level4) level5lllrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lllrrl && everyKey (rowOK 4 level4) level5lllrrr) = true
  rw [level5lllrrl_ok, level5lllrrr_ok]
  decide +kernel
def level5lllr : BinaryTree (List W) := .node [wa0,wdW,wg6,wj2,wtt,wyS] level5lllrl level5lllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllr_ok : everyKey (rowOK 4 level4) level5lllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lllrl && everyKey (rowOK 4 level4) level5lllrr) = true
  rw [level5lllrl_ok, level5lllrr_ok]
  decide +kernel
def level5lll : BinaryTree (List W) := .node [waf,web,wg6,wmE,wtt,wwe] level5llll level5lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lll_ok : everyKey (rowOK 4 level4) level5lll = true := by
  change (_ && everyKey (rowOK 4 level4) level5llll && everyKey (rowOK 4 level4) level5lllr) = true
  rw [level5llll_ok, level5lllr_ok]
  decide +kernel
def level5llrlll : BinaryTree (List W) := (.node [wbx,wg6,wjl,wtt,wwe,wyS] (.node [wbp,wg6,wmE,wp6,wtt,wyS] (.node [wbm,wg6,wmE,wtt,wv4,wyS] (.node [wbm,wg6,wmE,wp6,wtt,wyS] (.node [wbm,wg6,wmE,wp6,wtj,wyS] (.node [wbm,wg6,wmE,woH,wtt,wyS] .nil .nil) (.node [wbm,wg6,wmE,wp6,wtt,wyI] .nil .nil)) (.node [wbm,wg6,wmE,wtj,wyS,wA8] (.node [wbm,wg6,wmE,wqO,wtt,wyS] .nil .nil) .nil)) (.node [wbm,wiC,wmE,wtt,wyS,wA8] (.node [wbm,wg6,wmE,wtt,wyS,wA8] (.node [wbm,wg6,wmE,wtt,wyI,wA8] .nil .nil) .nil) (.node [wbn,wg6,wmE,wtt,wyS,wA8] (.node [wbn,wg6,wmE,wp6,wtt,wyS] .nil .nil) .nil))) (.node [wbu,wg6,wmE,wp6,wtt,wyS] (.node [wbs,wg6,wmE,wp6,wtt,wyS] (.node [wbq,wg6,wmE,wtt,wyS,wA8] (.node [wbq,wg6,wmE,wp6,wtt,wyS] .nil .nil) .nil) (.node [wbt,wg6,wmE,wtt,wyS,wA8] (.node [wbt,wg6,wmE,wp6,wtt,wyS] .nil .nil) .nil)) (.node [wbw,wg6,wmE,wp6,wtt,wwe] (.node [wbw,wg6,wmE,wp6,wtt,wvJ] (.node [wbw,wg6,wmE,wp6,wtt] .nil .nil) .nil) (.node [wbw,wg6,wmE,wp6,wtt,wAR] (.node [wbw,wg6,wmE,wp6,wtt,wyS] .nil .nil) .nil)))) (.node [wbK,whW,wiC,wmE,wwe,wyS] (.node [wbK,wbY,wg6,wjl,wwe,wyS] (.node [wby,wg6,wmE,wtt,wwe,wyS] (.node [wbx,wg6,wmE,wrg,wwe,wyS] (.node [wbx,wg6,wkw,wtt,wwe,wyS] .nil .nil) (.node [wby,wg6,wks,wtt,wwe,wyS] .nil .nil)) (.node [wbH,wg6,wjl,wtt,wwe,wyS] (.node [wbz,wg6,wjl,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wbK,wg6,wmr,wtt,wwe,wyS] (.node [wbK,wg6,wkt,wtt,wwe,wyS] (.node [wbK,wc2,whW,wmE,wwe,wyS] .nil .nil) .nil) (.node [wbK,whM,wmE,wp6,wwe,wyS] (.node [wbK,whL,wmE,wp6,wwe,wyS] .nil .nil) .nil))) (.node [wbK,wia,wmE,wp6,wwe,wyS] (.node [wbK,whW,wmE,wp6,wwe,wyS] (.node [wbK,whW,wmE,wov,wwe,wyS] (.node [wbK,whW,wjl,wmE,wwe,wyS] .nil .nil) .nil) (.node [wbK,whW,wmE,wwe,wyS,wA8] (.node [wbK,whW,wmE,wq8,wwe,wyS] .nil .nil) .nil)) (.node [wbS,wf8,wg6,wmE,wwe,wyS] (.node [wbR,wg6,wmE,wp6,wtt,wyS] (.node [wbO,wga,wg6,wmE,wwe,wyS] .nil .nil) .nil) (.node [wbT,wg6,wmE,wp6,wtt,wwe] (.node [wbS,wg6,wjl,wvk,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrlll_ok : everyKey (rowOK 4 level4) level5llrlll = true := by decide +kernel
def level5llrllr : BinaryTree (List W) := (.node [wbY,wg6,wjl,wwe,wyS,wAH] (.node [wbY,wfq,wg6,wp6,wwe,wyS] (.node [wbY,wfe,wg6,wnp,wp6,wwe] (.node [wbY,wfe,wg6,wjl,wwe,wyS] (.node [wbY,wc2,wfe,wg6,wwe,wyS] (.node [wbX,wg6,wmr,wtt,wwe,wyS] .nil .nil) (.node [wbY,wfe,wg6,wiC,wwe,wyS] .nil .nil)) (.node [wbY,wfe,wg6,wni,wp6,wyS] (.node [wbY,wfe,wg6,wkM,wwe,wyS] .nil .nil) .nil)) (.node [wbY,wfe,wg6,wp6,ww9,wyS] (.node [wbY,wfe,wg6,wp6,wwe,wzK] (.node [wbY,wfe,wg6,wp6,wwe,wyS] .nil .nil) .nil) (.node [wbY,wfe,wg6,wwe,wyS,wA8] (.node [wbY,wfe,wg6,wrs,wwe,wyS] .nil .nil) .nil))) (.node [wbY,wgb,wg6,wp6,wwe,wyS] (.node [wbY,wf8,wg6,wjl,wwe,wyS] (.node [wbY,wfV,wg6,wp6,wwe,wyS] (.node [wbY,wfv,wg6,wp6,wwe,wyS] .nil .nil) .nil) (.node [wbY,wf9,wg6,wjl,wwe,wyS] (.node [wbY,wf8,wg6,wp6,wwe,wyS] .nil .nil) .nil)) (.node [wbY,wg6,wjl,wu3,wwe,wyS] (.node [wbY,wg6,wjl,wtt,wwe,wyS] (.node [wbY,wg6,wir,wtt,wwe,wyS] .nil .nil) .nil) (.node [wbY,wg6,wjl,wwe,wyr,wyS] (.node [wbY,wg6,wjl,wvk,wwe,wyS] .nil .nil) .nil)))) (.node [wbZ,wg6,wmE,wp6,wwe,wyS] (.node [wbY,wg6,wmE,wp6,wxj,wyS] (.node [wbY,wg6,wmE,wp6,wwe,wzK] (.node [wbY,wg6,wmr,wtt,wwe,wyS] (.node [wbY,wg6,wkM,wtt,wwe,wyS] .nil .nil) .nil) (.node [wbY,wg6,wmE,wp6,ww9,wyS] (.node [wbY,wg6,wmE,wp6,wwe,wzT] .nil .nil) .nil)) (.node [wbY,wg6,wp6,wtf,wwe,wyS] (.node [wbY,wg6,wpW,wtt,wwe,wyS] (.node [wbY,wg6,wnu,wp6,wwe,wyS] .nil .nil) .nil) (.node [wbY,wg6,wtt,wwe,wyS,wAX] (.node [wbY,wg6,wp6,wvg,wwe,wyS] .nil .nil) .nil))) (.node [wb3,wg6,wmE,wp6,wtt,wwe] (.node [wb1,wg6,wmE,wp6,wwe,wyS] (.node [wb0,wg6,wmE,wp6,wwe,wAH] (.node [wb0,wg6,wjl,wtt,wwe,wyS] .nil .nil) .nil) (.node [wb2,wg6,wmE,wp6,wyr,wyS] (.node [wb2,wg6,wjl,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wb7,wdH,wg6,wmE,wqY,wyS] (.node [wb7,wdH,wg6,wkw,wwe,wyS] (.node [wb5,wg6,wmE,wp6,wtt,wyS] .nil .nil) .nil) (.node [wb7,wdH,wg6,wmE,wwe,wyS] (.node [wb7,wdH,wg6,wmE,wq4,wwe] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrllr_ok : everyKey (rowOK 4 level4) level5llrllr = true := by decide +kernel
def level5llrll : BinaryTree (List W) := .node [wbV,wg6,wmE,wp6,wtt,wyS] level5llrlll level5llrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrll_ok : everyKey (rowOK 4 level4) level5llrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrlll && everyKey (rowOK 4 level4) level5llrllr) = true
  rw [level5llrlll_ok, level5llrllr_ok]
  decide +kernel
def level5llrlrl : BinaryTree (List W) := (.node [wb8,wg6,wmE,wp6,wwe,wyS] (.node [wb7,wg6,wmE,wp6,wwe,wzK] (.node [wb7,wf8,wg6,wmE,wwe,wyS] (.node [wb7,wd8,wg6,wmE,wwe,wyS] (.node [wb7,wdH,wg6,wnG,wwe,wyS] (.node [wb7,wdH,wg6,wmE,wwT,wyS] .nil .nil) (.node [wb7,wdT,wg6,wmE,wwe,wyS] .nil .nil)) (.node [wb7,weI,wg6,wmE,wwe,wyS] (.node [wb7,wek,wg6,wmE,wwe,wyS] .nil .nil) .nil)) (.node [wb7,wg6,wkw,wtt,wwe,wyS] (.node [wb7,wg6,wjl,wvk,wwe,wyS] (.node [wb7,wga,wg6,wmE,wwe,wyS] .nil .nil) .nil) (.node [wb7,wg6,wmE,wp6,wwe,wzv] (.node [wb7,wg6,wmr,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wb7,wg6,wmE,wrg,wwe,wyS] (.node [wb7,wg6,wmE,wp6,ww9,wyS] (.node [wb7,wg6,wmE,wp6,wwT,wyS] (.node [wb7,wg6,wmE,wp6,wwe,wzT] .nil .nil) .nil) (.node [wb7,wg6,wmE,wq8,wwe,wyS] (.node [wb7,wg6,wmE,wp6,wxj,wyS] .nil .nil) .nil)) (.node [wb7,wg6,wmE,wvw,wwe,wyS] (.node [wb7,wg6,wmE,wtj,wwe,wyS] (.node [wb7,wg6,wmE,wrs,wwe,wyS] .nil .nil) .nil) (.node [wb7,wg6,wp6,wvg,wwe,wyS] (.node [wb7,wg6,wnG,wp6,wwe,wyS] .nil .nil) .nil)))) (.node [wci,wdM,wg6,wmE,wp6,wyS] (.node [wcc,wg6,wmE,wp6,wtt,wwe] (.node [wca,wg6,wmE,wp6,wwe,wyS] (.node [wb9,wg6,wmE,wp6,wwe,wAH] (.node [wb8,wg6,wmE,wqt,wwe,wyS] .nil .nil) .nil) (.node [wcb,wg6,wmE,wp6,wyr,wyS] (.node [wca,wg6,wmE,wqO,wwe,wyS] .nil .nil) .nil)) (.node [wcg,wg6,wjl,wtt,wwe,wyS] (.node [wcf,wg6,wmE,wr5,wwe,wyS] (.node [wcf,wg6,wmE,wp6,wwe,wyS] .nil .nil) .nil) (.node [wci,wcJ,wg6,wmE,wp6,wyS] (.node [wch,wg6,wmE,wp6,wtt,wAR] .nil .nil) .nil))) (.node [wci,wg6,wmE,wp6,wtt,wAB] (.node [wci,wg6,wmr,wtt,wwe,wyS] (.node [wci,wgf,wg6,wmE,wp6,wyS] (.node [wci,wfh,wg6,wmE,wp6,wyS] .nil .nil) .nil) (.node [wci,wg6,wmE,wp6,wsZ,wyS] (.node [wci,wg6,wmE,wpP,wtt,wyS] .nil .nil) .nil)) (.node [wcl,wg6,wmE,wp6,wtt,wyS] (.node [wck,wg6,wmE,wp6,wtt,wyS] (.node [wcj,wg6,wmE,wp6,wtt,wyS] .nil .nil) .nil) (.node [wcm,wg6,wiC,wmE,wtt,wyS] (.node [wcm,wc2,wg6,wmE,wtt,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrlrl_ok : everyKey (rowOK 4 level4) level5llrlrl = true := by decide +kernel
def level5llrlrr : BinaryTree (List W) := (.node [wcu,wg6,wmE,wp6,wwe,wyS] (.node [wcq,wg6,wjl,wtt,wwe,wyS] (.node [wcp,wfg,wg6,wmE,wp6,wwe] (.node [wcn,wg6,wjl,wtt,wwe,wyS] (.node [wcm,wg6,wmE,wp6,wtt,wyS] (.node [wcm,wg6,wmE,wp6,wsY,wAH] .nil .nil) (.node [wcm,wg6,wmE,wtt,wyS,wA8] .nil .nil)) (.node [wcp,wdL,wg6,wmE,wp6,wwe] (.node [wcp,wcF,wg6,wmE,wp6,wwe] .nil .nil) .nil)) (.node [wcp,wg6,wmE,wpP,wtt,wwe] (.node [wcp,wg6,wmr,wtt,wwe,wyS] (.node [wcp,wgd,wg6,wmE,wp6,wwe] .nil .nil) .nil) (.node [wcp,wg6,wmE,wp6,wtt,wyl] (.node [wcp,wg6,wmE,wp6,wsL,wwe] .nil .nil) .nil))) (.node [wcu,weq,wg6,wmE,wwe,wyS] (.node [wct,wg6,wmE,wwe,wyS,wAX] (.node [wct,wg6,wmE,wp6,wwe,wyS] (.node [wct,wg6,wjl,wmE,wwe,wyS] .nil .nil) .nil) (.node [wcu,wdl,wp6,wwe,wyS,wA1] (.node [wcu,wc2,wg6,wmE,wwe,wyS] .nil .nil) .nil)) (.node [wcu,wg6,wmE,wpW,wwe,wyS] (.node [wcu,wg6,wjl,wmE,wwe,wyS] (.node [wcu,wg6,wiC,wmE,wwe,wyS] .nil .nil) .nil) (.node [wcu,wg6,wmE,wp6,wwe,wyE] (.node [wcu,wg6,wmE,wp6,wv0,wyS] .nil .nil) .nil)))) (.node [wcv,wg6,wmr,wwe,wyS] (.node [wcv,wfz,wg6,wwe,wyS,wA8] (.node [wcv,wdH,wg6,wmE,wwe,wyS] (.node [wcv,wc2,wg6,wmE,wwe,wyS] (.node [wcu,wg6,wmE,wwe,wyS,wA8] .nil .nil) .nil) (.node [wcv,wfz,wg6,wp6,wwe,wyS] (.node [wcv,weZ,wmE,wwe,wyS,wA8] .nil .nil) .nil)) (.node [wcv,wg6,wmr,wmE,wwe,wyS] (.node [wcv,wg6,wjl,wmE,wwe,wyS] (.node [wcv,wg6,wiC,wmE,wwe,wyS] .nil .nil) .nil) (.node [wcv,wg6,wmr,wtt,wwe,wyS] (.node [wcv,wg6,wmr,wp6,wwe,wyS] .nil .nil) .nil))) (.node [wcv,wg6,wmE,wq8,wwe,wyS] (.node [wcv,wg6,wmE,wp6,wv4,wyS] (.node [wcv,wg6,wmE,wn8,wwe,wyS] (.node [wcv,wg6,wmr,wwe,wyS,wA8] .nil .nil) .nil) (.node [wcv,wg6,wmE,wp6,wwe,wyS] (.node [wcv,wg6,wmE,wp6,wwe,wyI] .nil .nil) .nil)) (.node [wcv,wg6,wmE,wwe,wyI,wA8] (.node [wcv,wg6,wmE,wv4,wyS,wA8] (.node [wcv,wg6,wmE,wtj,wwe,wyS] .nil .nil) .nil) (.node [wcv,wiC,wmE,wwe,wyS,wA8] (.node [wcv,wg6,wmE,wwe,wyS,wA8] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrlrr_ok : everyKey (rowOK 4 level4) level5llrlrr = true := by decide +kernel
def level5llrlr : BinaryTree (List W) := .node [wcm,wg6,wjl,wmE,wtt,wyS] level5llrlrl level5llrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrlr_ok : everyKey (rowOK 4 level4) level5llrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrlrl && everyKey (rowOK 4 level4) level5llrlrr) = true
  rw [level5llrlrl_ok, level5llrlrr_ok]
  decide +kernel
def level5llrl : BinaryTree (List W) := .node [wb7,wdH,wg6,wmE,wwe,wzv] level5llrll level5llrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrl_ok : everyKey (rowOK 4 level4) level5llrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrll && everyKey (rowOK 4 level4) level5llrlr) = true
  rw [level5llrll_ok, level5llrlr_ok]
  decide +kernel
def level5llrrll : BinaryTree (List W) := (.node [wcK,wg6,wmE,wp6,wsK,wyr] (.node [wcF,wg6,wmE,wp6,wwe,wAH] (.node [wcC,wg6,wmE,wwe,wyS,wA8] (.node [wcz,wg6,wmE,wwe,wyS,wA8] (.node [wcy,wg6,wmE,wp6,wwe,wyS] (.node [wcw,wg6,wmE,wwe,wyS,wA8] .nil .nil) (.node [wcz,wg6,wmE,wp6,wwe,wyS] .nil .nil)) (.node [wcC,wg6,wmE,wp6,wwe,wyS] (.node [wcB,wg6,wmE,wp6,wwe,wyS] .nil .nil) .nil)) (.node [wcF,wg6,wmE,wp6,wtt,wwe] (.node [wcF,wg6,wmE,wp6,wsY,wwe] (.node [wcD,wg6,wmE,wp6,wwe,wyS] .nil .nil) .nil) (.node [wcF,wg6,wmE,wp6,wwe,wyS] (.node [wcF,wg6,wmE,wp6,wwe] .nil .nil) .nil))) (.node [wcJ,wg6,wmE,wp6,wwe,wyS] (.node [wcI,wg6,wmE,wp6,wtt,wwe] (.node [wcH,wg6,wmE,wp6,wtt,wwe] (.node [wcG,wg6,wmE,wp6,wtt,wwe] .nil .nil) .nil) (.node [wcJ,wg6,wmE,wp6,wtt,wyS] (.node [wcJ,wg6,wmE,wp6,wsK,wyS] .nil .nil) .nil)) (.node [wcK,wc2,wg6,wmE,wtt,wwe] (.node [wcJ,wg6,wmE,wp6,wyS] (.node [wcJ,wg6,wmE,wp6,wyr,wyS] .nil .nil) .nil) (.node [wcK,wg6,wjl,wmE,wtt,wwe] (.node [wcK,wg6,wiC,wmE,wtt,wwe] .nil .nil) .nil)))) (.node [wcW,wg6,wmE,wtt,wwe,wyS] (.node [wcQ,wg6,wmE,wt2,wwe,wyS] (.node [wcO,wg6,wjl,wtt,wwe,wyS] (.node [wcK,wg6,wmE,wtt,wwe,wA8] (.node [wcK,wg6,wmE,wp6,wtt,wwe] .nil .nil) .nil) (.node [wcQ,wg6,wmE,wrT,wtt,wwe] (.node [wcQ,wg6,wmE,wrx,wtt,wyS] .nil .nil) .nil)) (.node [wcT,wg6,wmE,wrT,wtt,wwe] (.node [wcT,wg6,wmE,wrg,wwe,wyS] (.node [wcR,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wcU,wg6,wmE,wtt,wwe,wyS] (.node [wcT,wg6,wmE,wtt,wwN,wyS] .nil .nil) .nil))) (.node [wc0,wg6,wmE,wtt,wwe,wyS] (.node [wcX,wg6,wmE,wtt,wwe,wzp] (.node [wcX,wg6,wmE,wrx,wtt,wyS] (.node [wcX,wg6,wmE,wrg,wwe,wyS] .nil .nil) .nil) (.node [wcZ,wg6,wmE,wtt,wwe,wyS] (.node [wcY,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wc1,wg7,wmE,wtt,wwe,wyS] (.node [wc1,wg6,wmr,wtt,wwe,wyS] (.node [wc1,wg6,wjl,wtt,wwe,wyS] .nil .nil) .nil) (.node [wc2,weV,wg6,wrg,wwe,wyS] (.node [wc2,wdl,wtt,wwe,wyS,wA1] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrll_ok : everyKey (rowOK 4 level4) level5llrrll = true := by decide +kernel
def level5llrrlr : BinaryTree (List W) := (.node [wc2,wg6,wjl,wt2,wwe,wyS] (.node [wc2,wgr,wmE,wtt,wxz,wyS] (.node [wc2,wfp,wg6,wtt,wwe,wyS] (.node [wc2,weV,wg6,wtt,wwN,wyS] (.node [wc2,weV,wg6,wtt,wwe,wyS] (.node [wc2,weV,wg6,wrT,wtt,wwe] .nil .nil) (.node [wc2,weV,wg6,wtt,wwe,wzp] .nil .nil)) (.node [wc2,wfj,wg6,wtt,wwe,wyS] (.node [wc2,weV,wg6,wt2,wwe,wyS] .nil .nil) .nil)) (.node [wc2,wfz,wg6,wtt,wwe,wyS] (.node [wc2,wfx,wiv,wtt,wwe,wyS] (.node [wc2,wfu,wg6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wc2,wf9,wmE,wuS,wwe,wyS] (.node [wc2,wf3,wg6,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wc2,wg6,wjl,wrg,wwe,wyS] (.node [wc2,wg6,wh8,wmE,wwe,wyS] (.node [wc2,wg6,wh3,wmE,wwe,wyS] (.node [wc2,wgR,wmE,wtt,wwe,wz7] .nil .nil) .nil) (.node [wc2,wg6,wi5,wtt,wwe,wyS] (.node [wc2,wg6,wil,wmE,wtt,wyS] .nil .nil) .nil)) (.node [wc2,wg6,wjl,wtt,wwe,wyS] (.node [wc2,wg6,wjl,wrT,wtt,wwe] (.node [wc2,wg6,wjl,wrx,wtt,wyS] .nil .nil) .nil) (.node [wc2,wg6,wjl,wtt,wwN,wyS] (.node [wc2,wg6,wjl,wtt,wwe,wzp] .nil .nil) .nil)))) (.node [wc2,wg6,wll,wmE,wwe,wyS] (.node [wc2,wg6,wks,wtt,wwe,wyS] (.node [wc2,wg6,wjY,wtt,wwe,wyS] (.node [wc2,wg6,wjF,wtt,wwe,wyS] (.node [wc2,wg6,wjp,wtt,wwe,wyS] .nil .nil) .nil) (.node [wc2,wg6,wkn,wmE,wtt,wwe] (.node [wc2,wg6,wj2,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wc2,wg6,wk2,wmE,wtt,wwe] (.node [wc2,wg6,wkX,wmE,wtt,wyS] (.node [wc2,wg6,wkw,wtt,wwe,wyS] .nil .nil) .nil) (.node [wc2,wg6,wlg,wmE,wwe,wyS] (.node [wc2,wg6,wla,wvk,wwe,wyS] .nil .nil) .nil))) (.node [wc2,wg6,wmc,wtt,wwe,wyS] (.node [wc2,wg6,wlI,wmE,wtt,wyS] (.node [wc2,wg6,wlC,wtt,wxV,wyS] (.node [wc2,wg6,wlu,wtt,wwe,wyS] .nil .nil) .nil) (.node [wc2,wg6,wl2,wtt,wwe,wAo] (.node [wc2,wg6,wlR,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wc2,wg6,wmE,wni,wtt,wyS] (.node [wc2,wg6,wmE,wm7,wtt,wwe] (.node [wc2,wg6,wmr,wtt,wwe,wyS] .nil .nil) .nil) (.node [wc2,wg6,wmE,woe,wwe,wyS] (.node [wc2,wg6,wmE,wnp,wtt,wwe] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrlr_ok : everyKey (rowOK 4 level4) level5llrrlr = true := by decide +kernel
def level5llrrl : BinaryTree (List W) := .node [wc2,weV,wg6,wrx,wtt,wyS] level5llrrll level5llrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrl_ok : everyKey (rowOK 4 level4) level5llrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrrll && everyKey (rowOK 4 level4) level5llrrlr) = true
  rw [level5llrrll_ok, level5llrrlr_ok]
  decide +kernel
def level5llrrrl : BinaryTree (List W) := (.node [wc2,wg6,wmE,wrU,wtt,wwe] (.node [wc2,wg6,wmE,wrk,wwe,wyS] (.node [wc2,wg6,wmE,wrg,wrT,wwe] (.node [wc2,wg6,wmE,wq4,wtt,wwe] (.node [wc2,wg6,wmE,wqK,wtt,wwe] (.node [wc2,wg6,wmE,woN,wtt,wyS] .nil .nil) (.node [wc2,wg6,wmE,wqY,wtt,wyS] .nil .nil)) (.node [wc2,wg6,wmE,wrg,wrx,wyS] (.node [wc2,wg6,wmE,wre,wwe,wyS] .nil .nil) .nil)) (.node [wc2,wg6,wmE,wrg,wwN,wyS] (.node [wc2,wg6,wmE,wrg,wwe,wzp] (.node [wc2,wg6,wmE,wrg,wwe,wyS] .nil .nil) .nil) (.node [wc2,wg6,wmE,wri,wwe,wyS] (.node [wc2,wg6,wmE,wrh,wwe,wyS] .nil .nil) .nil))) (.node [wc2,wg6,wmE,wry,wtt,wyS] (.node [wc2,wg6,wmE,wrx,wtt,wyS] (.node [wc2,wg6,wmE,wrx,wrT,wtt] (.node [wc2,wg6,wmE,wrv,wtt,wyS] .nil .nil) .nil) (.node [wc2,wg6,wmE,wrx,wt2,wyS] (.node [wc2,wg6,wmE,wrx,wtt,wzp] .nil .nil) .nil)) (.node [wc2,wg6,wmE,wrT,wtt,wwe] (.node [wc2,wg6,wmE,wrM,wtt,wwe] (.node [wc2,wg6,wmE,wrz,wtt,wyS] .nil .nil) .nil) (.node [wc2,wg6,wmE,wrT,wt2,wwe] (.node [wc2,wg6,wmE,wrT,wtt,wwN] .nil .nil) .nil)))) (.node [wc2,wg6,wmE,wtt,wvF,wwe] (.node [wc2,wg6,wmE,wsY,wwe,wAH] (.node [wc2,wg6,wmE,wsf,wtt,wwe] (.node [wc2,wg6,wmE,wsd,wtt,wyS] (.node [wc2,wg6,wmE,wsa,wtt,wwe] .nil .nil) .nil) (.node [wc2,wg6,wmE,wsX,wwe,wyS] (.node [wc2,wg6,wmE,wsK,wyr,wyS] .nil .nil) .nil)) (.node [wc2,wg6,wmE,wtj,wwe,wyS] (.node [wc2,wg6,wmE,wtf,wwe,wyS] (.node [wc2,wg6,wmE,wta,wwe,wyS] .nil .nil) .nil) (.node [wc2,wg6,wmE,wtt,wvD,wyS] (.node [wc2,wg6,wmE,wtm,wwe,wyS] .nil .nil) .nil))) (.node [wc2,wg6,wmE,wtt,wwe,wya] (.node [wc2,wg6,wmE,wtt,wv0,wyS] (.node [wc2,wg6,wmE,wtt,wvV,wyS] (.node [wc2,wg6,wmE,wtt,wvJ,wAR] .nil .nil) .nil) (.node [wc2,wg6,wmE,wtt,wv7,wyS] (.node [wc2,wg6,wmE,wtt,wv4,wyS] .nil .nil) .nil)) (.node [wc2,wg6,wmE,wtt,wwe,wyL] (.node [wc2,wg6,wmE,wtt,wwe,wyI] (.node [wc2,wg6,wmE,wtt,wwe,wyE] .nil .nil) .nil) (.node [wc2,wg6,wmE,wtt,wwe,wyT] (.node [wc2,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrrl_ok : everyKey (rowOK 4 level4) level5llrrrl = true := by decide +kernel
def level5llrrrr : BinaryTree (List W) := (.node [wc2,wg6,wmE,wtt,ww9,wyS] (.node [wc2,wg6,wmE,wtt,wwe,wAB] (.node [wc2,wg6,wmE,wtt,wwe,wzv] (.node [wc2,wg6,wmE,wtt,wwe,wzo] (.node [wc2,wg6,wmE,wtt,wwe,wzl] (.node [wc2,wg6,wmE,wtt,wwe,wy9] .nil .nil) (.node [wc2,wg6,wmE,wtt,wwe,wzn] .nil .nil)) (.node [wc2,wg6,wmE,wtt,wwe,wzr] (.node [wc2,wg6,wmE,wtt,wwe,wzp] .nil .nil) .nil)) (.node [wc2,wg6,wmE,wtt,wwe,wzN] (.node [wc2,wg6,wmE,wtt,wwe,wzK] (.node [wc2,wg6,wmE,wtt,wwe,wzy] .nil .nil) .nil) (.node [wc2,wg6,wmE,wtt,wwe,wz0] (.node [wc2,wg6,wmE,wtt,wwe,wzT] .nil .nil) .nil))) (.node [wc2,wg6,wmE,wtt,wwM,wyS] (.node [wc2,wg6,wmE,wtt,wwv,wyS] (.node [wc2,wg6,wmE,wtt,wwm,wyS] (.node [wc2,wg6,wmE,wtt,wwf,wyS] .nil .nil) .nil) (.node [wc2,wg6,wmE,wtt,wwL,wyS] (.node [wc2,wg6,wmE,wtt,wwJ,wyS] .nil .nil) .nil)) (.node [wc2,wg6,wmE,wtt,wwP,wyS] (.node [wc2,wg6,wmE,wtt,wwN,wzp] (.node [wc2,wg6,wmE,wtt,wwN,wyS] .nil .nil) .nil) (.node [wc2,wg6,wmE,wtt,wwX,wyS] (.node [wc2,wg6,wmE,wtt,wwT,wyS] .nil .nil) .nil)))) (.node [wc2,wg6,wmE,wt2,wwe,wzp] (.node [wc2,wg6,wmE,wtB,wwe,wyS] (.node [wc2,wg6,wmE,wtt,wxs,wyS] (.node [wc2,wg6,wmE,wtt,wxj,wyS] (.node [wc2,wg6,wmE,wtt,wxd,wyS] .nil .nil) .nil) (.node [wc2,wg6,wmE,wtu,wwe,wyS] (.node [wc2,wg6,wmE,wtt,wyl,wyS] .nil .nil) .nil)) (.node [wc2,wg6,wmE,wt0,wwe,wyS] (.node [wc2,wg6,wmE,wtY,wwe,wyS] (.node [wc2,wg6,wmE,wtK,wwe,wyS] .nil .nil) .nil) (.node [wc2,wg6,wmE,wt2,wwe,wyS] (.node [wc2,wg6,wmE,wt1,wwe,wyS] .nil .nil) .nil))) (.node [wc2,wg6,wmE,wuu,wwe,wyS] (.node [wc2,wg6,wmE,wt9,wwe,wyS] (.node [wc2,wg6,wmE,wt4,wwe,wyS] (.node [wc2,wg6,wmE,wt2,wwN,wyS] .nil .nil) .nil) (.node [wc2,wg6,wmE,wuq,wwe,wyS] (.node [wc2,wg6,wmE,wud,wwe,wyS] .nil .nil) .nil)) (.node [wc2,wg6,wmE,wwe,wyh,wyS] (.node [wc2,wg6,wmE,wuL,wwe,wyS] (.node [wc2,wg6,wmE,wuC,wwe,wyS] .nil .nil) .nil) (.node [wc2,wg6,wnO,wtt,wwe,wyS] (.node [wc2,wg6,wnG,wtt,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrrr_ok : everyKey (rowOK 4 level4) level5llrrrr = true := by decide +kernel
def level5llrrr : BinaryTree (List W) := .node [wc2,wg6,wmE,wtt,wwe,wy0] level5llrrrl level5llrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrr_ok : everyKey (rowOK 4 level4) level5llrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrrrl && everyKey (rowOK 4 level4) level5llrrrr) = true
  rw [level5llrrrl_ok, level5llrrrr_ok]
  decide +kernel
def level5llrr : BinaryTree (List W) := .node [wc2,wg6,wmE,woj,wwe,wyS] level5llrrl level5llrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrr_ok : everyKey (rowOK 4 level4) level5llrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrrl && everyKey (rowOK 4 level4) level5llrrr) = true
  rw [level5llrrl_ok, level5llrrr_ok]
  decide +kernel
def level5llr : BinaryTree (List W) := .node [wcw,wg6,wmE,wp6,wwe,wyS] level5llrl level5llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llr_ok : everyKey (rowOK 4 level4) level5llr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrl && everyKey (rowOK 4 level4) level5llrr) = true
  rw [level5llrl_ok, level5llrr_ok]
  decide +kernel
def level5ll : BinaryTree (List W) := .node [wbm,wg6,wmr,wtt,wyS,wA8] level5lll level5llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5ll_ok : everyKey (rowOK 4 level4) level5ll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lll && everyKey (rowOK 4 level4) level5llr) = true
  rw [level5lll_ok, level5llr_ok]
  decide +kernel
def level5lrllll : BinaryTree (List W) := (.node [wdl,wgN,wjl,wtt,wwe,wyS] (.node [wdb,wg6,wmE,wtt,wwe,wyS] (.node [wc5,wg6,wmE,wtt,wwe,wyS] (.node [wc2,wg6,wtt,wwe,wyS,wAk] (.node [wc2,wg6,wtt,wvg,wwe,wyS] (.node [wc2,wg6,wnZ,wtt,wwe,wyS] .nil .nil) (.node [wc2,wg6,wtt,wwe,wxR,wyS] .nil .nil)) (.node [wc4,wg6,wmE,wtt,wwe,wyS] (.node [wc3,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wc8,wg6,wmE,wtt,wwe,wyS] (.node [wc7,wg6,wmE,wtt,wwe,wyS] (.node [wc6,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wda,wg6,wmE,wtt,wwe,wyS] (.node [wc9,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wdh,wg6,wmE,wtt,wwe,wyS] (.node [wde,wg6,wmE,wtt,wwe,wyS] (.node [wdd,wg6,wmE,wtt,wwe,wyS] (.node [wdc,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wdf,wg6,wjl,wtt,wwe,wyS] (.node [wdf,wfs,wg6,wp6,wtt,wwe] .nil .nil) .nil)) (.node [wdk,wg6,wmE,wtt,wwe,wyS] (.node [wdj,wg6,wmE,wtt,wwe,wyS] (.node [wdi,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wdl,wfx,wjl,wtt,wwe,wyS] (.node [wdl,weq,wtt,wwe,wyS,wA1] .nil .nil) .nil)))) (.node [wdl,wiC,wtt,wwe,wyS,wA1] (.node [wdl,wg6,wjl,wtt,wwP,wyS] (.node [wdl,wg6,wjl,wrM,wtt,wwe] (.node [wdl,wg6,wjl,wre,wwe,wyS] (.node [wdl,wg6,wir,wtt,wwe,wyS] .nil .nil) (.node [wdl,wg6,wjl,wrv,wtt,wyS] .nil .nil)) (.node [wdl,wg6,wjl,wtt,wwe,wzr] (.node [wdl,wg6,wjl,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wdl,wg6,wpW,wtt,wwe,wyS] (.node [wdl,wg6,wmr,wtt,wwe,wyS] (.node [wdl,wg6,wjl,wt4,wwe,wyS] .nil .nil) .nil) (.node [wdl,wg7,wmE,wtt,wwe,wyS] (.node [wdl,wg6,wtt,wwe,wyS,wAX] .nil .nil) .nil))) (.node [wdl,wp6,wre,wwe,wyS,wA1] (.node [wdl,wmE,wtt,wwe,wyS,wAX] (.node [wdl,wjl,wtt,wwe,wyS,wA1] (.node [wdl,wjl,wtt,wwe,wyS,wAX] .nil .nil) .nil) (.node [wdl,wpW,wtt,wwe,wyS,wA1] (.node [wdl,wpi,wtt,wwe,wyS,wA1] .nil .nil) .nil)) (.node [wdl,wp6,wrP,wtt,wwe,wyS] (.node [wdl,wp6,wrM,wtt,wwe,wA1] (.node [wdl,wp6,wrv,wtt,wyS,wA1] .nil .nil) .nil) (.node [wdl,wp6,wtt,wv0,wyS,wA1] (.node [wdl,wp6,wtf,wwe,wyS,wA1] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrllll_ok : everyKey (rowOK 4 level4) level5lrllll = true := by decide +kernel
def level5lrlllr : BinaryTree (List W) := (.node [wdr,wg6,wmE,wtt,wwe,wyS] (.node [wdm,wg6,wmE,wrd,wwe,wyS] (.node [wdl,wtt,wwe,wyS,wAX] (.node [wdl,wp6,wtt,wwP,wyS,wA1] (.node [wdl,wp6,wtt,wwe,wyS,wA1] (.node [wdl,wp6,wtt,wwe,wyS,wAX] .nil .nil) (.node [wdl,wp6,wtt,wwe,wzr,wA1] .nil .nil)) (.node [wdl,wsB,wtt,wwe,wyS,wA1] (.node [wdl,wp6,wt4,wwe,wyS,wA1] .nil .nil) .nil)) (.node [wdm,wg6,wir,wtt,wwe,wyS] (.node [wdm,weV,wg6,wtt,wwe,wyS] (.node [wdl,wtt,wwe,wyS,wA1,wA8] .nil .nil) .nil) (.node [wdm,wg6,wjl,wtt,wwe,wyS] (.node [wdm,wg6,wiv,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wdm,wg6,wmE,wt5,wwe,wyS] (.node [wdm,wg6,wmE,wtt,wwe,wyS] (.node [wdm,wg6,wmE,wrL,wtt,wwe] (.node [wdm,wg6,wmE,wru,wtt,wyS] .nil .nil) .nil) (.node [wdm,wg6,wmE,wtt,wwQ,wyS] (.node [wdm,wg6,wmE,wtt,wwe,wzs] .nil .nil) .nil)) (.node [wdp,wfs,wg6,wp6,wtt,wwe] (.node [wdo,wip,wmE,wp6,wtt,wwe] (.node [wdm,wg6,wtt,wwe,wyS,wA1] .nil .nil) .nil) (.node [wdq,wg6,wmE,wtt,wwe,wyS] (.node [wdp,wg6,wjl,wtt,wwe,wyS] .nil .nil) .nil)))) (.node [wdB,whW,wmE,wp6,wwe,wyS] (.node [wdw,wfm,wg6,wp6,wtt,wyS] (.node [wdu,wie,wmE,wp6,wtt,wyS] (.node [wdt,wg6,wmE,wtt,wwe,wyS] (.node [wds,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wdv,wg6,wjl,wtt,wwe,wyS] (.node [wdv,wfm,wg6,wp6,wtt,wyS] .nil .nil) .nil)) (.node [wdy,wg6,wmE,wtt,wwe,wyS] (.node [wdx,wg6,wmE,wtt,wwe,wyS] (.node [wdw,wg6,wjl,wtt,wwe,wyS] .nil .nil) .nil) (.node [wdA,wg6,wmE,wtt,wwe,wyS] (.node [wdz,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wdH,wg6,wjF,wtt,wwe,wyS] (.node [wdD,wfe,wg6,wp6,wwe,wyS] (.node [wdC,wg6,wjl,wtt,wwe,wyS] (.node [wdC,wfe,wg6,wp6,wwe,wyS] .nil .nil) .nil) (.node [wdH,weI,wg6,wmE,wwe,wyS] (.node [wdD,wg6,wjl,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wdH,wg6,wmE,woN,wtt,wyS] (.node [wdH,wg6,wmr,wtt,wwe,wyS] (.node [wdH,wg6,wj2,wtt,wwe,wyS] .nil .nil) .nil) (.node [wdH,wg6,wmE,wrx,wtt,wyS] (.node [wdH,wg6,wmE,wqK,wtt,wwe] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlllr_ok : everyKey (rowOK 4 level4) level5lrlllr = true := by decide +kernel
def level5lrlll : BinaryTree (List W) := .node [wdl,wp6,wtt,wwe,wyE,wA1] level5lrllll level5lrlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlll_ok : everyKey (rowOK 4 level4) level5lrlll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrllll && everyKey (rowOK 4 level4) level5lrlllr) = true
  rw [level5lrllll_ok, level5lrlllr_ok]
  decide +kernel
def level5lrllrl : BinaryTree (List W) := (.node [wdT,wg6,wmE,wt2,wwe,wyS] (.node [wdR,wg6,wmE,wtt,wwe,wyS] (.node [wdJ,wg6,wmE,wtt,wwe,wyS] (.node [wdH,wg6,wmE,wt9,wwe,wyS] (.node [wdH,wg6,wmE,wtt,wwe,wyI] (.node [wdH,wg6,wmE,wtt,wv4,wyS] .nil .nil) (.node [wdH,wg6,wmE,wt2,wwe,wyS] .nil .nil)) (.node [wdI,wg6,wmE,wtt,wwe,wyS] (.node [wdH,wg6,wmE,wud,wwe,wyS] .nil .nil) .nil)) (.node [wdO,wg6,wmE,wtt,wwe,wyS] (.node [wdN,wg6,wmE,wp6,wwe,wyS] (.node [wdK,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wdQ,wg6,wmE,wtt,wwe,wyS] (.node [wdP,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wdT,wg6,wmE,wn8,wwe,wyS] (.node [wdT,weV,wg6,wtt,wwe,wyS] (.node [wdS,wg6,wtt,wvg,wwe,wyS] (.node [wdS,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wdT,wg6,wla,wvk,wwe,wyS] (.node [wdT,wg6,wjl,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wdT,wg6,wmE,wtt,wwe,wyS] (.node [wdT,wg6,wmE,wqS,wtt,wwe] (.node [wdT,wg6,wmE,wqQ,wtt,wyS] .nil .nil) .nil) (.node [wdT,wg6,wmE,wtt,wwU,wyS] (.node [wdT,wg6,wmE,wtt,wwe,wzw] .nil .nil) .nil)))) (.node [wdW,wg6,wmE,wtt,wwN,wyS] (.node [wdW,wg6,wmE,woe,wwe,wyS] (.node [wdW,wg6,wjF,wtt,wwe,wyS] (.node [wdW,weE,wg6,wmE,wtt,wyS] (.node [wdT,wg6,wnG,wtt,wwe,wyS] .nil .nil) .nil) (.node [wdW,wg6,wmr,wtt,wwe,wyS] (.node [wdW,wg6,wkw,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wdW,wg6,wmE,wrT,wtt,wwe] (.node [wdW,wg6,wmE,wrg,wwe,wyS] (.node [wdW,wg6,wmE,wq4,wtt,wwe] .nil .nil) .nil) (.node [wdW,wg6,wmE,wtt,wwe,wyI] (.node [wdW,wg6,wmE,wtj,wwe,wyS] .nil .nil) .nil))) (.node [wd1,wg6,wmE,wtt,wwe,wyS] (.node [wdX,wg6,wmE,wtt,wwe,wyS] (.node [wdW,wg6,wmE,wtt,wwX,wyS] (.node [wdW,wg6,wmE,wtt,wwT,wyS] .nil .nil) .nil) (.node [wdZ,wg6,wmE,wtt,wwe,wyS] (.node [wdY,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wd4,wg6,wmE,wtt,wwe,wyS] (.node [wd3,wg6,wmE,wtt,wwe,wyS] (.node [wd2,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wd5,weV,wg6,wtt,wwe,wyS] (.node [wd4,wg6,wtt,wwe,wxR,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrllrl_ok : everyKey (rowOK 4 level4) level5lrllrl = true := by decide +kernel
def level5lrllrr : BinaryTree (List W) := (.node [web,weB,wg6,wmE,wtt,wwe] (.node [wd7,wg6,wmE,wtt,wyl,wyS] (.node [wd5,wg6,wmE,wtt,wwN,wyS] (.node [wd5,wg6,wmE,wqC,wtt,wwe] (.node [wd5,wg6,wmE,woh,wwe,wyS] (.node [wd5,wg6,wlC,wtt,wxV,wyS] .nil .nil) (.node [wd5,wg6,wmE,woH,wtt,wyS] .nil .nil)) (.node [wd5,wg6,wmE,wtt,wwe,wzz] (.node [wd5,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wd6,wg6,wmE,wtt,wwe,wyS] (.node [wd5,wg6,wnO,wtt,wwe,wyS] (.node [wd5,wg6,wmE,wua,wwe,wyS] .nil .nil) .nil) (.node [wd7,wg6,wmE,wtt,wwe,wyS] (.node [wd6,wg6,wmE,wwe,wyh,wyS] .nil .nil) .nil))) (.node [wd8,wg6,wmE,wtt,wwe,wyS] (.node [wd8,wg6,wmE,woH,wtt,wyS] (.node [wd8,wg6,wmE,wn8,wwe,wyS] (.node [wd8,wg6,wjQ,wtt,wwe,wyS] .nil .nil) .nil) (.node [wd8,wg6,wmE,wsK,wyr,wyS] (.node [wd8,wg6,wmE,wqv,wtt,wwe] .nil .nil) .nil)) (.node [wd8,wg6,wmE,wt9,wwe,wyS] (.node [wd8,wg6,wmE,wtt,wwT,wyS] (.node [wd8,wg6,wmE,wtt,wwe,wzA] .nil .nil) .nil) (.node [wd9,wg6,wmE,wtt,wwe,wyS] (.node [wd8,wg6,wnR,wtt,wwe,wyS] .nil .nil) .nil)))) (.node [web,wg6,wmE,wtt,wwe,wzy] (.node [web,wg6,wmE,wrg,wwe,wyS] (.node [web,wg6,wmr,wtt,wwe,wyS] (.node [web,wg6,wkw,wtt,wwe,wyS] (.node [web,wg6,wj2,wtt,wwe,wyS] .nil .nil) .nil) (.node [web,wg6,wmE,wqY,wtt,wyS] (.node [web,wg6,wmE,woj,wwe,wyS] .nil .nil) .nil)) (.node [web,wg6,wmE,wtt,wv4,wyS] (.node [web,wg6,wmE,wtj,wwe,wyS] (.node [web,wg6,wmE,wrx,wtt,wyS] .nil .nil) .nil) (.node [web,wg6,wmE,wtt,wwe,wzv] (.node [web,wg6,wmE,wtt,wwe,wzp] .nil .nil) .nil))) (.node [weh,wg6,wmE,wtt,wwe,wyS] (.node [wee,wg6,wmE,wtt,wwe,wyS] (.node [wed,wg6,wmE,wtt,wwe,wyS] (.node [wec,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [weg,wg6,wmE,wtt,wwe,wyS] (.node [wef,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wei,wg6,wjl,wtt,wwe,wyS] (.node [wei,weV,wg6,wtt,wwe,wyS] (.node [weh,wg6,wtt,wwe,wyS,wAk] .nil .nil) .nil) (.node [wei,wg6,wmE,woc,wwe,wyS] (.node [wei,wg6,wl2,wtt,wwe,wAo] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrllrr_ok : everyKey (rowOK 4 level4) level5lrllrr = true := by decide +kernel
def level5lrllr : BinaryTree (List W) := .node [wd5,wg6,wjl,wtt,wwe,wyS] level5lrllrl level5lrllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrllr_ok : everyKey (rowOK 4 level4) level5lrllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrllrl && everyKey (rowOK 4 level4) level5lrllrr) = true
  rw [level5lrllrl_ok, level5lrllrr_ok]
  decide +kernel
def level5lrll : BinaryTree (List W) := .node [wdH,wg6,wmE,wrT,wtt,wwe] level5lrlll level5lrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrll_ok : everyKey (rowOK 4 level4) level5lrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrlll && everyKey (rowOK 4 level4) level5lrllr) = true
  rw [level5lrlll_ok, level5lrllr_ok]
  decide +kernel
def level5lrlrll : BinaryTree (List W) := (.node [wem,wg6,wmE,wtt,wwe,wyS] (.node [wek,wg6,wmE,wsY,wwe,wAH] (.node [wej,wg6,wmE,wtt,wwe,wyS] (.node [wei,wg6,wmE,wtt,wwY,wyS] (.node [wei,wg6,wmE,wtt,wwe,wyS] (.node [wei,wg6,wmE,wpo,wtt,wwe] .nil .nil) (.node [wei,wg6,wmE,wtt,wwe,wzp] .nil .nil)) (.node [wei,wg6,wnV,wtt,wwe,wyS] (.node [wei,wg6,wmE,wue,wwe,wyS] .nil .nil) .nil)) (.node [wek,wg6,wmE,wn8,wwe,wyS] (.node [wek,wg6,wjz,wtt,wwe,wyS] (.node [wej,wg6,wmE,wtt,wwe,wAB] .nil .nil) .nil) (.node [wek,wg6,wmE,wpo,wtt,wwe] (.node [wek,wg6,wmE,woK,wtt,wyS] .nil .nil) .nil))) (.node [wel,wg6,wmE,wtt,wwe,wyS] (.node [wek,wg6,wmE,wtt,wwZ,wyS] (.node [wek,wg6,wmE,wtt,wwe,wzv] (.node [wek,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wek,wg6,wnW,wtt,wwe,wyS] (.node [wek,wg6,wmE,wud,wwe,wyS] .nil .nil) .nil)) (.node [wem,wg6,wmE,woH,wtt,wyS] (.node [wem,wg6,wmE,woa,wwe,wyS] (.node [wem,wg6,wjw,wtt,wwe,wyS] .nil .nil) .nil) (.node [wem,wg6,wmE,wtt,wvJ,wAR] (.node [wem,wg6,wmE,wpo,wtt,wwe] .nil .nil) .nil)))) (.node [weq,wg6,wmE,wtt,wwe,wyE] (.node [wep,wg6,wmr,wtt,wwe,wyS] (.node [wem,wg6,wnX,wtt,wwe,wyS] (.node [wem,wg6,wmE,wtt,wwX,wyS] (.node [wem,wg6,wmE,wtt,wwe,wzy] .nil .nil) (.node [wem,wg6,wmE,wuf,wwe,wyS] .nil .nil)) (.node [weo,wg6,wmE,wtt,wwe,wyS] (.node [wen,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wep,wmE,wnQ,wtt,wwe,wyS] (.node [wep,wiC,wmE,wtt,wwe,wyS] (.node [wep,wg7,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [weq,wg6,wmE,wtt,wv0,wyS] (.node [weq,wg6,wmE,wtf,wwe,wyS] .nil .nil) .nil))) (.node [wey,wg6,wmE,wtt,wwe,wyS] (.node [weu,wg6,wmE,wtt,wwe,wyS] (.node [wes,wg6,wmE,wtt,wwe,wyS] (.node [weq,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wex,wg6,wmE,wtt,wwe,wyS] (.node [wev,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [weB,wg6,wmE,wpo,wtt,wwe] (.node [weA,wiC,wmE,wtt,wwe,wyS] (.node [wez,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [weB,wg6,wmE,wtt,wwe] (.node [weB,wg6,wmE,wp6,wtt,wwe] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrll_ok : everyKey (rowOK 4 level4) level5lrlrll = true := by decide +kernel
def level5lrlrlr : BinaryTree (List W) := (.node [weV,wg6,wr5,wtt,wwe,wyS] (.node [weI,wg6,wmE,wvy,wwe,wyS] (.node [weE,wg6,wmE,wtt,wx5,wyS] (.node [weE,wg6,wmE,woH,wtt,wyS] (.node [weC,wiC,wmE,wtt,wwe,wyS] (.node [weB,wg6,wmE,wtt,wwe,wAu] .nil .nil) (.node [weD,wiC,wmE,wtt,wwe,wyS] .nil .nil)) (.node [weE,wg6,wmE,wtt,wwe,wyS] (.node [weE,wg6,wmE,wp6,wtt,wyS] .nil .nil) .nil)) (.node [weI,wg6,wmE,wn8,wwe,wyS] (.node [weH,wiC,wmE,wtt,wwe,wyS] (.node [weE,wg6,wmE,wtt,wyS] .nil .nil) .nil) (.node [weI,wg6,wmE,wtt,wwe,wyS] (.node [weI,wg6,wmE,wp6,wwe,wyS] .nil .nil) .nil))) (.node [weV,wg6,wp6,wtt,wwe,wzp] (.node [weO,wg6,wmE,wp6,wtt,wwe] (.node [weK,wg6,wmE,wp6,wtt,wyS] (.node [weI,wg6,wmE,wwe,wyS] .nil .nil) .nil) (.node [weV,wg6,wmr,wtt,wwe,wyS] (.node [weV,wf3,wg6,wtt,wwe,wyS] .nil .nil) .nil)) (.node [weV,wg6,wp6,wtt,wwP,wyS] (.node [weV,wg6,wp6,wtt,wwN,wyS] (.node [weV,wg6,wp6,wtt,wwe,wzr] .nil .nil) .nil) (.node [weV,wg6,wp6,wt4,wwe,wyS] (.node [weV,wg6,wp6,wt2,wwe,wyS] .nil .nil) .nil)))) (.node [weZ,wmE,wtt,wwe,wyS,wAX] (.node [weZ,wg6,wmr,wtt,wwe,wyS] (.node [weW,wg6,wqt,wtt,wwe,wyS] (.node [weW,wg6,wp6,wtt,wwe,wyS] (.node [weV,wg6,wsB,wtt,wwe,wyS] .nil .nil) .nil) (.node [weZ,wfz,wtt,wwe,wyS,wA8] (.node [weX,wg6,wp6,wtt,wwe,wAo] .nil .nil) .nil)) (.node [weZ,wmE,wtj,wwe,wyS,wA8] (.node [weZ,wmE,wnQ,wtt,wwe,wyS] (.node [weZ,wmr,wtt,wwe,wyS,wA8] .nil .nil) .nil) (.node [weZ,wmE,wtt,wwe,wyI,wA8] (.node [weZ,wmE,wtt,wv4,wyS,wA8] .nil .nil) .nil))) (.node [we5,wg6,wp6,wtt,wxV,wyS] (.node [we3,wg6,wp6,wtt,wwe,wyS] (.node [we1,wmE,wtt,wwe,wyS,wA8] (.node [weZ,wmE,wtt,wwe,wyS,wA8] .nil .nil) .nil) (.node [we4,wmE,wtt,wwe,wyS,wA8] (.node [we3,wg6,wqO,wtt,wwe,wyS] .nil .nil) .nil)) (.node [we8,wmE,wtt,wwe,wyS,wA8] (.node [we7,wg6,wq8,wtt,wwe,wyS] (.node [we7,wg6,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wfe,wfV,wg6,wp6,wwe,wyS] (.node [we9,wg6,wp6,wvk,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrlr_ok : everyKey (rowOK 4 level4) level5lrlrlr = true := by decide +kernel
def level5lrlrl : BinaryTree (List W) := .node [weB,wg6,wmE,wtt,wwe,wyS] level5lrlrll level5lrlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrl_ok : everyKey (rowOK 4 level4) level5lrlrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrlrll && everyKey (rowOK 4 level4) level5lrlrlr) = true
  rw [level5lrlrll_ok, level5lrlrlr_ok]
  decide +kernel
def level5lrlrrl : BinaryTree (List W) := (.node [wfz,wg6,wjl,wtt,wwe,wyS] (.node [wfx,wg6,wr4,wtt,wwe,wyS] (.node [wfs,wg6,wmr,wtt,wwe,wyS] (.node [wfm,wg6,wmr,wtt,wwe,wyS] (.node [wfi,wg6,wmE,wp6,wwe,wyS] (.node [wff,wg6,wmr,wtt,wwe,wyS] .nil .nil) (.node [wfm,wfQ,wg6,wp6,wtt,wyS] .nil .nil)) (.node [wfs,wfL,wg6,wp6,wtt,wwe] (.node [wfn,wg6,wmr,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wfx,wg6,wjl,wtt,wwe,wyS] (.node [wfx,wg6,wir,wtt,wwe,wyS] (.node [wft,wg6,wmr,wtt,wwe,wyS] .nil .nil) .nil) (.node [wfx,wg6,wpW,wtt,wwe,wyS] (.node [wfx,wg6,wmr,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wfx,wiv,wjt,wtt,wwe,wyS] (.node [wfx,wir,wiv,wtt,wwe,wyS] (.node [wfx,whh,wp6,wtt,wwe,wyS] (.node [wfx,wg6,wtt,wwe,wyS,wAX] .nil .nil) .nil) (.node [wfx,wiv,wjl,wtt,wwe,wyS] (.node [wfx,wiv,wiC,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wfx,wiv,wtt,wwe,wyS,wA8] (.node [wfx,wiv,wr5,wtt,wwe,wyS] (.node [wfx,wiv,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wfz,wg6,wiC,wtt,wwe,wyS] (.node [wfx,wp6,wrP,wtt,wwe,wyS] .nil .nil) .nil)))) (.node [wfA,wg6,wjl,wtt,wwe,wyS] (.node [wfz,wg6,wr5,wtt,wwe,wyS] (.node [wfz,wg6,wp6,wtt,wv4,wyS] (.node [wfz,wg6,wp6,wtj,wwe,wyS] (.node [wfz,wg6,wmr,wtt,wwe,wyS] .nil .nil) .nil) (.node [wfz,wg6,wp6,wtt,wwe,wyS] (.node [wfz,wg6,wp6,wtt,wwe,wyI] .nil .nil) .nil)) (.node [wfz,wg6,wtt,wwe,wyI,wA8] (.node [wfz,wg6,wtt,wv4,wyS,wA8] (.node [wfz,wg6,wtj,wwe,wyS,wA8] .nil .nil) .nil) (.node [wfz,wiC,wtt,wwe,wyS,wA8] (.node [wfz,wg6,wtt,wwe,wyS,wA8] .nil .nil) .nil))) (.node [wfE,wg6,wp6,wtt,wwe,wyS] (.node [wfC,wg6,wjl,wtt,wwe,wyS] (.node [wfB,wg6,wtt,wwe,wyS,wA8] (.node [wfB,wg6,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wfD,wg6,wtt,wwe,wyS,wA8] (.node [wfD,wg6,wp6,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wfG,wg6,wtt,wwe,wyS,wA8] (.node [wfG,wg6,wp6,wtt,wwe,wyS] (.node [wfF,wg6,wjl,wtt,wwe,wyS] .nil .nil) .nil) (.node [wfI,wg6,wp6,wtt,wwe,wyS] (.node [wfH,wg6,wp6,wtt,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrrl_ok : everyKey (rowOK 4 level4) level5lrlrrl = true := by decide +kernel
def level5lrlrrr : BinaryTree (List W) := (.node [wf4,wmE,wtt,wwe,wyS,wA8] (.node [wfV,wg6,wmE,wp6,wwe,wyS] (.node [wfQ,wg6,wlC,wp6,wtt,wyS] (.node [wfL,wg6,wp6,wtt,wwe,wAo] (.node [wfL,wg6,wp6,wtt,wwe] (.node [wfL,wg6,wmE,wp6,wtt,wwe] .nil .nil) (.node [wfL,wg6,wp6,wtt,wwe,wyS] .nil .nil)) (.node [wfN,wmE,wtt,wwe,wyS,wA8] (.node [wfN,wg6,wjl,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wfQ,wg6,wp6,wtt,wxV,wyS] (.node [wfQ,wg6,wp6,wtt,wwe,wyS] (.node [wfQ,wg6,wmE,wp6,wtt,wyS] .nil .nil) .nil) (.node [wfV,wg6,wla,wp6,wwe,wyS] (.node [wfQ,wg6,wp6,wtt,wyS] .nil .nil) .nil))) (.node [wf3,wg6,wjl,wtt,wwe,wyS] (.node [wfV,wg6,wp6,wwe,wyS] (.node [wfV,wg6,wp6,wvk,wwe,wyS] (.node [wfV,wg6,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wf2,wg6,wmE,wp6,wtt,wwe] (.node [wfY,wg6,wmE,wp6,wtt,wyS] .nil .nil) .nil)) (.node [wf3,wg6,wsC,wtt,wwe,wyS] (.node [wf3,wg6,wp6,wtt,wwe,wyS] (.node [wf3,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wf4,wg6,wjl,wtt,wwe,wyS] (.node [wf3,wg6,wtt,wwe,wyS] .nil .nil) .nil)))) (.node [wf9,wmE,wp6,wuS,wwe,wyS] (.node [wf9,wks,wp6,wuS,wwe,wyS] (.node [wf9,wia,wmE,wp6,wwe,wyS] (.node [wf9,wg6,wmr,wtt,wwe,wyS] (.node [wf5,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wf9,wjl,wmE,wuS,wwe,wyS] (.node [wf9,wiC,wmE,wuS,wwe,wyS] .nil .nil) .nil)) (.node [wf9,wk2,wmE,wp6,wuS,wwe] (.node [wf9,wkX,wmE,wp6,wuS,wyS] (.node [wf9,wkK,wmE,wuS,wwe,wyS] .nil .nil) .nil) (.node [wf9,wmE,wp6,wuR,wwe,wyS] (.node [wf9,wmE,wp6,wuQ,wwe,wyS] .nil .nil) .nil))) (.node [wgc,wip,wmE,wp6,wtt,wwe] (.node [wf9,wmE,wuS,wvw,wwe,wyS] (.node [wf9,wmE,wp6,wuS,wxj,wyS] (.node [wf9,wmE,wp6,wuS,wwe,wzT] .nil .nil) .nil) (.node [wf9,wp6,wuS,wvg,wwe,wyS] (.node [wf9,wmE,wuS,wwe,wyS,wA8] .nil .nil) .nil)) (.node [wgh,wg6,wjl,wtt,wwe,wyS] (.node [wgg,wg6,wmE,wp6,wwe,wyS] (.node [wge,wie,wmE,wp6,wtt,wyS] .nil .nil) .nil) (.node [wgh,wg6,wtt,wvk,wwe,wyS] (.node [wgh,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrrr_ok : everyKey (rowOK 4 level4) level5lrlrrr = true := by decide +kernel
def level5lrlrr : BinaryTree (List W) := .node [wfL,wg6,wl2,wp6,wtt,wwe] level5lrlrrl level5lrlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrr_ok : everyKey (rowOK 4 level4) level5lrlrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrlrrl && everyKey (rowOK 4 level4) level5lrlrrr) = true
  rw [level5lrlrrl_ok, level5lrlrrr_ok]
  decide +kernel
def level5lrlr : BinaryTree (List W) := .node [wfe,wg6,wmr,wtt,wwe,wyS] level5lrlrl level5lrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlr_ok : everyKey (rowOK 4 level4) level5lrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrlrl && everyKey (rowOK 4 level4) level5lrlrr) = true
  rw [level5lrlrl_ok, level5lrlrr_ok]
  decide +kernel
def level5lrl : BinaryTree (List W) := .node [wei,wg6,wmE,woL,wtt,wyS] level5lrll level5lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrl_ok : everyKey (rowOK 4 level4) level5lrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrll && everyKey (rowOK 4 level4) level5lrlr) = true
  rw [level5lrll_ok, level5lrlr_ok]
  decide +kernel
def level5lrrlll : BinaryTree (List W) := (.node [wgu,wip,wmE,wp6,wtt,wwe] (.node [wgr,wjl,wmE,wtt,wxz,wyS] (.node [wgn,wg6,wjl,wtt,wwe,wyS] (.node [wgk,wg6,wmE,wtt,wwe,wyS] (.node [wgj,wmE,wp6,wuS,wwe,wyS] (.node [wgj,wg6,wjl,wtt,wwe,wyS] .nil .nil) (.node [wgj,wp6,wtt,wwe,wyS,wA1] .nil .nil)) (.node [wgm,wmE,wtt,wwe,wyS,wA8] (.node [wgl,wiC,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wgr,wh8,wmE,wp6,wxz,wyS] (.node [wgr,wg6,wmr,wtt,wwe,wyS] (.node [wgn,wiv,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wgr,wiC,wmE,wtt,wxz,wyS] (.node [wgr,wim,wmE,wp6,wtt,wyS] .nil .nil) .nil))) (.node [wgr,wmE,wp6,wtt,wxz,wyS] (.node [wgr,wkn,wmE,wp6,wtt,wxz] (.node [wgr,wkc,wmE,wtt,wxz,wyS] (.node [wgr,wjY,wp6,wtt,wxz,wyS] .nil .nil) .nil) (.node [wgr,wmE,wp6,wtt,wxy,wyS] (.node [wgr,wmE,wp6,wtt,wxx,wyS] .nil .nil) .nil)) (.node [wgr,wmE,wtt,wxz,wx3,wyS] (.node [wgr,wmE,wp6,wuC,wxz,wyS] (.node [wgr,wmE,wp6,wtt,wxz,wz0] .nil .nil) .nil) (.node [wgr,wp6,wtt,wxz,wxR,wyS] (.node [wgr,wmE,wtt,wxz,wyS,wA8] .nil .nil) .nil)))) (.node [wgD,wiv,wp6,wtt,wwe,wyS] (.node [wgz,wmE,wp6,wtt,wxz,wyS] (.node [wgx,wg6,wtt,wwe,wxV,wyS] (.node [wgx,wg6,wjl,wtt,wwe,wyS] (.node [wgw,whW,wmE,wp6,wwe,wyS] .nil .nil) (.node [wgx,wg6,wmE,wtt,wwe,wyS] .nil .nil)) (.node [wgz,wg6,wjl,wtt,wwe,wyS] (.node [wgy,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wgB,wiC,wmE,wtt,wwe,wyS] (.node [wgA,wg6,wmE,wtt,wwe,wyS] (.node [wgz,wp6,wtt,wwe,wyS,wA1] .nil .nil) .nil) (.node [wgD,wg6,wjl,wtt,wwe,wyS] (.node [wgC,wmE,wtt,wwe,wyS,wA8] .nil .nil) .nil))) (.node [wgJ,wg6,wmE,wtt,wwe,wyS] (.node [wgG,wmE,wp6,wuS,wwe,wyS] (.node [wgG,wmE,wp6,wtt,wxz,wyS] (.node [wgF,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wgJ,wg6,wjl,wtt,wwe,wyS] (.node [wgH,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wgM,wg6,wmE,wtt,wwe,wyS] (.node [wgL,wg6,wmE,wtt,wwe,wyS] (.node [wgJ,wg6,wtt,wwe,wyS,wAo] .nil .nil) .nil) (.node [wgN,wiC,wmE,wtt,wwe,wyS] (.node [wgN,wir,wmE,wtt,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrlll_ok : everyKey (rowOK 4 level4) level5lrrlll = true := by decide +kernel
def level5lrrllr : BinaryTree (List W) := (.node [wg0,wmE,wtt,wwe,wyS,wA8] (.node [wgR,wmE,wp6,wuL,wwe,wz7] (.node [wgR,wja,wmE,wtt,wwe,wz7] (.node [wgR,wiq,wmE,wp6,wtt,wwe] (.node [wgR,wh3,wmE,wp6,wwe,wz7] (.node [wgR,wg6,wmr,wtt,wwe,wyS] .nil .nil) (.node [wgR,wil,wmE,wp6,wtt,wz7] .nil .nil)) (.node [wgR,wi5,wp6,wtt,wwe,wz7] (.node [wgR,wiC,wmE,wtt,wwe,wz7] .nil .nil) .nil)) (.node [wgR,wmE,wp6,wtt,wwe,wz6] (.node [wgR,wmE,wp6,wtt,wwe,wz5] (.node [wgR,wjl,wmE,wtt,wwe,wz7] .nil .nil) .nil) (.node [wgR,wmE,wp6,wtt,wxs,wz7] (.node [wgR,wmE,wp6,wtt,wwe,wz7] .nil .nil) .nil))) (.node [wgW,wg6,wmE,wtt,wwe,wyS] (.node [wgR,wp6,wtt,wwe,wz7,wAk] (.node [wgR,wmE,wtt,wwe,wz7,wA8] (.node [wgR,wmE,wtt,wwe,wz7,wAs] .nil .nil) .nil) (.node [wgV,whW,wmE,wp6,wwe,wyS] (.node [wgU,wie,wmE,wp6,wtt,wyS] .nil .nil) .nil)) (.node [wgX,wp6,wtt,wwe,wyS,wA1] (.node [wgX,wmE,wp6,wtt,wwe,wz7] (.node [wgX,wg6,wjl,wtt,wwe,wyS] .nil .nil) .nil) (.node [wgZ,wiC,wmE,wtt,wwe,wyS] (.node [wgY,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil)))) (.node [wg6,wg7,wmE,wrT,wtt,wwe] (.node [wg4,wmE,wp6,wtt,wwe,wz7] (.node [wg2,wmE,wp6,wtt,wwe,wz7] (.node [wg1,wiv,wp6,wtt,wwe,wyS] (.node [wg1,wg6,wjl,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg3,wg6,wmE,wtt,wwe,wyS] (.node [wg2,wmE,wp6,wuS,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wg6,wmr,wtt,wwe,wyS] (.node [wg5,wg6,wmE,wtt,wwe,wyS] (.node [wg4,wmE,wp6,wtt,wxz,wyS] .nil .nil) .nil) (.node [wg6,wg7,wmE,wrx,wtt,wyS] (.node [wg6,wg7,wmE,wrg,wwe,wyS] .nil .nil) .nil))) (.node [wg6,whb,wmE,wtt,wwe,wyS] (.node [wg6,wg7,wmE,wtt,wwN,wyS] (.node [wg6,wg7,wmE,wtt,wwe,wzp] (.node [wg6,wg7,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wg9,wmE,wtt,wwe,wyS] (.node [wg6,wg7,wmE,wt2,wwe,wyS] .nil .nil) .nil)) (.node [wg6,whf,wmE,wtt,wwe,wyS] (.node [wg6,whe,wmE,wtt,wwe,wyS] (.node [wg6,whc,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,whm,wmE,wp6,wtt,wwe] (.node [wg6,whg,wmE,wtt,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrllr_ok : everyKey (rowOK 4 level4) level5lrrllr = true := by decide +kernel
def level5lrrll : BinaryTree (List W) := .node [wgO,wg6,wmE,wtt,wwe,wyS] level5lrrlll level5lrrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrll_ok : everyKey (rowOK 4 level4) level5lrrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrlll && everyKey (rowOK 4 level4) level5lrrllr) = true
  rw [level5lrrlll_ok, level5lrrllr_ok]
  decide +kernel
def level5lrrlrl : BinaryTree (List W) := (.node [wg6,wh3,wil,wmE,wp6,wyS] (.node [wg6,whW,wmE,wp6,wxj,wyS] (.node [wg6,whV,wmE,wuY,wwe,wyS] (.node [wg6,whS,wmE,wp6,wyr,wyS] (.node [wg6,whJ,wmE,wp6,wtt,wyS] (.node [wg6,whG,wmE,wp6,wwe,wyS] .nil .nil) (.node [wg6,whR,wmE,wp6,wtt,wwe] .nil .nil)) (.node [wg6,whU,wp6,wvk,wwe,wyS] (.node [wg6,whT,wmE,wp6,wwe,wAH] .nil .nil) .nil)) (.node [wg6,whW,wmE,wp6,wwe,wzK] (.node [wg6,whW,wmr,wtt,wwe,wyS] (.node [wg6,whW,wjl,wvk,wwe,wyS] .nil .nil) .nil) (.node [wg6,whW,wmE,wp6,ww9,wyS] (.node [wg6,whW,wmE,wp6,wwe,wzT] .nil .nil) .nil))) (.node [wg6,whZ,wmE,wp6,wwe,wyS] (.node [wg6,whX,wmE,wu3,wwe,wyS] (.node [wg6,whX,wjl,wvk,wwe,wyS] (.node [wg6,whW,wp6,wvg,wwe,wyS] .nil .nil) .nil) (.node [wg6,whY,wmE,wp6,wwe,wyS] (.node [wg6,whX,wp6,wvk,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wh1,wmE,wp6,wwe,wyS] (.node [wg6,wh0,wmE,wp6,wwe,wyS] (.node [wg6,wh0,wjl,wmE,wwe,wyS] .nil .nil) .nil) (.node [wg6,wh2,wmE,wp6,wwe,wyS] (.node [wg6,wh2,wiC,wmE,wwe,wyS] .nil .nil) .nil)))) (.node [wg6,wh5,wmE,wp6,wwe,wyS] (.node [wg6,wh3,wmE,wp6,wxs,wyS] (.node [wg6,wh3,wja,wmE,wwe,wyS] (.node [wg6,wh3,wi5,wp6,wwe,wyS] (.node [wg6,wh3,wiC,wmE,wwe,wyS] .nil .nil) .nil) (.node [wg6,wh3,wmE,wp6,wwe,wyS] (.node [wg6,wh3,wjl,wmE,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wh3,wp6,wwe,wyS,wAk] (.node [wg6,wh3,wmE,wwe,wyS,wA8] (.node [wg6,wh3,wmE,wwe,wyS,wAs] .nil .nil) .nil) (.node [wg6,wh5,wjl,wmE,wwe,wyS] (.node [wg6,wh4,wmE,wp6,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wh8,wjY,wp6,wwe,wyS] (.node [wg6,wh7,wmE,wp6,wwe,wyS] (.node [wg6,wh7,wiC,wmE,wwe,wyS] (.node [wg6,wh6,wmE,wp6,wwe,wyS] .nil .nil) .nil) (.node [wg6,wh8,wjl,wmE,wwe,wyS] (.node [wg6,wh8,wiC,wmE,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wh8,wmE,wp6,wwe,wyS] (.node [wg6,wh8,wkn,wmE,wp6,wwe] (.node [wg6,wh8,wkc,wmE,wwe,wyS] .nil .nil) .nil) (.node [wg6,wh8,wmE,wwe,wx3,wyS] (.node [wg6,wh8,wmE,wp6,wwe,wz0] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrlrl_ok : everyKey (rowOK 4 level4) level5lrrlrl = true := by decide +kernel
def level5lrrlrr : BinaryTree (List W) := (.node [wg6,wil,wi5,wp6,wtt,wyS] (.node [wg6,wie,wp6,wtt,wxR,wyS] (.node [wg6,wie,wjl,wtt,wxV,wyS] (.node [wg6,wib,wmE,wp6,wtt,wAR] (.node [wg6,wh9,wmE,wp6,wwe,wyS] (.node [wg6,wh8,wp6,wwe,wxR,wyS] .nil .nil) (.node [wg6,wia,wmE,wp6,wwe,wyS] .nil .nil)) (.node [wg6,wid,wmE,wtt,wxD,wyS] (.node [wg6,wic,wp6,wtt,wxV,wyS] .nil .nil) .nil)) (.node [wg6,wie,wmE,wp6,wtt,wz0] (.node [wg6,wie,wmE,wp6,wtt,wzN] (.node [wg6,wie,wmr,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wie,wmE,wp6,wuC,wyS] (.node [wg6,wie,wmE,wp6,wuq,wyS] .nil .nil) .nil))) (.node [wg6,wii,wjl,wmE,wtt,wyS] (.node [wg6,wif,wp6,wtt,wxV,wyS] (.node [wg6,wif,wmE,wtt,wxI,wyS] (.node [wg6,wif,wjl,wtt,wxV,wyS] .nil .nil) .nil) (.node [wg6,wih,wmE,wp6,wtt,wyS] (.node [wg6,wig,wmE,wp6,wtt,wyS] .nil .nil) .nil)) (.node [wg6,wik,wiC,wmE,wtt,wyS] (.node [wg6,wij,wmE,wp6,wtt,wyS] (.node [wg6,wii,wmE,wp6,wtt,wyS] .nil .nil) .nil) (.node [wg6,wil,wiC,wmE,wtt,wyS] (.node [wg6,wik,wmE,wp6,wtt,wyS] .nil .nil) .nil)))) (.node [wg6,wip,wmr,wtt,wwe,wyS] (.node [wg6,wil,wmE,wtt,wyS,wA8] (.node [wg6,wil,wmE,wp6,wtt,wyS] (.node [wg6,wil,wjl,wmE,wtt,wyS] (.node [wg6,wil,wja,wmE,wtt,wyS] .nil .nil) .nil) (.node [wg6,wil,wmE,wtt,wyS,wAs] (.node [wg6,wil,wmE,wp6,wuL,wyS] .nil .nil) .nil)) (.node [wg6,win,wp6,wtt,wwe,wAo] (.node [wg6,wim,wmE,wp6,wtt,wyS] (.node [wg6,wil,wp6,wtt,wyS,wAk] .nil .nil) .nil) (.node [wg6,wip,wjl,wtt,wwe,wAo] (.node [wg6,wio,wmE,wtt,wwe,wAa] .nil .nil) .nil))) (.node [wg6,wiq,wmE,wp6,wtt,wwe] (.node [wg6,wip,wmE,wp6,wuu,wwe] (.node [wg6,wip,wmE,wp6,wtt,wxs] (.node [wg6,wip,wmE,wp6,wtt,wxd] .nil .nil) .nil) (.node [wg6,wip,wp6,wtt,wwe,wAk] (.node [wg6,wip,wmE,wp6,wuL,wwe] .nil .nil) .nil)) (.node [wg6,wir,wmJ,wtt,wwe,wyS] (.node [wg6,wir,wmE,wtt,wwe,wyS] (.node [wg6,wir,wmr,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wir,wtt,wwe,wxV,wyS] (.node [wg6,wir,wtt,wvk,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrlrr_ok : everyKey (rowOK 4 level4) level5lrrlrr = true := by decide +kernel
def level5lrrlr : BinaryTree (List W) := .node [wg6,wh8,wmE,wwe,wyS,wA8] level5lrrlrl level5lrrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrlr_ok : everyKey (rowOK 4 level4) level5lrrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrlrl && everyKey (rowOK 4 level4) level5lrrlrr) = true
  rw [level5lrrlrl_ok, level5lrrlrr_ok]
  decide +kernel
def level5lrrl : BinaryTree (List W) := .node [wg6,whv,wmE,wp6,wtt,wyS] level5lrrll level5lrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrl_ok : everyKey (rowOK 4 level4) level5lrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrll && everyKey (rowOK 4 level4) level5lrrlr) = true
  rw [level5lrrll_ok, level5lrrlr_ok]
  decide +kernel
def level5lrrrll : BinaryTree (List W) := (.node [wg6,wiC,wkW,wmE,wtt,wyS] (.node [wg6,wiB,wmE,wtt,wwe,wyS] (.node [wg6,wiv,wp6,wt4,wwe,wyS] (.node [wg6,wiv,wmr,wtt,wwe,wyS] (.node [wg6,wit,wmE,wtt,wwe,wyS] (.node [wg6,wis,wmE,wtt,wwe,wyS] .nil .nil) (.node [wg6,wiu,wmE,wtt,wwe,wyS] .nil .nil)) (.node [wg6,wiv,wp6,wtt,wwP,wyS] (.node [wg6,wiv,wp6,wtt,wwe,wzr] .nil .nil) .nil)) (.node [wg6,wiy,wmE,wtt,wwe,wyS] (.node [wg6,wix,wmE,wtt,wwe,wyS] (.node [wg6,wiw,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wiA,wmE,wtt,wwe,wyS] (.node [wg6,wiz,wmE,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wiC,wj2,wtt,wwe,wyS] (.node [wg6,wiC,wjF,wtt,wwe,wyS] (.node [wg6,wiC,wi5,wtt,wwe,wyS] (.node [wg6,wiC,wi4,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wiC,wjY,wtt,wwe,wyS] (.node [wg6,wiC,wjX,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wiC,wkr,wtt,wwe,wyS] (.node [wg6,wiC,wkn,wmE,wtt,wwe] (.node [wg6,wiC,wkm,wmE,wtt,wwe] .nil .nil) .nil) (.node [wg6,wiC,wkw,wtt,wwe,wyS] (.node [wg6,wiC,wks,wtt,wwe,wyS] .nil .nil) .nil)))) (.node [wg6,wiC,wmE,wni,wtt,wyS] (.node [wg6,wiC,wll,wmE,wwe,wyS] (.node [wg6,wiC,wk2,wmE,wtt,wwe] (.node [wg6,wiC,wk1,wmE,wtt,wwe] (.node [wg6,wiC,wkX,wmE,wtt,wyS] .nil .nil) .nil) (.node [wg6,wiC,wlg,wmE,wwe,wyS] (.node [wg6,wiC,wla,wvk,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wiC,wl2,wtt,wwe,wAo] (.node [wg6,wiC,wlI,wmE,wtt,wyS] (.node [wg6,wiC,wlC,wtt,wxV,wyS] .nil .nil) .nil) (.node [wg6,wiC,wmE,wm7,wtt,wwe] (.node [wg6,wiC,wmr,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wiC,wmE,wqY,wtt,wyS] (.node [wg6,wiC,wmE,woj,wwe,wyS] (.node [wg6,wiC,wmE,woe,wwe,wyS] (.node [wg6,wiC,wmE,wnp,wtt,wwe] .nil .nil) .nil) (.node [wg6,wiC,wmE,wqK,wtt,wwe] (.node [wg6,wiC,wmE,woN,wtt,wyS] .nil .nil) .nil)) (.node [wg6,wiC,wmE,wre,wwe,wyS] (.node [wg6,wiC,wmE,wrd,wwe,wyS] (.node [wg6,wiC,wmE,wq4,wtt,wwe] .nil .nil) .nil) (.node [wg6,wiC,wmE,wru,wtt,wyS] (.node [wg6,wiC,wmE,wrg,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrll_ok : everyKey (rowOK 4 level4) level5lrrrll = true := by decide +kernel
def level5lrrrlr : BinaryTree (List W) := (.node [wg6,wiC,wmE,wtt,wwe,wzN] (.node [wg6,wiC,wmE,wtt,wv4,wyS] (.node [wg6,wiC,wmE,wtf,wwe,wyS] (.node [wg6,wiC,wmE,wrT,wtt,wwe] (.node [wg6,wiC,wmE,wrL,wtt,wwe] (.node [wg6,wiC,wmE,wrx,wtt,wyS] .nil .nil) (.node [wg6,wiC,wmE,wrM,wtt,wwe] .nil .nil)) (.node [wg6,wiC,wmE,wsY,wwe,wAH] (.node [wg6,wiC,wmE,wsK,wyr,wyS] .nil .nil) .nil)) (.node [wg6,wiC,wmE,wtt,wvJ,wAR] (.node [wg6,wiC,wmE,wtj,wwe,wyS] (.node [wg6,wiC,wmE,wti,wwe,wyS] .nil .nil) .nil) (.node [wg6,wiC,wmE,wtt,wv3,wyS] (.node [wg6,wiC,wmE,wtt,wv0,wyS] .nil .nil) .nil))) (.node [wg6,wiC,wmE,wtt,wwe,wzp] (.node [wg6,wiC,wmE,wtt,wwe,wyI] (.node [wg6,wiC,wmE,wtt,wwe,wyH] (.node [wg6,wiC,wmE,wtt,wwe,wyE] .nil .nil) .nil) (.node [wg6,wiC,wmE,wtt,wwe,wyW] (.node [wg6,wiC,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wiC,wmE,wtt,wwe,wzv] (.node [wg6,wiC,wmE,wtt,wwe,wzs] (.node [wg6,wiC,wmE,wtt,wwe,wzr] .nil .nil) .nil) (.node [wg6,wiC,wmE,wtt,wwe,wzK] (.node [wg6,wiC,wmE,wtt,wwe,wzy] .nil .nil) .nil)))) (.node [wg6,wiC,wmE,wtt,ww9,wyS] (.node [wg6,wiC,wmE,wtt,wwi,wyS] (.node [wg6,wiC,wmE,wtt,wwe,wz0] (.node [wg6,wiC,wmE,wtt,wwe,wzU] (.node [wg6,wiC,wmE,wtt,wwe,wzT] .nil .nil) .nil) (.node [wg6,wiC,wmE,wtt,wwe,wAB] (.node [wg6,wiC,wmE,wtt,wwe,wz1] .nil .nil) .nil)) (.node [wg6,wiC,wmE,wtt,wwQ,wyS] (.node [wg6,wiC,wmE,wtt,wwP,wyS] (.node [wg6,wiC,wmE,wtt,wwN,wyS] .nil .nil) .nil) (.node [wg6,wiC,wmE,wtt,wwX,wyS] (.node [wg6,wiC,wmE,wtt,wwT,wyS] .nil .nil) .nil))) (.node [wg6,wiC,wmE,wtt,wyl,wyS] (.node [wg6,wiC,wmE,wtt,wxk,wyS] (.node [wg6,wiC,wmE,wtt,wxj,wyS] (.node [wg6,wiC,wmE,wtt,wxd,wyS] .nil .nil) .nil) (.node [wg6,wiC,wmE,wtt,wxt,wyS] (.node [wg6,wiC,wmE,wtt,wxs,wyS] .nil .nil) .nil)) (.node [wg6,wiC,wmE,wt4,wwe,wyS] (.node [wg6,wiC,wmE,wt2,wwe,wyS] (.node [wg6,wiC,wmE,wtx,wwe,wyS] .nil .nil) .nil) (.node [wg6,wiC,wmE,wt9,wwe,wyS] (.node [wg6,wiC,wmE,wt5,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrlr_ok : everyKey (rowOK 4 level4) level5lrrrlr = true := by decide +kernel
def level5lrrrl : BinaryTree (List W) := .node [wg6,wiC,wmE,wrv,wtt,wyS] level5lrrrll level5lrrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrl_ok : everyKey (rowOK 4 level4) level5lrrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrrll && everyKey (rowOK 4 level4) level5lrrrlr) = true
  rw [level5lrrrll_ok, level5lrrrlr_ok]
  decide +kernel
def level5lrrrrl : BinaryTree (List W) := (.node [wg6,wiW,wmE,wtt,wwe,wyS] (.node [wg6,wiC,wtt,wwe,wxR,wyS] (.node [wg6,wiC,wmE,wwe,wyh,wyS] (.node [wg6,wiC,wmE,wuD,wwe,wyS] (.node [wg6,wiC,wmE,wuu,wwe,wyS] (.node [wg6,wiC,wmE,wuq,wwe,wyS] .nil .nil) (.node [wg6,wiC,wmE,wuC,wwe,wyS] .nil .nil)) (.node [wg6,wiC,wmE,wuM,wwe,wyS] (.node [wg6,wiC,wmE,wuL,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wiC,wnV,wtt,wwe,wyS] (.node [wg6,wiC,wnO,wtt,wwe,wyS] (.node [wg6,wiC,wnG,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wiC,wtt,wvh,wwe,wyS] (.node [wg6,wiC,wtt,wvg,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wiF,wmE,wtt,wwe,wyS] (.node [wg6,wiC,wtt,wwe,wyS,wAl] (.node [wg6,wiC,wtt,wwe,wyS,wAk] (.node [wg6,wiC,wtt,wwe,wxS,wyS] .nil .nil) .nil) (.node [wg6,wiE,wmE,wtt,wwe,wyS] (.node [wg6,wiD,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wiT,wp6,wtt,wwe,wyS] (.node [wg6,wiR,wmE,wtt,wwe,wyS] (.node [wg6,wiQ,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wiV,wmE,wtt,wwe,wyS] (.node [wg6,wiU,wmE,wtt,wwe,wyS] .nil .nil) .nil)))) (.node [wg6,wi5,wp6,wuL,wwe,wyS] (.node [wg6,wi2,wmE,wtt,wwe,wyS] (.node [wg6,wiY,wmE,wtt,wwe,wyS] (.node [wg6,wiY,wi5,wtt,wwe,wyS] (.node [wg6,wiX,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wi1,wp6,wtt,wwe,wyS] (.node [wg6,wiZ,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wi5,wjl,wtt,wwe,wyS] (.node [wg6,wi5,wja,wtt,wwe,wyS] (.node [wg6,wi4,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wi5,wp6,wtt,wxs,wyS] (.node [wg6,wi5,wp6,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wi9,wmE,wtt,wwe,wyS] (.node [wg6,wi6,wmE,wtt,wwe,wyS] (.node [wg6,wi5,wtt,wwe,wyS,wA8] (.node [wg6,wi5,wtt,wwe,wyS,wAs] .nil .nil) .nil) (.node [wg6,wi8,wmE,wtt,wwe,wyS] (.node [wg6,wi7,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wja,wmE,wuL,wwe,wyS] (.node [wg6,wja,wmE,wtt,wxs,wyS] (.node [wg6,wja,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wjb,wmE,wtt,wwe,wyS] (.node [wg6,wja,wtt,wwe,wyS,wAk] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrrl_ok : everyKey (rowOK 4 level4) level5lrrrrl = true := by decide +kernel
def level5lrrrrr : BinaryTree (List W) := (.node [wg6,wjl,wld,wtt,wwe,wyS] (.node [wg6,wjl,wjF,wtt,wwe,wyS] (.node [wg6,wjg,wmE,wtt,wwe,wyS] (.node [wg6,wje,wmE,wtt,wwe,wyS] (.node [wg6,wjc,wp6,wtt,wwe,wAo] (.node [wg6,wjc,wmE,wtt,wwe,wAf] .nil .nil) (.node [wg6,wjd,wmE,wtt,wwe,wyS] .nil .nil)) (.node [wg6,wjg,wjY,wtt,wwe,wyS] (.node [wg6,wjf,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wjj,wks,wtt,wwe,wyS] (.node [wg6,wji,wmE,wtt,wwe,wyS] (.node [wg6,wjh,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wjk,wmE,wtt,wwe,wyS] (.node [wg6,wjj,wmE,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wjl,wkw,wtt,wwe,wyS] (.node [wg6,wjl,wkk,wmE,wtt,wwe] (.node [wg6,wjl,wj2,wtt,wwe,wyS] (.node [wg6,wjl,wjY,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wjl,wks,wtt,wwe,wyS] (.node [wg6,wjl,wkn,wmE,wtt,wwe] .nil .nil) .nil)) (.node [wg6,wjl,wkZ,wmE,wtt,wwe] (.node [wg6,wjl,wkX,wmE,wtt,wyS] (.node [wg6,wjl,wkU,wmE,wtt,wyS] .nil .nil) .nil) (.node [wg6,wjl,wla,wvk,wwe,wyS] (.node [wg6,wjl,wk2,wmE,wtt,wwe] .nil .nil) .nil)))) (.node [wg6,wjl,wlZ,wtt,wwe,wyS] (.node [wg6,wjl,wlC,wtt,wxV,wyS] (.node [wg6,wjl,wll,wmE,wwe,wyS] (.node [wg6,wjl,wli,wtt,wwe,wyS] (.node [wg6,wjl,wlg,wmE,wwe,wyS] .nil .nil) .nil) (.node [wg6,wjl,wlp,wtt,wwe,wyS] (.node [wg6,wjl,wlo,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wjl,wlK,wtt,wwe,wyS] (.node [wg6,wjl,wlI,wmE,wtt,wyS] (.node [wg6,wjl,wlE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wjl,wlM,wtt,wwe,wyS] (.node [wg6,wjl,wlL,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wjl,wmr,wtt,wwe,wyS] (.node [wg6,wjl,wl5,wtt,wwe,wyS] (.node [wg6,wjl,wl4,wtt,wwe,wyS] (.node [wg6,wjl,wl2,wtt,wwe,wAo] .nil .nil) .nil) (.node [wg6,wjl,wl7,wtt,wwe,wyS] (.node [wg6,wjl,wl6,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wjl,wmE,wnp,wtt,wwe] (.node [wg6,wjl,wmE,wni,wtt,wyS] (.node [wg6,wjl,wmE,wm7,wtt,wwe] .nil .nil) .nil) (.node [wg6,wjl,wmE,woj,wwe,wyS] (.node [wg6,wjl,wmE,woe,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrrr_ok : everyKey (rowOK 4 level4) level5lrrrrr = true := by decide +kernel
def level5lrrrr : BinaryTree (List W) := .node [wg6,wjc,wjl,wtt,wwe,wAo] level5lrrrrl level5lrrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrr_ok : everyKey (rowOK 4 level4) level5lrrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrrrl && everyKey (rowOK 4 level4) level5lrrrrr) = true
  rw [level5lrrrrl_ok, level5lrrrrr_ok]
  decide +kernel
def level5lrrr : BinaryTree (List W) := .node [wg6,wiC,wmE,wud,wwe,wyS] level5lrrrl level5lrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrr_ok : everyKey (rowOK 4 level4) level5lrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrrl && everyKey (rowOK 4 level4) level5lrrrr) = true
  rw [level5lrrrl_ok, level5lrrrr_ok]
  decide +kernel
def level5lrr : BinaryTree (List W) := .node [wg6,wir,wtt,wwe,wyS,wAo] level5lrrl level5lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrr_ok : everyKey (rowOK 4 level4) level5lrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrl && everyKey (rowOK 4 level4) level5lrrr) = true
  rw [level5lrrl_ok, level5lrrr_ok]
  decide +kernel
def level5lr : BinaryTree (List W) := .node [wgi,wg6,wmE,wtt,wwe,wyS] level5lrl level5lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lr_ok : everyKey (rowOK 4 level4) level5lr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrl && everyKey (rowOK 4 level4) level5lrr) = true
  rw [level5lrl_ok, level5lrr_ok]
  decide +kernel
def level5l : BinaryTree (List W) := .node [wc2,wg6,wnV,wtt,wwe,wyS] level5ll level5lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5l_ok : everyKey (rowOK 4 level4) level5l = true := by
  change (_ && everyKey (rowOK 4 level4) level5ll && everyKey (rowOK 4 level4) level5lr) = true
  rw [level5ll_ok, level5lr_ok]
  decide +kernel
def level5rlllll : BinaryTree (List W) := (.node [wg6,wjl,wmE,wtt,wwe,wyS] (.node [wg6,wjl,wmE,wte,wwe,wyS] (.node [wg6,wjl,wmE,wrx,wtt,wyS] (.node [wg6,wjl,wmE,wre,wwe,wyS] (.node [wg6,wjl,wmE,wqY,wtt,wyS] (.node [wg6,wjl,wmE,wqK,wtt,wwe] .nil .nil) (.node [wg6,wjl,wmE,wq4,wtt,wwe] .nil .nil)) (.node [wg6,wjl,wmE,wrv,wtt,wyS] (.node [wg6,wjl,wmE,wrg,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wjl,wmE,wsK,wyr,wyS] (.node [wg6,wjl,wmE,wrT,wtt,wwe] (.node [wg6,wjl,wmE,wrM,wtt,wwe] .nil .nil) .nil) (.node [wg6,wjl,wmE,wtd,wwe,wyS] (.node [wg6,wjl,wmE,wsY,wwe,wAH] .nil .nil) .nil))) (.node [wg6,wjl,wmE,wtt,wv0,wyS] (.node [wg6,wjl,wmE,wtt,wvJ,wAR] (.node [wg6,wjl,wmE,wtj,wwe,wyS] (.node [wg6,wjl,wmE,wtf,wwe,wyS] .nil .nil) .nil) (.node [wg6,wjl,wmE,wtt,wvZ,wyS] (.node [wg6,wjl,wmE,wtt,wvY,wyS] .nil .nil) .nil)) (.node [wg6,wjl,wmE,wtt,wwe,wyD] (.node [wg6,wjl,wmE,wtt,wwe,wyx] (.node [wg6,wjl,wmE,wtt,wv4,wyS] .nil .nil) .nil) (.node [wg6,wjl,wmE,wtt,wwe,wyI] (.node [wg6,wjl,wmE,wtt,wwe,wyE] .nil .nil) .nil)))) (.node [wg6,wjl,wmE,wtt,wwy,wyS] (.node [wg6,wjl,wmE,wtt,wwe,wzN] (.node [wg6,wjl,wmE,wtt,wwe,wzv] (.node [wg6,wjl,wmE,wtt,wwe,wzp] (.node [wg6,wjl,wmE,wtt,wwe,wzc] .nil .nil) (.node [wg6,wjl,wmE,wtt,wwe,wzr] .nil .nil)) (.node [wg6,wjl,wmE,wtt,wwe,wzK] (.node [wg6,wjl,wmE,wtt,wwe,wzy] .nil .nil) .nil)) (.node [wg6,wjl,wmE,wtt,wwe,wzX] (.node [wg6,wjl,wmE,wtt,wwe,wzT] (.node [wg6,wjl,wmE,wtt,wwe,wzS] .nil .nil) .nil) (.node [wg6,wjl,wmE,wtt,wwe,wAB] (.node [wg6,wjl,wmE,wtt,wwe,wz0] .nil .nil) .nil))) (.node [wg6,wjl,wmE,wtt,wxd,wyS] (.node [wg6,wjl,wmE,wtt,wwT,wyS] (.node [wg6,wjl,wmE,wtt,wwP,wyS] (.node [wg6,wjl,wmE,wtt,wwN,wyS] .nil .nil) .nil) (.node [wg6,wjl,wmE,wtt,ww9,wyS] (.node [wg6,wjl,wmE,wtt,wwX,wyS] .nil .nil) .nil)) (.node [wg6,wjl,wmE,wtt,wxn,wyS] (.node [wg6,wjl,wmE,wtt,wxj,wyS] (.node [wg6,wjl,wmE,wtt,wxi,wyS] .nil .nil) .nil) (.node [wg6,wjl,wmE,wtt,wyl,wyS] (.node [wg6,wjl,wmE,wtt,wxs,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlllll_ok : everyKey (rowOK 4 level4) level5rlllll = true := by decide +kernel
def level5rllllr : BinaryTree (List W) := (.node [wg6,wjl,wnG,wtt,wwe,wyS] (.node [wg6,wjl,wmK,wtt,wwe,wyS] (.node [wg6,wjl,wmE,wuB,wwe,wyS] (.node [wg6,wjl,wmE,wud,wwe,wyS] (.node [wg6,wjl,wmE,wt4,wwe,wyS] (.node [wg6,wjl,wmE,wt2,wwe,wyS] .nil .nil) (.node [wg6,wjl,wmE,wt9,wwe,wyS] .nil .nil)) (.node [wg6,wjl,wmE,wuu,wwe,wyS] (.node [wg6,wjl,wmE,wuq,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wjl,wmE,wuL,wwe,wyS] (.node [wg6,wjl,wmE,wuG,wwe,wyS] (.node [wg6,wjl,wmE,wuC,wwe,wyS] .nil .nil) .nil) (.node [wg6,wjl,wmJ,wtt,wwe,wyS] (.node [wg6,wjl,wmE,wwe,wyh,wyS] .nil .nil) .nil))) (.node [wg6,wjl,wm2,wtt,wwe,wyS] (.node [wg6,wjl,wmR,wtt,wwe,wyS] (.node [wg6,wjl,wmM,wtt,wwe,wyS] (.node [wg6,wjl,wmL,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wjl,wmV,wtt,wwe,wyS] (.node [wg6,wjl,wmT,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wjl,wnf,wtt,wwe,wyS] (.node [wg6,wjl,wna,wtt,wwe,wyS] (.node [wg6,wjl,wm4,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wjl,wns,wtt,wwe,wyS] (.node [wg6,wjl,wnm,wtt,wwe,wyS] .nil .nil) .nil)))) (.node [wg6,wjl,wqo,wtt,wwe,wyS] (.node [wg6,wjl,wp6,wtt,wwe,wzp] (.node [wg6,wjl,wn8,wvk,wwe,wyS] (.node [wg6,wjl,wnV,wtt,wwe,wyS] (.node [wg6,wjl,wnO,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wjl,wpo,wtt,wwe,wAo] (.node [wg6,wjl,woH,wtt,wxV,wyS] .nil .nil) .nil)) (.node [wg6,wjl,wp6,wtt,wwP,wyS] (.node [wg6,wjl,wp6,wtt,wwN,wyS] (.node [wg6,wjl,wp6,wtt,wwe,wzr] .nil .nil) .nil) (.node [wg6,wjl,wp6,wt4,wwe,wyS] (.node [wg6,wjl,wp6,wt2,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wjl,wss,wtt,wwe,wyS] (.node [wg6,wjl,wr4,wtt,wwe,wyS] (.node [wg6,wjl,wqW,wtt,wwe,wyS] (.node [wg6,wjl,wqG,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wjl,wsm,wtt,wwe,wyS] (.node [wg6,wjl,wr5,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wjl,wsB,wtt,wwe,wyS] (.node [wg6,wjl,wsA,wtt,wwe,wyS] (.node [wg6,wjl,wsx,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wjl,wtt,wtF,wwe,wyS] (.node [wg6,wjl,wsC,wtt,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllllr_ok : everyKey (rowOK 4 level4) level5rllllr = true := by decide +kernel
def level5rllll : BinaryTree (List W) := .node [wg6,wjl,wmE,wtN,wwe,wyS] level5rlllll level5rllllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllll_ok : everyKey (rowOK 4 level4) level5rllll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlllll && everyKey (rowOK 4 level4) level5rllllr) = true
  rw [level5rlllll_ok, level5rllllr_ok]
  decide +kernel
def level5rlllrl : BinaryTree (List W) := (.node [wg6,wjl,wtt,wwe,wyS,wAo] (.node [wg6,wjl,wtt,wwe,wxf,wyS] (.node [wg6,wjl,wtt,wvk,wwe,wyS] (.node [wg6,wjl,wtt,wu8,wwe,wyS] (.node [wg6,wjl,wtt,wt4,wwe,wyS] (.node [wg6,wjl,wtt,wt2,wwe,wyS] .nil .nil) (.node [wg6,wjl,wtt,wuw,wwe,wyS] .nil .nil)) (.node [wg6,wjl,wtt,wvg,wwe,wyS] (.node [wg6,wjl,wtt,wvd,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wjl,wtt,wwe,wwA,wyS] (.node [wg6,wjl,wtt,wwe,wwq,wyS] (.node [wg6,wjl,wtt,wvI,wwe,wyS] .nil .nil) .nil) (.node [wg6,wjl,wtt,wwe,wwP,wyS] (.node [wg6,wjl,wtt,wwe,wwN,wyS] .nil .nil) .nil))) (.node [wg6,wjl,wtt,wwe,wyS,wy4] (.node [wg6,wjl,wtt,wwe,wxV,wyS] (.node [wg6,wjl,wtt,wwe,wxR,wyS] (.node [wg6,wjl,wtt,wwe,wxO,wyS] .nil .nil) .nil) (.node [wg6,wjl,wtt,wwe,wyA,wyS] (.node [wg6,wjl,wtt,wwe,wyd,wyS] .nil .nil) .nil)) (.node [wg6,wjl,wtt,wwe,wyS,wzr] (.node [wg6,wjl,wtt,wwe,wyS,wzp] (.node [wg6,wjl,wtt,wwe,wyS,wze] .nil .nil) .nil) (.node [wg6,wjl,wtt,wwe,wyS,wAk] (.node [wg6,wjl,wtt,wwe,wyS,wzP] .nil .nil) .nil)))) (.node [wg6,wjl,wuS,wvk,wwe,wyS] (.node [wg6,wjl,wtt,wwe,wz7,wAo] (.node [wg6,wjl,wtt,wwe,wyS,wAT] (.node [wg6,wjl,wtt,wwe,wyS,wAL] (.node [wg6,wjl,wtt,wwe,wyS,wAz] .nil .nil) .nil) (.node [wg6,wjl,wtt,wwe,wzr] (.node [wg6,wjl,wtt,wwe,wzp] .nil .nil) .nil)) (.node [wg6,wjl,wtt,wxz,wxV,wyS] (.node [wg6,wjl,wtt,wwP,wyS] (.node [wg6,wjl,wtt,wwN,wyS] .nil .nil) .nil) (.node [wg6,wjl,wt4,wwe,wyS] (.node [wg6,wjl,wt2,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wjs,wmE,wtt,wwe,wyS] (.node [wg6,wjo,wmE,wtt,wwe,wyS] (.node [wg6,wjn,wmE,wtt,wwe,wyS] (.node [wg6,wjm,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wjr,wmE,wtt,wwe,wyS] (.node [wg6,wjq,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wjw,wp6,wtt,wwe,wyS] (.node [wg6,wjw,wmE,wtt,wwe,wyS] (.node [wg6,wjt,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wjw,wtt,wwe,wyS,wAR] (.node [wg6,wjw,wtt,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlllrl_ok : everyKey (rowOK 4 level4) level5rlllrl = true := by decide +kernel
def level5rlllrr : BinaryTree (List W) := (.node [wg6,wjK,wmE,wtt,wwe,wyS] (.node [wg6,wjF,woN,wp6,wtt,wyS] (.node [wg6,wjC,wp6,wtt,wwe,wyS] (.node [wg6,wjz,wtt,wwe,wyS,wAH] (.node [wg6,wjz,wp6,wtt,wwe,wyS] (.node [wg6,wjz,wmE,wtt,wwe,wyS] .nil .nil) (.node [wg6,wjz,wtt,wwe,wyS] .nil .nil)) (.node [wg6,wjC,wmE,wtt,wwe,wyS] (.node [wg6,wjB,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wjF,wn8,wtt,wwe,wyS] (.node [wg6,wjC,wtt,wwe,wyS] (.node [wg6,wjC,wqt,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wjF,woH,wtt,wwe,wyS] (.node [wg6,wjF,woe,wp6,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wjG,wp6,wtt,wwe,wyS] (.node [wg6,wjF,wp6,wud,wwe,wyS] (.node [wg6,wjF,wp6,wtt,wwX,wyS] (.node [wg6,wjF,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wjF,wtt,wwe,wyS,wA8] (.node [wg6,wjF,wtt,wwe,wyS,wAu] .nil .nil) .nil)) (.node [wg6,wjJ,wmE,wtt,wwe,wyS] (.node [wg6,wjI,wmE,wtt,wwe,wyS] (.node [wg6,wjH,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wjK,wlI,wmE,wtt,wyS] (.node [wg6,wjK,wlg,wmE,wwe,wyS] .nil .nil) .nil)))) (.node [wg6,wjU,wmE,wtt,wwe,wyS] (.node [wg6,wjO,wp6,wtt,wwe,wyS] (.node [wg6,wjK,wtt,wwe,wyS,wAo] (.node [wg6,wjK,wmE,wuu,wwe,wyS] (.node [wg6,wjK,wmE,wtt,wxd,wyS] .nil .nil) .nil) (.node [wg6,wjM,wmE,wtt,wwe,wyS] (.node [wg6,wjL,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wjQ,wtt,wwe,wyr,wyS] (.node [wg6,wjQ,wp6,wtt,wwe,wyS] (.node [wg6,wjQ,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wjT,wmE,wtt,wwe,wyS] (.node [wg6,wjQ,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wjY,wp6,wtt,wwe,wz0] (.node [wg6,wjY,wkc,wtt,wwe,wyS] (.node [wg6,wjX,wp6,wtt,wwe,wyS] (.node [wg6,wjV,wmE,wp6,wtt,wwe] .nil .nil) .nil) (.node [wg6,wjY,wp6,wtt,wwe,wyS] (.node [wg6,wjY,wkn,wp6,wtt,wwe] .nil .nil) .nil)) (.node [wg6,wjY,wtt,wwe,wyS,wA8] (.node [wg6,wjY,wtt,wwe,wx3,wyS] (.node [wg6,wjY,wp6,wuC,wwe,wyS] .nil .nil) .nil) (.node [wg6,wjZ,wp6,wtt,wwe,wyS] (.node [wg6,wjZ,wmE,wtt,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlllrr_ok : everyKey (rowOK 4 level4) level5rlllrr = true := by decide +kernel
def level5rlllr : BinaryTree (List W) := .node [wg6,wjx,wmE,wtt,wwe,wyS] level5rlllrl level5rlllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlllr_ok : everyKey (rowOK 4 level4) level5rlllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlllrl && everyKey (rowOK 4 level4) level5rlllrr) = true
  rw [level5rlllrl_ok, level5rlllrr_ok]
  decide +kernel
def level5rlll : BinaryTree (List W) := .node [wg6,wjl,wtt,wtP,wwe,wyS] level5rllll level5rlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlll_ok : everyKey (rowOK 4 level4) level5rlll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rllll && everyKey (rowOK 4 level4) level5rlllr) = true
  rw [level5rllll_ok, level5rlllr_ok]
  decide +kernel
def level5rllrll : BinaryTree (List W) := (.node [wg6,wke,wmE,wtt,wwe,wyS] (.node [wg6,wj6,wp6,wtt,wwe,wyS] (.node [wg6,wj2,wp6,wtt,wwe,wzy] (.node [wg6,wj2,wpo,wtt,wwe,wyS] (.node [wg6,wj2,wn8,wtt,wwe,wyS] (.node [wg6,wjZ,wtt,wwe,wyS] .nil .nil) (.node [wg6,wj2,woj,wp6,wwe,wyS] .nil .nil)) (.node [wg6,wj2,wp6,wtt,wwe,wyS] (.node [wg6,wj2,wp6,wqK,wtt,wwe] .nil .nil) .nil)) (.node [wg6,wj2,wtt,wwe,wyS,wA8] (.node [wg6,wj2,wtt,wwe,wx5,wyS] (.node [wg6,wj2,wp6,wt9,wwe,wyS] .nil .nil) .nil) (.node [wg6,wj5,wp6,wtt,wwe,wyS] (.node [wg6,wj3,wp6,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wkc,wkn,wmE,wtt,wwe] (.node [wg6,wj9,wmE,wtt,wwe,wyS] (.node [wg6,wj8,wmE,wtt,wwe,wyS] (.node [wg6,wj7,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wkb,wmE,wtt,wwe,wyS] (.node [wg6,wka,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wkc,wmE,wuC,wwe,wyS] (.node [wg6,wkc,wmE,wtt,wwe,wz0] (.node [wg6,wkc,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wkd,wmE,wtt,wwe,wyS] (.node [wg6,wkc,wtt,wwe,wxR,wyS] .nil .nil) .nil)))) (.node [wg6,wkm,wmE,wp6,wtt,wwe] (.node [wg6,wkg,wmE,wtt,wwe,wyS] (.node [wg6,wkf,wmE,wtt,wwe,wzN] (.node [wg6,wkf,wmE,wm7,wtt,wwe] (.node [wg6,wkf,wll,wmE,wwe,wyS] .nil .nil) (.node [wg6,wkf,wmE,wtt,wwe,wyS] .nil .nil)) (.node [wg6,wkf,wtt,wwe,wxV,wyS] (.node [wg6,wkf,wmE,wuq,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wkj,wmE,wp6,wtt,wwe] (.node [wg6,wki,wmE,wtt,wwe,wyS] (.node [wg6,wkh,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wkl,wmE,wp6,wtt,wwe] (.node [wg6,wkk,wmE,wp6,wtt,wwe] .nil .nil) .nil))) (.node [wg6,wko,wmE,wtt,wwe,wyS] (.node [wg6,wkn,wmE,wtt,wwe,wx3] (.node [wg6,wkn,wmE,wp6,wuC,wwe] (.node [wg6,wkn,wmE,wp6,wtt,wwe] .nil .nil) .nil) (.node [wg6,wkn,wp6,wtt,wwe,wxR] (.node [wg6,wkn,wmE,wtt,wwe,wA8] .nil .nil) .nil)) (.node [wg6,wks,wkK,wtt,wwe,wyS] (.node [wg6,wkr,wp6,wtt,wwe,wyS] (.node [wg6,wkp,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wks,wk2,wp6,wtt,wwe] (.node [wg6,wks,wkX,wp6,wtt,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrll_ok : everyKey (rowOK 4 level4) level5rllrll = true := by decide +kernel
def level5rllrlr : BinaryTree (List W) := (.node [wg6,wkG,wmE,wtt,wwe,wyS] (.node [wg6,wkw,wp6,wtt,wwe,wyS] (.node [wg6,wkt,wq8,wtt,wwe,wyS] (.node [wg6,wks,wtt,wwe,wyS,wA8] (.node [wg6,wks,wp6,wtt,wxj,wyS] (.node [wg6,wks,wp6,wtt,wwe,wzT] .nil .nil) (.node [wg6,wks,wtt,wvw,wwe,wyS] .nil .nil)) (.node [wg6,wkt,wp6,wtt,wwe,wyS] (.node [wg6,wkt,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wkw,wpo,wtt,wwe,wyS] (.node [wg6,wkw,woH,wtt,wwe,wyS] (.node [wg6,wkt,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wkw,wp6,wq4,wtt,wwe] (.node [wg6,wkw,wp6,wqY,wtt,wyS] .nil .nil) .nil))) (.node [wg6,wkz,wp6,wtt,wwe,wyS] (.node [wg6,wkw,wtt,wvy,wwe,wyS] (.node [wg6,wkw,wp6,wtt,wwT,wyS] (.node [wg6,wkw,wp6,wtt,wwe,wzv] .nil .nil) .nil) (.node [wg6,wkx,wp6,wtt,wwe,wyS] (.node [wg6,wkw,wtt,wwe,wyS,wA8] .nil .nil) .nil)) (.node [wg6,wkD,wp6,wtt,wwe,wyS] (.node [wg6,wkC,wp6,wtt,wwe,wyS] (.node [wg6,wkA,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wkF,wmE,wtt,wwe,wyS] (.node [wg6,wkE,wmE,wtt,wwe,wyS] .nil .nil) .nil)))) (.node [wg6,wkM,wmE,wnp,wtt,wwe] (.node [wg6,wkK,wmE,wtt,wwe,wyS] (.node [wg6,wkJ,wmE,wtt,wwe,wyS] (.node [wg6,wkI,wmE,wtt,wwe,wyS] (.node [wg6,wkH,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wkK,wk2,wmE,wtt,wwe] (.node [wg6,wkK,wkX,wmE,wtt,wyS] .nil .nil) .nil)) (.node [wg6,wkK,wtt,wvg,wwe,wyS] (.node [wg6,wkK,wmE,wtt,wxj,wyS] (.node [wg6,wkK,wmE,wtt,wwe,wzT] .nil .nil) .nil) (.node [wg6,wkM,wmE,wni,wtt,wyS] (.node [wg6,wkL,wmE,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wkO,wmE,wtt,wwe,wyS] (.node [wg6,wkM,wmE,wtt,ww9,wyS] (.node [wg6,wkM,wmE,wtt,wwe,wzK] (.node [wg6,wkM,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wkN,wmE,wtt,wwe,wyS] (.node [wg6,wkM,wtt,wvk,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wkR,wmE,wtt,wwe,wyS] (.node [wg6,wkQ,wmE,wtt,wwe,wyS] (.node [wg6,wkP,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wkT,wmE,wp6,wtt,wwe] (.node [wg6,wkS,wmE,wp6,wtt,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrlr_ok : everyKey (rowOK 4 level4) level5rllrlr = true := by decide +kernel
def level5rllrl : BinaryTree (List W) := .node [wg6,wks,wp6,wtt,wwe,wyS] level5rllrll level5rllrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrl_ok : everyKey (rowOK 4 level4) level5rllrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rllrll && everyKey (rowOK 4 level4) level5rllrlr) = true
  rw [level5rllrll_ok, level5rllrlr_ok]
  decide +kernel
def level5rllrrl : BinaryTree (List W) := (.node [wg6,wla,wmE,wp6,wwe,wzK] (.node [wg6,wk2,wmE,wp6,wtt,wwe] (.node [wg6,wkX,wmE,wtt,wyS,wA8] (.node [wg6,wkX,wmE,wp6,wtt,wyS] (.node [wg6,wkW,wmE,wp6,wtt,wyS] (.node [wg6,wkV,wmE,wp6,wtt,wyS] .nil .nil) (.node [wg6,wkX,wk2,wmE,wp6,wtt] .nil .nil)) (.node [wg6,wkX,wmE,wtt,wvw,wyS] (.node [wg6,wkX,wmE,wp6,wtt,wzT] .nil .nil) .nil)) (.node [wg6,wkZ,wmE,wp6,wtt,wwe] (.node [wg6,wkY,wmE,wp6,wtt,wyS] (.node [wg6,wkX,wp6,wtt,wvg,wyS] .nil .nil) .nil) (.node [wg6,wk1,wmE,wp6,wtt,wwe] (.node [wg6,wk0,wmE,wp6,wtt,wwe] .nil .nil) .nil))) (.node [wg6,wk4,wmE,wtt,wwe,wyS] (.node [wg6,wk2,wmE,wtt,wwe,wA8] (.node [wg6,wk2,wmE,wtt,wvw,wwe] (.node [wg6,wk2,wmE,wp6,wtt,wxj] .nil .nil) .nil) (.node [wg6,wk3,wmE,wtt,wwe,wyS] (.node [wg6,wk2,wp6,wtt,wvg,wwe] .nil .nil) .nil)) (.node [wg6,wk8,wmE,wp6,wwe,wAH] (.node [wg6,wk7,wmE,wp6,wyr,wyS] (.node [wg6,wk5,wmE,wp6,wtt,wwe] .nil .nil) .nil) (.node [wg6,wla,wmr,wtt,wwe,wyS] (.node [wg6,wk9,wmr,wtt,wwe,wyS] .nil .nil) .nil)))) (.node [wg6,wlg,wlI,wmE,wp6,wyS] (.node [wg6,wla,woB,wvk,wwe,wyS] (.node [wg6,wla,wmE,wp6,wxj,wyS] (.node [wg6,wla,wmE,wp6,ww9,wyS] (.node [wg6,wla,wmE,wp6,wwe,wzT] .nil .nil) .nil) (.node [wg6,wla,wm4,wp6,wwe,wyS] (.node [wg6,wla,wmT,wp6,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wla,wvk,wwe,wyS,wA8] (.node [wg6,wla,wp6,wvk,wwe,wyS] (.node [wg6,wla,wp6,wvg,wwe,wyS] .nil .nil) .nil) (.node [wg6,wlf,wmE,wp6,wwe,wyS] (.node [wg6,wlc,wmE,wp6,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wlk,wmE,wp6,wwe,wyS] (.node [wg6,wlg,wmE,wrY,wwe,wyS] (.node [wg6,wlg,wmE,wp6,wxd,wyS] (.node [wg6,wlg,wmE,wp6,wwe,wyS] .nil .nil) .nil) (.node [wg6,wlh,wmE,wp6,wwe,wyS] (.node [wg6,wlg,wmE,wwe,wyS,wA8] .nil .nil) .nil)) (.node [wg6,wll,wmE,wp6,wwe,wzN] (.node [wg6,wll,wmE,wp6,wwe,wyS] (.node [wg6,wll,wmE,wm7,wp6,wwe] .nil .nil) .nil) (.node [wg6,wll,wmE,wwe,wyS,wA8] (.node [wg6,wll,wmE,wrG,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrrl_ok : everyKey (rowOK 4 level4) level5rllrrl = true := by decide +kernel
def level5rllrrr : BinaryTree (List W) := (.node [wg6,wlI,wmE,wp6,wtt,wyS] (.node [wg6,wlC,wmE,wp6,wtt,wzN] (.node [wg6,wlw,wp6,wtt,wwe,wyS] (.node [wg6,wlq,wmE,wp6,wwe,wyS] (.node [wg6,wlo,wp6,wvk,wwe,wyS] (.node [wg6,wln,wmE,wp6,wwe,wyS] .nil .nil) (.node [wg6,wlp,wp6,wvk,wwe,wyS] .nil .nil)) (.node [wg6,wlt,wmE,wtt,wwe,wyS] (.node [wg6,wls,wp6,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wlA,wmE,wp6,wtt,wAR] (.node [wg6,wlz,wp6,wtt,wwe,wyS] (.node [wg6,wlx,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wlC,wmr,wtt,wwe,wyS] (.node [wg6,wlB,wmr,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wlC,wo3,wtt,wxV,wyS] (.node [wg6,wlC,wmE,wp6,wuC,wyS] (.node [wg6,wlC,wmE,wp6,wuq,wyS] (.node [wg6,wlC,wmE,wp6,wtt,wz0] .nil .nil) .nil) (.node [wg6,wlC,wnm,wp6,wtt,wyS] (.node [wg6,wlC,wmV,wp6,wtt,wyS] .nil .nil) .nil)) (.node [wg6,wlC,wtt,wxV,wyS,wA8] (.node [wg6,wlC,wp6,wtt,wxV,wyS] (.node [wg6,wlC,wp6,wtt,wxR,wyS] .nil .nil) .nil) (.node [wg6,wlH,wmE,wp6,wtt,wyS] (.node [wg6,wlF,wmE,wp6,wtt,wyS] .nil .nil) .nil)))) (.node [wg6,wlW,wp6,wtt,wwe,wyS] (.node [wg6,wlM,wp6,wtt,wxV,wyS] (.node [wg6,wlI,wmE,wtt,wyS,wA8] (.node [wg6,wlI,wmE,wrY,wtt,wyS] (.node [wg6,wlI,wmE,wp6,wuu,wyS] .nil .nil) .nil) (.node [wg6,wlL,wp6,wtt,wxV,wyS] (.node [wg6,wlJ,wmE,wp6,wtt,wyS] .nil .nil) .nil)) (.node [wg6,wlQ,wmE,wtt,wwe,wyS] (.node [wg6,wlP,wp6,wtt,wwe,wyS] (.node [wg6,wlN,wmE,wp6,wtt,wyS] .nil .nil) .nil) (.node [wg6,wlU,wp6,wtt,wwe,wyS] (.node [wg6,wlT,wp6,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wl2,wmE,wp6,wtt,wxs] (.node [wg6,wl1,wmr,wtt,wwe,wyS] (.node [wg6,wl0,wp6,wtt,wwe,wyS] (.node [wg6,wlY,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wl2,wmE,wp6,wtt,wxd] (.node [wg6,wl2,wmr,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wl2,wna,wp6,wtt,wwe] (.node [wg6,wl2,wmE,wp6,wuL,wwe] (.node [wg6,wl2,wmE,wp6,wuu,wwe] .nil .nil) .nil) (.node [wg6,wl2,wpC,wtt,wwe,wAo] (.node [wg6,wl2,wns,wp6,wtt,wwe] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrrr_ok : everyKey (rowOK 4 level4) level5rllrrr = true := by decide +kernel
def level5rllrr : BinaryTree (List W) := .node [wg6,wlm,wmE,wp6,wwe,wyS] level5rllrrl level5rllrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrr_ok : everyKey (rowOK 4 level4) level5rllrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rllrrl && everyKey (rowOK 4 level4) level5rllrrr) = true
  rw [level5rllrrl_ok, level5rllrrr_ok]
  decide +kernel
def level5rllr : BinaryTree (List W) := .node [wg6,wkU,wmE,wp6,wtt,wyS] level5rllrl level5rllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllr_ok : everyKey (rowOK 4 level4) level5rllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rllrl && everyKey (rowOK 4 level4) level5rllrr) = true
  rw [level5rllrl_ok, level5rllrr_ok]
  decide +kernel
def level5rll : BinaryTree (List W) := .node [wg6,wjZ,wqO,wtt,wwe,wyS] level5rlll level5rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rll_ok : everyKey (rowOK 4 level4) level5rll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlll && everyKey (rowOK 4 level4) level5rllr) = true
  rw [level5rlll_ok, level5rllr_ok]
  decide +kernel
def level5rlrlll : BinaryTree (List W) := (.node [wg6,wmr,wp6,wtt,wwe,wyI] (.node [wg6,wmm,wp6,wtt,wwe,wyS] (.node [wg6,wmb,wmE,wtt,wwe,wyS] (.node [wg6,wl7,wp6,wtt,wwe,wAo] (.node [wg6,wl2,wtt,wwe,wAo,wA8] (.node [wg6,wl2,wp6,wtt,wwe,wAo] .nil .nil) (.node [wg6,wl6,wp6,wtt,wwe,wAo] .nil .nil)) (.node [wg6,wma,wp6,wtt,wwe,wyS] (.node [wg6,wl8,wmE,wp6,wtt,wwe] .nil .nil) .nil)) (.node [wg6,wmh,wp6,wtt,wwe,wyS] (.node [wg6,wmf,wp6,wtt,wwe,wyS] (.node [wg6,wme,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmk,wp6,wtt,wwe,wyS] (.node [wg6,wmj,wp6,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wmr,wmE,wtt,wwe,wyS] (.node [wg6,wmr,wmE,wtj,wwe,wyS] (.node [wg6,wmr,wmr,wtt,wwe,wyS] (.node [wg6,wmn,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmr,wmE,wtt,wwe,wyI] (.node [wg6,wmr,wmE,wtt,wv4,wyS] .nil .nil) .nil)) (.node [wg6,wmr,wpo,wtt,wwe,wyS] (.node [wg6,wmr,woH,wtt,wwe,wyS] (.node [wg6,wmr,wn8,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmr,wp6,wtt,wv4,wyS] (.node [wg6,wmr,wp6,wtj,wwe,wyS] .nil .nil) .nil)))) (.node [wg6,wmr,wtt,wvJ,wwe,wyS] (.node [wg6,wmr,wtj,wwe,wyS] (.node [wg6,wmr,wsK,wtt,wwe,wyS] (.node [wg6,wmr,wsB,wtt,wwe,wyS] (.node [wg6,wmr,wp6,wtt,wwe,wyS] .nil .nil) (.node [wg6,wmr,wsC,wtt,wwe,wyS] .nil .nil)) (.node [wg6,wmr,wtj,wtt,wwe,wyS] (.node [wg6,wmr,wsY,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmr,wtt,wvj,wwe,wyS] (.node [wg6,wmr,wtt,wuS,wwe,wyS] (.node [wg6,wmr,wtj,wwe,wyS,wA8] .nil .nil) .nil) (.node [wg6,wmr,wtt,wvy,wwe,wyS] (.node [wg6,wmr,wtt,wvk,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wmr,wtt,wwe,wxV,wyS] (.node [wg6,wmr,wtt,wv4,wyS,wA8] (.node [wg6,wmr,wtt,wv4,wyS] (.node [wg6,wmr,wtt,wv4,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmr,wtt,wwe,wxU,wyS] (.node [wg6,wmr,wtt,wwe,wxz,wyS] .nil .nil) .nil)) (.node [wg6,wmr,wtt,wwe,wyI] (.node [wg6,wmr,wtt,wwe,wyr,wyS] (.node [wg6,wmr,wtt,wwe,wx5,wyS] .nil .nil) .nil) (.node [wg6,wmr,wtt,wwe,wyI,wA8] (.node [wg6,wmr,wtt,wwe,wyI,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrlll_ok : everyKey (rowOK 4 level4) level5rlrlll = true := by decide +kernel
def level5rlrllr : BinaryTree (List W) := (.node [wg6,wmB,wp6,wtt,wwe,wyS] (.node [wg6,wmr,wtt,wwe,wyS,wBj] (.node [wg6,wmr,wtt,wwe,wyS,wAX] (.node [wg6,wmr,wtt,wwe,wyS,wAu] (.node [wg6,wmr,wtt,wwe,wyS,wAn] (.node [wg6,wmr,wtt,wwe,wyS,wz7] .nil .nil) (.node [wg6,wmr,wtt,wwe,wyS,wAo] .nil .nil)) (.node [wg6,wmr,wtt,wwe,wyS,wAR] (.node [wg6,wmr,wtt,wwe,wyS,wAH] .nil .nil) .nil)) (.node [wg6,wmr,wtt,wwe,wyS,wBc] (.node [wg6,wmr,wtt,wwe,wyS,wA8] (.node [wg6,wmr,wtt,wwe,wyS,wA1] .nil .nil) .nil) (.node [wg6,wmr,wtt,wwe,wyS,wBg] (.node [wg6,wmr,wtt,wwe,wyS,wBe] .nil .nil) .nil))) (.node [wg6,wmx,wtt,wwe,wyS,wA8] (.node [wg6,wmw,wp6,wtt,wwe,wyS] (.node [wg6,wmu,wtt,wwe,wyS,wA8] (.node [wg6,wmu,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmx,wp6,wtt,wwe,wyS] (.node [wg6,wmw,wtt,wwe,wyS,wA8] .nil .nil) .nil)) (.node [wg6,wmz,wp6,wtt,wwe,wyS] (.node [wg6,wmy,wtt,wwe,wyS,wA8] (.node [wg6,wmy,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmA,wp6,wtt,wwe,wyS] (.node [wg6,wmz,wtt,wwe,wyS,wA8] .nil .nil) .nil)))) (.node [wg6,wmE,wm8,wp6,wtt,wwe] (.node [wg6,wmE,wmY,wp6,wtt,wwe] (.node [wg6,wmD,wp6,wtt,wwe,wyS] (.node [wg6,wmC,wp6,wtt,wwe,wyS] (.node [wg6,wmB,wtt,wwe,wyS,wA8] .nil .nil) .nil) (.node [wg6,wmE,wmW,wtt,wwe,wyS] (.node [wg6,wmE,wmI,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wm7,wp6,wuq,wwe] (.node [wg6,wmE,wm7,wp6,wtt,wwe] (.node [wg6,wmE,wm6,wp6,wtt,wwe] .nil .nil) .nil) (.node [wg6,wmE,wm7,wtt,wwe,wA8] (.node [wg6,wmE,wm7,wrG,wtt,wwe] .nil .nil) .nil))) (.node [wg6,wmE,wni,wrs,wtt,wyS] (.node [wg6,wmE,wni,wnp,wp6,wtt] (.node [wg6,wmE,wnh,wp6,wtt,wyS] (.node [wg6,wmE,wnb,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wni,wp6,wtt,wzK] (.node [wg6,wmE,wni,wp6,wtt,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wnk,wp6,wtt,wyS] (.node [wg6,wmE,wnj,wp6,wtt,wyS] (.node [wg6,wmE,wni,wtt,wyS,wA8] .nil .nil) .nil) (.node [wg6,wmE,wnp,wp6,wtt,wwe] (.node [wg6,wmE,wno,wp6,wtt,wwe] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrllr_ok : everyKey (rowOK 4 level4) level5rlrllr = true := by decide +kernel
def level5rlrll : BinaryTree (List W) := .node [wg6,wmr,wtt,wwe,wyS] level5rlrlll level5rlrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrll_ok : everyKey (rowOK 4 level4) level5rlrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrlll && everyKey (rowOK 4 level4) level5rlrllr) = true
  rw [level5rlrlll_ok, level5rlrllr_ok]
  decide +kernel
def level5rlrlrl : BinaryTree (List W) := (.node [wg6,wmE,wn8,wp6,wwe,wzv] (.node [wg6,wmE,wnY,wtt,wwe,wyS] (.node [wg6,wmE,wnz,wp6,wwe,wyS] (.node [wg6,wmE,wnt,wtt,wwe,wyS] (.node [wg6,wmE,wnp,wtt,wwe,wA8] (.node [wg6,wmE,wnp,wrs,wtt,wwe] .nil .nil) (.node [wg6,wmE,wnq,wp6,wtt,wwe] .nil .nil)) (.node [wg6,wmE,wny,wp6,wwe,wyS] (.node [wg6,wmE,wnv,wp6,wtt,wwe] .nil .nil) .nil)) (.node [wg6,wmE,wnJ,wp6,wtt,wyS] (.node [wg6,wmE,wnB,wp6,wwe,wyS] (.node [wg6,wmE,wnA,wp6,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wnQ,wtt,wwe,wyS] (.node [wg6,wmE,wnK,wp6,wtt,wyS] .nil .nil) .nil))) (.node [wg6,wmE,wn5,wp6,wtt,wwe] (.node [wg6,wmE,wn2,wp6,wtt,wyS] (.node [wg6,wmE,wn1,wp6,wtt,wwe] (.node [wg6,wmE,wn0,wp6,wtt,wwe] .nil .nil) .nil) (.node [wg6,wmE,wn4,wp6,wtt,wwe] (.node [wg6,wmE,wn3,wp6,wtt,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wn8,woH,wyr,wyS] (.node [wg6,wmE,wn7,wp6,wwe,wAH] (.node [wg6,wmE,wn6,wp6,wyr,wyS] .nil .nil) .nil) (.node [wg6,wmE,wn8,wpo,wwe,wAH] (.node [wg6,wmE,wn8,woN,wtt,wyS] .nil .nil) .nil)))) (.node [wg6,wmE,wn8,wrT,wtt,wwe] (.node [wg6,wmE,wn8,wqq,wwe,wyS] (.node [wg6,wmE,wn8,wp6,wwT,wyS] (.node [wg6,wmE,wn8,wp6,wwe,wzT] (.node [wg6,wmE,wn8,wp6,wwe,wzK] .nil .nil) .nil) (.node [wg6,wmE,wn8,wp6,wxj,wyS] (.node [wg6,wmE,wn8,wp6,ww9,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wn8,wq8,wwe,wyS] (.node [wg6,wmE,wn8,wqK,wtt,wwe] (.node [wg6,wmE,wn8,wqI,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wn8,wrx,wtt,wyS] (.node [wg6,wmE,wn8,wrs,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wmE,wn8,wuY,wwe,wyS] (.node [wg6,wmE,wn8,wt2,wwe,wyS] (.node [wg6,wmE,wn8,wtt,wwe,wyI] (.node [wg6,wmE,wn8,wtt,wv4,wyS] .nil .nil) .nil) (.node [wg6,wmE,wn8,wud,wwe,wyS] (.node [wg6,wmE,wn8,wt9,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wn8,wvv,wwe,wyS] (.node [wg6,wmE,wn8,wvr,wwe,wyS] (.node [wg6,wmE,wn8,wu3,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wn8,wvy,wwe,wyS] (.node [wg6,wmE,wn8,wvw,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrlrl_ok : everyKey (rowOK 4 level4) level5rlrlrl = true := by decide +kernel
def level5rlrlrr : BinaryTree (List W) := (.node [wg6,wmE,wot,wtt,wwe,wyS] (.node [wg6,wmE,woj,wpo,wwe,wyS] (.node [wg6,wmE,woe,wp6,wwX,wyS] (.node [wg6,wmE,woe,woH,wwe,wyS] (.node [wg6,wmE,wod,wp6,wwe,wyS] (.node [wg6,wmE,woc,wp6,wwe,wyS] .nil .nil) (.node [wg6,wmE,wod,wqt,wwe,wyS] .nil .nil)) (.node [wg6,wmE,woe,wp6,wwe,wyS] (.node [wg6,wmE,woe,woN,wp6,wyS] .nil .nil) .nil)) (.node [wg6,wmE,woh,wp6,wwe,wyS] (.node [wg6,wmE,wof,wp6,wwe,wyS] (.node [wg6,wmE,woe,wwe,wyS,wA8] .nil .nil) .nil) (.node [wg6,wmE,woi,wqO,wwe,wyS] (.node [wg6,wmE,woi,wp6,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wmE,wol,wp6,wwe,wyS] (.node [wg6,wmE,woj,wp6,wwe,wzy] (.node [wg6,wmE,woj,wp6,wwe,wyS] (.node [wg6,wmE,woj,wp6,wqK,wwe] .nil .nil) .nil) (.node [wg6,wmE,wok,wp6,wwe,wyS] (.node [wg6,wmE,woj,wwe,wyS,wA8] .nil .nil) .nil)) (.node [wg6,wmE,woq,wtt,wwe,wyS] (.node [wg6,wmE,wop,wtt,wwe,wyS] (.node [wg6,wmE,woo,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wos,wtt,wwe,wyS] (.node [wg6,wmE,wor,wtt,wwe,wyS] .nil .nil) .nil)))) (.node [wg6,wmE,woF,wtt,wwe,wyS] (.node [wg6,wmE,woz,wtt,wwe,wyS] (.node [wg6,wmE,wow,wtt,wwe,wyS] (.node [wg6,wmE,wov,wtt,wwe,wyS] (.node [wg6,wmE,wou,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,woy,wtt,wwe,wyS] (.node [wg6,wmE,wox,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmE,woC,wtt,wwe,wyS] (.node [wg6,wmE,woB,wtt,wwe,wyS] (.node [wg6,wmE,woA,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,woE,wtt,wwe,wyS] (.node [wg6,wmE,woD,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wmE,woH,wp6,wt9,wyS] (.node [wg6,wmE,woH,wp6,wtt,wzy] (.node [wg6,wmE,woH,wpo,wtt,wAR] (.node [wg6,wmE,woG,wp6,wtt,wAR] .nil .nil) .nil) (.node [wg6,wmE,woH,wp6,wtt,wz0] (.node [wg6,wmE,woH,wp6,wtt,wzN] .nil .nil) .nil)) (.node [wg6,wmE,woH,wqs,wtt,wyS] (.node [wg6,wmE,woH,wp6,wuC,wyS] (.node [wg6,wmE,woH,wp6,wuq,wyS] .nil .nil) .nil) (.node [wg6,wmE,woH,wq2,wtt,wyS] (.node [wg6,wmE,woH,wqO,wtt,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrlrr_ok : everyKey (rowOK 4 level4) level5rlrlrr = true := by decide +kernel
def level5rlrlr : BinaryTree (List W) := .node [wg6,wmE,woa,wp6,wwe,wyS] level5rlrlrl level5rlrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrlr_ok : everyKey (rowOK 4 level4) level5rlrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrlrl && everyKey (rowOK 4 level4) level5rlrlrr) = true
  rw [level5rlrlrl_ok, level5rlrlrr_ok]
  decide +kernel
def level5rlrl : BinaryTree (List W) := .node [wg6,wmE,wnp,wp6,wtt,ww9] level5rlrll level5rlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrl_ok : everyKey (rowOK 4 level4) level5rlrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrll && everyKey (rowOK 4 level4) level5rlrlr) = true
  rw [level5rlrll_ok, level5rlrlr_ok]
  decide +kernel
def level5rlrrll : BinaryTree (List W) := (.node [wg6,wmE,woU,wtt,wwe,wyS] (.node [wg6,wmE,woH,wtt,wx3,wyS] (.node [wg6,wmE,woH,wtt,wwT,wyS] (.node [wg6,wmE,woH,wtj,wwe,wyS] (.node [wg6,wmE,woH,wrG,wtt,wyS] (.node [wg6,wmE,woH,wrg,wwe,wyS] .nil .nil) (.node [wg6,wmE,woH,wrT,wtt,wwe] .nil .nil)) (.node [wg6,wmE,woH,wtt,wwN,wyS] (.node [wg6,wmE,woH,wtt,wwe,wyI] .nil .nil) .nil)) (.node [wg6,wmE,woH,wtt,wxI,wyS] (.node [wg6,wmE,woH,wtt,wxD,wyS] (.node [wg6,wmE,woH,wtt,wwX,wyS] .nil .nil) .nil) (.node [wg6,wmE,woH,wtt,wx2,wyS] (.node [wg6,wmE,woH,wtt,wxY,wyS] .nil .nil) .nil))) (.node [wg6,wmE,woN,wp6,wtt,wyS] (.node [wg6,wmE,woL,wp6,wtt,wyS] (.node [wg6,wmE,woK,wp6,wtt,wyS] (.node [wg6,wmE,woH,wtt,wx5,wyS] .nil .nil) .nil) (.node [wg6,wmE,woM,wqt,wtt,wyS] (.node [wg6,wmE,woM,wp6,wtt,wyS] .nil .nil) .nil)) (.node [wg6,wmE,woO,wp6,wtt,wyS] (.node [wg6,wmE,woN,wtt,wyS,wA8] (.node [wg6,wmE,woN,wp6,wud,wyS] .nil .nil) .nil) (.node [wg6,wmE,woT,wtt,wwe,wyS] (.node [wg6,wmE,woS,wtt,wwe,wyS] .nil .nil) .nil)))) (.node [wg6,wmE,wo6,wtt,wwe,wyS] (.node [wg6,wmE,wo0,wtt,wwe,wyS] (.node [wg6,wmE,woX,wtt,wwe,wyS] (.node [wg6,wmE,woW,wtt,wwe,wyS] (.node [wg6,wmE,woV,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,woZ,wtt,wwe,wyS] (.node [wg6,wmE,woY,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wo3,wtt,wwe,wyS] (.node [wg6,wmE,wo2,wtt,wwe,wyS] (.node [wg6,wmE,wo1,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wo5,wtt,wwe,wyS] (.node [wg6,wmE,wo4,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wmE,wpb,wsK,wyr,wyS] (.node [wg6,wmE,wo8,wwe,wyh,wyS] (.node [wg6,wmE,wo8,wtt,wwe,wyS] (.node [wg6,wmE,wo7,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wpa,wtt,wyl,wyS] (.node [wg6,wmE,wpa,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wpb,wwe,wyS,wAH] (.node [wg6,wmE,wpb,wtt,wyS,wAR] (.node [wg6,wmE,wpb,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wpd,wtt,wwe,wyS] (.node [wg6,wmE,wpc,wtt,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrll_ok : everyKey (rowOK 4 level4) level5rlrrll = true := by decide +kernel
def level5rlrrlr : BinaryTree (List W) := (.node [wg6,wmE,wpo,wrY,wtt,wwe] (.node [wg6,wmE,wpo,wp6,wtt,wwX] (.node [wg6,wmE,wpi,wt4,wwe,wyS] (.node [wg6,wmE,wpi,wtt,wwe,wyS] (.node [wg6,wmE,wpi,wrv,wtt,wyS] (.node [wg6,wmE,wpi,wre,wwe,wyS] .nil .nil) (.node [wg6,wmE,wpi,wrM,wtt,wwe] .nil .nil)) (.node [wg6,wmE,wpi,wtt,wwP,wyS] (.node [wg6,wmE,wpi,wtt,wwe,wzr] .nil .nil) .nil)) (.node [wg6,wmE,wpl,wtt,wwe,wyS] (.node [wg6,wmE,wpk,wtt,wwe,wyS] (.node [wg6,wmE,wpj,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wpn,wtt,wwe,wyS] (.node [wg6,wmE,wpm,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wmE,wpo,wqt,wtt,wwe] (.node [wg6,wmE,wpo,wp6,wud,wwe] (.node [wg6,wmE,wpo,wp6,wtt,wxs] (.node [wg6,wmE,wpo,wp6,wtt,wxd] .nil .nil) .nil) (.node [wg6,wmE,wpo,wp6,wuL,wwe] (.node [wg6,wmE,wpo,wp6,wuu,wwe] .nil .nil) .nil)) (.node [wg6,wmE,wpo,wq7,wtt,wwe] (.node [wg6,wmE,wpo,wqY,wtt,wyS] (.node [wg6,wmE,wpo,wqN,wtt,wwe] .nil .nil) .nil) (.node [wg6,wmE,wpo,wrx,wtt,wyS] (.node [wg6,wmE,wpo,wrg,wwe,wyS] .nil .nil) .nil)))) (.node [wg6,wmE,wpu,wtt,wwe,wyS] (.node [wg6,wmE,wpo,wtt,wwe,wAa] (.node [wg6,wmE,wpo,wtt,wwe,wzp] (.node [wg6,wmE,wpo,wtt,wv4,wyS] (.node [wg6,wmE,wpo,wtj,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wpo,wtt,wwe,wzy] (.node [wg6,wmE,wpo,wtt,wwe,wzv] .nil .nil) .nil)) (.node [wg6,wmE,wpo,wtt,wwe,wAr] (.node [wg6,wmE,wpo,wtt,wwe,wAq] (.node [wg6,wmE,wpo,wtt,wwe,wAf] .nil .nil) .nil) (.node [wg6,wmE,wpo,wtt,wwe,wAu] (.node [wg6,wmE,wpo,wtt,wwe,wAs] .nil .nil) .nil))) (.node [wg6,wmE,wpA,wtt,wwe,wyS] (.node [wg6,wmE,wpx,wtt,wwe,wyS] (.node [wg6,wmE,wpw,wtt,wwe,wyS] (.node [wg6,wmE,wpv,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wpz,wtt,wwe,wyS] (.node [wg6,wmE,wpy,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wpD,wtt,wwe,wyS] (.node [wg6,wmE,wpC,wtt,wwe,wyS] (.node [wg6,wmE,wpB,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wpF,wtt,wwe,wyS] (.node [wg6,wmE,wpE,wtt,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrlr_ok : everyKey (rowOK 4 level4) level5rlrrlr = true := by decide +kernel
def level5rlrrl : BinaryTree (List W) := .node [wg6,wmE,wpg,wtt,wwe,wyS] level5rlrrll level5rlrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrl_ok : everyKey (rowOK 4 level4) level5rlrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrrll && everyKey (rowOK 4 level4) level5rlrrlr) = true
  rw [level5rlrrll_ok, level5rlrrlr_ok]
  decide +kernel
def level5rlrrrl : BinaryTree (List W) := (.node [wg6,wmE,wpW,wtt,wwe,wyE] (.node [wg6,wmE,wpP,wtt,wvJ,wAR] (.node [wg6,wmE,wpJ,wtt,wwe,wyS] (.node [wg6,wmE,wpI,wtt,wwe,wyS] (.node [wg6,wmE,wpH,wtt,wwe,wAB] (.node [wg6,wmE,wpH,wtt,wwe,wyS] .nil .nil) (.node [wg6,wmE,wpI,wsY,wwe,wAH] .nil .nil)) (.node [wg6,wmE,wpI,wwe,wyr,wyS] (.node [wg6,wmE,wpI,wtt,wwe,wAR] .nil .nil) .nil)) (.node [wg6,wmE,wpM,wtt,wwe,wyS] (.node [wg6,wmE,wpL,wtt,wwe,wyS] (.node [wg6,wmE,wpK,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wpO,wtt,wwe,wyS] (.node [wg6,wmE,wpN,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wmE,wpS,wtt,wwe,wyS] (.node [wg6,wmE,wpP,wtt,wyr,wyS] (.node [wg6,wmE,wpP,wtt,wwe,wAH] (.node [wg6,wmE,wpP,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wpR,wtt,wwe,wyS] (.node [wg6,wmE,wpQ,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wpV,wtt,wwe,wyS] (.node [wg6,wmE,wpU,wtt,wwe,wyS] (.node [wg6,wmE,wpT,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wpW,wtt,wv0,wyS] (.node [wg6,wmE,wpW,wtf,wwe,wyS] .nil .nil) .nil)))) (.node [wg6,wmE,wp6,wqC,wtt,wwe] (.node [wg6,wmE,wp1,wtt,wwe,wyS] (.node [wg6,wmE,wpY,wtt,wwe,wyS] (.node [wg6,wmE,wpX,wtt,wwe,wyS] (.node [wg6,wmE,wpW,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp0,wtt,wwe,wyS] (.node [wg6,wmE,wpZ,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wp4,wtt,wwe,wyS] (.node [wg6,wmE,wp3,wtt,wwe,wyS] (.node [wg6,wmE,wp2,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wqv,wtt,wwe] (.node [wg6,wmE,wp5,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wmE,wp6,wqS,wtt,wwe] (.node [wg6,wmE,wp6,wqK,wt9,wwe] (.node [wg6,wmE,wp6,wqK,wtt,wwe] (.node [wg6,wmE,wp6,wqJ,wtt,wwe] .nil .nil) .nil) (.node [wg6,wmE,wp6,wqQ,wtt,wyS] (.node [wg6,wmE,wp6,wqL,wtt,wwe] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wqY,wtt,wyS] (.node [wg6,wmE,wp6,wqY,wq4,wtt] (.node [wg6,wmE,wp6,wqX,wtt,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wqZ,wtt,wyS] (.node [wg6,wmE,wp6,wqY,wtt,wzv] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrrl_ok : everyKey (rowOK 4 level4) level5rlrrrl = true := by decide +kernel
def level5rlrrrr : BinaryTree (List W) := (.node [wg6,wmE,wp6,wrv,wtt,wyS] (.node [wg6,wmE,wp6,wrg,wrx,wyS] (.node [wg6,wmE,wp6,wre,wrv,wyS] (.node [wg6,wmE,wp6,wq5,wtt,wwe] (.node [wg6,wmE,wp6,wq4,wtt,wwe] (.node [wg6,wmE,wp6,wq3,wtt,wwe] .nil .nil) (.node [wg6,wmE,wp6,wq4,wtt,wwT] .nil .nil)) (.node [wg6,wmE,wp6,wrd,wwe,wyS] (.node [wg6,wmE,wp6,wra,wtt,wwe] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wre,wwe,wzr] (.node [wg6,wmE,wp6,wre,wwe,wyS] (.node [wg6,wmE,wp6,wre,wrM,wwe] .nil .nil) .nil) (.node [wg6,wmE,wp6,wrf,wwe,wyS] (.node [wg6,wmE,wp6,wre,wwP,wyS] .nil .nil) .nil))) (.node [wg6,wmE,wp6,wri,wwe,wyS] (.node [wg6,wmE,wp6,wrg,wwe,wzp] (.node [wg6,wmE,wp6,wrg,wwe,wyS] (.node [wg6,wmE,wp6,wrg,wrT,wwe] .nil .nil) .nil) (.node [wg6,wmE,wp6,wrh,wwe,wyS] (.node [wg6,wmE,wp6,wrg,wwN,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wrl,wwe,wyS] (.node [wg6,wmE,wp6,wrk,wwe,wyS] (.node [wg6,wmE,wp6,wrj,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wrv,wrM,wtt] (.node [wg6,wmE,wp6,wru,wtt,wyS] .nil .nil) .nil)))) (.node [wg6,wmE,wp6,wrM,wtt,wwe] (.node [wg6,wmE,wp6,wrx,wtt,wzp] (.node [wg6,wmE,wp6,wrw,wtt,wyS] (.node [wg6,wmE,wp6,wrv,wt4,wyS] (.node [wg6,wmE,wp6,wrv,wtt,wzr] .nil .nil) .nil) (.node [wg6,wmE,wp6,wrx,wtt,wyS] (.node [wg6,wmE,wp6,wrx,wrT,wtt] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wrz,wtt,wyS] (.node [wg6,wmE,wp6,wry,wtt,wyS] (.node [wg6,wmE,wp6,wrx,wt2,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wrL,wtt,wwe] (.node [wg6,wmE,wp6,wrA,wtt,wyS] .nil .nil) .nil))) (.node [wg6,wmE,wp6,wrT,wt2,wwe] (.node [wg6,wmE,wp6,wrS,wtt,wwe] (.node [wg6,wmE,wp6,wrM,wt4,wwe] (.node [wg6,wmE,wp6,wrM,wtt,wwP] .nil .nil) .nil) (.node [wg6,wmE,wp6,wrT,wtt,wwN] (.node [wg6,wmE,wp6,wrT,wtt,wwe] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wsb,wtt,wwe] (.node [wg6,wmE,wp6,wsa,wtt,wwe] (.node [wg6,wmE,wp6,wrU,wtt,wwe] .nil .nil) .nil) (.node [wg6,wmE,wp6,wse,wtt,wyS] (.node [wg6,wmE,wp6,wsd,wtt,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrrr_ok : everyKey (rowOK 4 level4) level5rlrrrr = true := by decide +kernel
def level5rlrrr : BinaryTree (List W) := .node [wg6,wmE,wp6,wq0,wtt,wyS] level5rlrrrl level5rlrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrr_ok : everyKey (rowOK 4 level4) level5rlrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrrrl && everyKey (rowOK 4 level4) level5rlrrrr) = true
  rw [level5rlrrrl_ok, level5rlrrrr_ok]
  decide +kernel
def level5rlrr : BinaryTree (List W) := .node [wg6,wmE,wpG,wtt,wwe,wyS] level5rlrrl level5rlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrr_ok : everyKey (rowOK 4 level4) level5rlrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrrl && everyKey (rowOK 4 level4) level5rlrrr) = true
  rw [level5rlrrl_ok, level5rlrrr_ok]
  decide +kernel
def level5rlr : BinaryTree (List W) := .node [wg6,wmE,woH,wq4,wtt,wwe] level5rlrl level5rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlr_ok : everyKey (rowOK 4 level4) level5rlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrl && everyKey (rowOK 4 level4) level5rlrr) = true
  rw [level5rlrl_ok, level5rlrr_ok]
  decide +kernel
def level5rl : BinaryTree (List W) := .node [wg6,wl2,wp6,wtt,wwe,wAk] level5rll level5rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rl_ok : everyKey (rowOK 4 level4) level5rl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rll && everyKey (rowOK 4 level4) level5rlr) = true
  rw [level5rll_ok, level5rlr_ok]
  decide +kernel
def level5rrllll : BinaryTree (List W) := (.node [wg6,wmE,wp6,ws8,wwe,wyS] (.node [wg6,wmE,wp6,wsR,wwe,wyS] (.node [wg6,wmE,wp6,wsH,wtt,wwe] (.node [wg6,wmE,wp6,wsq,wtt,wyS] (.node [wg6,wmE,wp6,wsj,wwe,wyS] (.node [wg6,wmE,wp6,wsg,wtt,wwe] .nil .nil) (.node [wg6,wmE,wp6,wsk,wwe,wyS] .nil .nil)) (.node [wg6,wmE,wp6,wsG,wtt,wyS] (.node [wg6,wmE,wp6,wsE,wtt,wwe] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wsN,wyr,wyS] (.node [wg6,wmE,wp6,wsK,wyr,wAB] (.node [wg6,wmE,wp6,wsK,wyr,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wsP,wyr,wyS] (.node [wg6,wmE,wp6,wsO,wyr,wyS] .nil .nil) .nil))) (.node [wg6,wmE,wp6,wsY,wyl,wAH] (.node [wg6,wmE,wp6,wsW,wwe,wyS] (.node [wg6,wmE,wp6,wsV,wwe,wyS] (.node [wg6,wmE,wp6,wsT,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wsY,wwe,wAH] (.node [wg6,wmE,wp6,wsX,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wp6,ws2,wwe,wAH] (.node [wg6,wmE,wp6,ws1,wwe,wAH] (.node [wg6,wmE,wp6,ws0,wwe,wAH] .nil .nil) .nil) (.node [wg6,wmE,wp6,ws6,wwe,wyS] (.node [wg6,wmE,wp6,ws4,wwe,wyS] .nil .nil) .nil)))) (.node [wg6,wmE,wp6,wti,wwe,wyS] (.node [wg6,wmE,wp6,wte,wwe,wyS] (.node [wg6,wmE,wp6,wtb,wyr,wyS] (.node [wg6,wmE,wp6,wta,wwe,wyS] (.node [wg6,wmE,wp6,ws9,wwe,wyS] .nil .nil) (.node [wg6,wmE,wp6,wtb,wwe,wAH] .nil .nil)) (.node [wg6,wmE,wp6,wtd,wwe,wyS] (.node [wg6,wmE,wp6,wtc,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wtf,wwe,wyS] (.node [wg6,wmE,wp6,wtf,wwe,wyE] (.node [wg6,wmE,wp6,wtf,wv0,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wth,wwe,wyS] (.node [wg6,wmE,wp6,wtg,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wmE,wp6,wtm,wwe,wyS] (.node [wg6,wmE,wp6,wtj,wwe,wyS] (.node [wg6,wmE,wp6,wtj,wwe,wyI] (.node [wg6,wmE,wp6,wtj,wv4,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtl,wwe,wyS] (.node [wg6,wmE,wp6,wtk,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wtp,wwe,wyS] (.node [wg6,wmE,wp6,wto,wwe,wyS] (.node [wg6,wmE,wp6,wtn,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtr,wwe,wyS] (.node [wg6,wmE,wp6,wtq,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrllll_ok : everyKey (rowOK 4 level4) level5rrllll = true := by decide +kernel
def level5rrlllr : BinaryTree (List W) := (.node [wg6,wmE,wp6,wtt,wv0,wyS] (.node [wg6,wmE,wp6,wtt,wvM,wAR] (.node [wg6,wmE,wp6,wtt,wvC,wyS] (.node [wg6,wmE,wp6,wtt,wvl,wwe] (.node [wg6,wmE,wp6,wtt,wu4,wwe] (.node [wg6,wmE,wp6,wtt,wuU,wyS] .nil .nil) (.node [wg6,wmE,wp6,wtt,wu6,wyS] .nil .nil)) (.node [wg6,wmE,wp6,wtt,wvA,wwe] (.node [wg6,wmE,wp6,wtt,wvn,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wtt,wvF,wwe] (.node [wg6,wmE,wp6,wtt,wvE,wwe] (.node [wg6,wmE,wp6,wtt,wvD,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wvL,wAR] (.node [wg6,wmE,wp6,wtt,wvJ,wAR] .nil .nil) .nil))) (.node [wg6,wmE,wp6,wtt,wvV,wyS] (.node [wg6,wmE,wp6,wtt,wvR,wyS] (.node [wg6,wmE,wp6,wtt,wvP,wyS] (.node [wg6,wmE,wp6,wtt,wvN,wAR] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wvU,wyS] (.node [wg6,wmE,wp6,wtt,wvT,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wtt,wvY,wyS] (.node [wg6,wmE,wp6,wtt,wvX,wyS] (.node [wg6,wmE,wp6,wtt,wvW,wAR] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wv0,wyE] (.node [wg6,wmE,wp6,wtt,wvZ,wyS] .nil .nil) .nil)))) (.node [wg6,wmE,wp6,wtt,wwb,wyS] (.node [wg6,wmE,wp6,wtt,wv5,wyS] (.node [wg6,wmE,wp6,wtt,wv3,wyS] (.node [wg6,wmE,wp6,wtt,wv2,wyS] (.node [wg6,wmE,wp6,wtt,wv1,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wv4,wyS] (.node [wg6,wmE,wp6,wtt,wv4,wyI] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wtt,wv8,wyS] (.node [wg6,wmE,wp6,wtt,wv7,wyS] (.node [wg6,wmE,wp6,wtt,wv6,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wwa,wyS] (.node [wg6,wmE,wp6,wtt,wv9,wyS] .nil .nil) .nil))) (.node [wg6,wmE,wp6,wtt,wwe,wx9] (.node [wg6,wmE,wp6,wtt,wwe,wxJ] (.node [wg6,wmE,wp6,wtt,wwd,wyS] (.node [wg6,wmE,wp6,wtt,wwc,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wwe,wx7] (.node [wg6,wmE,wp6,wtt,wwe,wxW] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wtt,wwe,wyx] (.node [wg6,wmE,wp6,wtt,wwe,wyu] (.node [wg6,wmE,wp6,wtt,wwe,wya] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wwe,wyE] (.node [wg6,wmE,wp6,wtt,wwe,wyD] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlllr_ok : everyKey (rowOK 4 level4) level5rrlllr = true := by decide +kernel
def level5rrlll : BinaryTree (List W) := .node [wg6,wmE,wp6,wts,wwe,wyS] level5rrllll level5rrlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlll_ok : everyKey (rowOK 4 level4) level5rrlll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrllll && everyKey (rowOK 4 level4) level5rrlllr) = true
  rw [level5rrllll_ok, level5rrlllr_ok]
  decide +kernel
def level5rrllrl : BinaryTree (List W) := (.node [wg6,wmE,wp6,wtt,wwe,wy6] (.node [wg6,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wwe,wyM] (.node [wg6,wmE,wp6,wtt,wwe,wyJ] (.node [wg6,wmE,wp6,wtt,wwe,wyH] (.node [wg6,wmE,wp6,wtt,wwe,wyG] .nil .nil) (.node [wg6,wmE,wp6,wtt,wwe,wyI] .nil .nil)) (.node [wg6,wmE,wp6,wtt,wwe,wyL] (.node [wg6,wmE,wp6,wtt,wwe,wyK] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wtt,wwe,wyP] (.node [wg6,wmE,wp6,wtt,wwe,wyO] (.node [wg6,wmE,wp6,wtt,wwe,wyN] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wwe,wyR] (.node [wg6,wmE,wp6,wtt,wwe,wyQ] .nil .nil) .nil))) (.node [wg6,wmE,wp6,wtt,wwe,wyY] (.node [wg6,wmE,wp6,wtt,wwe,wyV] (.node [wg6,wmE,wp6,wtt,wwe,wyU] (.node [wg6,wmE,wp6,wtt,wwe,wyT] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wwe,wyX] (.node [wg6,wmE,wp6,wtt,wwe,wyW] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wtt,wwe,wy1] (.node [wg6,wmE,wp6,wtt,wwe,wy0] (.node [wg6,wmE,wp6,wtt,wwe,wyZ] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wwe,wy3] (.node [wg6,wmE,wp6,wtt,wwe,wy2] .nil .nil) .nil)))) (.node [wg6,wmE,wp6,wtt,wwe,wzo] (.node [wg6,wmE,wp6,wtt,wwe,wzg] (.node [wg6,wmE,wp6,wtt,wwe,wzb] (.node [wg6,wmE,wp6,wtt,wwe,wza] (.node [wg6,wmE,wp6,wtt,wwe,wy9] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wwe,wzd] (.node [wg6,wmE,wp6,wtt,wwe,wzc] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wtt,wwe,wzl] (.node [wg6,wmE,wp6,wtt,wwe,wzk] (.node [wg6,wmE,wp6,wtt,wwe,wzj] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wwe,wzn] (.node [wg6,wmE,wp6,wtt,wwe,wzm] .nil .nil) .nil))) (.node [wg6,wmE,wp6,wtt,wwe,wzu] (.node [wg6,wmE,wp6,wtt,wwe,wzr] (.node [wg6,wmE,wp6,wtt,wwe,wzq] (.node [wg6,wmE,wp6,wtt,wwe,wzp] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wwe,wzt] (.node [wg6,wmE,wp6,wtt,wwe,wzs] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wtt,wwe,wzx] (.node [wg6,wmE,wp6,wtt,wwe,wzw] (.node [wg6,wmE,wp6,wtt,wwe,wzv] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wwe,wzz] (.node [wg6,wmE,wp6,wtt,wwe,wzy] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrllrl_ok : everyKey (rowOK 4 level4) level5rrllrl = true := by decide +kernel
def level5rrllrr : BinaryTree (List W) := (.node [wg6,wmE,wp6,wtt,wwe,wAp] (.node [wg6,wmE,wp6,wtt,wwe,wzT] (.node [wg6,wmE,wp6,wtt,wwe,wzK] (.node [wg6,wmE,wp6,wtt,wwe,wzG] (.node [wg6,wmE,wp6,wtt,wwe,wzD] (.node [wg6,wmE,wp6,wtt,wwe,wzC] .nil .nil) (.node [wg6,wmE,wp6,wtt,wwe,wzE] .nil .nil)) (.node [wg6,wmE,wp6,wtt,wwe,wzJ] (.node [wg6,wmE,wp6,wtt,wwe,wzI] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wtt,wwe,wzQ] (.node [wg6,wmE,wp6,wtt,wwe,wzN] (.node [wg6,wmE,wp6,wtt,wwe,wzM] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wwe,wzS] (.node [wg6,wmE,wp6,wtt,wwe,wzR] .nil .nil) .nil))) (.node [wg6,wmE,wp6,wtt,wwe,wz1] (.node [wg6,wmE,wp6,wtt,wwe,wzX] (.node [wg6,wmE,wp6,wtt,wwe,wzV] (.node [wg6,wmE,wp6,wtt,wwe,wzU] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wwe,wz0] (.node [wg6,wmE,wp6,wtt,wwe,wzZ] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wtt,wwe,wz4] (.node [wg6,wmE,wp6,wtt,wwe,wz3] (.node [wg6,wmE,wp6,wtt,wwe,wz2] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wwe,wAg] (.node [wg6,wmE,wp6,wtt,wwe,wAb] .nil .nil) .nil)))) (.node [wg6,wmE,wp6,wtt,wwj,wyS] (.node [wg6,wmE,wp6,wtt,wwe,wAJ] (.node [wg6,wmE,wp6,wtt,wwe,wAD] (.node [wg6,wmE,wp6,wtt,wwe,wAC] (.node [wg6,wmE,wp6,wtt,wwe,wAB] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wwe,wAI] (.node [wg6,wmE,wp6,wtt,wwe,wAG] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wtt,wwg,wyS] (.node [wg6,wmE,wp6,wtt,wwf,wyS] (.node [wg6,wmE,wp6,wtt,wwe,wAQ] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wwi,wyS] (.node [wg6,wmE,wp6,wtt,wwh,wyS] .nil .nil) .nil))) (.node [wg6,wmE,wp6,wtt,wwp,wyS] (.node [wg6,wmE,wp6,wtt,wwm,wyS] (.node [wg6,wmE,wp6,wtt,wwl,wyS] (.node [wg6,wmE,wp6,wtt,wwk,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wwo,wyS] (.node [wg6,wmE,wp6,wtt,wwn,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wtt,www,wyS] (.node [wg6,wmE,wp6,wtt,wwv,wyS] (.node [wg6,wmE,wp6,wtt,wws,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wwy,wyS] (.node [wg6,wmE,wp6,wtt,wwx,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrllrr_ok : everyKey (rowOK 4 level4) level5rrllrr = true := by decide +kernel
def level5rrllr : BinaryTree (List W) := .node [wg6,wmE,wp6,wtt,wwe,wzA] level5rrllrl level5rrllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrllr_ok : everyKey (rowOK 4 level4) level5rrllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrllrl && everyKey (rowOK 4 level4) level5rrllrr) = true
  rw [level5rrllrl_ok, level5rrllrr_ok]
  decide +kernel
def level5rrll : BinaryTree (List W) := .node [wg6,wmE,wp6,wtt,wwe,wyF] level5rrlll level5rrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrll_ok : everyKey (rowOK 4 level4) level5rrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrlll && everyKey (rowOK 4 level4) level5rrllr) = true
  rw [level5rrlll_ok, level5rrllr_ok]
  decide +kernel
def level5rrlrll : BinaryTree (List W) := (.node [wg6,wmE,wp6,wtt,ww2,wyS] (.node [wg6,wmE,wp6,wtt,wwQ,wyS] (.node [wg6,wmE,wp6,wtt,wwM,wyS] (.node [wg6,wmE,wp6,wtt,wwJ,wyS] (.node [wg6,wmE,wp6,wtt,wwH,wyS] (.node [wg6,wmE,wp6,wtt,wwE,wyS] .nil .nil) (.node [wg6,wmE,wp6,wtt,wwI,wyS] .nil .nil)) (.node [wg6,wmE,wp6,wtt,wwL,wyS] (.node [wg6,wmE,wp6,wtt,wwK,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wtt,wwO,wyS] (.node [wg6,wmE,wp6,wtt,wwN,wzp] (.node [wg6,wmE,wp6,wtt,wwN,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wwP,wzr] (.node [wg6,wmE,wp6,wtt,wwP,wyS] .nil .nil) .nil))) (.node [wg6,wmE,wp6,wtt,wwV,wAR] (.node [wg6,wmE,wp6,wtt,wwT,wyS] (.node [wg6,wmE,wp6,wtt,wwS,wyS] (.node [wg6,wmE,wp6,wtt,wwR,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wwU,wyS] (.node [wg6,wmE,wp6,wtt,wwT,wzv] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wtt,wwY,wyS] (.node [wg6,wmE,wp6,wtt,wwX,wyS] (.node [wg6,wmE,wp6,wtt,wwW,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,ww1,wyS] (.node [wg6,wmE,wp6,wtt,wwZ,wyS] .nil .nil) .nil)))) (.node [wg6,wmE,wp6,wtt,wxi,wyS] (.node [wg6,wmE,wp6,wtt,wxb,wAR] (.node [wg6,wmE,wp6,wtt,ww8,wyS] (.node [wg6,wmE,wp6,wtt,ww5,wyS] (.node [wg6,wmE,wp6,wtt,ww3,wyS] .nil .nil) (.node [wg6,wmE,wp6,wtt,ww7,wyS] .nil .nil)) (.node [wg6,wmE,wp6,wtt,ww9,wzK] (.node [wg6,wmE,wp6,wtt,ww9,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wtt,wxd,wz7] (.node [wg6,wmE,wp6,wtt,wxd,wyS] (.node [wg6,wmE,wp6,wtt,wxc,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wxh,wyS] (.node [wg6,wmE,wp6,wtt,wxg,wyS] .nil .nil) .nil))) (.node [wg6,wmE,wp6,wtt,wxp,wyS] (.node [wg6,wmE,wp6,wtt,wxk,wyS] (.node [wg6,wmE,wp6,wtt,wxj,wzT] (.node [wg6,wmE,wp6,wtt,wxj,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wxn,wyS] (.node [wg6,wmE,wp6,wtt,wxl,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wtt,wxs,wyS] (.node [wg6,wmE,wp6,wtt,wxr,wAR] (.node [wg6,wmE,wp6,wtt,wxq,wAR] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wxt,wyS] (.node [wg6,wmE,wp6,wtt,wxs,wz7] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrll_ok : everyKey (rowOK 4 level4) level5rrlrll = true := by decide +kernel
def level5rrlrlr : BinaryTree (List W) := (.node [wg6,wmE,wp6,wtA,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wyn,wyS] (.node [wg6,wmE,wp6,wtt,wxX,wyS] (.node [wg6,wmE,wp6,wtt,wxz,wz0] (.node [wg6,wmE,wp6,wtt,wxw,wyS] (.node [wg6,wmE,wp6,wtt,wxv,wyS] .nil .nil) (.node [wg6,wmE,wp6,wtt,wxz,wzN] .nil .nil)) (.node [wg6,wmE,wp6,wtt,wxK,wyS] (.node [wg6,wmE,wp6,wtt,wxE,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wtt,wyl,wyS] (.node [wg6,wmE,wp6,wtt,wyh,wAR] (.node [wg6,wmE,wp6,wtt,wye,wAR] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wym,wyS] (.node [wg6,wmE,wp6,wtt,wyl,wAH] .nil .nil) .nil))) (.node [wg6,wmE,wp6,wtu,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wyt,wyS] (.node [wg6,wmE,wp6,wtt,wyr,wAB] (.node [wg6,wmE,wp6,wtt,wyq,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wyS,wAP] (.node [wg6,wmE,wp6,wtt,wyw,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wtx,wwe,wyS] (.node [wg6,wmE,wp6,wtw,wwe,wyS] (.node [wg6,wmE,wp6,wtv,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtz,wwe,wyS] (.node [wg6,wmE,wp6,wty,wwe,wyS] .nil .nil) .nil)))) (.node [wg6,wmE,wp6,wtW,wwe,wyS] (.node [wg6,wmE,wp6,wtK,wwe,wyS] (.node [wg6,wmE,wp6,wtD,wwe,wyS] (.node [wg6,wmE,wp6,wtC,wwe,wyS] (.node [wg6,wmE,wp6,wtB,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtH,wwe,wyS] (.node [wg6,wmE,wp6,wtE,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wtN,wwe,wyS] (.node [wg6,wmE,wp6,wtM,wwe,wyS] (.node [wg6,wmE,wp6,wtL,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtS,wwe,wyS] (.node [wg6,wmE,wp6,wtO,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wmE,wp6,wt2,wwe,wyS] (.node [wg6,wmE,wp6,wtZ,wwe,wyS] (.node [wg6,wmE,wp6,wtY,wwe,wyS] (.node [wg6,wmE,wp6,wtX,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wt1,wwe,wyS] (.node [wg6,wmE,wp6,wt0,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wt3,wwe,wyS] (.node [wg6,wmE,wp6,wt2,wwN,wyS] (.node [wg6,wmE,wp6,wt2,wwe,wzp] .nil .nil) .nil) (.node [wg6,wmE,wp6,wt4,wwe,wzr] (.node [wg6,wmE,wp6,wt4,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrlr_ok : everyKey (rowOK 4 level4) level5rrlrlr = true := by decide +kernel
def level5rrlrl : BinaryTree (List W) := .node [wg6,wmE,wp6,wtt,wxu,wyS] level5rrlrll level5rrlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrl_ok : everyKey (rowOK 4 level4) level5rrlrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrlrll && everyKey (rowOK 4 level4) level5rrlrlr) = true
  rw [level5rrlrll_ok, level5rrlrlr_ok]
  decide +kernel
def level5rrlrrl : BinaryTree (List W) := (.node [wg6,wmE,wp6,wut,wwe,wyS] (.node [wg6,wmE,wp6,wuf,wwe,wyS] (.node [wg6,wmE,wp6,wua,wwe,wyS] (.node [wg6,wmE,wp6,wt8,wwe,wyS] (.node [wg6,wmE,wp6,wt6,wyr,wyS] (.node [wg6,wmE,wp6,wt5,wwe,wyS] .nil .nil) (.node [wg6,wmE,wp6,wt7,wwe,wyS] .nil .nil)) (.node [wg6,wmE,wp6,wt9,wwe,wzy] (.node [wg6,wmE,wp6,wt9,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wud,wwe,wyS] (.node [wg6,wmE,wp6,wuc,wwe,wyS] (.node [wg6,wmE,wp6,wub,wwe,wAH] .nil .nil) .nil) (.node [wg6,wmE,wp6,wue,wwe,wyS] (.node [wg6,wmE,wp6,wud,wwX,wyS] .nil .nil) .nil))) (.node [wg6,wmE,wp6,wuo,wwe,wyS] (.node [wg6,wmE,wp6,wuj,wwe,wyS] (.node [wg6,wmE,wp6,wui,wwe,wyS] (.node [wg6,wmE,wp6,wuh,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wun,wyr,wyS] (.node [wg6,wmE,wp6,wul,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wuq,wwe,wzN] (.node [wg6,wmE,wp6,wuq,wwe,wyS] (.node [wg6,wmE,wp6,wup,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wus,wwe,wAH] (.node [wg6,wmE,wp6,wuq,wxz,wyS] .nil .nil) .nil)))) (.node [wg6,wmE,wp6,wuD,wwe,wyS] (.node [wg6,wmE,wp6,wuz,wyr,wyS] (.node [wg6,wmE,wp6,wuu,wxd,wyS] (.node [wg6,wmE,wp6,wuu,wwe,wz7] (.node [wg6,wmE,wp6,wuu,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wuy,wyr,wyS] (.node [wg6,wmE,wp6,wux,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wuC,wwe,wyS] (.node [wg6,wmE,wp6,wuB,wwe,wyS] (.node [wg6,wmE,wp6,wuA,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wuC,wxz,wyS] (.node [wg6,wmE,wp6,wuC,wwe,wz0] .nil .nil) .nil))) (.node [wg6,wmE,wp6,wuL,wwe,wyS] (.node [wg6,wmE,wp6,wuI,wwe,wyS] (.node [wg6,wmE,wp6,wuG,wwe,wyS] (.node [wg6,wmE,wp6,wuE,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wuK,wwe,wAH] (.node [wg6,wmE,wp6,wuJ,wwe,wAH] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wuM,wwe,wyS] (.node [wg6,wmE,wp6,wuL,wxs,wyS] (.node [wg6,wmE,wp6,wuL,wwe,wz7] .nil .nil) .nil) (.node [wg6,wmE,wp6,wuO,wwe,wyS] (.node [wg6,wmE,wp6,wuN,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrrl_ok : everyKey (rowOK 4 level4) level5rrlrrl = true := by decide +kernel
def level5rrlrrr : BinaryTree (List W) := (.node [wg6,wmE,wp6,wyr,wyS,wAB] (.node [wg6,wmE,wp6,wwe,wyi,wyS] (.node [wg6,wmE,wp6,wvq,wwe,wyS] (.node [wg6,wmE,wp6,wuS,wxj,wyS] (.node [wg6,wmE,wp6,wuS,wwe,wzT] (.node [wg6,wmE,wp6,wuS,wwe,wzK] .nil .nil) (.node [wg6,wmE,wp6,wuS,ww9,wyS] .nil .nil)) (.node [wg6,wmE,wp6,wu9,wwe,wyS] (.node [wg6,wmE,wp6,wuZ,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wwe,wye,wAH] (.node [wg6,wmE,wp6,wvW,wyr,wyS] (.node [wg6,wmE,wp6,wvJ,wyh,wAR] .nil .nil) .nil) (.node [wg6,wmE,wp6,wwe,wyh,wAR] (.node [wg6,wmE,wp6,wwe,wyh,wyS] .nil .nil) .nil))) (.node [wg6,wmE,wp6,wwe,wyv,wyS] (.node [wg6,wmE,wp6,wwe,wyp,wyS] (.node [wg6,wmE,wp6,wwe,wyl,wAH] (.node [wg6,wmE,wp6,wwe,wyj,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wwe,wys,wyS] (.node [wg6,wmE,wp6,wwe,wyr,wAB] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wyh,wAR] (.node [wg6,wmE,wp6,wyh,wyS,wAR] (.node [wg6,wmE,wp6,wwe,wyS,wAF] .nil .nil) .nil) (.node [wg6,wmE,wp6,wyl,wAH] (.node [wg6,wmE,wp6,wyl,wyS,wAH] .nil .nil) .nil)))) (.node [wg6,wmE,wqk,wtt,wwe,wyS] (.node [wg6,wmE,wqe,wtt,wwe,wyS] (.node [wg6,wmE,wp7,wtt,wwe,wyS] (.node [wg6,wmE,wp6,wyr,wAH,wAR] (.node [wg6,wmE,wp6,wyr,wAB] .nil .nil) .nil) (.node [wg6,wmE,wp9,wtt,wwe,wyS] (.node [wg6,wmE,wp8,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wqh,wtt,wwe,wyS] (.node [wg6,wmE,wqg,wtt,wwe,wyS] (.node [wg6,wmE,wqf,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wqj,wtt,wwe,wyS] (.node [wg6,wmE,wqi,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wmE,wqt,wtt,wwe,wyS] (.node [wg6,wmE,wqn,wtt,wwe,wyS] (.node [wg6,wmE,wqm,wtt,wwe,wyS] (.node [wg6,wmE,wql,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wqr,wtt,wwe,wyS] (.node [wg6,wmE,wqp,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wqz,wtt,wwe,wyS] (.node [wg6,wmE,wqy,wtt,wwe,wyS] (.node [wg6,wmE,wqu,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wqD,wtt,wwe,wyS] (.node [wg6,wmE,wqB,wtt,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrrr_ok : everyKey (rowOK 4 level4) level5rrlrrr = true := by decide +kernel
def level5rrlrr : BinaryTree (List W) := .node [wg6,wmE,wp6,wuP,wwe,wyS] level5rrlrrl level5rrlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrr_ok : everyKey (rowOK 4 level4) level5rrlrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrlrrl && everyKey (rowOK 4 level4) level5rrlrrr) = true
  rw [level5rrlrrl_ok, level5rrlrrr_ok]
  decide +kernel
def level5rrlr : BinaryTree (List W) := .node [wg6,wmE,wp6,wt4,wwP,wyS] level5rrlrl level5rrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlr_ok : everyKey (rowOK 4 level4) level5rrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrlrl && everyKey (rowOK 4 level4) level5rrlrr) = true
  rw [level5rrlrl_ok, level5rrlrr_ok]
  decide +kernel
def level5rrl : BinaryTree (List W) := .node [wg6,wmE,wp6,wtt,wwz,wyS] level5rrll level5rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrl_ok : everyKey (rowOK 4 level4) level5rrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrll && everyKey (rowOK 4 level4) level5rrlr) = true
  rw [level5rrll_ok, level5rrlr_ok]
  decide +kernel
def level5rrrlll : BinaryTree (List W) := (.node [wg6,wmE,wrg,wrx,wtt,wyS] (.node [wg6,wmE,wqY,wtt,wyS,wA8] (.node [wg6,wmE,wqP,wtt,wwe,wyS] (.node [wg6,wmE,wqK,wtt,wwe,wA8] (.node [wg6,wmE,wqH,wtt,wwe,wyS] (.node [wg6,wmE,wqF,wtt,wwe,wyS] .nil .nil) (.node [wg6,wmE,wqJ,wqO,wtt,wwe] .nil .nil)) (.node [wg6,wmE,wqO,wtt,wwe,wyS] (.node [wg6,wmE,wqM,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wqU,wtt,wwe,wyS] (.node [wg6,wmE,wqT,wtt,wwe,wyS] (.node [wg6,wmE,wqR,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wqX,wq8,wtt,wyS] (.node [wg6,wmE,wqV,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wmE,wq9,wtt,wwe,wyS] (.node [wg6,wmE,wq4,wtt,wwe,wA8] (.node [wg6,wmE,wq3,wq8,wtt,wwe] (.node [wg6,wmE,wq1,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wq8,wtt,wwe,wyS] (.node [wg6,wmE,wq6,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wre,wwe,wyS,wA8] (.node [wg6,wmE,wre,wsB,wwe,wyS] (.node [wg6,wmE,wrb,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wrg,wrs,wwe,wyS] (.node [wg6,wmE,wrf,wr5,wwe,wyS] .nil .nil) .nil)))) (.node [wg6,wmE,wrr,wtt,wwe,wyS] (.node [wg6,wmE,wrg,wvy,wwe,wyS] (.node [wg6,wmE,wrg,wrT,wwe] (.node [wg6,wmE,wrg,wrx,wyS] (.node [wg6,wmE,wrg,wrx,wwe,wyS] .nil .nil) (.node [wg6,wmE,wrg,wrT,wtt,wwe] .nil .nil)) (.node [wg6,wmE,wrg,wt2,wwe,wyS] (.node [wg6,wmE,wrg,wrT,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wro,wtt,wwe,wyS] (.node [wg6,wmE,wrn,wtt,wwe,wyS] (.node [wg6,wmE,wrg,wwe,wyS,wA8] .nil .nil) .nil) (.node [wg6,wmE,wrq,wtt,wwe,wyS] (.node [wg6,wmE,wrp,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wmE,wrw,wr5,wtt,wyS] (.node [wg6,wmE,wrs,wtt,ww9,wyS] (.node [wg6,wmE,wrs,wtt,wwe,wzK] (.node [wg6,wmE,wrs,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wrv,wtt,wyS,wA8] (.node [wg6,wmE,wrv,wsB,wtt,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wrx,wrT,wtt,wwe] (.node [wg6,wmE,wrx,wrT,wtt] (.node [wg6,wmE,wrx,wrG,wtt,wyS] .nil .nil) .nil) (.node [wg6,wmE,wrx,wtt,wwN,wyS] (.node [wg6,wmE,wrx,wrT,wtt,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrlll_ok : everyKey (rowOK 4 level4) level5rrrlll = true := by decide +kernel
def level5rrrllr : BinaryTree (List W) := (.node [wg6,wmE,wr0,wtt,wwe,wyS] (.node [wg6,wmE,wrQ,wtt,wwe,wyS] (.node [wg6,wmE,wrG,wtt,wwe,wzN] (.node [wg6,wmE,wrE,wtt,wwe,wyS] (.node [wg6,wmE,wrC,wtt,wwe,wyS] (.node [wg6,wmE,wrx,wtt,wyS,wA8] .nil .nil) (.node [wg6,wmE,wrD,wtt,wwe,wyS] .nil .nil)) (.node [wg6,wmE,wrG,wtt,wwe,wyS] (.node [wg6,wmE,wrF,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wrM,wsB,wtt,wwe] (.node [wg6,wmE,wrJ,wtt,wwe,wyS] (.node [wg6,wmE,wrG,wuq,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wrN,wtt,wwe,wyS] (.node [wg6,wmE,wrM,wtt,wwe,wA8] .nil .nil) .nil))) (.node [wg6,wmE,wrT,wtt,wwe,wA8] (.node [wg6,wmE,wrT,wrY,wtt,wwe] (.node [wg6,wmE,wrS,wr5,wtt,wwe] (.node [wg6,wmE,wrR,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wrT,wtt,wwe,wAu] (.node [wg6,wmE,wrT,wtt,wwe,wzp] .nil .nil) .nil)) (.node [wg6,wmE,wrY,wtt,wwe,wyS] (.node [wg6,wmE,wrX,wtt,wwe,wyS] (.node [wg6,wmE,wrW,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wrY,wuu,wwe,wyS] (.node [wg6,wmE,wrY,wtt,wxd,wyS] .nil .nil) .nil)))) (.node [wg6,wmE,wsn,wtt,wwe,wyS] (.node [wg6,wmE,wr6,wtt,wwe,wyS] (.node [wg6,wmE,wr3,wtt,wwe,wyS] (.node [wg6,wmE,wr2,wtt,wwe,wyS] (.node [wg6,wmE,wr1,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wr5,wtt,wwe,wyS] (.node [wg6,wmE,wr4,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wr9,wtt,wwe,wyS] (.node [wg6,wmE,wr8,wtt,wwe,wyS] (.node [wg6,wmE,wr7,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wsh,wtt,wwe,wyS] (.node [wg6,wmE,wsc,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wmE,wsB,wt4,wwe,wyS] (.node [wg6,wmE,wsB,wtt,wwe,wyS] (.node [wg6,wmE,wsy,wtt,wwe,wyS] (.node [wg6,wmE,wst,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wsB,wtt,wwP,wyS] (.node [wg6,wmE,wsB,wtt,wwe,wzr] .nil .nil) .nil)) (.node [wg6,wmE,wsI,wtt,wwe,wyS] (.node [wg6,wmE,wsF,wtt,wwe,wyS] (.node [wg6,wmE,wsD,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wsY,wwe,wAH,wA8] (.node [wg6,wmE,wsK,wyr,wyS,wA8] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrllr_ok : everyKey (rowOK 4 level4) level5rrrllr = true := by decide +kernel
def level5rrrll : BinaryTree (List W) := .node [wg6,wmE,wrx,wtt,wx5,wyS] level5rrrlll level5rrrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrll_ok : everyKey (rowOK 4 level4) level5rrrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrlll && everyKey (rowOK 4 level4) level5rrrllr) = true
  rw [level5rrrlll_ok, level5rrrllr_ok]
  decide +kernel
def level5rrrlrl : BinaryTree (List W) := (.node [wg6,wmE,wtt,wvw,wwe,wyS] (.node [wg6,wmE,wtj,wwe,wyS,wBe] (.node [wg6,wmE,wtj,wv4,wyS] (.node [wg6,wmE,wtj,wvw,wwe,wyS] (.node [wg6,wmE,wtj,wtt,wv4,wyS] (.node [wg6,wmE,wtf,wwe,wyS,wA8] .nil .nil) (.node [wg6,wmE,wtj,wtt,wwe,wyI] .nil .nil)) (.node [wg6,wmE,wtj,wv4,wwe,wyS] (.node [wg6,wmE,wtj,wvy,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wtj,wwe,wyI,wyS] (.node [wg6,wmE,wtj,wwe,wyI] (.node [wg6,wmE,wtj,wv4,wyS,wA8] .nil .nil) .nil) (.node [wg6,wmE,wtj,wwe,wyS,wA8] (.node [wg6,wmE,wtj,wwe,wyI,wA8] .nil .nil) .nil))) (.node [wg6,wmE,wtr,wwe,wyS,wA8] (.node [wg6,wmE,wtm,wwe,wyS,wA8] (.node [wg6,wmE,wtl,wwe,wyS,wA8] (.node [wg6,wmE,wtk,wwe,wyS,wA8] .nil .nil) .nil) (.node [wg6,wmE,wtp,wwe,wyS,wA8] (.node [wg6,wmE,wtn,wwe,wyS,wA8] .nil .nil) .nil)) (.node [wg6,wmE,wtt,wvi,wwe,wyS] (.node [wg6,wmE,wtt,wu2,wwe,wyS] (.node [wg6,wmE,wtt,wuW,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wtt,wvt,wwe,wyS] (.node [wg6,wmE,wtt,wvo,wwe,wyS] .nil .nil) .nil)))) (.node [wg6,wmE,wtt,wv4,wx3,wyS] (.node [wg6,wmE,wtt,wvG,wwe,wyS] (.node [wg6,wmE,wtt,wvx,wwe,wyS] (.node [wg6,wmE,wtt,wvw,wxj,wyS] (.node [wg6,wmE,wtt,wvw,wwe,wzT] .nil .nil) .nil) (.node [wg6,wmE,wtt,wvB,wwe,wyS] (.node [wg6,wmE,wtt,wvz,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wtt,wvZ,wyS,wAX] (.node [wg6,wmE,wtt,wvJ,wAR,wA8] (.node [wg6,wmE,wtt,wvH,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wtt,wv4,wwe,wyI] (.node [wg6,wmE,wtt,wv0,wyS,wA8] .nil .nil) .nil))) (.node [wg6,wmE,wtt,wv4,wyS,wBg] (.node [wg6,wmE,wtt,wv4,wyI,wyS] (.node [wg6,wmE,wtt,wv4,wyI] (.node [wg6,wmE,wtt,wv4,wx5,wyS] .nil .nil) .nil) (.node [wg6,wmE,wtt,wv4,wyS,wA8] (.node [wg6,wmE,wtt,wv4,wyI,wA8] .nil .nil) .nil)) (.node [wg6,wmE,wtt,wv7,wyS,wA8] (.node [wg6,wmE,wtt,wv6,wyS,wA8] (.node [wg6,wmE,wtt,wv5,wyS,wA8] .nil .nil) .nil) (.node [wg6,wmE,wtt,wwa,wyS,wA8] (.node [wg6,wmE,wtt,wv8,wyS,wA8] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrlrl_ok : everyKey (rowOK 4 level4) level5rrrlrl = true := by decide +kernel
def level5rrrlrr : BinaryTree (List W) := (.node [wg6,wmE,wtt,wwe,wyQ,wA8] (.node [wg6,wmE,wtt,wwe,wyB,wyS] (.node [wg6,wmE,wtt,wwe,wx4,wyS] (.node [wg6,wmE,wtt,wwe,wx0,wyS] (.node [wg6,wmE,wtt,wwe,wxH,wyS] (.node [wg6,wmE,wtt,wwe,wxB,wyS] .nil .nil) (.node [wg6,wmE,wtt,wwe,wxT,wyS] .nil .nil)) (.node [wg6,wmE,wtt,wwe,wx3,wz0] (.node [wg6,wmE,wtt,wwe,wx3,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wtt,wwe,wyb,wyS] (.node [wg6,wmE,wtt,wwe,wx8,wyS] (.node [wg6,wmE,wtt,wwe,wx6,wyS] .nil .nil) .nil) (.node [wg6,wmE,wtt,wwe,wyo,wyS] (.node [wg6,wmE,wtt,wwe,wyc,wyS] .nil .nil) .nil))) (.node [wg6,wmE,wtt,wwe,wyI,wBj] (.node [wg6,wmE,wtt,wwe,wyI,wAs] (.node [wg6,wmE,wtt,wwe,wyE,wA8] (.node [wg6,wmE,wtt,wwe,wyD,wAX] .nil .nil) .nil) (.node [wg6,wmE,wtt,wwe,wyI,wA8] (.node [wg6,wmE,wtt,wwe,wyI,wAu] .nil .nil) .nil)) (.node [wg6,wmE,wtt,wwe,wyL,wA8] (.node [wg6,wmE,wtt,wwe,wyK,wA8] (.node [wg6,wmE,wtt,wwe,wyJ,wA8] .nil .nil) .nil) (.node [wg6,wmE,wtt,wwe,wyO,wA8] (.node [wg6,wmE,wtt,wwe,wyM,wA8] .nil .nil) .nil)))) (.node [wg6,wmE,wtt,wwe,wyS,wAO] (.node [wg6,wmE,wtt,wwe,wyS,wAv] (.node [wg6,wmE,wtt,wwe,wyS,wAm] (.node [wg6,wmE,wtt,wwe,wyS,wAe] (.node [wg6,wmE,wtt,wwe,wyS,wz8] .nil .nil) .nil) (.node [wg6,wmE,wtt,wwe,wyS,wAt] (.node [wg6,wmE,wtt,wwe,wyS,wAs] .nil .nil) .nil)) (.node [wg6,wmE,wtt,wwe,wyS,wAy] (.node [wg6,wmE,wtt,wwe,wyS,wAx] (.node [wg6,wmE,wtt,wwe,wyS,wAw] .nil .nil) .nil) (.node [wg6,wmE,wtt,wwe,wyS,wAM] (.node [wg6,wmE,wtt,wwe,wyS,wAE] .nil .nil) .nil))) (.node [wg6,wmE,wtt,wwe,wyS,wA2] (.node [wg6,wmE,wtt,wwe,wyS,wAY] (.node [wg6,wmE,wtt,wwe,wyS,wAX] (.node [wg6,wmE,wtt,wwe,wyS,wAU] .nil .nil) .nil) (.node [wg6,wmE,wtt,wwe,wyS,wA0] (.node [wg6,wmE,wtt,wwe,wyS,wAZ] .nil .nil) .nil)) (.node [wg6,wmE,wtt,wwe,wyS,wA5] (.node [wg6,wmE,wtt,wwe,wyS,wA4] (.node [wg6,wmE,wtt,wwe,wyS,wA3] .nil .nil) .nil) (.node [wg6,wmE,wtt,wwe,wyS,wA7] (.node [wg6,wmE,wtt,wwe,wyS,wA6] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrlrr_ok : everyKey (rowOK 4 level4) level5rrrlrr = true := by decide +kernel
def level5rrrlr : BinaryTree (List W) := .node [wg6,wmE,wtt,wwc,wyS,wA8] level5rrrlrl level5rrrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrlr_ok : everyKey (rowOK 4 level4) level5rrrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrlrl && everyKey (rowOK 4 level4) level5rrrlrr) = true
  rw [level5rrrlrl_ok, level5rrrlrr_ok]
  decide +kernel
def level5rrrl : BinaryTree (List W) := .node [wg6,wmE,wte,wwe,wyS,wAX] level5rrrll level5rrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrl_ok : everyKey (rowOK 4 level4) level5rrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrll && everyKey (rowOK 4 level4) level5rrrlr) = true
  rw [level5rrrll_ok, level5rrrlr_ok]
  decide +kernel
def level5rrrrll : BinaryTree (List W) := (.node [wg6,wmE,wtt,wxj,wyS,wA8] (.node [wg6,wmE,wtt,wwe,wzT,wA8] (.node [wg6,wmE,wtt,wwe,wzp,wA8] (.node [wg6,wmE,wtt,wwe,wyT,wA8] (.node [wg6,wmE,wtt,wwe,wyS,wBa] (.node [wg6,wmE,wtt,wwe,wyS,wA9] .nil .nil) (.node [wg6,wmE,wtt,wwe,wyS,wBb] .nil .nil)) (.node [wg6,wmE,wtt,wwe,wyV,wA8] (.node [wg6,wmE,wtt,wwe,wyU,wA8] .nil .nil) .nil)) (.node [wg6,wmE,wtt,wwe,wzy,wA8] (.node [wg6,wmE,wtt,wwe,wzv,wA8] (.node [wg6,wmE,wtt,wwe,wzr,wA8] .nil .nil) .nil) (.node [wg6,wmE,wtt,wwe,wzN,wA8] (.node [wg6,wmE,wtt,wwe,wzK,wA8] .nil .nil) .nil))) (.node [wg6,wmE,wtt,wwN,wyS,wA8] (.node [wg6,wmE,wtt,wwf,wyS,wA8] (.node [wg6,wmE,wtt,wwe,wAB,wA8] (.node [wg6,wmE,wtt,wwe,wz0,wA8] .nil .nil) .nil) (.node [wg6,wmE,wtt,wwh,wyS,wA8] (.node [wg6,wmE,wtt,wwg,wyS,wA8] .nil .nil) .nil)) (.node [wg6,wmE,wtt,wwX,wyS,wA8] (.node [wg6,wmE,wtt,wwT,wyS,wA8] (.node [wg6,wmE,wtt,wwP,wyS,wA8] .nil .nil) .nil) (.node [wg6,wmE,wtt,wxd,wyS,wA8] (.node [wg6,wmE,wtt,ww9,wyS,wA8] .nil .nil) .nil)))) (.node [wg6,wmE,wuu,wwe,wyS,wA8] (.node [wg6,wmE,wtw,wwe,wyS,wA8] (.node [wg6,wmE,wtt,wyl,wyS,wA8] (.node [wg6,wmE,wtt,wxs,wyS,wA8] (.node [wg6,wmE,wtt,wxs,wyS,wAs] .nil .nil) .nil) (.node [wg6,wmE,wtv,wwe,wyS,wA8] (.node [wg6,wmE,wtu,wwe,wyS,wA8] .nil .nil) .nil)) (.node [wg6,wmE,wt9,wwe,wyS,wA8] (.node [wg6,wmE,wt4,wwe,wyS,wA8] (.node [wg6,wmE,wt2,wwe,wyS,wA8] .nil .nil) .nil) (.node [wg6,wmE,wuq,wwe,wyS,wA8] (.node [wg6,wmE,wud,wwe,wyS,wA8] .nil .nil) .nil))) (.node [wg6,wmF,wp6,wtt,wwe,wyS] (.node [wg6,wmE,wuL,wwe,wyS,wAs] (.node [wg6,wmE,wuC,wwe,wyS,wA8] (.node [wg6,wmE,wuC,wwe,wx3,wyS] .nil .nil) .nil) (.node [wg6,wmE,wwe,wyh,wyS,wA8] (.node [wg6,wmE,wuL,wwe,wyS,wA8] .nil .nil) .nil)) (.node [wg6,wmG,wtt,wwe,wyS,wA8] (.node [wg6,wmG,wp6,wtt,wwe,wyS] (.node [wg6,wmF,wtt,wwe,wyS,wA8] .nil .nil) .nil) (.node [wg6,wmH,wtt,wwe,wyS,wA8] (.node [wg6,wmH,wp6,wtt,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrll_ok : everyKey (rowOK 4 level4) level5rrrrll = true := by decide +kernel
def level5rrrrlr : BinaryTree (List W) := (.node [wg6,wnG,wtt,wwe,wyS,wA8] (.node [wg6,wnl,wp6,wtt,wwe,wyS] (.node [wg6,wm0,wp6,wtt,wwe,wyS] (.node [wg6,wmS,wp6,wtt,wwe,wyS] (.node [wg6,wmP,wp6,wtt,wwe,wyS] (.node [wg6,wmO,wp6,wtt,wwe,wyS] .nil .nil) (.node [wg6,wmQ,wp6,wtt,wwe,wyS] .nil .nil)) (.node [wg6,wmZ,wp6,wtt,wwe,wyS] (.node [wg6,wmU,wp6,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wm9,wp6,wtt,wwe,wyS] (.node [wg6,wm3,wp6,wtt,wwe,wyS] (.node [wg6,wm1,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wne,wp6,wtt,wwe,wyS] (.node [wg6,wnd,wp6,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wnG,wn8,wp6,wwe,wyS] (.node [wg6,wnC,wp6,wtt,wwe,wyS] (.node [wg6,wnx,wp6,wvk,wwe,wyS] (.node [wg6,wnr,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wnF,wp6,wtt,wwe,wyS] (.node [wg6,wnD,wp6,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wnG,wp6,wtt,wwe,wyS] (.node [wg6,wnG,wp6,wq4,wtt,wwe] (.node [wg6,wnG,wp6,wqY,wtt,wyS] .nil .nil) .nil) (.node [wg6,wnG,wp6,wtt,wwT,wyS] (.node [wg6,wnG,wp6,wtt,wwe,wzv] .nil .nil) .nil)))) (.node [wg6,wnS,wp6,wtt,wwe,wAo] (.node [wg6,wnO,wp6,wqK,wtt,wwe] (.node [wg6,wnN,wp6,wtt,wwe,wyS] (.node [wg6,wnL,wp6,wtt,wwe,wyS] (.node [wg6,wnI,wp6,wtt,wxV,wyS] .nil .nil) .nil) (.node [wg6,wnO,woH,wp6,wtt,wyS] (.node [wg6,wnO,woj,wp6,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wnO,wp6,wt9,wwe,wyS] (.node [wg6,wnO,wp6,wtt,wwe,wzy] (.node [wg6,wnO,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wnR,wp6,wtt,wwe,wyS] (.node [wg6,wnO,wtt,wwe,wyS,wA8] .nil .nil) .nil))) (.node [wg6,wnV,wp6,wtt,wwX,wyS] (.node [wg6,wnV,woN,wp6,wtt,wyS] (.node [wg6,wnV,woe,wp6,wwe,wyS] (.node [wg6,wnU,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wnV,wp6,wtt,wwe,wyS] (.node [wg6,wnV,wpo,wp6,wtt,wwe] .nil .nil) .nil)) (.node [wg6,wnW,wp6,wtt,wwe,wyS] (.node [wg6,wnV,wtt,wwe,wyS,wA8] (.node [wg6,wnV,wp6,wud,wwe,wyS] .nil .nil) .nil) (.node [wg6,wn8,wp6,wvg,wwe,wyS] (.node [wg6,wnX,wp6,wtt,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrlr_ok : everyKey (rowOK 4 level4) level5rrrrlr = true := by decide +kernel
def level5rrrrl : BinaryTree (List W) := .node [wg6,wmN,wp6,wtt,wwe,wyS] level5rrrrll level5rrrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrl_ok : everyKey (rowOK 4 level4) level5rrrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrrll && everyKey (rowOK 4 level4) level5rrrrlr) = true
  rw [level5rrrrll_ok, level5rrrrlr_ok]
  decide +kernel
def level5rrrrrl : BinaryTree (List W) := (.node [wg6,wp6,wtt,wwe,wxS,wyS] (.node [wg6,wp6,wtf,wvk,wwe,wyS] (.node [wg6,wpW,wtt,wwe,wyS,wAo] (.node [wg6,wpB,wtt,wwe,wyS,wAk] (.node [wg6,wo2,wtt,wwe,wxR,wyS] (.node [wg6,woH,wp6,wtt,wxR,wyS] .nil .nil) (.node [wg6,wpo,wp6,wtt,wwe,wAk] .nil .nil)) (.node [wg6,wpW,wtt,wwe,wxV,wyS] (.node [wg6,wpW,wtt,wvk,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wp6,wsr,wtt,wwe,wyS] (.node [wg6,wp6,wsl,wtt,wwe,wyS] (.node [wg6,wp6,wrP,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wp6,wtf,wvg,wwe,wyS] (.node [wg6,wp6,wsw,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wp6,wtt,wvh,wwe,wyS] (.node [wg6,wp6,wtt,wvg,wwe,wyS] (.node [wg6,wp6,wtt,wvc,wwe,wyS] (.node [wg6,wp6,wtt,wu7,wwe,wyS] .nil .nil) .nil) (.node [wg6,wp6,wtt,wvg,wxj,wyS] (.node [wg6,wp6,wtt,wvg,wwe,wzT] .nil .nil) .nil)) (.node [wg6,wp6,wtt,wwe,wxN,wyS] (.node [wg6,wp6,wtt,wv0,wxV,wyS] (.node [wg6,wp6,wtt,wv0,wxR,wyS] .nil .nil) .nil) (.node [wg6,wp6,wtt,wwe,wxR,wz0] (.node [wg6,wp6,wtt,wwe,wxR,wyS] .nil .nil) .nil)))) (.node [wg6,wp6,wtt,wxs,wyS,wAk] (.node [wg6,wp6,wtt,wwe,wyS,wAK] (.node [wg6,wp6,wtt,wwe,wyE,wAo] (.node [wg6,wp6,wtt,wwe,wyE,wAk] (.node [wg6,wp6,wtt,wwe,wyz,wyS] .nil .nil) .nil) (.node [wg6,wp6,wtt,wwe,wyS,wAl] (.node [wg6,wp6,wtt,wwe,wyS,wAk] .nil .nil) .nil)) (.node [wg6,wp6,wtt,wwe,wz5,wAo] (.node [wg6,wp6,wtt,wwe,wzr,wA1] (.node [wg6,wp6,wtt,wwe,wyS,wAS] .nil .nil) .nil) (.node [wg6,wp6,wtt,wwP,wyS,wA1] (.node [wg6,wp6,wtt,wwe,wz7,wAk] .nil .nil) .nil))) (.node [wg6,wp6,wuQ,wvk,wwe,wyS] (.node [wg6,wp6,wt4,wwe,wyS,wA1] (.node [wg6,wp6,wtt,wxz,wxR,wyS] (.node [wg6,wp6,wtt,wxx,wxV,wyS] .nil .nil) .nil) (.node [wg6,wp6,wuL,wwe,wyS,wAk] (.node [wg6,wp6,wuC,wwe,wxR,wyS] .nil .nil) .nil)) (.node [wg6,wtt,wvg,wwe,wyS,wA8] (.node [wg6,wtt,wvg,wvw,wwe,wyS] (.node [wg6,wp6,wuS,wvg,wwe,wyS] .nil .nil) .nil) (.node [wg6,wtt,wwe,wxR,wx3,wyS] (.node [wg6,wtt,wvk,wwe,wyS,wAX] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrrl_ok : everyKey (rowOK 4 level4) level5rrrrrl = true := by decide +kernel
def level5rrrrrr : BinaryTree (List W) := (.node [wiq,wmE,wp6,wtt,wwe,wz7] (.node [whM,wiC,wmE,wtt,wwe,wyS] (.node [wg8,wmE,wtt,wwe,wyS,wA8] (.node [wg6,wtt,wwe,wyS,wAo,wAX] (.node [wg6,wtt,wwe,wyS,wAk,wAs] (.node [wg6,wtt,wwe,wxV,wyS,wAX] .nil .nil) (.node [wg6,wtt,wwe,wyS,wAk,wA8] .nil .nil)) (.node [wg7,wmE,wtt,wwe,wyS,wA8] (.node [wg7,wiv,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [whh,wiC,wmE,wtt,wwe,wyS] (.node [whd,wmE,wtt,wwe,wyS,wA8] (.node [wha,wmE,wtt,wwe,wyS,wA8] .nil .nil) .nil) (.node [whz,wiC,wmE,wtt,wwe,wyS] (.node [whp,wiC,wmE,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wim,wmE,wp6,wtt,wwe,wyS] (.node [wia,wmE,wp6,wuS,wwe,wyS] (.node [wia,wmE,wp6,wtt,wwe,wyS] (.node [whW,wia,wmE,wp6,wwe,wyS] .nil .nil) .nil) (.node [wie,wim,wmE,wp6,wtt,wyS] (.node [wia,wmE,wp6,wwe,wyS] .nil .nil) .nil)) (.node [wip,wiq,wmE,wp6,wtt,wwe] (.node [wim,wmE,wp6,wtt,wyS] (.node [wim,wmE,wp6,wtt,wxz,wyS] .nil .nil) .nil) (.node [wiq,wmE,wp6,wtt,wwe,wyS] (.node [wiq,wmE,wp6,wtt,wwe] .nil .nil) .nil)))) (.node [wiC,wmE,wtt,wwe,wyS,wAX] (.node [wiC,wmE,wtj,wwe,wyS,wA8] (.node [wiv,wp6,wrP,wtt,wwe,wyS] (.node [wiv,wmE,wtt,wwe,wyS,wAX] (.node [wir,wmE,wtt,wwe,wyS,wAX] .nil .nil) .nil) (.node [wiC,wmE,wnQ,wtt,wwe,wyS] (.node [wiC,wmr,wtt,wwe,wyS,wA8] .nil .nil) .nil)) (.node [wiC,wmE,wtt,wwe,wxy,wyS] (.node [wiC,wmE,wtt,wv4,wyS,wA8] (.node [wiC,wmE,wtt,wuR,wwe,wyS] .nil .nil) .nil) (.node [wiC,wmE,wtt,wwe,wyS,wz6] (.node [wiC,wmE,wtt,wwe,wyI,wA8] .nil .nil) .nil))) (.node [wmE,wnQ,wp6,wtt,wwe,wyS] (.node [wiI,wmE,wtt,wwe,wyS,wA8] (.node [wiG,wmE,wtt,wwe,wyS,wA8] (.node [wiC,wmE,wtt,wwe,wyS,wA8] .nil .nil) .nil) (.node [wiN,wmE,wtt,wwe,wyS,wA8] (.node [wiK,wmE,wtt,wwe,wyS,wA8] .nil .nil) .nil)) (.node [wmE,wp6,wrP,wtt,wwe,wyS] (.node [wmE,wnQ,wtt,wwe,wyS,wA8] (.node [wmE,wnQ,wtt,wwe,wyS] .nil .nil) .nil) (.node [wp6,wrP,wtt,wwe,wyS,wA1] (.node [wp6,wrP,wtt,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrrr_ok : everyKey (rowOK 4 level4) level5rrrrrr = true := by decide +kernel
def level5rrrrr : BinaryTree (List W) := .node [wg6,wtt,wwe,wxR,wyS,wA8] level5rrrrrl level5rrrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrr_ok : everyKey (rowOK 4 level4) level5rrrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrrrl && everyKey (rowOK 4 level4) level5rrrrrr) = true
  rw [level5rrrrrl_ok, level5rrrrrr_ok]
  decide +kernel
def level5rrrr : BinaryTree (List W) := .node [wg6,woA,wtt,wvg,wwe,wyS] level5rrrrl level5rrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrr_ok : everyKey (rowOK 4 level4) level5rrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrrl && everyKey (rowOK 4 level4) level5rrrrr) = true
  rw [level5rrrrl_ok, level5rrrrr_ok]
  decide +kernel
def level5rrr : BinaryTree (List W) := .node [wg6,wmE,wtt,wwe,wyS,wA8] level5rrrl level5rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrr_ok : everyKey (rowOK 4 level4) level5rrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrl && everyKey (rowOK 4 level4) level5rrrr) = true
  rw [level5rrrl_ok, level5rrrr_ok]
  decide +kernel
def level5rr : BinaryTree (List W) := .node [wg6,wmE,wqE,wtt,wwe,wyS] level5rrl level5rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rr_ok : everyKey (rowOK 4 level4) level5rr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrl && everyKey (rowOK 4 level4) level5rrr) = true
  rw [level5rrl_ok, level5rrr_ok]
  decide +kernel
def level5r : BinaryTree (List W) := .node [wg6,wmE,wp6,wsf,wtt,wwe] level5rl level5rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5r_ok : everyKey (rowOK 4 level4) level5r = true := by
  change (_ && everyKey (rowOK 4 level4) level5rl && everyKey (rowOK 4 level4) level5rr) = true
  rw [level5rl_ok, level5rr_ok]
  decide +kernel
def level5 : BinaryTree (List W) := .node [wg6,wjl,wmE,woN,wtt,wyS] level5l level5r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5_ok : everyKey (rowOK 4 level4) level5 = true := by
  change (_ && everyKey (rowOK 4 level4) level5l && everyKey (rowOK 4 level4) level5r) = true
  rw [level5l_ok, level5r_ok]
  decide +kernel
theorem closed5 : Closed 5 level5 := closed_next 4 (by decide) level5 level4 closed4 level5_ok
def level6lllll : BinaryTree (List W) := (.node [ws,wg6,wmE,wp6,wtt,wwe,wyS] (.node [we,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wb,wg6,wiv,wmE,wtt,wwe,wyS] (.node [wa,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wa,wg6,wiC,wmE,wtt,wwe,wyS] (.node [wa,wc2,wg6,wmE,wtt,wwe,wyS] .nil .nil) (.node [wa,wg6,wjl,wmE,wtt,wwe,wyS] .nil .nil)) (.node [wb,wc2,wg6,wmE,wtt,wwe,wyS] (.node [wa,wg6,wmE,wtt,wwe,wyS,wA8] .nil .nil) .nil)) (.node [wb,wg6,wmE,wtt,wwe,wyS,wA8] (.node [wb,wg6,wmE,wtt,wwe,wyS] (.node [wb,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wc,wg6,wmE,wtt,wwe,wyS,wA8] (.node [wc,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wm,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wh,wg6,wmE,wtt,wwe,wyS,wA8] (.node [wh,wg6,wmE,wp6,wtt,wwe,wyS] (.node [we,wg6,wmE,wtt,wwe,wyS,wA8] .nil .nil) .nil) (.node [wl,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wl,wg6,wiC,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wp,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wo,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wn,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wr,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wq,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil)))) (.node [wF,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wz,wg6,wmE,wp6,wtt,wwe,wyS] (.node [ww,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wu,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wt,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) (.node [wv,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil)) (.node [wx,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wx,wc2,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wC,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wB,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wA,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wE,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wD,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wK,wY,wg6,wmE,wp6,wtt,wwe] (.node [wI,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wH,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wG,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wK,wT,wg6,wmE,wp6,wtt,wwe] (.node [wJ,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wK,wg6,wip,wmE,wp6,wtt,wwe] (.node [wK,wgR,wmE,wp6,wtt,wwe,wyS] (.node [wK,wc2,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wK,wg6,wjl,wmE,wtt,wwe,wyS] (.node [wK,wg6,wiC,wmE,wtt,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllll_ok : everyKey (rowOK 5 level5) level6lllll = true := by decide +kernel
def level6llllr : BinaryTree (List W) := (.node [wT,wgR,wg6,wmE,wp6,wtt,wwe] (.node [wO,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wK,wip,wmE,wp6,wtt,wwe] (.node [wK,wg6,wmE,wp6,wtt,wwe,wz7] (.node [wK,wg6,wmE,wpx,wtt,wwe,wyS] (.node [wK,wg6,wmE,wpo,wp6,wtt,wwe] .nil .nil) (.node [wK,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil)) (.node [wK,wg6,wmE,wtt,wwe,wyS,wA8] (.node [wK,wg6,wmE,wqt,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wM,wg6,wiC,wmE,wtt,wwe,wyS] (.node [wL,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wK,wip,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wN,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wM,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wT,wcp,wg6,wmE,wp6,wtt,wwe] (.node [wQ,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wP,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wP,wg6,wjl,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wT,wbg,wg6,wmE,wp6,wtt,wwe] (.node [wR,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wT,wfs,wg6,wmE,wp6,wtt,wwe] (.node [wT,weV,wg6,wp6,wtt,wwe,wyS] (.node [wT,wc2,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wT,wfs,wg6,wp6,wtt,wwe,wyS] (.node [wT,wfs,wg6,wp6,wtt,wwe] .nil .nil) .nil)))) (.node [wW,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wT,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wT,wg6,wjl,wp6,wtt,wwe,wyS] (.node [wT,wg6,wiC,wmE,wtt,wwe,wyS] (.node [wT,wg6,wiv,wp6,wtt,wwe,wyS] .nil .nil) (.node [wT,wg6,wjl,wmE,wtt,wwe,wyS] .nil .nil)) (.node [wT,wg6,wl2,wp6,wtt,wwe,wyS] (.node [wT,wg6,wjl,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wT,wg6,wmE,wp6,wtt,wwe,wAR] (.node [wT,wg6,wmE,wp6,wtt,wwe,wAH] (.node [wT,wg6,wmE,wp6,wtt,wwe,wAo] .nil .nil) .nil) (.node [wT,wg6,wp6,wtt,wwe,wyS,wA1] (.node [wT,wg6,wmE,wtt,wwe,wyS,wA8] .nil .nil) .nil))) (.node [wY,web,wg6,wmE,wtt,wwe] (.node [wY,wcp,wg6,wmE,wp6,wtt,wwe] (.node [wY,wbg,wg6,wmE,wp6,wtt,wwe] (.node [wX,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wY,web,wg6,wmE,wp6,wtt,wwe] (.node [wY,wc2,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wY,wgR,wg6,wmE,wp6,wtt,wwe] (.node [wY,wfs,wg6,wmE,wp6,wtt,wwe] (.node [wY,web,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wY,wg6,wjl,wmE,wtt,wwe,wyS] (.node [wY,wg6,wiC,wmE,wtt,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llllr_ok : everyKey (rowOK 5 level5) level6llllr = true := by decide +kernel
def level6llll : BinaryTree (List W) := .node [wK,wg6,wl2,wmE,wp6,wtt,wwe] level6lllll level6llllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llll_ok : everyKey (rowOK 5 level5) level6llll = true := by
  change (_ && everyKey (rowOK 5 level5) level6lllll && everyKey (rowOK 5 level5) level6llllr) = true
  rw [level6lllll_ok, level6llllr_ok]
  decide +kernel
def level6lllrl : BinaryTree (List W) := (.node [w6,wg6,wmE,wp6,wwe,wyr,wyS] (.node [w6,wcp,wg6,wmE,wp6,wwe] (.node [w4,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wY,wg6,wmE,wp6,wtt,wwe,wAH] (.node [wY,wg6,wmE,wp6,wtt,wwe,wAo] (.node [wY,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) (.node [wY,wg6,wmE,wp6,wtt,wwe,wAu] .nil .nil)) (.node [wY,wg6,wmE,wtt,wwe,wyS,wA8] (.node [wY,wg6,wmE,wp6,wtt,wwe,wAR] .nil .nil) .nil)) (.node [w6,wbY,wg6,wmE,wp6,wwe,wyS] (.node [w6,wa9,wg6,wmE,wp6,wwe,wyS] (.node [w5,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [w6,wcp,wg6,wmE,wp6,wtt,wwe] (.node [w6,wb7,wg6,wmE,wp6,wwe,wyS] .nil .nil) .nil))) (.node [w6,wg6,wla,wmE,wp6,wwe,wyS] (.node [w6,wg6,whW,wmE,wp6,wwe,wyS] (.node [w6,wc2,wg6,wmE,wtt,wwe,wyS] (.node [w6,wcp,wg6,wmE,wp6,wwe,wyS] .nil .nil) .nil) (.node [w6,wg6,wjl,wmE,wtt,wwe,wyS] (.node [w6,wg6,wiC,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [w6,wg6,wmE,wp6,wtt,wwe,wyS] (.node [w6,wg6,wmE,wp6,wsY,wwe,wyS] (.node [w6,wg6,wmE,wn8,wp6,wwe,wyS] .nil .nil) .nil) (.node [w6,wg6,wmE,wp6,wuS,wwe,wyS] (.node [w6,wg6,wmE,wp6,wtt,wwe,wAH] .nil .nil) .nil)))) (.node [w9,wg6,wjl,wmE,wtt,wwe,wyS] (.node [w9,wbg,wg6,wmE,wp6,wtt,wwe] (.node [w9,waT,wg6,wmE,wp6,wtt,wyS] (.node [w7,wg6,wmE,wp6,wtt,wwe,wyS] (.node [w6,wg6,wmE,wtt,wwe,wyS,wA8] .nil .nil) (.node [w8,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil)) (.node [w9,wbg,wg6,wmE,wp6,wtt] (.node [w9,wa0,wg6,wmE,wp6,wtt,wyS] .nil .nil) .nil)) (.node [w9,wc2,wg6,wmE,wtt,wwe,wyS] (.node [w9,wci,wg6,wmE,wp6,wtt,wyS] (.node [w9,wbg,wg6,wmE,wp6,wtt,wyS] .nil .nil) .nil) (.node [w9,wg6,wiC,wmE,wtt,wwe,wyS] (.node [w9,wg6,wie,wmE,wp6,wtt,wyS] .nil .nil) .nil))) (.node [w9,wg6,wmE,wp6,wtt,wxz,wyS] (.node [w9,wg6,wmE,wp6,wtt,wvJ,wyS] (.node [w9,wg6,wmE,woH,wp6,wtt,wyS] (.node [w9,wg6,wlC,wmE,wp6,wtt,wyS] .nil .nil) .nil) (.node [w9,wg6,wmE,wp6,wtt,wwe,wAR] (.node [w9,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil)) (.node [waa,wg6,wmE,wp6,wtt,wwe,wyS] (.node [w9,wg6,wmE,wtt,wwe,wyS,wA8] (.node [w9,wg6,wmE,wp6,wtt,wyr,wyS] .nil .nil) .nil) (.node [wac,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wab,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllrl_ok : everyKey (rowOK 5 level5) level6lllrl = true := by decide +kernel
def level6lllrr : BinaryTree (List W) := (.node [waD,wg6,wmE,wp6,wtt,wwe,wyS] (.node [war,wg6,wmE,wp6,wtt,wwe,wyS] (.node [waf,wg6,wmE,wtt,wwe,wA8] (.node [waf,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wae,wg6,wmE,wp6,wtt,wwe,wA1] (.node [wae,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) (.node [waf,wg6,wmE,wp6,wtt,wwe] .nil .nil)) (.node [waf,wg6,wmE,wtt,wwe,wyS,wA8] (.node [waf,wg6,wmE,wp6,wtt,wwe,wA8] .nil .nil) .nil)) (.node [wap,wg6,wjl,wmE,wtt,wwe,wyS] (.node [wak,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wah,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [waq,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wap,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wax,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wau,wc2,wg6,wmE,wtt,wwe,wyS] (.node [wat,wg6,wmE,wp6,wtt,wwe,wyS] (.node [was,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [waw,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wau,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil)) (.node [waA,wg6,wmE,wp6,wtt,wwe,wyS] (.node [waz,wg6,wmE,wp6,wtt,wwe,wyS] (.node [way,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [waC,wg6,wmE,wp6,wtt,wwe,wyS] (.node [waB,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil)))) (.node [waH,wg6,wmE,woX,wtt,wwe,wyS] (.node [waH,wgr,wmE,wp6,wtt,wwe,wyS] (.node [waH,waT,wg6,wmE,wp6,wtt,wyS] (.node [waF,wg6,wmE,wp6,wtt,wwe,wyS] (.node [waE,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) (.node [waG,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil)) (.node [waH,wc2,wg6,wmE,wtt,wwe,wyS] (.node [waH,wa0,wg6,wmE,wp6,wtt,wyS] .nil .nil) .nil)) (.node [waH,wg6,wjl,wmE,wtt,wwe,wyS] (.node [waH,wg6,wiC,wmE,wtt,wwe,wyS] (.node [waH,wg6,wie,wmE,wp6,wtt,wyS] .nil .nil) .nil) (.node [waH,wg6,wmE,woH,wp6,wtt,wyS] (.node [waH,wg6,wlC,wmE,wp6,wtt,wyS] .nil .nil) .nil))) (.node [waH,wie,wmE,wp6,wtt,wyS] (.node [waH,wg6,wmE,wqO,wtt,wwe,wyS] (.node [waH,wg6,wmE,wp6,wtt,wxz,wyS] (.node [waH,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [waH,wie,wmE,wp6,wtt,wwe,wyS] (.node [waH,wg6,wmE,wtt,wwe,wyS,wA8] .nil .nil) .nil)) (.node [waK,wg6,wiC,wmE,wtt,wwe,wyS] (.node [waJ,wg6,wmE,wp6,wtt,wwe,wyS] (.node [waI,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [waL,wg6,wmE,wp6,wtt,wwe,wyS] (.node [waK,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllrr_ok : everyKey (rowOK 5 level5) level6lllrr = true := by decide +kernel
def level6lllr : BinaryTree (List W) := .node [wae,wg6,wmE,wp6,wtt,wwe] level6lllrl level6lllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllr_ok : everyKey (rowOK 5 level5) level6lllr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lllrl && everyKey (rowOK 5 level5) level6lllrr) = true
  rw [level6lllrl_ok, level6lllrr_ok]
  decide +kernel
def level6lll : BinaryTree (List W) := .node [wY,wg6,wmE,wpo,wtt,wwe,wyS] level6llll level6lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lll_ok : everyKey (rowOK 5 level5) level6lll = true := by
  change (_ && everyKey (rowOK 5 level5) level6llll && everyKey (rowOK 5 level5) level6lllr) = true
  rw [level6llll_ok, level6lllr_ok]
  decide +kernel
def level6llrll : BinaryTree (List W) := (.node [waX,wg6,wmE,wp6,wtt,wwe,wyS] (.node [waT,wg6,wiC,wmE,wtt,wwe,wyS] (.node [waT,weV,wg6,wp6,wtt,wwe,wyS] (.node [waR,wg6,wmE,wp6,wtt,wwe,wyS] (.node [waO,wg6,wmE,wp6,wtt,wwe,wyS] (.node [waO,wg6,wjl,wmE,wtt,wwe,wyS] .nil .nil) (.node [waP,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil)) (.node [waT,wc2,wg6,wmE,wtt,wwe,wyS] (.node [waT,wci,wg6,wmE,wp6,wtt,wyS] .nil .nil) .nil)) (.node [waT,wfm,wg6,wp6,wtt,wyS] (.node [waT,wfm,wg6,wp6,wtt,wwe,wyS] (.node [waT,wfm,wg6,wmE,wp6,wtt,wyS] .nil .nil) .nil) (.node [waT,wg6,wiv,wp6,wtt,wwe,wyS] (.node [waT,wgr,wg6,wmE,wp6,wtt,wyS] .nil .nil) .nil))) (.node [waT,wg6,wmE,wp6,wtt,wxV,wyS] (.node [waT,wg6,wjl,wtt,wwe,wyS] (.node [waT,wg6,wjl,wp6,wtt,wwe,wyS] (.node [waT,wg6,wjl,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [waT,wg6,wmE,wp6,wtt,wwe,wyS] (.node [waT,wg6,wlC,wp6,wtt,wwe,wyS] .nil .nil) .nil)) (.node [waT,wg6,wmE,wtt,wwe,wyS,wA8] (.node [waT,wg6,wmE,wp6,wtt,wyS,wAR] (.node [waT,wg6,wmE,wp6,wtt,wyr,wyS] .nil .nil) .nil) (.node [waV,wg6,wmE,wp6,wtt,wwe,wyS] (.node [waT,wg6,wp6,wtt,wwe,wyS,wA1] .nil .nil) .nil)))) (.node [wa0,wg6,wmE,wp6,wtt,wxV,wyS] (.node [wa0,wfm,wg6,wmE,wp6,wtt,wyS] (.node [wa0,wdW,wg6,wmE,wp6,wtt,wyS] (.node [wa0,wci,wg6,wmE,wp6,wtt,wyS] (.node [waZ,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) (.node [wa0,wc2,wg6,wmE,wtt,wwe,wyS] .nil .nil)) (.node [wa0,wdW,wg6,wmE,wtt,wyS] (.node [wa0,wdW,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wa0,wg6,wjl,wmE,wtt,wwe,wyS] (.node [wa0,wg6,wiC,wmE,wtt,wwe,wyS] (.node [wa0,wgr,wg6,wmE,wp6,wtt,wyS] .nil .nil) .nil) (.node [wa0,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wa0,wg6,wmE,woH,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wa7,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wa0,wg6,wmE,wp6,wtt,wyS,wAR] (.node [wa0,wg6,wmE,wp6,wtt,wyr,wyS] (.node [wa0,wg6,wmE,wp6,wtt,wx5,wyS] .nil .nil) .nil) (.node [wa2,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wa0,wg6,wmE,wtt,wwe,wyS,wA8] .nil .nil) .nil)) (.node [wa9,wb7,wg6,wmE,wp6,wwe,wyS] (.node [wa9,wbY,wg6,wmE,wp6,wwe,wyS] (.node [wa8,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wa9,wci,wg6,wmE,wp6,wwe,wyS] (.node [wa9,wci,wg6,wmE,wp6,wtt,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrll_ok : everyKey (rowOK 5 level5) level6llrll = true := by decide +kernel
def level6llrlr : BinaryTree (List W) := (.node [wbg,wg6,wmE,wp6,wtt,wvJ,wwe] (.node [wbd,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wa9,wg6,wmE,wp6,wsK,wwe,wyS] (.node [wa9,wg6,wjl,wmE,wtt,wwe,wyS] (.node [wa9,wg6,whW,wmE,wp6,wwe,wyS] (.node [wa9,wc2,wg6,wmE,wtt,wwe,wyS] .nil .nil) (.node [wa9,wg6,wiC,wmE,wtt,wwe,wyS] .nil .nil)) (.node [wa9,wg6,wmE,wn8,wp6,wwe,wyS] (.node [wa9,wg6,wla,wmE,wp6,wwe,wyS] .nil .nil) .nil)) (.node [wa9,wg6,wmE,wp6,wuS,wwe,wyS] (.node [wa9,wg6,wmE,wp6,wtt,wyr,wyS] (.node [wa9,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wa9,wg6,wmE,wtt,wwe,wyS,wA8] (.node [wa9,wg6,wmE,wp6,wwe,wyS,wAH] .nil .nil) .nil))) (.node [wbg,wc2,wg6,wmE,wtt,wwe,wyS] (.node [wbe,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wbd,wg6,wmE,wp6,wwe,wyS] (.node [wbd,wg6,wmE,wp6,wvJ,wwe,wyS] .nil .nil) .nil) (.node [wbg,wcp,wg6,wmE,wp6,wtt,wwe] (.node [wbf,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wbg,wg6,wjl,wmE,wtt,wwe,wyS] (.node [wbg,wg6,wiC,wmE,wtt,wwe,wyS] (.node [wbg,wg6,wip,wmE,wp6,wtt,wwe] .nil .nil) .nil) (.node [wbg,wg6,wmE,wpo,wp6,wtt,wwe] (.node [wbg,wg6,wl2,wmE,wp6,wtt,wwe] .nil .nil) .nil)))) (.node [wbm,wg6,wmE,wp6,wtt,wyS] (.node [wbi,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wbg,wg6,wmE,wp6,wtt,wyS,wAR] (.node [wbg,wg6,wmE,wp6,wtt,wwe,wz7] (.node [wbg,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) (.node [wbg,wg6,wmE,wp6,wtt,wwe,wAH] .nil .nil)) (.node [wbh,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wbg,wg6,wmE,wtt,wwe,wyS,wA8] .nil .nil) .nil)) (.node [wbl,wg6,wmE,wp6,wtt,wyS] (.node [wbl,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wbj,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wbm,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wbl,wg6,wmE,wp6,wtt,wyS,wA1] .nil .nil) .nil))) (.node [wbx,wc2,wg6,wmE,wtt,wwe,wyS] (.node [wbm,wg6,wmE,wtt,wyS,wA8] (.node [wbm,wg6,wmE,wtt,wwe,wyS,wA8] (.node [wbm,wg6,wmE,wp6,wtt,wyS,wA8] .nil .nil) .nil) (.node [wbr,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wbo,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wbA,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wbz,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wbx,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wbC,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wbB,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrlr_ok : everyKey (rowOK 5 level5) level6llrlr = true := by decide +kernel
def level6llrl : BinaryTree (List W) := .node [wa9,wci,wg6,wmE,wp6,wyS] level6llrll level6llrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrl_ok : everyKey (rowOK 5 level5) level6llrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6llrll && everyKey (rowOK 5 level5) level6llrlr) = true
  rw [level6llrll_ok, level6llrlr_ok]
  decide +kernel
def level6llrrl : BinaryTree (List W) := (.node [wbN,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wbK,wg6,wjl,wmE,wtt,wwe,wyS] (.node [wbK,wbY,wg6,wmE,wp6,wwe,wyS] (.node [wbH,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wbF,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wbE,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) (.node [wbG,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil)) (.node [wbJ,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wbI,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wbK,wf9,wmE,wp6,wtt,wwe,wyS] (.node [wbK,wc2,wg6,wmE,wtt,wwe,wyS] (.node [wbK,wb7,wg6,wmE,wp6,wwe,wyS] .nil .nil) .nil) (.node [wbK,wg6,wiC,wmE,wtt,wwe,wyS] (.node [wbK,wg6,whW,wmE,wp6,wwe,wyS] .nil .nil) .nil))) (.node [wbK,wg6,wmE,wq8,wtt,wwe,wyS] (.node [wbK,wg6,wmE,wov,wtt,wwe,wyS] (.node [wbK,wg6,wmE,wn8,wp6,wwe,wyS] (.node [wbK,wg6,wla,wmE,wp6,wwe,wyS] .nil .nil) .nil) (.node [wbK,wg6,wmE,wp6,wuS,wwe,wyS] (.node [wbK,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wbK,whW,wmE,wp6,wwe,wyS] (.node [wbK,whW,wmE,wp6,wtt,wwe,wyS] (.node [wbK,wg6,wmE,wtt,wwe,wyS,wA8] .nil .nil) .nil) (.node [wbM,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wbL,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil)))) (.node [wbY,wfe,wg6,wp6,wwe,wyS] (.node [wbU,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wbQ,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wbO,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wbO,wg6,wiC,wmE,wtt,wwe,wyS] .nil .nil) (.node [wbP,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil)) (.node [wbS,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wbS,wg6,wjl,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wbY,weV,wg6,wp6,wtt,wwe,wyS] (.node [wbY,wc2,wg6,wmE,wtt,wwe,wyS] (.node [wbW,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wbY,wfe,wg6,wp6,wtt,wwe,wyS] (.node [wbY,wfe,wg6,wmE,wp6,wwe,wyS] .nil .nil) .nil))) (.node [wbY,wg6,wjl,wtt,wwe,wyS] (.node [wbY,wg6,wiC,wmE,wtt,wwe,wyS] (.node [wbY,wg6,wiv,wp6,wtt,wwe,wyS] (.node [wbY,wf9,wg6,wmE,wp6,wwe,wyS] .nil .nil) .nil) (.node [wbY,wg6,wjl,wp6,wtt,wwe,wyS] (.node [wbY,wg6,wjl,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wbY,wg6,wmE,wp6,wvk,wwe,wyS] (.node [wbY,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wbY,wg6,wla,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wbY,wg6,wmE,wp6,wwe,wyS,wAH] (.node [wbY,wg6,wmE,wp6,wwe,wyr,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrrl_ok : everyKey (rowOK 5 level5) level6llrrl = true := by decide +kernel
def level6llrrr : BinaryTree (List W) := (.node [wci,wc2,wg6,wmE,wtt,wwe,wyS] (.node [wb7,wg6,wjl,wmE,wtt,wwe,wyS] (.node [wb7,wdH,wg6,wmE,wp6,wwe,wyS] (.node [wb4,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wb0,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wbY,wg6,wp6,wtt,wwe,wyS,wA1] .nil .nil) (.node [wb2,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil)) (.node [wb7,wc2,wg6,wmE,wtt,wwe,wyS] (.node [wb6,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wb7,wfe,wg6,wmE,wp6,wwe,wyS] (.node [wb7,wdH,wg6,wmE,wwe,wyS] (.node [wb7,wdH,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wb7,wg6,wiC,wmE,wtt,wwe,wyS] (.node [wb7,wf9,wg6,wmE,wp6,wwe,wyS] .nil .nil) .nil))) (.node [wb7,wg6,wmE,wp6,wwe,wyS,wAH] (.node [wb7,wg6,wmE,wp6,wvk,wwe,wyS] (.node [wb7,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wb7,wg6,wmE,wn8,wtt,wwe,wyS] .nil .nil) .nil) (.node [wb7,wg6,wmE,wp6,wwe,wyr,wyS] (.node [wb7,wg6,wmE,wp6,wvy,wwe,wyS] .nil .nil) .nil)) (.node [wcb,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wb9,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wb7,wg6,wmE,wtt,wwe,wyS,wA8] .nil .nil) .nil) (.node [wch,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wcg,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil)))) (.node [wcm,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wci,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wci,wg6,wlC,wmE,wp6,wtt,wyS] (.node [wci,wg6,wiC,wmE,wtt,wwe,wyS] (.node [wci,wg6,wie,wmE,wp6,wtt,wyS] .nil .nil) (.node [wci,wg6,wjl,wmE,wtt,wwe,wyS] .nil .nil)) (.node [wci,wg6,wmE,wp6,wsK,wtt,wyS] (.node [wci,wg6,wmE,woH,wp6,wtt,wyS] .nil .nil) .nil)) (.node [wci,wg6,wmE,wp6,wwe,wyr,wyS] (.node [wci,wg6,wmE,wp6,wtt,wyS,wAR] (.node [wci,wg6,wmE,wp6,wtt,wxz,wyS] .nil .nil) .nil) (.node [wcm,wg6,wmE,wp6,wsY,wtt,wyS] (.node [wci,wg6,wmE,wtt,wwe,wyS,wA8] .nil .nil) .nil))) (.node [wcp,wg6,wiC,wmE,wtt,wwe,wyS] (.node [wco,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wcn,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wcm,wg6,wmE,wp6,wtt,wyS] .nil .nil) .nil) (.node [wcp,wg6,wip,wmE,wp6,wtt,wwe] (.node [wcp,wc2,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wcp,wg6,wmE,wpo,wp6,wtt,wwe] (.node [wcp,wg6,wl2,wmE,wp6,wtt,wwe] (.node [wcp,wg6,wjl,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wcp,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wcp,wg6,wmE,wp6,wsY,wtt,wwe] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrrr_ok : everyKey (rowOK 5 level5) level6llrrr = true := by decide +kernel
def level6llrr : BinaryTree (List W) := .node [wbY,wg6,wmE,wtt,wwe,wyS,wA8] level6llrrl level6llrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrr_ok : everyKey (rowOK 5 level5) level6llrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6llrrl && everyKey (rowOK 5 level5) level6llrrr) = true
  rw [level6llrrl_ok, level6llrrr_ok]
  decide +kernel
def level6llr : BinaryTree (List W) := .node [wbD,wg6,wmE,wp6,wtt,wwe,wyS] level6llrl level6llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llr_ok : everyKey (rowOK 5 level5) level6llr = true := by
  change (_ && everyKey (rowOK 5 level5) level6llrl && everyKey (rowOK 5 level5) level6llrr) = true
  rw [level6llrl_ok, level6llrr_ok]
  decide +kernel
def level6ll : BinaryTree (List W) := .node [waM,wg6,wmE,wp6,wtt,wwe,wyS] level6lll level6llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6ll_ok : everyKey (rowOK 5 level5) level6ll = true := by
  change (_ && everyKey (rowOK 5 level5) level6lll && everyKey (rowOK 5 level5) level6llr) = true
  rw [level6lll_ok, level6llr_ok]
  decide +kernel
def level6lrlll : BinaryTree (List W) := (.node [wcQ,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wcv,wg6,wmE,wtt,wwe,wyS,wA8] (.node [wcu,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wcq,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wcp,wg6,wmE,wp6,wwe,wyS,wAH] (.node [wcp,wg6,wmE,wp6,wtt,wwe,wAR] .nil .nil) (.node [wcp,wg6,wmE,wtt,wwe,wyS,wA8] .nil .nil)) (.node [wcs,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wcr,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wcv,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wcu,wg6,wmE,wp6,wwe,wyS,wA1] (.node [wcu,wg6,wmE,wp6,wwe,wyS] .nil .nil) .nil) (.node [wcv,wg6,wmE,wp6,wwe,wyS,wA8] (.node [wcv,wg6,wmE,wp6,wwe,wyS] .nil .nil) .nil))) (.node [wcK,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wcA,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wcx,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wcv,wg6,wmE,wwe,wyS,wA8] .nil .nil) .nil) (.node [wcK,wg6,wmE,wp6,wtt,wwe] (.node [wcK,wg6,wmE,wp6,wsK,wtt,wwe] .nil .nil) .nil)) (.node [wcN,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wcM,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wcL,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wcQ,wc2,wg6,wmE,wtt,wwe,wyS] (.node [wcO,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil)))) (.node [wc2,web,wg6,wmE,wtt,wwe,wyS] (.node [wc1,wc2,wg6,wmE,wtt,wwe,wyS] (.node [wcV,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wcT,wc2,wg6,wmE,wtt,wwe,wyS] (.node [wcS,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) (.node [wcT,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil)) (.node [wcX,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wcX,wc2,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wc2,wdl,wg6,wmE,wtt,wwe,wyS] (.node [wc2,wc2,wg6,wmE,wtt,wwe,wyS] (.node [wc1,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wc2,wdW,wg6,wmE,wtt,wwe,wyS] (.node [wc2,wdH,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wc2,wfe,wg6,wmE,wtt,wwe,wyS] (.node [wc2,weV,wg6,wp6,wtt,wwe,wyS] (.node [wc2,weV,wg6,wmE,wtt,wwe,wyS] (.node [wc2,wep,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wc2,weZ,wg6,wmE,wtt,wwe,wyS] (.node [wc2,weV,wg6,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wc2,wfx,wg6,wmE,wtt,wwe,wyS] (.node [wc2,wfs,wg6,wmE,wtt,wwe,wyS] (.node [wc2,wfm,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wc2,wf9,wg6,wmE,wtt,wwe,wyS] (.node [wc2,wfN,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlll_ok : everyKey (rowOK 5 level5) level6lrlll = true := by decide +kernel
def level6lrllr : BinaryTree (List W) := (.node [wc2,wg6,wmE,wrg,wtt,wwe,wyS] (.node [wc2,wg6,wl2,wmE,wtt,wwe,wyS] (.node [wc2,wg6,wiC,wmE,wtt,wwe,wyS] (.node [wc2,wg6,wie,wmE,wtt,wwe,wyS] (.node [wc2,wg6,wg7,wmE,wtt,wwe,wyS] (.node [wc2,wgR,wg6,wmE,wtt,wwe,wyS] .nil .nil) (.node [wc2,wg6,whW,wmE,wtt,wwe,wyS] .nil .nil)) (.node [wc2,wg6,wiv,wmE,wtt,wwe,wyS] (.node [wc2,wg6,wip,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wc2,wg6,wjl,wtt,wwe,wyS] (.node [wc2,wg6,wjl,wp6,wtt,wwe,wyS] (.node [wc2,wg6,wjl,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wc2,wg6,wlC,wmE,wtt,wwe,wyS] (.node [wc2,wg6,wla,wmE,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wc2,wg6,wmE,wp6,wrx,wtt,wyS] (.node [wc2,wg6,wmE,woH,wtt,wwe,wyS] (.node [wc2,wg6,wmE,wn8,wtt,wwe,wyS] (.node [wc2,wg6,wmE,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wc2,wg6,wmE,wp6,wrg,wwe,wyS] (.node [wc2,wg6,wmE,wpo,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wc2,wg6,wmE,wp6,wtt,wwe,wzp] (.node [wc2,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wc2,wg6,wmE,wp6,wrT,wtt,wwe] .nil .nil) .nil) (.node [wc2,wg6,wmE,wp6,wt2,wwe,wyS] (.node [wc2,wg6,wmE,wp6,wtt,wwN,wyS] .nil .nil) .nil)))) (.node [wc2,wg6,wmE,wtt,wvJ,wwe,wyS] (.node [wc2,wg6,wmE,wsK,wtt,wwe,wyS] (.node [wc2,wg6,wmE,wrT,wtt,wwe] (.node [wc2,wg6,wmE,wrx,wtt,wwe,wyS] (.node [wc2,wg6,wmE,wrg,wwe,wyS] .nil .nil) (.node [wc2,wg6,wmE,wrx,wtt,wyS] .nil .nil)) (.node [wc2,wg6,wmE,wsC,wtt,wwe,wyS] (.node [wc2,wg6,wmE,wrT,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wc2,wg6,wmE,wtt,wuS,wwe,wyS] (.node [wc2,wg6,wmE,wtt,wt2,wwe,wyS] (.node [wc2,wg6,wmE,wsY,wtt,wwe,wyS] .nil .nil) .nil) (.node [wc2,wg6,wmE,wtt,wvy,wwe,wyS] (.node [wc2,wg6,wmE,wtt,wvk,wwe,wyS] .nil .nil) .nil))) (.node [wc2,wg6,wmE,wtt,wwe,wyS] (.node [wc2,wg6,wmE,wtt,wwe,wxV,wyS] (.node [wc2,wg6,wmE,wtt,wwe,wxz,wyS] (.node [wc2,wg6,wmE,wtt,wwe,wwN,wyS] .nil .nil) .nil) (.node [wc2,wg6,wmE,wtt,wwe,wyr,wyS] (.node [wc2,wg6,wmE,wtt,wwe,wx5,wyS] .nil .nil) .nil)) (.node [wc2,wg6,wmE,wtt,wwe,wyS,wAo] (.node [wc2,wg6,wmE,wtt,wwe,wyS,wz7] (.node [wc2,wg6,wmE,wtt,wwe,wyS,wzp] .nil .nil) .nil) (.node [wc2,wg6,wmE,wtt,wwe,wyS,wAH] (.node [wc2,wg6,wmE,wtt,wwe,wyS,wAu] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrllr_ok : everyKey (rowOK 5 level5) level6lrllr = true := by decide +kernel
def level6lrll : BinaryTree (List W) := .node [wc2,wgr,wg6,wmE,wtt,wwe,wyS] level6lrlll level6lrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrll_ok : everyKey (rowOK 5 level5) level6lrll = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrlll && everyKey (rowOK 5 level5) level6lrllr) = true
  rw [level6lrlll_ok, level6lrllr_ok]
  decide +kernel
def level6lrlrl : BinaryTree (List W) := (.node [wdl,wg6,wp6,wtt,wwe,wyS,wA1] (.node [wdl,wg6,wjl,wp6,wtt,wwe,wyS] (.node [wdg,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wc2,wg6,wmE,wtt,wwN,wyS] (.node [wc2,wg6,wmE,wtt,wwe,wyS,wA8] (.node [wc2,wg6,wmE,wtt,wwe,wyS,wA1] .nil .nil) (.node [wc2,wg6,wmE,wtt,wwe,wzp] .nil .nil)) (.node [wdf,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wc2,wg6,wmE,wt2,wwe,wyS] .nil .nil) .nil)) (.node [wdl,wg6,wiv,wp6,wtt,wwe,wyS] (.node [wdl,wfx,wmE,wp6,wtt,wwe,wyS] (.node [wdl,weV,wg6,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wdl,wg6,wjl,wmE,wtt,wwe,wyS] (.node [wdl,wg6,wiC,wmE,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wdl,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wdl,wg6,wmE,wp6,wre,wwe,wyS] (.node [wdl,wg6,wmE,wpi,wtt,wwe,wyS] (.node [wdl,wg6,wjl,wtt,wwe,wyS] .nil .nil) .nil) (.node [wdl,wg6,wmE,wp6,wrM,wtt,wwe] (.node [wdl,wg6,wmE,wp6,wrv,wtt,wyS] .nil .nil) .nil)) (.node [wdl,wg6,wmE,wp6,wt4,wwe,wyS] (.node [wdl,wg6,wmE,wp6,wtt,wwP,wyS] (.node [wdl,wg6,wmE,wp6,wtt,wwe,wzr] .nil .nil) .nil) (.node [wdl,wg6,wmE,wtt,wwe,wyS,wA8] (.node [wdl,wg6,wmE,wsB,wtt,wwe,wyS] .nil .nil) .nil)))) (.node [wdD,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wdp,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wdm,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wdl,wp6,wtt,wwe,wyS,wA1] (.node [wdl,wmE,wp6,wtt,wwe,wyS,wA1] .nil .nil) (.node [wdm,wg6,wiC,wmE,wtt,wwe,wyS] .nil .nil)) (.node [wdo,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wdm,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wdw,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wdv,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wdu,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wdC,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wdB,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wdH,wg6,wiC,wmE,wtt,wwe,wyS] (.node [wdG,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wdF,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wdE,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wdH,web,wg6,wmE,wtt,wwe,wyS] (.node [wdH,wdW,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wdH,wg6,wmE,wn8,wp6,wwe,wyS] (.node [wdH,wg6,wkw,wp6,wtt,wwe,wyS] (.node [wdH,wg6,wjl,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wdH,wg6,wmE,wpo,wtt,wwe,wyS] (.node [wdH,wg6,wmE,woH,wtt,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlrl_ok : everyKey (rowOK 5 level5) level6lrlrl = true := by decide +kernel
def level6lrlrr : BinaryTree (List W) := (.node [wdW,wg6,wmE,wp6,wtt,wwe,wzy] (.node [wdU,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wdH,wg6,wnG,wp6,wtt,wwe,wyS] (.node [wdH,wg6,wmE,wp6,wtt,wwT,wyS] (.node [wdH,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wdH,wg6,wmE,wp6,wq4,wtt,wwe] .nil .nil) (.node [wdH,wg6,wmE,wp6,wtt,wwe,wzv] .nil .nil)) (.node [wdH,wg6,wmE,wtt,wwe,wyS,wA8] (.node [wdH,wg6,wmE,wtt,wvy,wwe,wyS] .nil .nil) .nil)) (.node [wdT,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wdM,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wdL,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wdT,wg6,wmE,wtt,wwe,wyS] (.node [wdT,wg6,wmE,wtt,wvk,wwe,wyS] .nil .nil) .nil))) (.node [wdW,wg6,wmE,wn8,wtt,wwe,wyS] (.node [wdW,wg6,wiC,wmE,wtt,wwe,wyS] (.node [wdW,web,wg6,wmE,wtt,wwe,wyS] (.node [wdV,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wdW,wg6,wj2,wp6,wtt,wwe,wyS] (.node [wdW,wg6,wjl,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wdW,wg6,wmE,wpo,wtt,wwe,wyS] (.node [wdW,wg6,wmE,woH,wp6,wtt,wyS] (.node [wdW,wg6,wmE,woj,wp6,wwe,wyS] .nil .nil) .nil) (.node [wdW,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wdW,wg6,wmE,wp6,wqK,wtt,wwe] .nil .nil) .nil)))) (.node [web,wg6,wiC,wmE,wtt,wwe,wyS] (.node [wd5,wg6,wmE,wtt,wwe,wxV,wyS] (.node [wdW,wg6,wnO,wp6,wtt,wwe,wyS] (.node [wdW,wg6,wmE,wtt,wwe,wx5,wyS] (.node [wdW,wg6,wmE,wp6,wt9,wwe,wyS] .nil .nil) (.node [wdW,wg6,wmE,wtt,wwe,wyS,wA8] .nil .nil)) (.node [wd5,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wd0,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wd8,wg6,wmE,wtt,wwe,wyr,wyS] (.node [wd8,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wd5,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wea,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wd8,wg6,wmE,wtt,wwe,wyS] .nil .nil) .nil))) (.node [web,wg6,wmE,woN,wp6,wtt,wyS] (.node [web,wg6,wmE,wn8,wtt,wwe,wyS] (.node [web,wg6,wjF,wp6,wtt,wwe,wyS] (.node [web,wg6,wjl,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [web,wg6,wmE,woH,wtt,wwe,wyS] (.node [web,wg6,wmE,woe,wp6,wwe,wyS] .nil .nil) .nil)) (.node [web,wg6,wmE,wp6,wtt,wwX,wyS] (.node [web,wg6,wmE,wp6,wtt,wwe,wyS] (.node [web,wg6,wmE,wpo,wp6,wtt,wwe] .nil .nil) .nil) (.node [web,wg6,wmE,wtt,wwe,wyS,wAu] (.node [web,wg6,wmE,wp6,wud,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlrr_ok : everyKey (rowOK 5 level5) level6lrlrr = true := by decide +kernel
def level6lrlr : BinaryTree (List W) := .node [wdH,wg6,wmE,wp6,wqY,wtt,wyS] level6lrlrl level6lrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlr_ok : everyKey (rowOK 5 level5) level6lrlr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrlrl && everyKey (rowOK 5 level5) level6lrlrr) = true
  rw [level6lrlrl_ok, level6lrlrr_ok]
  decide +kernel
def level6lrl : BinaryTree (List W) := .node [wc2,wg6,wmE,wtt,wwe,wyS,wAR] level6lrll level6lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrl_ok : everyKey (rowOK 5 level5) level6lrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrll && everyKey (rowOK 5 level5) level6lrlr) = true
  rw [level6lrll_ok, level6lrlr_ok]
  decide +kernel
def level6lrrll : BinaryTree (List W) := (.node [weC,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wep,wg6,wjl,wmE,wtt,wwe,wyS] (.node [wek,wg6,wmE,wtt,wwe,wyS,wAH] (.node [wei,wg6,wmE,wtt,wwe,wyS,wAo] (.node [wei,wg6,wmE,wp6,wtt,wwe,wyS] (.node [web,wg6,wnV,wp6,wtt,wwe,wyS] .nil .nil) (.node [wei,wg6,wmE,wtt,wwe,wyS] .nil .nil)) (.node [wek,wg6,wmE,wtt,wwe,wyS] (.node [wek,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wem,wg6,wmE,wtt,wwe,wyS,wAR] (.node [wem,wg6,wmE,wtt,wwe,wyS] (.node [wem,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wep,wg6,wiC,wmE,wtt,wwe,wyS] (.node [wep,weZ,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil))) (.node [weq,wg6,wmE,wtt,wwe,wyS] (.node [wep,wiC,wmE,wp6,wtt,wwe,wyS] (.node [wep,wg6,wmE,wtt,wwe,wyS,wA8] (.node [wep,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [weq,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wep,wiC,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wet,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wer,wg6,wmE,wp6,wtt,wwe,wyS] (.node [weq,wg6,wmE,wtt,wwe,wyS,wA1] .nil .nil) .nil) (.node [weA,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wew,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil)))) (.node [weV,wg6,wiC,wmE,wtt,wwe,wyS] (.node [weQ,wg6,wmE,wp6,wtt,wwe,wyS] (.node [weJ,wg6,wmE,wp6,wtt,wwe,wyS] (.node [weF,wg6,wmE,wp6,wtt,wwe,wyS] (.node [weD,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) (.node [weH,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil)) (.node [weP,wg6,wmE,wp6,wtt,wwe,wyS] (.node [weL,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil)) (.node [weT,wg6,wmE,wp6,wtt,wwe,wyS] (.node [weS,wg6,wmE,wp6,wtt,wwe,wyS] (.node [weR,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [weV,wfx,wg6,wp6,wtt,wwe,wyS] (.node [weU,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil))) (.node [weV,wg6,wp6,wtt,wwe,wxV,wyS] (.node [weV,wg6,wmE,wtt,wwe,wyS,wA8] (.node [weV,wg6,wmE,wp6,wtt,wwe,wyS] (.node [weV,wg6,wjl,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [weV,wg6,wp6,wtt,wvk,wwe,wyS] (.node [weV,wg6,wp6,wsC,wtt,wwe,wyS] .nil .nil) .nil)) (.node [weY,wg6,wmE,wp6,wtt,wwe,wyS] (.node [weX,wg6,wmE,wp6,wtt,wwe,wyS] (.node [weV,wg6,wp6,wtt,wwe,wyS,wAo] .nil .nil) .nil) (.node [weZ,wg6,wjl,wmE,wtt,wwe,wyS] (.node [weZ,wg6,wiC,wmE,wtt,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrll_ok : everyKey (rowOK 5 level5) level6lrrll = true := by decide +kernel
def level6lrrlr : BinaryTree (List W) := (.node [wfe,wg6,wmE,wp6,wtt,wwe,wzK] (.node [wfb,wg6,wmE,wp6,wtt,wwe,wyS] (.node [we4,wg6,wmE,wp6,wtt,wwe,wyS] (.node [we0,wg6,wmE,wp6,wtt,wwe,wyS] (.node [weZ,wmE,wp6,wtt,wwe,wyS,wA8] (.node [weZ,wg6,wmE,wtt,wwe,wyS,wA8] .nil .nil) (.node [weZ,wmE,wtt,wwe,wyS,wA8] .nil .nil)) (.node [we2,wg6,wmE,wp6,wtt,wwe,wyS] (.node [we1,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil)) (.node [we8,wg6,wmE,wp6,wtt,wwe,wyS] (.node [we6,wg6,wmE,wp6,wtt,wwe,wyS] (.node [we5,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wfa,wg6,wmE,wp6,wtt,wwe,wyS] (.node [we9,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wfe,wg6,wkM,wmE,wtt,wwe,wyS] (.node [wfe,wg6,whW,wmE,wp6,wwe,wyS] (.node [wfd,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wfc,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wfe,wg6,wjl,wmE,wtt,wwe,wyS] (.node [wfe,wg6,wiC,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wfe,wg6,wmE,wnp,wp6,wtt,wwe] (.node [wfe,wg6,wmE,wni,wp6,wtt,wyS] (.node [wfe,wg6,wla,wmE,wp6,wwe,wyS] .nil .nil) .nil) (.node [wfe,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wfe,wg6,wmE,wn8,wp6,wwe,wyS] .nil .nil) .nil)))) (.node [wfm,wg6,wjl,wmE,wtt,wwe,wyS] (.node [wfh,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wfe,wg6,wmE,wtt,wwe,wyS,wA8] (.node [wfe,wg6,wmE,wp6,wuS,wwe,wyS] (.node [wfe,wg6,wmE,wp6,wtt,ww9,wyS] .nil .nil) (.node [wfe,wg6,wmE,wrs,wtt,wwe,wyS] .nil .nil)) (.node [wfg,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wfe,wg6,wp6,wtt,wvk,wwe,wyS] .nil .nil) .nil)) (.node [wfl,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wfk,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wfj,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wfm,wg6,wiC,wmE,wtt,wwe,wyS] (.node [wfm,wg6,wie,wmE,wp6,wtt,wyS] .nil .nil) .nil))) (.node [wfm,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wfm,wg6,wlC,wmE,wp6,wtt,wyS] (.node [wfm,wg6,wll,wmE,wp6,wwe,wyS] (.node [wfm,wg6,wkf,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wfm,wg6,wmE,woH,wp6,wtt,wyS] (.node [wfm,wg6,wmE,wm7,wp6,wtt,wwe] .nil .nil) .nil)) (.node [wfm,wg6,wmE,wp6,wuq,wwe,wyS] (.node [wfm,wg6,wmE,wp6,wtt,wxz,wyS] (.node [wfm,wg6,wmE,wp6,wtt,wwe,wzN] .nil .nil) .nil) (.node [wfm,wg6,wmE,wtt,wwe,wyS,wA8] (.node [wfm,wg6,wmE,wrG,wtt,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrlr_ok : everyKey (rowOK 5 level5) level6lrrlr = true := by decide +kernel
def level6lrrl : BinaryTree (List W) := .node [weZ,wg6,wmE,wp6,wtt,wwe,wyS] level6lrrll level6lrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrl_ok : everyKey (rowOK 5 level5) level6lrrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrrll && everyKey (rowOK 5 level5) level6lrrlr) = true
  rw [level6lrrll_ok, level6lrrlr_ok]
  decide +kernel
def level6lrrrl : BinaryTree (List W) := (.node [wfx,wg6,wjl,wmE,wtt,wwe,wyS] (.node [wfs,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wfs,wg6,wjl,wmE,wtt,wwe,wyS] (.node [wfr,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wfp,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wfo,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) (.node [wfq,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil)) (.node [wfs,wg6,wiC,wmE,wtt,wwe,wyS] (.node [wfs,wg6,wip,wmE,wp6,wtt,wwe] .nil .nil) .nil)) (.node [wfs,wg6,wlI,wmE,wp6,wtt,wyS] (.node [wfs,wg6,wlg,wmE,wp6,wwe,wyS] (.node [wfs,wg6,wjK,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wfs,wg6,wmE,wpo,wp6,wtt,wwe] (.node [wfs,wg6,wl2,wmE,wp6,wtt,wwe] .nil .nil) .nil))) (.node [wfs,wg6,wp6,wtt,wwe,wyS,wAo] (.node [wfs,wg6,wmE,wp6,wuu,wwe,wyS] (.node [wfs,wg6,wmE,wp6,wtt,wxd,wyS] (.node [wfs,wg6,wmE,wp6,wtt,wwe,wz7] .nil .nil) .nil) (.node [wfs,wg6,wmE,wtt,wwe,wyS,wA8] (.node [wfs,wg6,wmE,wrY,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wfw,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wfv,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wfu,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wfx,wg6,wiC,wmE,wtt,wwe,wyS] (.node [wfx,wg6,wiv,wp6,wtt,wwe,wyS] .nil .nil) .nil)))) (.node [wfz,wg6,wp6,wtt,wwe,wyS,wA8] (.node [wfx,wg6,wp6,wtt,wwe,wyS,wA1] (.node [wfx,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wfx,wg6,wjl,wtt,wwe,wyS] (.node [wfx,wg6,wjl,wp6,wtt,wwe,wyS] .nil .nil) (.node [wfx,wg6,wjt,wmE,wtt,wwe,wyS] .nil .nil)) (.node [wfx,wg6,wmE,wtt,wwe,wyS,wA8] (.node [wfx,wg6,wmE,wr5,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wfz,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wfx,wiv,wp6,wtt,wwe,wyS] (.node [wfx,wiv,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wfz,wg6,wp6,wtt,wwe,wyS] (.node [wfz,wg6,wmE,wtt,wwe,wyS,wA8] .nil .nil) .nil))) (.node [wfN,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wfC,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wfA,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wfz,wg6,wtt,wwe,wyS,wA8] .nil .nil) .nil) (.node [wfK,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wfF,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wfU,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wfS,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wfP,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wfZ,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wfX,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrrl_ok : everyKey (rowOK 5 level5) level6lrrrl = true := by decide +kernel
def level6lrrrr : BinaryTree (List W) := (.node [wgb,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wf9,wg6,wmE,wn8,wp6,wwe,wyS] (.node [wf9,wg6,wjl,wmE,wtt,wwe,wyS] (.node [wf8,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wf7,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wf6,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) (.node [wf8,wg6,wjl,wmE,wtt,wwe,wyS] .nil .nil)) (.node [wf9,wg6,wiC,wmE,wtt,wwe,wyS] (.node [wf9,wg6,whW,wmE,wp6,wwe,wyS] .nil .nil) .nil)) (.node [wf9,wg6,wkX,wmE,wp6,wtt,wyS] (.node [wf9,wg6,wkK,wmE,wtt,wwe,wyS] (.node [wf9,wg6,wks,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wf9,wg6,wla,wmE,wp6,wwe,wyS] (.node [wf9,wg6,wk2,wmE,wp6,wtt,wwe] .nil .nil) .nil))) (.node [wf9,wg6,wmE,wtt,wwe,wyS,wA8] (.node [wf9,wg6,wmE,wp6,wtt,wxj,wyS] (.node [wf9,wg6,wmE,wp6,wtt,wwe,wzT] (.node [wf9,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wf9,wg6,wmE,wtt,wvw,wwe,wyS] (.node [wf9,wg6,wmE,wp6,wuS,wwe,wyS] .nil .nil) .nil)) (.node [wf9,wmE,wp6,wuS,wwe,wyS] (.node [wf9,wmE,wp6,wtt,wuS,wwe,wyS] (.node [wf9,wg6,wp6,wtt,wvg,wwe,wyS] .nil .nil) .nil) (.node [wga,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wga,wg6,wiC,wmE,wtt,wwe,wyS] .nil .nil) .nil)))) (.node [wgr,wg6,wh8,wmE,wp6,wwe,wyS] (.node [wgl,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wge,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wgd,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wgc,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wgj,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wgf,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wgp,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wgn,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wgm,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wgq,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wgq,wg6,wjl,wmE,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wgr,wg6,wkn,wmE,wp6,wtt,wwe] (.node [wgr,wg6,wjl,wmE,wtt,wwe,wyS] (.node [wgr,wg6,wiC,wmE,wtt,wwe,wyS] (.node [wgr,wg6,wie,wmE,wp6,wtt,wyS] .nil .nil) .nil) (.node [wgr,wg6,wkc,wmE,wtt,wwe,wyS] (.node [wgr,wg6,wjY,wp6,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wgr,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wgr,wg6,wmE,woH,wp6,wtt,wyS] (.node [wgr,wg6,wlC,wmE,wp6,wtt,wyS] .nil .nil) .nil) (.node [wgr,wg6,wmE,wp6,wtt,wxz,wyS] (.node [wgr,wg6,wmE,wp6,wtt,wwe,wz0] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrrr_ok : everyKey (rowOK 5 level5) level6lrrrr = true := by decide +kernel
def level6lrrr : BinaryTree (List W) := .node [wf4,wg6,wmE,wp6,wtt,wwe,wyS] level6lrrrl level6lrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrr_ok : everyKey (rowOK 5 level5) level6lrrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrrrl && everyKey (rowOK 5 level5) level6lrrrr) = true
  rw [level6lrrrl_ok, level6lrrrr_ok]
  decide +kernel
def level6lrr : BinaryTree (List W) := .node [wfm,wg6,wp6,wtt,wwe,wxV,wyS] level6lrrl level6lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrr_ok : everyKey (rowOK 5 level5) level6lrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrrl && everyKey (rowOK 5 level5) level6lrrr) = true
  rw [level6lrrl_ok, level6lrrr_ok]
  decide +kernel
def level6lr : BinaryTree (List W) := .node [web,wg6,wmE,wtt,wwe,wyS,wA8] level6lrl level6lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lr_ok : everyKey (rowOK 5 level5) level6lr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrl && everyKey (rowOK 5 level5) level6lrr) = true
  rw [level6lrl_ok, level6lrr_ok]
  decide +kernel
def level6l : BinaryTree (List W) := .node [wcp,wg6,wmE,wp6,wtt,wwe,wz7] level6ll level6lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6l_ok : everyKey (rowOK 5 level5) level6l = true := by
  change (_ && everyKey (rowOK 5 level5) level6ll && everyKey (rowOK 5 level5) level6lr) = true
  rw [level6ll_ok, level6lr_ok]
  decide +kernel
def level6rllll : BinaryTree (List W) := (.node [wgR,wg6,wi5,wp6,wtt,wwe,wyS] (.node [wgB,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wgs,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wgr,wmE,wp6,wtt,wwe,wxz,wyS] (.node [wgr,wg6,wmE,wtt,wwe,wyS,wA8] (.node [wgr,wg6,wmE,wtt,wwe,wx3,wyS] .nil .nil) (.node [wgr,wg6,wp6,wtt,wwe,wxR,wyS] .nil .nil)) (.node [wgs,wg6,wiC,wmE,wtt,wwe,wyS] (.node [wgr,wmE,wp6,wtt,wxz,wyS] .nil .nil) .nil)) (.node [wgv,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wgu,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wgt,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wgz,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wgw,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wgN,wg6,wjl,wmE,wtt,wwe,wyS] (.node [wgG,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wgD,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wgC,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wgI,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wgI,wg6,wjl,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wgR,wg6,wil,wmE,wp6,wtt,wyS] (.node [wgR,wg6,wh3,wmE,wp6,wwe,wyS] (.node [wgN,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wgR,wg6,wiC,wmE,wtt,wwe,wyS] (.node [wgR,wg6,wip,wmE,wp6,wtt,wwe] .nil .nil) .nil)))) (.node [wgR,wmE,wp6,wtt,wwe,wz7] (.node [wgR,wg6,wmE,wp6,wtt,wxs,wyS] (.node [wgR,wg6,wmE,wpo,wp6,wtt,wwe] (.node [wgR,wg6,wjl,wmE,wtt,wwe,wyS] (.node [wgR,wg6,wja,wmE,wtt,wwe,wyS] .nil .nil) (.node [wgR,wg6,wl2,wmE,wp6,wtt,wwe] .nil .nil)) (.node [wgR,wg6,wmE,wp6,wtt,wwe,wz7] (.node [wgR,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wgR,wg6,wmE,wtt,wwe,wyS,wA8] (.node [wgR,wg6,wmE,wtt,wwe,wyS,wAs] (.node [wgR,wg6,wmE,wp6,wuL,wwe,wyS] .nil .nil) .nil) (.node [wgR,wmE,wp6,wtt,wwe,wyS,wz7] (.node [wgR,wg6,wp6,wtt,wwe,wyS,wAk] .nil .nil) .nil))) (.node [wgX,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wgT,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wgS,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wgS,wg6,wiC,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wgV,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wgU,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg1,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wg0,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wgZ,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg4,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wg2,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllll_ok : everyKey (rowOK 5 level5) level6rllll = true := by decide +kernel
def level6rlllr : BinaryTree (List W) := (.node [wg6,whN,wmE,wp6,wtt,wwe,wyS] (.node [wg6,whp,wmE,wp6,wtt,wwe,wyS] (.node [wg6,whd,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wg7,wmE,wtt,wwe,wyS] (.node [wg6,wg6,wmE,wtt,wwe,wyS,wA8] (.node [wg6,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) (.node [wg6,wg7,wmE,wp6,wtt,wwe,wyS] .nil .nil)) (.node [wg6,wha,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wg8,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,whj,wmE,wp6,wtt,wwe,wyS] (.node [wg6,whi,wmE,wp6,wtt,wwe,wyS] (.node [wg6,whh,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,who,wmE,wp6,wtt,wwe,wyS] (.node [wg6,whk,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wg6,whA,wmE,wp6,wtt,wwe,wyS] (.node [wg6,whx,wmE,wp6,wtt,wwe,wyS] (.node [wg6,whr,wmE,wp6,wtt,wwe,wyS] (.node [wg6,whq,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,whz,wmE,wp6,wtt,wwe,wyS] (.node [wg6,why,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,whK,wmE,wp6,wtt,wwe,wyS] (.node [wg6,whI,wmE,wp6,wtt,wwe,wyS] (.node [wg6,whB,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,whM,wmE,wp6,wtt,wwe,wyS] (.node [wg6,whL,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil)))) (.node [wg6,whW,wmE,wtt,wwe,wyS,wA8] (.node [wg6,whW,wiC,wmE,wtt,wwe,wyS] (.node [wg6,whU,wmE,wp6,wtt,wwe,wyS] (.node [wg6,whS,wmE,wp6,wtt,wwe,wyS] (.node [wg6,whO,wmE,wp6,wtt,wwe,wyS] .nil .nil) (.node [wg6,whT,wmE,wp6,wtt,wwe,wyS] .nil .nil)) (.node [wg6,whV,wmE,wp6,wtt,wwe,wyS] (.node [wg6,whV,wiC,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,whW,wmE,wp6,wvk,wwe,wyS] (.node [wg6,whW,wmE,wp6,wtt,wwe,wyS] (.node [wg6,whW,wjl,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,whW,wmE,wp6,wwe,wyS,wAH] (.node [wg6,whW,wmE,wp6,wwe,wyr,wyS] .nil .nil) .nil))) (.node [wg6,wh8,wmE,wp6,wwe,wyS] (.node [wg6,wh3,wmE,wp6,wtt,wwe,wyS] (.node [wg6,whX,wmE,wp6,wtt,wwe,wyS] (.node [wg6,whX,wjl,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wh8,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wh3,wmE,wp6,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wid,wiC,wmE,wtt,wwe,wyS] (.node [wg6,wic,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wib,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wie,wiC,wmE,wtt,wwe,wyS] (.node [wg6,wid,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlllr_ok : everyKey (rowOK 5 level5) level6rlllr = true := by decide +kernel
def level6rlll : BinaryTree (List W) := .node [wg6,wg6,wiC,wmE,wtt,wwe,wyS] level6rllll level6rlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlll_ok : everyKey (rowOK 5 level5) level6rlll = true := by
  change (_ && everyKey (rowOK 5 level5) level6rllll && everyKey (rowOK 5 level5) level6rlllr) = true
  rw [level6rllll_ok, level6rlllr_ok]
  decide +kernel
def level6rllrl : BinaryTree (List W) := (.node [wg6,wiv,wiC,wmE,wtt,wwe,wyS] (.node [wg6,wip,wiC,wmE,wtt,wwe,wyS] (.node [wg6,wif,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wie,wmE,wp6,wtt,wyS,wAR] (.node [wg6,wie,wmE,wp6,wtt,wxV,wyS] (.node [wg6,wie,wmE,wp6,wtt,wwe,wyS] .nil .nil) (.node [wg6,wie,wmE,wp6,wtt,wyr,wyS] .nil .nil)) (.node [wg6,wif,wjl,wmE,wtt,wwe,wyS] (.node [wg6,wie,wmE,wtt,wwe,wyS,wA8] .nil .nil) .nil)) (.node [wg6,win,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wil,wmE,wp6,wtt,wyS] (.node [wg6,wil,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wio,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wio,wiC,wmE,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wip,wmE,wtt,wwe,wyS,wA8] (.node [wg6,wip,wmE,wp6,wtt,wwe,wAo] (.node [wg6,wip,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wip,wjl,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wip,wmE,wp6,wtt,wwe,wAR] (.node [wg6,wip,wmE,wp6,wtt,wwe,wAH] .nil .nil) .nil)) (.node [wg6,wir,wjl,wmE,wtt,wwe,wyS] (.node [wg6,wir,wiC,wmE,wtt,wwe,wyS] (.node [wg6,wir,wiv,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wir,wmE,wtt,wwe,wyS] (.node [wg6,wir,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil)))) (.node [wg6,wiC,wmE,wn8,wtt,wwe,wyS] (.node [wg6,wiC,wiC,wmE,wtt,wwe,wyS] (.node [wg6,wiv,wp6,wtt,wvk,wwe,wyS] (.node [wg6,wiv,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wiv,wjl,wmE,wtt,wwe,wyS] .nil .nil) (.node [wg6,wiv,wmE,wtt,wwe,wyS,wA8] .nil .nil)) (.node [wg6,wiv,wp6,wtt,wwe,wyS,wAo] (.node [wg6,wiv,wp6,wtt,wwe,wxV,wyS] .nil .nil) .nil)) (.node [wg6,wiC,wlC,wmE,wtt,wwe,wyS] (.node [wg6,wiC,wla,wmE,wtt,wwe,wyS] (.node [wg6,wiC,wjl,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wiC,wmE,wmJ,wtt,wwe,wyS] (.node [wg6,wiC,wl2,wmE,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wiC,wmE,wsY,wtt,wwe,wyS] (.node [wg6,wiC,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wiC,wmE,wpo,wtt,wwe,wyS] (.node [wg6,wiC,wmE,woH,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wiC,wmE,wsK,wtt,wwe,wyS] (.node [wg6,wiC,wmE,wsC,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wiC,wmE,wtt,wvk,wwe,wyS] (.node [wg6,wiC,wmE,wtt,wuY,wwe,wyS] (.node [wg6,wiC,wmE,wtt,wuS,wwe,wyS] .nil .nil) .nil) (.node [wg6,wiC,wmE,wtt,wvJ,wwe,wyS] (.node [wg6,wiC,wmE,wtt,wvy,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllrl_ok : everyKey (rowOK 5 level5) level6rllrl = true := by decide +kernel
def level6rllrr : BinaryTree (List W) := (.node [wg6,wi5,wp6,wtt,wwe,wyS] (.node [wg6,wiC,wmE,wtt,wwe,wyS,wA8] (.node [wg6,wiC,wmE,wtt,wwe,wyS,wAa] (.node [wg6,wiC,wmE,wtt,wwe,wyr,wyS] (.node [wg6,wiC,wmE,wtt,wwe,wxV,wyS] (.node [wg6,wiC,wmE,wtt,wwe,wxD,wyS] .nil .nil) (.node [wg6,wiC,wmE,wtt,wwe,wx5,wyS] .nil .nil)) (.node [wg6,wiC,wmE,wtt,wwe,wyS,wz7] (.node [wg6,wiC,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wiC,wmE,wtt,wwe,wyS,wAH] (.node [wg6,wiC,wmE,wtt,wwe,wyS,wAu] (.node [wg6,wiC,wmE,wtt,wwe,wyS,wAo] .nil .nil) .nil) (.node [wg6,wiC,wmE,wtt,wwe,wyS,wA1] (.node [wg6,wiC,wmE,wtt,wwe,wyS,wAR] .nil .nil) .nil))) (.node [wg6,wiL,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wiI,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wiH,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wiG,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wiK,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wiJ,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wiO,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wiN,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wiM,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wi5,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wiP,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil)))) (.node [wg6,wjl,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wjl,wlC,wmE,wtt,wwe,wyS] (.node [wg6,wjc,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wja,wmE,wtt,wwe,wyS] (.node [wg6,wja,wmE,wp6,wtt,wwe,wyS] .nil .nil) (.node [wg6,wjc,wjl,wmE,wtt,wwe,wyS] .nil .nil)) (.node [wg6,wjl,wla,wmE,wtt,wwe,wyS] (.node [wg6,wjl,wjl,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wjl,wmE,wn8,wtt,wwe,wyS] (.node [wg6,wjl,wmE,wmE,wtt,wwe,wyS] (.node [wg6,wjl,wl2,wmE,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wjl,wmE,wpo,wtt,wwe,wyS] (.node [wg6,wjl,wmE,woH,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wjl,wmE,wtt,wvk,wwe,wyS] (.node [wg6,wjl,wmE,wsY,wtt,wwe,wyS] (.node [wg6,wjl,wmE,wsK,wtt,wwe,wyS] (.node [wg6,wjl,wmE,wsC,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wjl,wmE,wtt,wu3,wwe,wyS] (.node [wg6,wjl,wmE,wtt,wuS,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wjl,wmE,wtt,wwe,wxz,wyS] (.node [wg6,wjl,wmE,wtt,wvJ,wwe,wyS] (.node [wg6,wjl,wmE,wtt,wvy,wwe,wyS] .nil .nil) .nil) (.node [wg6,wjl,wmE,wtt,wwe,wxV,wyS] (.node [wg6,wjl,wmE,wtt,wwe,wxI,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllrr_ok : everyKey (rowOK 5 level5) level6rllrr = true := by decide +kernel
def level6rllr : BinaryTree (List W) := .node [wg6,wiC,wmE,wtt,wwe,wxz,wyS] level6rllrl level6rllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllr_ok : everyKey (rowOK 5 level5) level6rllr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rllrl && everyKey (rowOK 5 level5) level6rllrr) = true
  rw [level6rllrl_ok, level6rllrr_ok]
  decide +kernel
def level6rll : BinaryTree (List W) := .node [wg6,wie,wjl,wmE,wtt,wwe,wyS] level6rlll level6rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rll_ok : everyKey (rowOK 5 level5) level6rll = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlll && everyKey (rowOK 5 level5) level6rllr) = true
  rw [level6rlll_ok, level6rllr_ok]
  decide +kernel
def level6rlrll : BinaryTree (List W) := (.node [wg6,wjK,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wjl,wp6,wtt,wvk,wwe,wyS] (.node [wg6,wjl,wmE,wtt,wwe,wyS,wAH] (.node [wg6,wjl,wmE,wtt,wwe,wyS,wAf] (.node [wg6,wjl,wmE,wtt,wwe,wyS] (.node [wg6,wjl,wmE,wtt,wwe,wyr,wyS] .nil .nil) (.node [wg6,wjl,wmE,wtt,wwe,wyS,wz7] .nil .nil)) (.node [wg6,wjl,wmE,wtt,wwe,wyS,wAu] (.node [wg6,wjl,wmE,wtt,wwe,wyS,wAo] .nil .nil) .nil)) (.node [wg6,wjl,wmE,wtt,wwe,wyS,wA1] (.node [wg6,wjl,wmE,wtt,wwe,wyS,wAX] (.node [wg6,wjl,wmE,wtt,wwe,wyS,wAR] .nil .nil) .nil) (.node [wg6,wjl,wp6,wsC,wtt,wwe,wyS] (.node [wg6,wjl,wmE,wtt,wwe,wyS,wA8] .nil .nil) .nil))) (.node [wg6,wjl,wtt,wwe,wyS,wAo] (.node [wg6,wjl,wsC,wtt,wwe,wyS] (.node [wg6,wjl,wp6,wtt,wwe,wyS,wAo] (.node [wg6,wjl,wp6,wtt,wwe,wxV,wyS] .nil .nil) .nil) (.node [wg6,wjl,wtt,wwe,wxV,wyS] (.node [wg6,wjl,wtt,wvk,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wjt,wmE,wtt,wwe,wyS] (.node [wg6,wjt,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wjp,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wjF,wp6,wtt,wwe,wyS] (.node [wg6,wjF,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil)))) (.node [wg6,wks,wp6,wtt,wwe,wyS] (.node [wg6,wkc,wmE,wtt,wwe,wyS] (.node [wg6,wj2,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wjY,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wjK,wmE,wtt,wwe,wyS] .nil .nil) (.node [wg6,wjY,wp6,wtt,wwe,wyS] .nil .nil)) (.node [wg6,wkc,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wj2,wp6,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wkn,wmE,wp6,wtt,wwe] (.node [wg6,wkf,wmE,wtt,wwe,wyS] (.node [wg6,wkf,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wks,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wkn,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wkM,wmE,wtt,wwe,wyS] (.node [wg6,wkK,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wkw,wp6,wtt,wwe,wyS] (.node [wg6,wkw,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wkM,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wkK,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wk2,wmE,wp6,wtt,wwe] (.node [wg6,wkX,wmE,wp6,wtt,wyS] (.node [wg6,wkX,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wk7,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wk2,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrll_ok : everyKey (rowOK 5 level5) level6rlrll = true := by decide +kernel
def level6rlrlr : BinaryTree (List W) := (.node [wg6,wlC,wp6,wtt,wwe,wxV,wyS] (.node [wg6,wll,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wla,wp6,wvk,wwe,wyS] (.node [wg6,wla,wmE,wp6,wwe,wyS,wAH] (.node [wg6,wla,wmE,wp6,wvk,wwe,wyS] (.node [wg6,wla,wmE,wp6,wtt,wwe,wyS] .nil .nil) (.node [wg6,wla,wmE,wp6,wwe,wyr,wyS] .nil .nil)) (.node [wg6,wla,wp6,wtt,wvk,wwe,wyS] (.node [wg6,wla,wmE,wtt,wwe,wyS,wA8] .nil .nil) .nil)) (.node [wg6,wlg,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wld,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wlb,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wli,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wlg,wmE,wp6,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wlA,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wlp,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wlo,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wll,wmE,wp6,wwe,wyS] .nil .nil) .nil) (.node [wg6,wlu,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wlr,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wlC,wmE,wp6,wtt,wyr,wyS] (.node [wg6,wlC,wmE,wp6,wtt,wxV,wyS] (.node [wg6,wlC,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wlC,wmE,wtt,wwe,wyS,wA8] (.node [wg6,wlC,wmE,wp6,wtt,wyS,wAR] .nil .nil) .nil)))) (.node [wg6,wl2,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wlL,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wlI,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wlD,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wlC,wp6,wtt,wxV,wyS] .nil .nil) (.node [wg6,wlE,wmE,wp6,wtt,wwe,wyS] .nil .nil)) (.node [wg6,wlK,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wlI,wmE,wp6,wtt,wyS] .nil .nil) .nil)) (.node [wg6,wlR,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wlO,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wlM,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wlZ,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wlX,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wl2,wp6,wtt,wwe,wAo] (.node [wg6,wl2,wmE,wp6,wtt,wwe,wAR] (.node [wg6,wl2,wmE,wp6,wtt,wwe,wAH] (.node [wg6,wl2,wmE,wp6,wtt,wwe,wAo] .nil .nil) .nil) (.node [wg6,wl2,wp6,wtt,wwe,wyS,wAo] (.node [wg6,wl2,wmE,wtt,wwe,wyS,wA8] .nil .nil) .nil)) (.node [wg6,wl5,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wl4,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wl3,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wl7,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wl6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrlr_ok : everyKey (rowOK 5 level5) level6rlrlr = true := by decide +kernel
def level6rlrl : BinaryTree (List W) := .node [wg6,wk8,wmE,wp6,wtt,wwe,wyS] level6rlrll level6rlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrl_ok : everyKey (rowOK 5 level5) level6rlrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlrll && everyKey (rowOK 5 level5) level6rlrlr) = true
  rw [level6rlrll_ok, level6rlrlr_ok]
  decide +kernel
def level6rlrrl : BinaryTree (List W) := (.node [wg6,wmE,wnc,wp6,wtt,wwe,wyS] (.node [wg6,wmE,wmK,wp6,wtt,wwe,wyS] (.node [wg6,wmr,wp6,wtt,wwe,wyS] (.node [wg6,wmr,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wmi,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wmc,wmE,wp6,wtt,wwe,wyS] .nil .nil) (.node [wg6,wml,wmE,wp6,wtt,wwe,wyS] .nil .nil)) (.node [wg6,wmr,wmE,wtt,wwe,wyS,wA8] (.node [wg6,wmr,wmE,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmr,wtt,wwe,wyS,wA8] (.node [wg6,wmr,wtt,wwe,wyS] (.node [wg6,wmr,wp6,wtt,wwe,wyS,wA8] .nil .nil) .nil) (.node [wg6,wmE,wmJ,wp6,wtt,wwe,wyS] (.node [wg6,wmE,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wmE,wmX,wp6,wtt,wwe,wyS] (.node [wg6,wmE,wmR,wp6,wtt,wwe,wyS] (.node [wg6,wmE,wmM,wp6,wtt,wwe,wyS] (.node [wg6,wmE,wmL,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wmV,wp6,wtt,wwe,wyS] (.node [wg6,wmE,wmT,wp6,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wm7,wp6,wtt,wwe] (.node [wg6,wmE,wm4,wp6,wtt,wwe,wyS] (.node [wg6,wmE,wm2,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wna,wp6,wtt,wwe,wyS] (.node [wg6,wmE,wm7,wp6,wtt,wwe,wyS] .nil .nil) .nil)))) (.node [wg6,wmE,wnI,wp6,wtt,wwe,wyS] (.node [wg6,wmE,wns,wp6,wtt,wwe,wyS] (.node [wg6,wmE,wnm,wp6,wtt,wwe,wyS] (.node [wg6,wmE,wni,wp6,wtt,wwe,wyS] (.node [wg6,wmE,wnf,wp6,wtt,wwe,wyS] .nil .nil) (.node [wg6,wmE,wni,wp6,wtt,wyS] .nil .nil)) (.node [wg6,wmE,wnp,wp6,wtt,wwe,wyS] (.node [wg6,wmE,wnp,wp6,wtt,wwe] .nil .nil) .nil)) (.node [wg6,wmE,wnx,wp6,wtt,wwe,wyS] (.node [wg6,wmE,wnw,wp6,wtt,wwe,wyS] (.node [wg6,wmE,wnu,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wnH,wp6,wtt,wwe,wyS] (.node [wg6,wmE,wnG,wp6,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wmE,wn6,wp6,wtt,wwe,wyS] (.node [wg6,wmE,wnS,wp6,wtt,wwe,wyS] (.node [wg6,wmE,wnP,wp6,wtt,wwe,wyS] (.node [wg6,wmE,wnO,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wnZ,wp6,wtt,wwe,wyS] (.node [wg6,wmE,wnV,wp6,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wn8,wpo,wtt,wwe,wyS] (.node [wg6,wmE,wn8,woH,wtt,wwe,wyS] (.node [wg6,wmE,wn7,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wn8,wp6,wvk,wwe,wyS] (.node [wg6,wmE,wn8,wp6,wtt,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrrl_ok : everyKey (rowOK 5 level5) level6rlrrl = true := by decide +kernel
def level6rlrrr : BinaryTree (List W) := (.node [wg6,wmE,woH,wp6,wtt,wyr,wyS] (.node [wg6,wmE,wom,wp6,wtt,wwe,wyS] (.node [wg6,wmE,wob,wp6,wtt,wwe,wyS] (.node [wg6,wmE,wn8,wtt,wwe,wyS,wA8] (.node [wg6,wmE,wn8,wp6,wwe,wyS,wAH] (.node [wg6,wmE,wn8,wp6,wwe,wyr,wyS] .nil .nil) (.node [wg6,wmE,wn8,wtt,wvy,wwe,wyS] .nil .nil)) (.node [wg6,wmE,wn9,wp6,wtt,wwe,wyS] (.node [wg6,wmE,wn8,wvy,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wog,wp6,wtt,wwe,wyS] (.node [wg6,wmE,woe,wp6,wwe,wyS] (.node [wg6,wmE,woe,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,woj,wp6,wwe,wyS] (.node [wg6,wmE,woj,wp6,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wmE,woB,wtt,wwe,wyS] (.node [wg6,wmE,wov,wtt,wwe,wyS] (.node [wg6,wmE,wov,wp6,wtt,wwe,wyS] (.node [wg6,wmE,won,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,woB,wtt,wvk,wwe,wyS] (.node [wg6,wmE,woB,wp6,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmE,woH,wp6,wtt,wwe,wyS] (.node [wg6,wmE,woH,wpo,wtt,wwe,wyS] (.node [wg6,wmE,woG,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,woH,wp6,wtt,wx5,wyS] (.node [wg6,wmE,woH,wp6,wtt,wxV,wyS] .nil .nil) .nil)))) (.node [wg6,wmE,woX,wtt,wwe,wyS] (.node [wg6,wmE,woN,wp6,wtt,wwe,wyS] (.node [wg6,wmE,woH,wtt,wx5,wyS] (.node [wg6,wmE,woH,wtt,wwe,wx5,wyS] (.node [wg6,wmE,woH,wp6,wtt,wyS,wAR] .nil .nil) (.node [wg6,wmE,woH,wtt,wwe,wyS,wA8] .nil .nil)) (.node [wg6,wmE,woJ,wp6,wtt,wwe,wyS] (.node [wg6,wmE,woI,wp6,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmE,woQ,wp6,wtt,wwe,wyS] (.node [wg6,wmE,woP,wp6,wtt,wwe,wyS] (.node [wg6,wmE,woN,wp6,wtt,wyS] .nil .nil) .nil) (.node [wg6,wmE,woX,wp6,wtt,wwe,wyS] (.node [wg6,wmE,woR,wp6,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wmE,wpb,wtt,wwe,wyS] (.node [wg6,wmE,wo3,wtt,wwe,wyS] (.node [wg6,wmE,wo3,wtt,wwe,wxV,wyS] (.node [wg6,wmE,wo3,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wpb,wtt,wwe,wyr,wyS] (.node [wg6,wmE,wpb,wp6,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wpo,wp6,wtt,wwe,wyS] (.node [wg6,wmE,wpi,wtt,wwe,wyS] (.node [wg6,wmE,wpi,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wpo,wp6,wtt,wwe,wAu] (.node [wg6,wmE,wpo,wp6,wtt,wwe,wAo] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrrr_ok : everyKey (rowOK 5 level5) level6rlrrr = true := by decide +kernel
def level6rlrr : BinaryTree (List W) := .node [wg6,wmE,wn8,wp6,wvy,wwe,wyS] level6rlrrl level6rlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrr_ok : everyKey (rowOK 5 level5) level6rlrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlrrl && everyKey (rowOK 5 level5) level6rlrrr) = true
  rw [level6rlrrl_ok, level6rlrrr_ok]
  decide +kernel
def level6rlr : BinaryTree (List W) := .node [wg6,wl9,wmE,wp6,wtt,wwe,wyS] level6rlrl level6rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlr_ok : everyKey (rowOK 5 level5) level6rlr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlrl && everyKey (rowOK 5 level5) level6rlrr) = true
  rw [level6rlrl_ok, level6rlrr_ok]
  decide +kernel
def level6rl : BinaryTree (List W) := .node [wg6,wjl,wmE,wtt,wwe,wx5,wyS] level6rll level6rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rl_ok : everyKey (rowOK 5 level5) level6rl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rll && everyKey (rowOK 5 level5) level6rlr) = true
  rw [level6rll_ok, level6rlr_ok]
  decide +kernel
def level6rrlll : BinaryTree (List W) := (.node [wg6,wmE,wp6,wqa,wtt,wwe,wyS] (.node [wg6,wmE,wpC,wtt,wwe,wyS] (.node [wg6,wmE,wpr,wp6,wtt,wwe,wyS] (.node [wg6,wmE,wpo,wtt,wwe,wAu] (.node [wg6,wmE,wpo,wtt,wwe,wyS,wAu] (.node [wg6,wmE,wpo,wp6,wtt,wwe,wAR] .nil .nil) (.node [wg6,wmE,wpo,wtt,wwe,wyS,wA8] .nil .nil)) (.node [wg6,wmE,wpq,wp6,wtt,wwe,wyS] (.node [wg6,wmE,wpp,wp6,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wpx,wp6,wtt,wwe,wyS] (.node [wg6,wmE,wpt,wp6,wtt,wwe,wyS] (.node [wg6,wmE,wps,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wpC,wp6,wtt,wwe,wyS] (.node [wg6,wmE,wpx,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wmE,wpP,wtt,wwe,wyS] (.node [wg6,wmE,wpI,wtt,wwe,wyS] (.node [wg6,wmE,wpI,wp6,wtt,wwe,wyS] (.node [wg6,wmE,wpC,wtt,wwe,wyS,wAo] .nil .nil) .nil) (.node [wg6,wmE,wpP,wp6,wtt,wwe,wyS] (.node [wg6,wmE,wpI,wtt,wwe,wyS,wAH] .nil .nil) .nil)) (.node [wg6,wmE,wpW,wtt,wwe,wyS] (.node [wg6,wmE,wpW,wp6,wtt,wwe,wyS] (.node [wg6,wmE,wpP,wtt,wwe,wyS,wAR] .nil .nil) .nil) (.node [wg6,wmE,wp6,wp6,wtt,wwe,wyS] (.node [wg6,wmE,wpW,wtt,wwe,wyS,wA1] .nil .nil) .nil)))) (.node [wg6,wmE,wp6,wqO,wtt,wwe,wyS] (.node [wg6,wmE,wp6,wqt,wtt,wwe,wyS] (.node [wg6,wmE,wp6,wqo,wtt,wwe,wyS] (.node [wg6,wmE,wp6,wqc,wtt,wwe,wyS] (.node [wg6,wmE,wp6,wqb,wtt,wwe,wyS] .nil .nil) (.node [wg6,wmE,wp6,wqd,wtt,wwe,wyS] .nil .nil)) (.node [wg6,wmE,wp6,wqs,wtt,wwe,wyS] (.node [wg6,wmE,wp6,wqq,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wqK,wtt,wwe] (.node [wg6,wmE,wp6,wqI,wtt,wwe,wyS] (.node [wg6,wmE,wp6,wqG,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wqN,wtt,wwe,wyS] (.node [wg6,wmE,wp6,wqK,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wmE,wp6,wq4,wtt,wwe,wyS] (.node [wg6,wmE,wp6,wqY,wtt,wyS] (.node [wg6,wmE,wp6,wqY,wtt,wwe,wyS] (.node [wg6,wmE,wp6,wqW,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wq4,wtt,wwe] (.node [wg6,wmE,wp6,wq2,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wre,wtt,wwe,wyS] (.node [wg6,wmE,wp6,wq8,wtt,wwe,wyS] (.node [wg6,wmE,wp6,wq7,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wrg,wtt,wwe,wyS] (.node [wg6,wmE,wp6,wre,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlll_ok : everyKey (rowOK 5 level5) level6rrlll = true := by decide +kernel
def level6rrllr : BinaryTree (List W) := (.node [wg6,wmE,wp6,wsJ,wtt,wwe,wyS] (.node [wg6,wmE,wp6,wsi,wtt,wwe,wyS] (.node [wg6,wmE,wp6,wrM,wtt,wwe] (.node [wg6,wmE,wp6,wrx,wtt,wwe,wyS] (.node [wg6,wmE,wp6,wrv,wtt,wwe,wyS] (.node [wg6,wmE,wp6,wrs,wtt,wwe,wyS] .nil .nil) (.node [wg6,wmE,wp6,wrv,wtt,wyS] .nil .nil)) (.node [wg6,wmE,wp6,wrG,wtt,wwe,wyS] (.node [wg6,wmE,wp6,wrx,wtt,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wrT,wtt,wwe,wyS] (.node [wg6,wmE,wp6,wrT,wtt,wwe] (.node [wg6,wmE,wp6,wrM,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wr5,wtt,wwe,wyS] (.node [wg6,wmE,wp6,wrY,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wmE,wp6,wsv,wtt,wwe,wyS] (.node [wg6,wmE,wp6,wsp,wtt,wwe,wyS] (.node [wg6,wmE,wp6,wso,wtt,wwe,wyS] (.node [wg6,wmE,wp6,wsm,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wsu,wtt,wwe,wyS] (.node [wg6,wmE,wp6,wss,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wsA,wtt,wwe,wyS] (.node [wg6,wmE,wp6,wsz,wtt,wwe,wyS] (.node [wg6,wmE,wp6,wsx,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wsC,wtt,wwe,wyS] (.node [wg6,wmE,wp6,wsB,wtt,wwe,wyS] .nil .nil) .nil)))) (.node [wg6,wmE,wp6,wsU,wtt,wwe,wyS] (.node [wg6,wmE,wp6,wsM,wtt,wwe,wyS] (.node [wg6,wmE,wp6,wsK,wwe,wyr,wyS] (.node [wg6,wmE,wp6,wsK,wtt,wwe,wAB] (.node [wg6,wmE,wp6,wsK,wtt,wwe,wyS] .nil .nil) (.node [wg6,wmE,wp6,wsK,wtt,wyr,wyS] .nil .nil)) (.node [wg6,wmE,wp6,wsL,wtt,wwe,wyS] (.node [wg6,wmE,wp6,wsK,wyr,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wsP,wtt,wwe,wyS] (.node [wg6,wmE,wp6,wsO,wtt,wwe,wyS] (.node [wg6,wmE,wp6,wsN,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wsS,wtt,wwe,wyS] (.node [wg6,wmE,wp6,wsQ,wtt,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wmE,wp6,wsZ,wtt,wwe,wyS] (.node [wg6,wmE,wp6,wsY,wtt,wyl,wyS] (.node [wg6,wmE,wp6,wsY,wtt,wwe,wAH] (.node [wg6,wmE,wp6,wsY,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wsY,wwe,wAH] (.node [wg6,wmE,wp6,wsY,wwe,wyS,wAH] .nil .nil) .nil)) (.node [wg6,wmE,wp6,ws2,wtt,wwe,wyS] (.node [wg6,wmE,wp6,ws1,wtt,wwe,wyS] (.node [wg6,wmE,wp6,ws0,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,ws5,wtt,wwe,wyS] (.node [wg6,wmE,wp6,ws3,wtt,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrllr_ok : everyKey (rowOK 5 level5) level6rrllr = true := by decide +kernel
def level6rrll : BinaryTree (List W) := .node [wg6,wmE,wp6,wrg,wwe,wyS] level6rrlll level6rrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrll_ok : everyKey (rowOK 5 level5) level6rrll = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrlll && everyKey (rowOK 5 level5) level6rrllr) = true
  rw [level6rrlll_ok, level6rrllr_ok]
  decide +kernel
def level6rrlrl : BinaryTree (List W) := (.node [wg6,wmE,wp6,wtt,wuk,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wtP,wwe,wyS] (.node [wg6,wmE,wp6,wtj,wwe,wyS,wA8] (.node [wg6,wmE,wp6,wtf,wwe,wyS,wA1] (.node [wg6,wmE,wp6,wtf,wtt,wwe,wyS] (.node [wg6,wmE,wp6,wtb,wtt,wwe,wyS] .nil .nil) (.node [wg6,wmE,wp6,wtf,wwe,wyS] .nil .nil)) (.node [wg6,wmE,wp6,wtj,wwe,wyS] (.node [wg6,wmE,wp6,wtj,wtt,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wtt,wtG,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wtF,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wtJ,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wtI,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wmE,wp6,wtt,wt4,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wtT,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wtR,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wtQ,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wt2,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wtU,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wtt,wub,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wt9,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wt6,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wug,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wud,wwe,wyS] .nil .nil) .nil)))) (.node [wg6,wmE,wp6,wtt,wuQ,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wuy,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wus,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wun,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wum,wwe,wyS] .nil .nil) (.node [wg6,wmE,wp6,wtt,wuq,wwe,wyS] .nil .nil)) (.node [wg6,wmE,wp6,wtt,wuw,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wuu,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wtt,wuJ,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wuC,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wuz,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wuL,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wuK,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wmE,wp6,wtt,wuY,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wuT,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wuS,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wuR,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wuX,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wuV,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wtt,wu3,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wu1,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wu0,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wu8,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wu5,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlrl_ok : everyKey (rowOK 5 level5) level6rrlrl = true := by decide +kernel
def level6rrlrr : BinaryTree (List W) := (.node [wg6,wmE,wp6,wtt,wvS,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wvy,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wvp,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wvg,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wvd,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wvb,wwe,wyS] .nil .nil) (.node [wg6,wmE,wp6,wtt,wve,wwe,wyS] .nil .nil)) (.node [wg6,wmE,wp6,wtt,wvm,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wvk,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wtt,wvu,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wvs,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wvr,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wvw,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wvv,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wmE,wp6,wtt,wvK,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wvJ,wwe,wAR] (.node [wg6,wmE,wp6,wtt,wvJ,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wvI,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wvJ,wAR] (.node [wg6,wmE,wp6,wtt,wvJ,wyS,wAR] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wtt,wvN,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wvM,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wvL,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wvQ,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wvO,wwe,wyS] .nil .nil) .nil)))) (.node [wg6,wmE,wp6,wtt,wwe,wwA,wyS] (.node [wg6,wmE,wp6,wtt,wv4,wyS,wA8] (.node [wg6,wmE,wp6,wtt,wv0,wyS,wA1] (.node [wg6,wmE,wp6,wtt,wv0,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wvW,wwe,wyS] .nil .nil) (.node [wg6,wmE,wp6,wtt,wv0,wyS] .nil .nil)) (.node [wg6,wmE,wp6,wtt,wv4,wyS] (.node [wg6,wmE,wp6,wtt,wv4,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wtt,wwe,wwr,wyS] (.node [wg6,wmE,wp6,wtt,wwe,wwq,wyS] (.node [wg6,wmE,wp6,wtt,wwe,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wwe,wwu,wyS] (.node [wg6,wmE,wp6,wtt,wwe,wwt,wyS] .nil .nil) .nil))) (.node [wg6,wmE,wp6,wtt,wwe,wwP,wyS] (.node [wg6,wmE,wp6,wtt,wwe,wwF,wyS] (.node [wg6,wmE,wp6,wtt,wwe,wwC,wyS] (.node [wg6,wmE,wp6,wtt,wwe,wwB,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wwe,wwN,wyS] (.node [wg6,wmE,wp6,wtt,wwe,wwG,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wtt,wwe,wwX,wyS] (.node [wg6,wmE,wp6,wtt,wwe,wwV,wyS] (.node [wg6,wmE,wp6,wtt,wwe,wwT,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wwe,ww4,wyS] (.node [wg6,wmE,wp6,wtt,wwe,ww0,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlrr_ok : everyKey (rowOK 5 level5) level6rrlrr = true := by decide +kernel
def level6rrlr : BinaryTree (List W) := .node [wg6,wmE,wp6,wtt,wva,wwe,wyS] level6rrlrl level6rrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlr_ok : everyKey (rowOK 5 level5) level6rrlr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrlrl && everyKey (rowOK 5 level5) level6rrlrr) = true
  rw [level6rrlrl_ok, level6rrlrr_ok]
  decide +kernel
def level6rrl : BinaryTree (List W) := .node [wg6,wmE,wp6,ws7,wtt,wwe,wyS] level6rrll level6rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrl_ok : everyKey (rowOK 5 level5) level6rrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrll && everyKey (rowOK 5 level5) level6rrlr) = true
  rw [level6rrll_ok, level6rrlr_ok]
  decide +kernel
def level6rrrll : BinaryTree (List W) := (.node [wg6,wmE,wp6,wtt,wwe,wxZ,wyS] (.node [wg6,wmE,wp6,wtt,wwe,wxC,wyS] (.node [wg6,wmE,wp6,wtt,wwe,wxr,wyS] (.node [wg6,wmE,wp6,wtt,wwe,wxf,wyS] (.node [wg6,wmE,wp6,wtt,wwe,wxb,wyS] (.node [wg6,wmE,wp6,wtt,wwe,ww9,wyS] .nil .nil) (.node [wg6,wmE,wp6,wtt,wwe,wxd,wyS] .nil .nil)) (.node [wg6,wmE,wp6,wtt,wwe,wxq,wyS] (.node [wg6,wmE,wp6,wtt,wwe,wxj,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wtt,wwe,wxy,wyS] (.node [wg6,wmE,wp6,wtt,wwe,wxx,wyS] (.node [wg6,wmE,wp6,wtt,wwe,wxs,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wwe,wxA,wyS] (.node [wg6,wmE,wp6,wtt,wwe,wxz,wyS] .nil .nil) .nil))) (.node [wg6,wmE,wp6,wtt,wwe,wxM,wyS] (.node [wg6,wmE,wp6,wtt,wwe,wxG,wyS] (.node [wg6,wmE,wp6,wtt,wwe,wxF,wyS] (.node [wg6,wmE,wp6,wtt,wwe,wxD,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wwe,wxL,wyS] (.node [wg6,wmE,wp6,wtt,wwe,wxI,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wtt,wwe,wxR,wyS] (.node [wg6,wmE,wp6,wtt,wwe,wxP,wyS] (.node [wg6,wmE,wp6,wtt,wwe,wxO,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wwe,wxY,wyS] (.node [wg6,wmE,wp6,wtt,wwe,wxV,wyS] .nil .nil) .nil)))) (.node [wg6,wmE,wp6,wtt,wwe,wyE,wyS] (.node [wg6,wmE,wp6,wtt,wwe,wyh,wyS] (.node [wg6,wmE,wp6,wtt,wwe,wx5,wyS] (.node [wg6,wmE,wp6,wtt,wwe,wx2,wyS] (.node [wg6,wmE,wp6,wtt,wwe,wx1,wyS] .nil .nil) (.node [wg6,wmE,wp6,wtt,wwe,wx3,wyS] .nil .nil)) (.node [wg6,wmE,wp6,wtt,wwe,wye,wyS] (.node [wg6,wmE,wp6,wtt,wwe,wyd,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wtt,wwe,wyA,wyS] (.node [wg6,wmE,wp6,wtt,wwe,wyr,wyS] (.node [wg6,wmE,wp6,wtt,wwe,wyl,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wwe,wyE] (.node [wg6,wmE,wp6,wtt,wwe,wyC,wyS] .nil .nil) .nil))) (.node [wg6,wmE,wp6,wtt,wwe,wyS,wyS] (.node [wg6,wmE,wp6,wtt,wwe,wyI,wyS] (.node [wg6,wmE,wp6,wtt,wwe,wyI] (.node [wg6,wmE,wp6,wtt,wwe,wyE,wA1] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wwe,wyI,wA8] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wtt,wwe,wyS,wy7] (.node [wg6,wmE,wp6,wtt,wwe,wyS,wy5] (.node [wg6,wmE,wp6,wtt,wwe,wyS,wy4] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wwe,wyS,wze] (.node [wg6,wmE,wp6,wtt,wwe,wyS,wy8] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrll_ok : everyKey (rowOK 5 level5) level6rrrll = true := by decide +kernel
def level6rrrlr : BinaryTree (List W) := (.node [wg6,wmE,wp6,wtt,wwe,wyS,wAk] (.node [wg6,wmE,wp6,wtt,wwe,wyS,wzT] (.node [wg6,wmE,wp6,wtt,wwe,wyS,wzB] (.node [wg6,wmE,wp6,wtt,wwe,wyS,wzr] (.node [wg6,wmE,wp6,wtt,wwe,wyS,wzi] (.node [wg6,wmE,wp6,wtt,wwe,wyS,wzh] .nil .nil) (.node [wg6,wmE,wp6,wtt,wwe,wyS,wzp] .nil .nil)) (.node [wg6,wmE,wp6,wtt,wwe,wyS,wzy] (.node [wg6,wmE,wp6,wtt,wwe,wyS,wzv] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wtt,wwe,wyS,wzK] (.node [wg6,wmE,wp6,wtt,wwe,wyS,wzH] (.node [wg6,wmE,wp6,wtt,wwe,wyS,wzF] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wwe,wyS,wzP] (.node [wg6,wmE,wp6,wtt,wwe,wyS,wzN] .nil .nil) .nil))) (.node [wg6,wmE,wp6,wtt,wwe,wyS,wAa] (.node [wg6,wmE,wp6,wtt,wwe,wyS,wz6] (.node [wg6,wmE,wp6,wtt,wwe,wyS,wz5] (.node [wg6,wmE,wp6,wtt,wwe,wyS,wz0] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wwe,wyS,wz9] (.node [wg6,wmE,wp6,wtt,wwe,wyS,wz7] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wtt,wwe,wyS,wAf] (.node [wg6,wmE,wp6,wtt,wwe,wyS,wAd] (.node [wg6,wmE,wp6,wtt,wwe,wyS,wAc] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wwe,wyS,wAi] (.node [wg6,wmE,wp6,wtt,wwe,wyS,wAh] .nil .nil) .nil)))) (.node [wg6,wmE,wp6,wtt,wwe,wyS,wAV] (.node [wg6,wmE,wp6,wtt,wwe,wyS,wAB] (.node [wg6,wmE,wp6,wtt,wwe,wyS,wAs] (.node [wg6,wmE,wp6,wtt,wwe,wyS,wAq] (.node [wg6,wmE,wp6,wtt,wwe,wyS,wAo] .nil .nil) (.node [wg6,wmE,wp6,wtt,wwe,wyS,wAr] .nil .nil)) (.node [wg6,wmE,wp6,wtt,wwe,wyS,wAz] (.node [wg6,wmE,wp6,wtt,wwe,wyS,wAu] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wtt,wwe,wyS,wAN] (.node [wg6,wmE,wp6,wtt,wwe,wyS,wAL] (.node [wg6,wmE,wp6,wtt,wwe,wyS,wAH] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wwe,wyS,wAT] (.node [wg6,wmE,wp6,wtt,wwe,wyS,wAR] .nil .nil) .nil))) (.node [wg6,wmE,wp6,wtt,wwe,wyS,wBd] (.node [wg6,wmE,wp6,wtt,wwe,wyS,wA1] (.node [wg6,wmE,wp6,wtt,wwe,wyS,wAX] (.node [wg6,wmE,wp6,wtt,wwe,wyS,wAW] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wwe,wyS,wBc] (.node [wg6,wmE,wp6,wtt,wwe,wyS,wA8] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wtt,wwe,wyS,wBg] (.node [wg6,wmE,wp6,wtt,wwe,wyS,wBf] (.node [wg6,wmE,wp6,wtt,wwe,wyS,wBe] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wwe,wyS,wBi] (.node [wg6,wmE,wp6,wtt,wwe,wyS,wBh] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrlr_ok : everyKey (rowOK 5 level5) level6rrrlr = true := by decide +kernel
def level6rrrl : BinaryTree (List W) := .node [wg6,wmE,wp6,wtt,wwe,wyS,wzf] level6rrrll level6rrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrl_ok : everyKey (rowOK 5 level5) level6rrrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrrll && everyKey (rowOK 5 level5) level6rrrlr) = true
  rw [level6rrrll_ok, level6rrrlr_ok]
  decide +kernel
def level6rrrrl : BinaryTree (List W) := (.node [wg6,wmE,wp6,wtt,wxz,wyr,wyS] (.node [wg6,wmE,wp6,wtt,wwe,wz7,wAR] (.node [wg6,wmE,wp6,wtt,wwe,wzK] (.node [wg6,wmE,wp6,wtt,wwe,wzr] (.node [wg6,wmE,wp6,wtt,wwe,wyS,wBl] (.node [wg6,wmE,wp6,wtt,wwe,wyS,wBk] .nil .nil) (.node [wg6,wmE,wp6,wtt,wwe,wzp] .nil .nil)) (.node [wg6,wmE,wp6,wtt,wwe,wzy] (.node [wg6,wmE,wp6,wtt,wwe,wzv] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wtt,wwe,wz0] (.node [wg6,wmE,wp6,wtt,wwe,wzT] (.node [wg6,wmE,wp6,wtt,wwe,wzN] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wwe,wz7,wAH] (.node [wg6,wmE,wp6,wtt,wwe,wz7,wAo] .nil .nil) .nil))) (.node [wg6,wmE,wp6,wtt,wwX,wyS] (.node [wg6,wmE,wp6,wtt,wwN,wyS] (.node [wg6,wmE,wp6,wtt,wwe,wAH,wAR] (.node [wg6,wmE,wp6,wtt,wwe,wAB] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wwT,wyS] (.node [wg6,wmE,wp6,wtt,wwP,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wtt,wxj,wyS] (.node [wg6,wmE,wp6,wtt,wxd,wyS] (.node [wg6,wmE,wp6,wtt,ww9,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wtt,wxz,wxV,wyS] (.node [wg6,wmE,wp6,wtt,wxs,wyS] .nil .nil) .nil)))) (.node [wg6,wmE,wp6,wuS,wwe,wyr,wyS] (.node [wg6,wmE,wp6,wud,wwe,wyS] (.node [wg6,wmE,wp6,wt2,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wyl,wyS] (.node [wg6,wmE,wp6,wtt,wxz,wyS,wAR] .nil .nil) (.node [wg6,wmE,wp6,wtt,wyr,wyS,wAR] .nil .nil)) (.node [wg6,wmE,wp6,wt9,wwe,wyS] (.node [wg6,wmE,wp6,wt4,wwe,wyS] .nil .nil) .nil)) (.node [wg6,wmE,wp6,wuC,wwe,wyS] (.node [wg6,wmE,wp6,wuu,wwe,wyS] (.node [wg6,wmE,wp6,wuq,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wp6,wuS,wvk,wwe,wyS] (.node [wg6,wmE,wp6,wuL,wwe,wyS] .nil .nil) .nil))) (.node [wg6,wmE,wqO,wtt,wwe,wyS] (.node [wg6,wmE,wp6,wwe,wyh,wyS] (.node [wg6,wmE,wp6,wvJ,wwe,wyh,wyS] (.node [wg6,wmE,wp6,wuS,wwe,wyS,wAH] .nil .nil) .nil) (.node [wg6,wmE,wqt,wtt,wwe,wyS] (.node [wg6,wmE,wp6,wwe,wyr,wyS,wAH] .nil .nil) .nil)) (.node [wg6,wmE,wrG,wtt,wwe,wyS] (.node [wg6,wmE,wrs,wtt,wwe,wyS] (.node [wg6,wmE,wq8,wtt,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wr5,wtt,wwe,wyS] (.node [wg6,wmE,wrY,wtt,wwe,wyS] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrrl_ok : everyKey (rowOK 5 level5) level6rrrrl = true := by decide +kernel
def level6rrrrr : BinaryTree (List W) := (.node [wg6,wmE,wtt,wwe,wyS,wAR,wA8] (.node [wg6,wmE,wtt,wwe,wxz,wyS,wA8] (.node [wg6,wmE,wtt,wvk,wwe,wyS,wA8] (.node [wg6,wmE,wtj,wtt,wwe,wyS,wA8] (.node [wg6,wmE,wsK,wtt,wwe,wyS,wA8] (.node [wg6,wmE,wsC,wtt,wwe,wyS,wA8] .nil .nil) (.node [wg6,wmE,wsY,wtt,wwe,wyS,wA8] .nil .nil)) (.node [wg6,wmE,wtt,wuS,wwe,wyS,wA8] (.node [wg6,wmE,wtj,wwe,wyS,wA8] .nil .nil) .nil)) (.node [wg6,wmE,wtt,wvJ,wwe,wyS,wA8] (.node [wg6,wmE,wtt,wvy,wwe,wyS,wA8] (.node [wg6,wmE,wtt,wvw,wwe,wyS] .nil .nil) .nil) (.node [wg6,wmE,wtt,wv4,wyS,wA8] (.node [wg6,wmE,wtt,wv4,wwe,wyS,wA8] .nil .nil) .nil))) (.node [wg6,wmE,wtt,wwe,wyI,wA8] (.node [wg6,wmE,wtt,wwe,wx5,wyS,wA8] (.node [wg6,wmE,wtt,wwe,wx3,wyS] (.node [wg6,wmE,wtt,wwe,wxV,wyS,wA8] .nil .nil) .nil) (.node [wg6,wmE,wtt,wwe,wyI,wyS,wA8] (.node [wg6,wmE,wtt,wwe,wyr,wyS,wA8] .nil .nil) .nil)) (.node [wg6,wmE,wtt,wwe,wyS,wAs] (.node [wg6,wmE,wtt,wwe,wyS,wAo,wA8] (.node [wg6,wmE,wtt,wwe,wyS,wz7,wA8] .nil .nil) .nil) (.node [wg6,wmE,wtt,wwe,wyS,wAH,wA8] (.node [wg6,wmE,wtt,wwe,wyS,wAu,wA8] .nil .nil) .nil)))) (.node [wg6,wp6,wtt,wvg,wwe,wyS] (.node [wg6,wmE,wtt,wwe,wyS,wA8,wBe] (.node [wg6,wmE,wtt,wwe,wyS,wA8] (.node [wg6,wmE,wtt,wwe,wyS,wA1,wA8] (.node [wg6,wmE,wtt,wwe,wyS,wAX] .nil .nil) .nil) (.node [wg6,wmE,wtt,wwe,wyS,wA8,wBc] (.node [wg6,wmE,wtt,wwe,wyS,wA8,wA8] .nil .nil) .nil)) (.node [wg6,wnG,wp6,wtt,wwe,wyS] (.node [wg6,wmE,wtt,wwe,wyS,wA8,wBj] (.node [wg6,wmE,wtt,wwe,wyS,wA8,wBg] .nil .nil) .nil) (.node [wg6,wnV,wp6,wtt,wwe,wyS] (.node [wg6,wnO,wp6,wtt,wwe,wyS] .nil .nil) .nil))) (.node [whW,wmE,wp6,wtt,wuS,wwe,wyS] (.node [wg6,wp6,wtt,wwe,wxV,wyS,wA1] (.node [wg6,wp6,wtt,wwe,wxR,wyS] (.node [wg6,wp6,wtt,wvk,wwe,wyS,wA1] .nil .nil) .nil) (.node [wg6,wp6,wtt,wwe,wyS,wAo,wA1] (.node [wg6,wp6,wtt,wwe,wyS,wAk] .nil .nil) .nil)) (.node [wiv,wmE,wp6,wtt,wwe,wyS,wA1] (.node [wip,wmE,wp6,wtt,wwe,wyS,wz7] (.node [wie,wmE,wp6,wtt,wwe,wxz,wyS] .nil .nil) .nil) (.node [wiC,wmE,wtt,wwe,wyS,wA8] (.node [wiC,wmE,wp6,wtt,wwe,wyS,wA8] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrrr_ok : everyKey (rowOK 5 level5) level6rrrrr = true := by decide +kernel
def level6rrrr : BinaryTree (List W) := .node [wg6,wmE,wsB,wtt,wwe,wyS] level6rrrrl level6rrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrr_ok : everyKey (rowOK 5 level5) level6rrrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrrrl && everyKey (rowOK 5 level5) level6rrrrr) = true
  rw [level6rrrrl_ok, level6rrrrr_ok]
  decide +kernel
def level6rrr : BinaryTree (List W) := .node [wg6,wmE,wp6,wtt,wwe,wyS,wBj] level6rrrl level6rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrr_ok : everyKey (rowOK 5 level5) level6rrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrrl && everyKey (rowOK 5 level5) level6rrrr) = true
  rw [level6rrrl_ok, level6rrrr_ok]
  decide +kernel
def level6rr : BinaryTree (List W) := .node [wg6,wmE,wp6,wtt,wwe,ww6,wyS] level6rrl level6rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rr_ok : everyKey (rowOK 5 level5) level6rr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrl && everyKey (rowOK 5 level5) level6rrr) = true
  rw [level6rrl_ok, level6rrr_ok]
  decide +kernel
def level6r : BinaryTree (List W) := .node [wg6,wmE,wpo,wp6,wtt,wwe,wAH] level6rl level6rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6r_ok : everyKey (rowOK 5 level5) level6r = true := by
  change (_ && everyKey (rowOK 5 level5) level6rl && everyKey (rowOK 5 level5) level6rr) = true
  rw [level6rl_ok, level6rr_ok]
  decide +kernel
def level6 : BinaryTree (List W) := .node [wgr,wg6,wmE,wp6,wuC,wwe,wyS] level6l level6r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6_ok : everyKey (rowOK 5 level5) level6 = true := by
  change (_ && everyKey (rowOK 5 level5) level6l && everyKey (rowOK 5 level5) level6r) = true
  rw [level6l_ok, level6r_ok]
  decide +kernel
theorem closed6 : Closed 6 level6 := closed_next 5 (by decide) level6 level5 closed5 level6_ok
def level7l : BinaryTree (List W) := (.node [wc2,wg6,wmE,wtt,wwe,wyS] (.node [wa9,wg6,wmE,wp6,wtt,wwe,wyS] (.node [w9,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wY,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wT,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wK,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) .nil) (.node [w6,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil)) (.node [waT,wg6,wmE,wp6,wtt,wwe,wyS] (.node [waH,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) (.node [wa0,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil))) (.node [wb7,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wbK,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wbg,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) (.node [wbY,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil)) (.node [wcp,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wci,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) (.node [wc2,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil)))) (.node [wfe,wg6,wmE,wp6,wtt,wwe,wyS] (.node [web,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wdH,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wdl,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) (.node [wdW,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil)) (.node [weV,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wep,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) (.node [weZ,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil))) (.node [wf9,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wfs,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wfm,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) (.node [wfx,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil)) (.node [wgR,wg6,wmE,wp6,wtt,wwe,wyS] (.node [wgr,wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil) (.node [wg6,whW,wmE,wp6,wtt,wwe,wyS] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7l_ok : everyKey (rowOK 6 level6) level7l = true := by decide +kernel
def level7r : BinaryTree (List W) := (.node [wg6,wmE,wp6,wtt,wuS,wwe,wyS] (.node [wg6,wlC,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wiC,wmE,wtt,wwe,wyS] (.node [wg6,wiv,wmE,wp6,wtt,wwe,wyS] (.node [wg6,wip,wmE,wp6,wtt,wwe,wyS] .nil .nil) (.node [wg6,wiC,wmE,wp6,wtt,wwe,wyS] .nil .nil)) (.node [wg6,wjl,wmE,wtt,wwe,wyS] (.node [wg6,wjl,wmE,wp6,wtt,wwe,wyS] .nil .nil) (.node [wg6,wla,wmE,wp6,wtt,wwe,wyS] .nil .nil))) (.node [wg6,wmE,wpo,wp6,wtt,wwe,wyS] (.node [wg6,wmE,wn8,wp6,wtt,wwe,wyS] (.node [wg6,wl2,wmE,wp6,wtt,wwe,wyS] .nil .nil) (.node [wg6,wmE,woH,wp6,wtt,wwe,wyS] .nil .nil)) (.node [wg6,wmE,wp6,wsK,wtt,wwe,wyS] (.node [wg6,wmE,wp6,wsC,wtt,wwe,wyS] .nil .nil) (.node [wg6,wmE,wp6,wsY,wtt,wwe,wyS] .nil .nil)))) (.node [wg6,wmE,wp6,wtt,wwe,wyS,wz7] (.node [wg6,wmE,wp6,wtt,wwe,wxz,wyS] (.node [wg6,wmE,wp6,wtt,wvy,wwe,wyS] (.node [wg6,wmE,wp6,wtt,wvk,wwe,wyS] .nil .nil) (.node [wg6,wmE,wp6,wtt,wvJ,wwe,wyS] .nil .nil)) (.node [wg6,wmE,wp6,wtt,wwe,wx5,wyS] (.node [wg6,wmE,wp6,wtt,wwe,wxV,wyS] .nil .nil) (.node [wg6,wmE,wp6,wtt,wwe,wyr,wyS] .nil .nil))) (.node [wg6,wmE,wp6,wtt,wwe,wyS,wAR] (.node [wg6,wmE,wp6,wtt,wwe,wyS,wAu] (.node [wg6,wmE,wp6,wtt,wwe,wyS,wAo] .nil .nil) (.node [wg6,wmE,wp6,wtt,wwe,wyS,wAH] .nil .nil)) (.node [wg6,wmE,wp6,wtt,wwe,wyS,wA8] (.node [wg6,wmE,wp6,wtt,wwe,wyS,wA1] .nil .nil) (.node [wg6,wmE,wtt,wwe,wyS,wA8] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7r_ok : everyKey (rowOK 6 level6) level7r = true := by decide +kernel
def level7 : BinaryTree (List W) := .node [wg6,wie,wmE,wp6,wtt,wwe,wyS] level7l level7r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7_ok : everyKey (rowOK 6 level6) level7 = true := by
  change (_ && everyKey (rowOK 6 level6) level7l && everyKey (rowOK 6 level6) level7r) = true
  rw [level7l_ok, level7r_ok]
  decide +kernel
theorem closed7 : Closed 7 level7 := closed_next 6 (by decide) level7 level6 closed6 level7_ok
def level8 : BinaryTree (List W) := (.node [wg6,wmE,wp6,wtt,wwe,wyS] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8_ok : everyKey (rowOK 7 level7) level8 = true := by decide +kernel
theorem closed8 : Closed 8 level8 := closed_next 7 (by decide) level8 level7 closed7 level8_ok

theorem lower : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z 8 ins.toFinset :=
  @no_build 8 level8 ins (by decide +kernel) (by decide) closed8 (by decide +kernel)
def witness : List Gate := [⟨.or,[3,5]⟩, ⟨.and,[3,5]⟩, ⟨.or,[4,6]⟩, ⟨.or,[1,8]⟩, ⟨.and,[4,6]⟩, ⟨.or,[7,10]⟩, ⟨.and,[1,11]⟩, ⟨.and,[2,12]⟩, ⟨.or,[0,13]⟩, ⟨.and,[9,14]⟩]
theorem upper : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 10 ∧ ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xeaeaeaaaeaaaaa88 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact ⟨witness,15,by simp [witness],rfl,by decide +kernel⟩
end PEqualNP.Outside.L_meta_16163_aux

open PEqualNP.Outside.L_meta_16163_aux in
theorem PEqualNP.Outside.L_meta_16163 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941264042 * 2 ^ 32 + 3937053320) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941264042 * 2 ^ 32 + 3937053320) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  have code : 3941264042 * 2 ^ 32 + 3937053320 = 0xeaeaeaaaeaaaaa88 := by decide
  simp only [code] at h ⊢
  obtain ⟨C,legal,size,computes⟩ := h
  obtain ⟨gs,o,mono,bound,ev⟩ := replace 0xeaeaeaaaeaaaaa88 10 ins (by decide +kernel) sampled rfl lower upper C.gates C.output legal computes
  exact ⟨⟨gs,o⟩,mono,bound.trans size,ev⟩
