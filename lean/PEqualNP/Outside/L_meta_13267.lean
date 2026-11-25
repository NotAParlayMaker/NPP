import PEqualNP.Defs

-- The live-wire search and circuit compiler are adapted from tacyon52 in L-meta-8639, pull request 12794 under Apache-2.0.
namespace PEqualNP.Outside.L_meta_13267_aux

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

-- The upper and lower halves represent opposite target labels on 50 pairs of assignments.
abbrev W := BitVec 100
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 50 := ((x >>> 50) ^^^ x).setWidth 50
def cuts (ws : List W) : BitVec 50 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 50) ++ (0 : BitVec 50)
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

def differs (i : Fin 50) (w : W) : Prop :=
  w.getLsbD (50+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 50) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 50+i.val < 100 := by omega
  have hi' : i.val < 100 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 50) :
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
  change (cuts ws)[j] = (BitVec.allOnes 50)[j]
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
  · change reachable av (BitVec.allOnes 100 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 100)
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

private def bit (k : Fin 100) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 100) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 100) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#100)[k.val] = false; simp
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
    (row : ∀ j : Fin 100, Nat.testBit T (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
    (width : ins.length = 6) (rejection : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z n ins.toFinset)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 6, if x i then 2^(i : ℕ) else 0)) : n < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ ins, holds ins.toFinset u := fun u hu =>
    .inr (.inr ⟨u,List.mem_toFinset.mpr hu,.inl rfl⟩)
  have evaluate (k : Fin 100) :
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
    (row : ∀ j : Fin 100, Nat.testBit T (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
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

def v0 : W := 0x3134001898
def v1 : W := 0x3830001c18
def v2 : W := 0x1100a40000000dc067
def v3 : W := 0x1100a40d00c80dc067
def v4 : W := 0x1980e400000001e01f
def v5 : W := 0x142060800000031e087
def v6 : W := 0x1420608000000c1c307
def v7 : W := 0x15326ac00000001c007
def v8 : W := 0x5dbe6ec00000031e007
def v9 : W := 0x5dbe6ec00000031f89f
def v10 : W := 0xb733fac000000cdc367
def v11 : W := 0xeb9f9e40000030e1c78
def v12 : W := 0xfe27f08000003f01f80
def v13 : W := 0xff37fac000003fddfe7
def v14 : W := 0xffbc040000003ffe000
def v15 : W := 0xffbe6ec000003fff89f
def v16 : W := 0xffbffec000000fdfbff
def v17 : W := 0xffbffec0000033ffcff
def v18 : W := 0xffbffec000003cfdf7f
def v19 : W := 0xffbffec000003f1ff9f
def v20 : W := 0xffbffec000003ffe367
def v21 : W := 0x41400020a4003030001818
def v22 : W := 0x4d700026bc00313400189f
def v23 : W := 0x73400039a40038f0001c78
def v24 : W := 0x734b733fac0038f0cddf7f
def v25 : W := 0x7e00003f08003f00001f80
def v26 : W := 0x7f40003fac003ff0001ff8
def v27 : W := 0x7f70000010003ffc000000
def v28 : W := 0x7f700026bc003ffc00189f
def v29 : W := 0x7f700039b4003ffc001c78
def v30 : W := 0x7f70003fbc0006c8000367
def v31 : W := 0x7f70003fbc0037fc001bff
def v32 : W := 0x7f70003fbc0039f4001cff
def v33 : W := 0x7f70003fbc003ef8001f7f
def v34 : W := 0x7f70003fbc003f34001f9f
def v35 : W := 0x7f7ffbc050003fffffe000
def v36 : W := 0x5003004001001c00c000000
def v37 : W := 0x1001401100a40c00c00dc067
def v38 : W := 0x1501700400100d00c8000000
def v39 : W := 0x1501701500b40d00c80dc067
def v40 : W := 0x1a01c01980e40e00f00e0078
def v41 : W := 0x1a01c01980e40e00f00fc07f
def v42 : W := 0x1a01c01980e40e00f00fe07f
def v43 : W := 0x1f00801d80400fc0000fe000
def v44 : W := 0x1f01f004001000c034000000
def v45 : W := 0x1f01f00400100fc0fc000000
def v46 : W := 0x1f01f01500b40fc0fc0dc067
def v47 : W := 0x1f01f01d80f400c03401e01f
def v48 : W := 0x1f01f01d80f40dc0fc0de07f
def v49 : W := 0x1f01f01d80f40ec0f40fe07f
def v50 : W := 0x1f01f01d80f40f00f80fc07f
def v51 : W := 0x1f01f01d80f40fc0c80fe067
def v52 : W := 0x1f01f01d80f40fc0fc0e0078
def v53 : W := 0x1f01ffe67f180fc0fff01f80
def v54 : W := 0x1f7e801dbf480fff000fff80
def v55 : W := 0x1f7ff00400100ffffc000000
def v56 : W := 0x1400c01420608f00700f00380
def v57 : W := 0x1450001460000f1c000f1e000
def v58 : W := 0x1450c3004001030c104000000
def v59 : W := 0x1450c30040010c10608000000
def v60 : W := 0x1450c30040010f1c70c000000
def v61 : W := 0x1450c30040010f1ff3c000000
def v62 : W := 0x1450c3146061830c10431e087
def v63 : W := 0x1450c31460618c10608c1c307
def v64 : W := 0x1450c31460618f0c704f1e387
def v65 : W := 0x1450c31460618f1c608f1e307
def v66 : W := 0x1450c31460618f1c70cf00380
def v67 : W := 0x1450c31460618f1c70cf1e387
def v68 : W := 0x1450c3ebdf9f4f1c70f0e1c78
def v69 : W := 0x1454d714626bc30f13431f89f
def v70 : W := 0x14573414639a4f1f8f0f1fc78
def v71 : W := 0x1457f70040010f1fffc000000
def v72 : W := 0x1457f700439b4f1fffc001c78
def v73 : W := 0x1554d70040010000000000000
def v74 : W := 0x1554d715726bc00000001c007
def v75 : W := 0x1554d715726bc00313401d89f
def v76 : W := 0x15a0dc15b86ecfe07f0fe03f8
def v77 : W := 0x15f0df0040010ffc7fc000000
def v78 : W := 0x4808004804003303903301c80
def v79 : W := 0x48a808000000332f934000000
def v80 : W := 0x48a808488c04030c000302000
def v81 : W := 0x48a808488c04030f134303898
def v82 : W := 0x48a808488c043020003020000
def v83 : W := 0x48a808488c043023833021c18
def v84 : W := 0x48a808488c04330f937303c98
def v85 : W := 0x48a808488c04332c003322000
def v86 : W := 0x48a808488c04332f937323c98
def v87 : W := 0x48a8085dbe6ec30f13431f89f
def v88 : W := 0x48a808b733faf32f934cdc367
def v89 : W := 0x48a808ffbc04332c003ffe000
def v90 : W := 0x48a808ffbffef32c003ffe367
def v91 : W := 0x48afff488ffff32c6cb322367
def v92 : W := 0x49581749540b73d39cb3ddce7
def v93 : W := 0x49a808499c040000000000000
def v94 : W := 0x49ac1c499e0e4003030001818
def v95 : W := 0x49ac1c5dbe6ec00303031f89f
def v96 : W := 0x49f80849dc0433fc0033fe000
def v97 : W := 0x49f81f00400133ff9fc000000
def v98 : W := 0x49f81f49dc0f73fc0cb3fe067
def v99 : W := 0x5c0cc05c26608303100301880
def v100 : W := 0x5c0cc05dbe6ec30310031f89f
def v101 : W := 0x5cf8085cec043f3c003f3e000
def v102 : W := 0x5cf8cb0040013f3ff3c000000
def v103 : W := 0x5cf8cb48cc053f3c70f322000
def v104 : W := 0x5cf8cb5cec65bc33e3bc3df1f
def v105 : W := 0x5df8085dfc04030c00031e000
def v106 : W := 0x5df8085dfc0403fc0003fe000
def v107 : W := 0x5df8085dfc040f1c000f1e000
def v108 : W := 0x5df8085dfc04332c00333e000
def v109 : W := 0x5df808fffc04030c003ffe000
def v110 : W := 0x5df8cb5dfc65830c10431e087
def v111 : W := 0x5dfcdf004001030c000000000
def v112 : W := 0x5dfcdf004001030f134000000
def v113 : W := 0x5dfcdf00400103ff1fc000000
def v114 : W := 0x5dfcdf0040010f1f73c000000
def v115 : W := 0x5dfcdf004001332f934000000
def v116 : W := 0x5dfcdf48cc05030f134303898
def v117 : W := 0x5dfcdf49de0f430f134001818
def v118 : W := 0x5dfcdf5c6661830f134301880
def v119 : W := 0x5dfcdf5dfe6fc00000001c007
def v120 : W := 0x5dfcdf5dfe6fc00303001d81f
def v121 : W := 0x5dfcdf5dfe6fc30c00031e007
def v122 : W := 0x5dfcdf5dfe6fc30c10431e087
def v123 : W := 0x5dfcdf5dfe6fc30f134301898
def v124 : W := 0x5dfcdf5dfe6fc30f13431f89f
def v125 : W := 0x5dffff004001030fffc000000
def v126 : W := 0xa20000a200003cf0003ce0000
def v127 : W := 0xa203200000003cf0ec8000000
def v128 : W := 0xa203205dbe6efcf0ec831f89f
def v129 : W := 0xa20320a201900cd06c8cc0360
def v130 : W := 0xa20320a2019030e08c30e0460
def v131 : W := 0xa20320a201903c00e03c00700
def v132 : W := 0xa20320a201903cf06cbce0360
def v133 : W := 0xa20320a201903cf0ecbce0760
def v134 : W := 0xa20320b733faccd06c8cdc367
def v135 : W := 0xa20320fe27f0bc00e03f01f80
def v136 : W := 0xa204d7a2026bfcf3137ce189f
def v137 : W := 0xa20734a2039a70e38f30e1c78
def v138 : W := 0xa30734a3139a40c00c00c0060
def v139 : W := 0xa30734a3139a40c38f00c1c78
def v140 : W := 0xa30734b733fac0c00c0cdc367
def v141 : W := 0xa3f33f0040013cfcefc000000
def v142 : W := 0xa3f33fa3d99f7c0ce37c1e71f
def v143 : W := 0xb603e0b621f0bf00f03f00780
def v144 : W := 0xb607e0b623f08c00600c00300
def v145 : W := 0xb607e0b623f08c03f00c01f80
def v146 : W := 0xb607e0b623f08f00700f00380
def v147 : W := 0xb607e0b623f0bc00e03c00700
def v148 : W := 0xb607e0b733facc00600cdc367
def v149 : W := 0xb607e0fe27f08c00603f01f80
def v150 : W := 0xb653e30040013ffcfcc000000
def v151 : W := 0xb653e3b661f1b3ec9c73fe4e7
def v152 : W := 0xb657e3b663f18c10608c00300
def v153 : W := 0xb657e3b663f18f1c70cc00300
def v154 : W := 0xb75000b770000cd0000cdc000
def v155 : W := 0xb757f70040010cd06c8000000
def v156 : W := 0xb757f70040010cd3ffc000000
def v157 : W := 0xb757f70040010fdc7cc000000
def v158 : W := 0xb757f70040013cf0ec8000000
def v159 : W := 0xb757f700439b4cd3ef8001c78
def v160 : W := 0xb757f7a241910cd06c8cc0360
def v161 : W := 0xb757f7a3539b4cd06c80c0060
def v162 : W := 0xb757f7a3539b4cd3ffc0c1c78
def v163 : W := 0xb757f7b663f18c00600c00300
def v164 : W := 0xb757f7b663f18cd06c8c00300
def v165 : W := 0xb757f7b773fbc0c00c00dc067
def v166 : W := 0xb757f7b773fbcc00600c00300
def v167 : W := 0xb757f7b773fbcc00600c1c307
def v168 : W := 0xb757f7b773fbccd06c8cc0360
def v169 : W := 0xb757f7b773fbccd06c8cdc367
def v170 : W := 0xb757f7b773fbccd37fccddbff
def v171 : W := 0xb757f7b773fbccd3ef8cddf7f
def v172 : W := 0xb7f7ff0040010cfc6fc000000
def v173 : W := 0xea0f20ea07903003803001c00
def v174 : W := 0xea0f20fe27f0b003803f01f80
def v175 : W := 0xeaa808ea8c043ffc003fe2000
def v176 : W := 0xeaab28ea8d940fdf7fcfc3bf8
def v177 : W := 0xeba808eb9c0430e00030e0000
def v178 : W := 0xeba808eb9c0433ec0033e2000
def v179 : W := 0xeba808eb9c043cf0003ce0000
def v180 : W := 0xeba808ffbc0430e0003ffe000
def v181 : W := 0xeba808ffbffef0e0003cfc367
def v182 : W := 0xebab28eb9d9430e08c30e0460
def v183 : W := 0xebaf3c00000030e38f0000000
def v184 : W := 0xebaf3ceb9f9e40c00c00c0060
def v185 : W := 0xebaf3ceb9f9e40c30f00c1878
def v186 : W := 0xebaf3ceb9f9e7003833001c18
def v187 : W := 0xebaf3ceb9f9e70e00c30e0060
def v188 : W := 0xebaf3ceb9f9e70e08c30e0460
def v189 : W := 0xebaf3ceb9f9e70e38f30e1c78
def v190 : W := 0xebaf3cffbffef0e00c3ffe367
def v191 : W := 0xebaf3cffbffef0e38f33ffcff
def v192 : W := 0xebaf3cffbffef0e38f3cfdf7f
def v193 : W := 0xebf808ebdc0430fc0030fe000
def v194 : W := 0xebff3f00400130ff8fc000000
def v195 : W := 0xebff3febdf9f70f38fb0e1c78
def v196 : W := 0xebff3febdf9f70ff8ff0e1c78
def v197 : W := 0xfe0800fe24003f00003f00000
def v198 : W := 0xfe0fe00000003f03f00000000
def v199 : W := 0xfe0fe0b623f0bf03f00c00300
def v200 : W := 0xfe0fe0fe27f08f03700f01b80
def v201 : W := 0xfe0fe0fe27f0b303903301c80
def v202 : W := 0xfe0fe0fe27f0bc03e03c01f00
def v203 : W := 0xfe0fe0fe27f0bf00603f00300
def v204 : W := 0xfe0fe0fe27f0bf03f03f01f80
def v205 : W := 0xfe0fe0ff37faff03f03fddfe7
def v206 : W := 0xfe0fe0ffbffeff03f03f1ff9f
def v207 : W := 0xfe5fe30040013f1ff0c000000
def v208 : W := 0xfe5fe3fe67f1bf0ff07f01f80
def v209 : W := 0xfe5fe3fe67f1bf13f0bf01f80
def v210 : W := 0xfe5fe3fe67f1bf1ff0ff01f80
def v211 : W := 0xfe5fe3fe67f1bf1ff3ff01f80
def v212 : W := 0xfea808feac043f2c003f22000
def v213 : W := 0xfeafe8fe27f0bf2ff37f01f80
def v214 : W := 0xfeafe8feaff4bf0ff37f03f98
def v215 : W := 0xfeafe8feaff4bf23f33f21f98
def v216 : W := 0xfeafe8feaff4bf2c603f22300
def v217 : W := 0xfeafe8feaff4bf2ff03f23f80
def v218 : W := 0xfeffebfe67f1bf3ff3ff01f80
def v219 : W := 0xff5ff70040013fd3fc8000000
def v220 : W := 0xff5ff7fe67f1bf03f03f01f80
def v221 : W := 0xff5ff7fe67f1bfd3fcbf01f80
def v222 : W := 0xff5ff7ff77fbffd3fcbfddfe7
def v223 : W := 0xffa808ffbc043fe0003fe0000
def v224 : W := 0xffaffcffbffeff03f33f01f98
def v225 : W := 0xffaffcffbffeffe3ff3fe1ff8
def v226 : W := 0xfff8080040003ffc000000000
def v227 : W := 0xfff80848cc043ffc003322000
def v228 : W := 0xfff8085dfc043ffc00031e000
def v229 : W := 0xfff808ebdc043ffc0030e0000
def v230 : W := 0xfff808fffc040fdc000fde000
def v231 : W := 0xfff808fffc0433ec0033fe000
def v232 : W := 0xfff808fffc043cf0003cfc000
def v233 : W := 0xfff808fffc043f0c003f1e000
def v234 : W := 0xfff808fffc043ffc003ffe000
def v235 : W := 0xfff808fffffefffc003ffe367
def v236 : W := 0xfff81f0040013ffc0fc000000
def v237 : W := 0xfff81ffffc0f7ffc0cbffe067
def v238 : W := 0xfff8c8fffc64bffc703ffe380
def v239 : W := 0xfff8cb0040013ffc70c000000
def v240 : W := 0xfff8cbebdc053ffc70f0e0000
def v241 : W := 0xfff8cbfffc053ffc70fffe000
def v242 : W := 0xfff8cbfffc65bffc107ffe087
def v243 : W := 0xfff8cbfffc65bffc60bffe307
def v244 : W := 0xfffb28fffc043ffcecbffe000
def v245 : W := 0xfffb28fffd943ffc6cbffe360
def v246 : W := 0xfffb28fffd943ffc8c3ffe460
def v247 : W := 0xfffb28fffd943ffce03ffe700
def v248 : W := 0xfffcdf0040013fff134000000
def v249 : W := 0xfffcdffffe6ffffc003ffe007
def v250 : W := 0xfffcdffffe6fffff137fff89f
def v251 : W := 0xffff3cffff9e7ffc0c3ffe060
def v252 : W := 0xffff3cffff9e7fff8f3fffc78
def v253 : W := 0xffffe8fffff4bffc603ffe300
def v254 : W := 0xffffe8fffff4bffff03ffff80
def v255 : W := 0xffffff0040010fdf7fc000000
def v256 : W := 0xffffff00400133ef9f4000000
def v257 : W := 0xffffff0040013cf3ef8000000
def v258 : W := 0xffffff0040013f0ff34000000
def v259 : W := 0xffffff0040013ffc6c8000000
def v260 : W := 0xffffff0040013fffffc000000
def v261 : W := 0xffffff00439b7fffffc001c78
def v262 : W := 0xffffff0043f1bfffffc001f80
def v263 : W := 0xffffff01d80f7fffffc0e0078
def v264 : W := 0xffffff146061bfffffcf00380
def v265 : W := 0xffffff4844013ffffff301c80
def v266 : W := 0xffffff48cc053ffc6cb322000
def v267 : W := 0xffffff48cc053fffffc303898
def v268 : W := 0xffffff48cc053ffffff021c18
def v269 : W := 0xffffff48cc053ffffff322000
def v270 : W := 0xffffff49de0f7fffffc001818
def v271 : W := 0xffffff5c6661bfffffc301880
def v272 : W := 0xffffff5dfe6fffffffc31f89f
def v273 : W := 0xffffffa240013ffffffce0000
def v274 : W := 0xffffffa241913fffffccc0360
def v275 : W := 0xffffffa241913ffffff0e0460
def v276 : W := 0xffffffa241913ffffffc00700
def v277 : W := 0xffffffa3539b7fffffc0c0060
def v278 : W := 0xffffffb663f18f0f734c00300
def v279 : W := 0xffffffb663f1bfffffcc00300
def v280 : W := 0xffffffb773fbffffffccdc367
def v281 : W := 0xffffffea47913ffffff001c00
def v282 : W := 0xffffffebdc053cf06cb0e0000
def v283 : W := 0xffffffebdc053ffffff0e0000
def v284 : W := 0xffffffebdf9f70e38f30e1c78
def v285 : W := 0xffffffebdf9f73ef9f70e1c78
def v286 : W := 0xffffffebdf9f7cf3efb0e1c78
def v287 : W := 0xffffffebdf9f7ffc6cb0e0060
def v288 : W := 0xffffffebdf9f7ffffff0e0060
def v289 : W := 0xffffffebdf9f7ffffff0e1c78
def v290 : W := 0xfffffffe64013fffffff00000
def v291 : W := 0xfffffffe67f1bf0ff03f01f80
def v292 : W := 0xfffffffe67f1bf0ff37f01f80
def v293 : W := 0xfffffffe67f1bf1ff3ff01f80
def v294 : W := 0xfffffffe67f1bf2ff37f01f80
def v295 : W := 0xfffffffe67f1bfffffff01f80
def v296 : W := 0xfffffffeeff5bf0ff37f03f98
def v297 : W := 0xfffffffffc053ffc6cbffe000
def v298 : W := 0xfffffffffc053ffffffffe000
def v299 : W := 0xffffffffffffccd06c8cdc367
def v300 : W := 0xffffffffffffcfdc6c8fde367
def v301 : W := 0xffffffffffffcfdf7fcfdfbff
def v302 : W := 0xfffffffffffff3ef9f73ffcff
def v303 : W := 0xfffffffffffffcf06cbcfc367
def v304 : W := 0xfffffffffffffcf3efbcfdf7f
def v305 : W := 0xffffffffffffff0ff37f01f98
def v306 : W := 0xffffffffffffff0ff37f1ff9f
def v307 : W := 0xfffffffffffffffc6cbffe367
def v308 : W := 0xffffffffffffffffffffe1ff8

def ins : List W := [v124, v169, v189, v204, v234, v260]
theorem sampled : ∀ j : Fin 100, Nat.testBit 0xe8a8c888e8a0c880 (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
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
def level2 : BinaryTree (List W) := (.node [v124, v152, v187] (.node [v121, v163, v189] (.node [v121, v152, v189] .nil .nil) .nil) (.node [v124, v163, v187] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level2_ok : everyKey (rowOK 1 level1) level2 = true := by decide +kernel
theorem closed2 : Closed 2 level2 := closed_next 1 (by decide) level2 level1 closed1 level2_ok
def level3ll : BinaryTree (List W) := (.node [v119, v138, v204, v260] (.node [v118, v169, v186, v234] (.node [v74, v184, v204, v260] .nil .nil) .nil) (.node [v119, v144, v189, v260] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level3ll_ok : everyKey (rowOK 2 level2) level3ll = true := by decide +kernel
def level3lr : BinaryTree (List W) := (.node [v121, v169, v189, v210] (.node [v121, v164, v189, v204] .nil .nil) (.node [v121, v169, v189, v291] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level3lr_ok : everyKey (rowOK 2 level2) level3lr = true := by decide +kernel
def level3l : BinaryTree (List W) := .node [v121, v144, v155, v189] level3ll level3lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level3l_ok : everyKey (rowOK 2 level2) level3l = true := by
  change (_ && everyKey (rowOK 2 level2) level3ll && everyKey (rowOK 2 level2) level3lr) = true
  rw [level3ll_ok, level3lr_ok]
  decide +kernel
def level3rl : BinaryTree (List W) := (.node [v124, v163, v189, v307] (.node [v124, v152, v189, v307] (.node [v124, v144, v155, v187] .nil .nil) .nil) (.node [v124, v164, v187, v204] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level3rl_ok : everyKey (rowOK 2 level2) level3rl = true := by decide +kernel
def level3rr : BinaryTree (List W) := (.node [v124, v169, v187, v211] (.node [v124, v169, v187, v210] .nil .nil) (.node [v124, v169, v187, v292] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level3rr_ok : everyKey (rowOK 2 level2) level3rr = true := by decide +kernel
def level3r : BinaryTree (List W) := .node [v124, v166, v189, v234] level3rl level3rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level3r_ok : everyKey (rowOK 2 level2) level3r = true := by
  change (_ && everyKey (rowOK 2 level2) level3rl && everyKey (rowOK 2 level2) level3rr) = true
  rw [level3rl_ok, level3rr_ok]
  decide +kernel
def level3 : BinaryTree (List W) := .node [v121, v169, v189, v292] level3l level3r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level3_ok : everyKey (rowOK 2 level2) level3 = true := by
  change (_ && everyKey (rowOK 2 level2) level3l && everyKey (rowOK 2 level2) level3r) = true
  rw [level3l_ok, level3r_ok]
  decide +kernel
theorem closed3 : Closed 3 level3 := closed_next 2 (by decide) level3 level2 closed2 level3_ok
def level4lllll : BinaryTree (List W) := (.node [v8, v121, v169, v189, v204] (.node [v3, v124, v169, v189, v234] .nil .nil) (.node [v9, v121, v169, v189, v204] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lllll_ok : everyKey (rowOK 3 level3) level4lllll = true := by decide +kernel
def level4llllr : BinaryTree (List W) := (.node [v10, v124, v169, v187, v204] (.node [v10, v121, v169, v189, v204] .nil .nil) (.node [v20, v121, v169, v189, v204] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llllr_ok : everyKey (rowOK 3 level3) level4llllr = true := by decide +kernel
def level4llll : BinaryTree (List W) := .node [v9, v124, v169, v187, v204] level4lllll level4llllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llll_ok : everyKey (rowOK 3 level3) level4llll = true := by
  change (_ && everyKey (rowOK 3 level3) level4lllll && everyKey (rowOK 3 level3) level4llllr) = true
  rw [level4lllll_ok, level4llllr_ok]
  decide +kernel
def level4lllrl : BinaryTree (List W) := (.node [v22, v124, v169, v189, v292] (.node [v22, v124, v169, v189, v210] .nil .nil) (.node [v23, v124, v169, v189, v210] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lllrl_ok : everyKey (rowOK 3 level3) level4lllrl = true := by decide +kernel
def level4lllrr : BinaryTree (List W) := (.node [v35, v124, v169, v189, v204] (.node [v24, v124, v169, v189, v204] .nil .nil) (.node [v37, v124, v169, v189, v234] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lllrr_ok : everyKey (rowOK 3 level3) level4lllrr = true := by decide +kernel
def level4lllr : BinaryTree (List W) := .node [v23, v124, v169, v189, v292] level4lllrl level4lllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lllr_ok : everyKey (rowOK 3 level3) level4lllr = true := by
  change (_ && everyKey (rowOK 3 level3) level4lllrl && everyKey (rowOK 3 level3) level4lllrr) = true
  rw [level4lllrl_ok, level4lllrr_ok]
  decide +kernel
def level4lll : BinaryTree (List W) := .node [v20, v124, v169, v187, v204] level4llll level4lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lll_ok : everyKey (rowOK 3 level3) level4lll = true := by
  change (_ && everyKey (rowOK 3 level3) level4llll && everyKey (rowOK 3 level3) level4lllr) = true
  rw [level4llll_ok, level4lllr_ok]
  decide +kernel
def level4llrll : BinaryTree (List W) := (.node [v39, v124, v164, v189, v234] (.node [v39, v124, v148, v189, v234] .nil .nil) (.node [v39, v124, v169, v187, v260] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llrll_ok : everyKey (rowOK 3 level3) level4llrll = true := by decide +kernel
def level4llrlr : BinaryTree (List W) := (.node [v41, v124, v169, v189, v234] (.node [v40, v66, v124, v169, v234] .nil .nil) (.node [v42, v124, v169, v189, v234] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llrlr_ok : everyKey (rowOK 3 level3) level4llrlr = true := by decide +kernel
def level4llrl : BinaryTree (List W) := .node [v39, v124, v169, v195, v234] level4llrll level4llrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llrl_ok : everyKey (rowOK 3 level3) level4llrl = true := by
  change (_ && everyKey (rowOK 3 level3) level4llrll && everyKey (rowOK 3 level3) level4llrlr) = true
  rw [level4llrll_ok, level4llrlr_ok]
  decide +kernel
def level4llrrl : BinaryTree (List W) := (.node [v51, v121, v169, v189, v260] (.node [v45, v124, v169, v187, v204] .nil .nil) (.node [v51, v124, v169, v187, v260] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llrrl_ok : everyKey (rowOK 3 level3) level4llrrl = true := by decide +kernel
def level4llrrr : BinaryTree (List W) := (.node [v60, v121, v169, v189, v204] (.node [v54, v124, v169, v189, v260] .nil .nil) (.node [v60, v124, v169, v187, v204] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llrrr_ok : everyKey (rowOK 3 level3) level4llrrr = true := by decide +kernel
def level4llrr : BinaryTree (List W) := .node [v53, v124, v169, v189, v234] level4llrrl level4llrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llrr_ok : everyKey (rowOK 3 level3) level4llrr = true := by
  change (_ && everyKey (rowOK 3 level3) level4llrrl && everyKey (rowOK 3 level3) level4llrrr) = true
  rw [level4llrrl_ok, level4llrrr_ok]
  decide +kernel
def level4llr : BinaryTree (List W) := .node [v45, v121, v169, v189, v204] level4llrl level4llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llr_ok : everyKey (rowOK 3 level3) level4llr = true := by
  change (_ && everyKey (rowOK 3 level3) level4llrl && everyKey (rowOK 3 level3) level4llrr) = true
  rw [level4llrl_ok, level4llrr_ok]
  decide +kernel
def level4ll : BinaryTree (List W) := .node [v39, v121, v169, v189, v260] level4lll level4llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4ll_ok : everyKey (rowOK 3 level3) level4ll = true := by
  change (_ && everyKey (rowOK 3 level3) level4lll && everyKey (rowOK 3 level3) level4llr) = true
  rw [level4lll_ok, level4llr_ok]
  decide +kernel
def level4lrlll : BinaryTree (List W) := (.node [v68, v124, v169, v204, v234] (.node [v65, v121, v169, v204, v260] .nil .nil) (.node [v70, v124, v169, v204, v260] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrlll_ok : everyKey (rowOK 3 level3) level4lrlll = true := by decide +kernel
def level4lrllr : BinaryTree (List W) := (.node [v74, v185, v204, v234, v260] (.node [v74, v105, v144, v189, v260] .nil .nil) (.node [v74, v189, v204, v260, v300] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrllr_ok : everyKey (rowOK 3 level3) level4lrllr = true := by decide +kernel
def level4lrll : BinaryTree (List W) := .node [v72, v124, v169, v189, v204] level4lrlll level4lrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrll_ok : everyKey (rowOK 3 level3) level4lrll = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrlll && everyKey (rowOK 3 level3) level4lrllr) = true
  rw [level4lrlll_ok, level4lrllr_ok]
  decide +kernel
def level4lrlrl : BinaryTree (List W) := (.node [v85, v124, v169, v189, v292] (.node [v85, v124, v169, v189, v210] .nil .nil) (.node [v88, v124, v189, v204, v234] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrlrl_ok : everyKey (rowOK 3 level3) level4lrlrl = true := by decide +kernel
def level4lrlrr : BinaryTree (List W) := (.node [v92, v124, v189, v234, v260] (.node [v91, v124, v189, v204, v260] .nil .nil) (.node [v94, v165, v204, v234, v260] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrlrr_ok : everyKey (rowOK 3 level3) level4lrlrr = true := by decide +kernel
def level4lrlr : BinaryTree (List W) := .node [v90, v124, v169, v189, v204] level4lrlrl level4lrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrlr_ok : everyKey (rowOK 3 level3) level4lrlr = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrlrl && everyKey (rowOK 3 level3) level4lrlrr) = true
  rw [level4lrlrl_ok, level4lrlrr_ok]
  decide +kernel
def level4lrl : BinaryTree (List W) := .node [v76, v124, v169, v234, v260] level4lrll level4lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrl_ok : everyKey (rowOK 3 level3) level4lrl = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrll && everyKey (rowOK 3 level3) level4lrlr) = true
  rw [level4lrll_ok, level4lrlr_ok]
  decide +kernel
def level4lrrll : BinaryTree (List W) := (.node [v104, v124, v204, v234, v260] (.node [v103, v124, v169, v189, v204] .nil .nil) (.node [v105, v124, v169, v189, v210] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrrll_ok : everyKey (rowOK 3 level3) level4lrrll = true := by decide +kernel
def level4lrrlr : BinaryTree (List W) := (.node [v112, v121, v169, v189, v204] (.node [v111, v121, v169, v189, v204] .nil .nil) (.node [v112, v124, v169, v187, v204] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrrlr_ok : everyKey (rowOK 3 level3) level4lrrlr = true := by decide +kernel
def level4lrrl : BinaryTree (List W) := .node [v105, v124, v169, v189, v292] level4lrrll level4lrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrrl_ok : everyKey (rowOK 3 level3) level4lrrl = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrrll && everyKey (rowOK 3 level3) level4lrrlr) = true
  rw [level4lrrll_ok, level4lrrlr_ok]
  decide +kernel
def level4lrrrl : BinaryTree (List W) := (.node [v120, v138, v204, v234, v260] (.node [v119, v169, v189, v204, v260] .nil .nil) (.node [v121, v144, v169, v189, v260] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrrrl_ok : everyKey (rowOK 3 level3) level4lrrrl = true := by decide +kernel
def level4lrrrr : BinaryTree (List W) := (.node [v121, v169, v189, v203, v260] (.node [v121, v169, v187, v204, v260] .nil .nil) (.node [v121, v169, v189, v204, v259] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrrrr_ok : everyKey (rowOK 3 level3) level4lrrrr = true := by decide +kernel
def level4lrrr : BinaryTree (List W) := .node [v121, v155, v169, v189, v204] level4lrrrl level4lrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrrr_ok : everyKey (rowOK 3 level3) level4lrrr = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrrrl && everyKey (rowOK 3 level3) level4lrrrr) = true
  rw [level4lrrrl_ok, level4lrrrr_ok]
  decide +kernel
def level4lrr : BinaryTree (List W) := .node [v118, v169, v189, v234, v306] level4lrrl level4lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrr_ok : everyKey (rowOK 3 level3) level4lrr = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrrl && everyKey (rowOK 3 level3) level4lrrr) = true
  rw [level4lrrl_ok, level4lrrr_ok]
  decide +kernel
def level4lr : BinaryTree (List W) := .node [v98, v124, v169, v189, v260] level4lrl level4lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lr_ok : everyKey (rowOK 3 level3) level4lr = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrl && everyKey (rowOK 3 level3) level4lrr) = true
  rw [level4lrl_ok, level4lrr_ok]
  decide +kernel
def level4l : BinaryTree (List W) := .node [v61, v124, v169, v187, v204] level4ll level4lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4l_ok : everyKey (rowOK 3 level3) level4l = true := by
  change (_ && everyKey (rowOK 3 level3) level4ll && everyKey (rowOK 3 level3) level4lr) = true
  rw [level4ll_ok, level4lr_ok]
  decide +kernel
def level4rllll : BinaryTree (List W) := (.node [v121, v169, v189, v204, v295] (.node [v121, v169, v189, v204, v289] .nil .nil) (.node [v122, v169, v189, v204, v260] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rllll_ok : everyKey (rowOK 3 level3) level4rllll = true := by decide +kernel
def level4rlllr : BinaryTree (List W) := (.node [v124, v144, v155, v189, v307] (.node [v124, v138, v204, v260, v303] .nil .nil) (.node [v124, v144, v161, v189, v234] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlllr_ok : everyKey (rowOK 3 level3) level4rlllr = true := by decide +kernel
def level4rlll : BinaryTree (List W) := .node [v123, v169, v189, v204, v234] level4rllll level4rlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlll_ok : everyKey (rowOK 3 level3) level4rlll = true := by
  change (_ && everyKey (rowOK 3 level3) level4rllll && everyKey (rowOK 3 level3) level4rlllr) = true
  rw [level4rllll_ok, level4rlllr_ok]
  decide +kernel
def level4rllrl : BinaryTree (List W) := (.node [v124, v152, v169, v189, v234] (.node [v124, v144, v189, v260, v303] .nil .nil) (.node [v124, v153, v169, v189, v234] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rllrl_ok : everyKey (rowOK 3 level3) level4rllrl = true := by decide +kernel
def level4rllrr : BinaryTree (List W) := (.node [v124, v162, v169, v189, v204] (.node [v124, v159, v169, v189, v204] .nil .nil) (.node [v124, v163, v169, v189, v234] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rllrr_ok : everyKey (rowOK 3 level3) level4rllrr = true := by decide +kernel
def level4rllr : BinaryTree (List W) := .node [v124, v155, v169, v187, v204] level4rllrl level4rllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rllr_ok : everyKey (rowOK 3 level3) level4rllr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rllrl && everyKey (rowOK 3 level3) level4rllrr) = true
  rw [level4rllrl_ok, level4rllrr_ok]
  decide +kernel
def level4rll : BinaryTree (List W) := .node [v124, v144, v169, v187, v260] level4rlll level4rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rll_ok : everyKey (rowOK 3 level3) level4rll = true := by
  change (_ && everyKey (rowOK 3 level3) level4rlll && everyKey (rowOK 3 level3) level4rllr) = true
  rw [level4rlll_ok, level4rllr_ok]
  decide +kernel
def level4rlrll : BinaryTree (List W) := (.node [v124, v168, v189, v204, v234] (.node [v124, v167, v189, v234, v295] .nil .nil) (.node [v124, v169, v177, v189, v210] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlrll_ok : everyKey (rowOK 3 level3) level4rlrll = true := by decide +kernel
def level4rlrlr : BinaryTree (List W) := (.node [v124, v169, v177, v204, v285] (.node [v124, v169, v177, v196, v204] .nil .nil) (.node [v124, v169, v180, v189, v210] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlrlr_ok : everyKey (rowOK 3 level3) level4rlrlr = true := by decide +kernel
def level4rlrl : BinaryTree (List W) := .node [v124, v169, v177, v189, v292] level4rlrll level4rlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlrl_ok : everyKey (rowOK 3 level3) level4rlrl = true := by
  change (_ && everyKey (rowOK 3 level3) level4rlrll && everyKey (rowOK 3 level3) level4rlrlr) = true
  rw [level4rlrll_ok, level4rlrlr_ok]
  decide +kernel
def level4rlrrl : BinaryTree (List W) := (.node [v124, v169, v184, v204, v260] (.node [v124, v169, v182, v204, v289] .nil .nil) (.node [v124, v169, v186, v234, v295] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlrrl_ok : everyKey (rowOK 3 level3) level4rlrrl = true := by decide +kernel
def level4rlrrr : BinaryTree (List W) := (.node [v124, v169, v187, v204, v260] (.node [v124, v169, v187, v204, v259] .nil .nil) (.node [v124, v169, v187, v204, v288] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlrrr_ok : everyKey (rowOK 3 level3) level4rlrrr = true := by decide +kernel
def level4rlrr : BinaryTree (List W) := .node [v124, v169, v187, v203, v260] level4rlrrl level4rlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlrr_ok : everyKey (rowOK 3 level3) level4rlrr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rlrrl && everyKey (rowOK 3 level3) level4rlrrr) = true
  rw [level4rlrrl_ok, level4rlrrr_ok]
  decide +kernel
def level4rlr : BinaryTree (List W) := .node [v124, v169, v181, v189, v204] level4rlrl level4rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlr_ok : everyKey (rowOK 3 level3) level4rlr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rlrl && everyKey (rowOK 3 level3) level4rlrr) = true
  rw [level4rlrl_ok, level4rlrr_ok]
  decide +kernel
def level4rl : BinaryTree (List W) := .node [v124, v164, v189, v204, v307] level4rll level4rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rl_ok : everyKey (rowOK 3 level3) level4rl = true := by
  change (_ && everyKey (rowOK 3 level3) level4rll && everyKey (rowOK 3 level3) level4rlr) = true
  rw [level4rll_ok, level4rlr_ok]
  decide +kernel
def level4rrlll : BinaryTree (List W) := (.node [v124, v169, v188, v204, v260] (.node [v124, v169, v187, v204, v295] .nil .nil) (.node [v124, v169, v189, v190, v204] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrlll_ok : everyKey (rowOK 3 level3) level4rrlll = true := by decide +kernel
def level4rrllr : BinaryTree (List W) := (.node [v124, v169, v189, v204, v282] (.node [v124, v169, v189, v204, v266] .nil .nil) (.node [v124, v169, v189, v204, v287] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrllr_ok : everyKey (rowOK 3 level3) level4rrllr = true := by decide +kernel
def level4rrll : BinaryTree (List W) := .node [v124, v169, v189, v204, v240] level4rrlll level4rrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrll_ok : everyKey (rowOK 3 level3) level4rrll = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrlll && everyKey (rowOK 3 level3) level4rrllr) = true
  rw [level4rrlll_ok, level4rrllr_ok]
  decide +kernel
def level4rrlrl : BinaryTree (List W) := (.node [v124, v169, v189, v210, v234] (.node [v124, v169, v189, v209, v234] .nil .nil) (.node [v124, v169, v189, v210, v241] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrlrl_ok : everyKey (rowOK 3 level3) level4rrlrl = true := by decide +kernel
def level4rrlrr : BinaryTree (List W) := (.node [v124, v169, v189, v218, v234] (.node [v124, v169, v189, v216, v260] .nil .nil) (.node [v124, v169, v189, v220, v234] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrlrr_ok : everyKey (rowOK 3 level3) level4rrlrr = true := by decide +kernel
def level4rrlr : BinaryTree (List W) := .node [v124, v169, v189, v210, v307] level4rrlrl level4rrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrlr_ok : everyKey (rowOK 3 level3) level4rrlr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrlrl && everyKey (rowOK 3 level3) level4rrlrr) = true
  rw [level4rrlrl_ok, level4rrlrr_ok]
  decide +kernel
def level4rrl : BinaryTree (List W) := .node [v124, v169, v189, v208, v234] level4rrll level4rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrl_ok : everyKey (rowOK 3 level3) level4rrl = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrll && everyKey (rowOK 3 level3) level4rrlr) = true
  rw [level4rrll_ok, level4rrlr_ok]
  decide +kernel
def level4rrrll : BinaryTree (List W) := (.node [v124, v169, v189, v234, v293] (.node [v124, v169, v189, v234, v292] .nil .nil) (.node [v124, v169, v189, v234, v294] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrrll_ok : everyKey (rowOK 3 level3) level4rrrll = true := by decide +kernel
def level4rrrlr : BinaryTree (List W) := (.node [v124, v169, v189, v292, v307] (.node [v124, v169, v189, v234, v305] .nil .nil) (.node [v124, v169, v195, v204, v234] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrrlr_ok : everyKey (rowOK 3 level3) level4rrrlr = true := by decide +kernel
def level4rrrl : BinaryTree (List W) := .node [v124, v169, v189, v234, v296] level4rrrll level4rrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrrl_ok : everyKey (rowOK 3 level3) level4rrrl = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrrll && everyKey (rowOK 3 level3) level4rrrlr) = true
  rw [level4rrrll_ok, level4rrrlr_ok]
  decide +kernel
def level4rrrrl : BinaryTree (List W) := (.node [v128, v169, v189, v204, v234] (.node [v124, v189, v204, v260, v299] .nil .nil) (.node [v132, v169, v187, v204, v260] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrrrl_ok : everyKey (rowOK 3 level3) level4rrrrl = true := by decide +kernel
def level4rrrrr : BinaryTree (List W) := (.node [v151, v169, v204, v234, v260] (.node [v142, v169, v189, v234, v260] .nil .nil) (.node [v176, v189, v204, v234, v260] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrrrr_ok : everyKey (rowOK 3 level3) level4rrrrr = true := by decide +kernel
def level4rrrr : BinaryTree (List W) := .node [v136, v169, v189, v204, v260] level4rrrrl level4rrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrrr_ok : everyKey (rowOK 3 level3) level4rrrr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrrrl && everyKey (rowOK 3 level3) level4rrrrr) = true
  rw [level4rrrrl_ok, level4rrrrr_ok]
  decide +kernel
def level4rrr : BinaryTree (List W) := .node [v124, v169, v204, v234, v284] level4rrrl level4rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrr_ok : everyKey (rowOK 3 level3) level4rrr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrrl && everyKey (rowOK 3 level3) level4rrrr) = true
  rw [level4rrrl_ok, level4rrrr_ok]
  decide +kernel
def level4rr : BinaryTree (List W) := .node [v124, v169, v189, v234, v278] level4rrl level4rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rr_ok : everyKey (rowOK 3 level3) level4rr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrl && everyKey (rowOK 3 level3) level4rrr) = true
  rw [level4rrl_ok, level4rrr_ok]
  decide +kernel
def level4r : BinaryTree (List W) := .node [v124, v169, v187, v204, v289] level4rl level4rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4r_ok : everyKey (rowOK 3 level3) level4r = true := by
  change (_ && everyKey (rowOK 3 level3) level4rl && everyKey (rowOK 3 level3) level4rr) = true
  rw [level4rl_ok, level4rr_ok]
  decide +kernel
def level4 : BinaryTree (List W) := .node [v121, v169, v189, v204, v260] level4l level4r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4_ok : everyKey (rowOK 3 level3) level4 = true := by
  change (_ && everyKey (rowOK 3 level3) level4l && everyKey (rowOK 3 level3) level4r) = true
  rw [level4l_ok, level4r_ok]
  decide +kernel
theorem closed4 : Closed 4 level4 := closed_next 3 (by decide) level4 level3 closed3 level4_ok
def level5llllll : BinaryTree (List W) := (.node [v2, v39, v124, v169, v189, v234] (.node [v1, v124, v169, v189, v204, v260] (.node [v0, v124, v169, v189, v204, v260] .nil .nil) .nil) (.node [v4, v124, v169, v189, v204, v234] (.node [v2, v124, v169, v189, v204, v234] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llllll_ok : everyKey (rowOK 4 level4) level5llllll = true := by decide +kernel
def level5lllllr : BinaryTree (List W) := (.node [v9, v22, v124, v169, v189, v204] (.node [v7, v124, v169, v189, v204, v234] (.node [v6, v124, v169, v189, v204, v234] .nil .nil) .nil) (.node [v9, v39, v124, v169, v189, v234] (.node [v9, v23, v124, v169, v189, v204] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllllr_ok : everyKey (rowOK 4 level4) level5lllllr = true := by decide +kernel
def level5lllll : BinaryTree (List W) := .node [v5, v124, v169, v189, v204, v234] level5llllll level5lllllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllll_ok : everyKey (rowOK 4 level4) level5lllll = true := by
  change (_ && everyKey (rowOK 4 level4) level5llllll && everyKey (rowOK 4 level4) level5lllllr) = true
  rw [level5llllll_ok, level5lllllr_ok]
  decide +kernel
def level5llllrl : BinaryTree (List W) := (.node [v9, v124, v144, v169, v189, v234] (.node [v9, v112, v169, v189, v204, v234] (.node [v9, v105, v124, v169, v189, v204] .nil .nil) .nil) (.node [v9, v124, v169, v189, v204, v234] (.node [v9, v124, v169, v177, v189, v204] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llllrl_ok : everyKey (rowOK 4 level4) level5llllrl = true := by decide +kernel
def level5llllrr : BinaryTree (List W) := (.node [v10, v23, v124, v169, v189, v204] (.node [v10, v22, v124, v169, v189, v204] (.node [v9, v127, v169, v189, v204, v234] .nil .nil) .nil) (.node [v10, v39, v124, v169, v189, v234] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llllrr_ok : everyKey (rowOK 4 level4) level5llllrr = true := by decide +kernel
def level5llllr : BinaryTree (List W) := .node [v9, v124, v169, v189, v204, v307] level5llllrl level5llllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llllr_ok : everyKey (rowOK 4 level4) level5llllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llllrl && everyKey (rowOK 4 level4) level5llllrr) = true
  rw [level5llllrl_ok, level5llllrr_ok]
  decide +kernel
def level5llll : BinaryTree (List W) := .node [v9, v85, v124, v169, v189, v204] level5lllll level5llllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llll_ok : everyKey (rowOK 4 level4) level5llll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lllll && everyKey (rowOK 4 level4) level5llllr) = true
  rw [level5lllll_ok, level5llllr_ok]
  decide +kernel
def level5lllrll : BinaryTree (List W) := (.node [v10, v124, v144, v169, v189, v234] (.node [v10, v105, v124, v169, v189, v204] (.node [v10, v85, v124, v169, v189, v204] .nil .nil) .nil) (.node [v10, v124, v169, v177, v189, v204] (.node [v10, v124, v155, v189, v204, v234] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrll_ok : everyKey (rowOK 4 level4) level5lllrll = true := by decide +kernel
def level5lllrlr : BinaryTree (List W) := (.node [v10, v124, v169, v189, v204, v307] (.node [v10, v124, v169, v189, v204, v235] (.node [v10, v124, v169, v189, v204, v234] .nil .nil) .nil) (.node [v12, v45, v124, v169, v189, v234] (.node [v11, v60, v124, v169, v204, v234] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrlr_ok : everyKey (rowOK 4 level4) level5lllrlr = true := by decide +kernel
def level5lllrl : BinaryTree (List W) := .node [v10, v124, v169, v189, v204, v227] level5lllrll level5lllrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrl_ok : everyKey (rowOK 4 level4) level5lllrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lllrll && everyKey (rowOK 4 level4) level5lllrlr) = true
  rw [level5lllrll_ok, level5lllrlr_ok]
  decide +kernel
def level5lllrrl : BinaryTree (List W) := (.node [v16, v124, v169, v189, v204, v234] (.node [v15, v124, v169, v189, v204, v234] (.node [v14, v27, v124, v169, v189, v204] .nil .nil) .nil) (.node [v18, v124, v169, v189, v204, v234] (.node [v17, v124, v169, v189, v204, v234] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrrl_ok : everyKey (rowOK 4 level4) level5lllrrl = true := by decide +kernel
def level5lllrrr : BinaryTree (List W) := (.node [v21, v124, v169, v189, v204, v260] (.node [v20, v124, v169, v189, v204, v307] (.node [v20, v124, v169, v189, v204, v234] .nil .nil) .nil) (.node [v22, v39, v124, v169, v189, v260] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrrr_ok : everyKey (rowOK 4 level4) level5lllrrr = true := by decide +kernel
def level5lllrr : BinaryTree (List W) := .node [v19, v124, v169, v189, v204, v234] level5lllrrl level5lllrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrr_ok : everyKey (rowOK 4 level4) level5lllrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lllrrl && everyKey (rowOK 4 level4) level5lllrrr) = true
  rw [level5lllrrl_ok, level5lllrrr_ok]
  decide +kernel
def level5lllr : BinaryTree (List W) := .node [v13, v124, v169, v189, v204, v234] level5lllrl level5lllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllr_ok : everyKey (rowOK 4 level4) level5lllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lllrl && everyKey (rowOK 4 level4) level5lllrr) = true
  rw [level5lllrl_ok, level5lllrr_ok]
  decide +kernel
def level5lll : BinaryTree (List W) := .node [v10, v79, v124, v189, v204, v234] level5llll level5lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lll_ok : everyKey (rowOK 4 level4) level5lll = true := by
  change (_ && everyKey (rowOK 4 level4) level5llll && everyKey (rowOK 4 level4) level5lllr) = true
  rw [level5llll_ok, level5lllr_ok]
  decide +kernel
def level5llrlll : BinaryTree (List W) := (.node [v22, v112, v124, v169, v189, v204] (.node [v22, v105, v169, v189, v204, v260] (.node [v22, v60, v124, v169, v189, v204] .nil .nil) .nil) (.node [v22, v124, v155, v169, v189, v204] (.node [v22, v124, v144, v169, v189, v260] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrlll_ok : everyKey (rowOK 4 level4) level5llrlll = true := by decide +kernel
def level5llrllr : BinaryTree (List W) := (.node [v22, v126, v169, v189, v204, v260] (.node [v22, v124, v169, v189, v204, v295] (.node [v22, v124, v169, v189, v204, v289] .nil .nil) .nil) (.node [v23, v45, v124, v169, v189, v204] (.node [v23, v39, v124, v169, v189, v260] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrllr_ok : everyKey (rowOK 4 level4) level5llrllr = true := by decide +kernel
def level5llrll : BinaryTree (List W) := .node [v22, v124, v169, v189, v204, v260] level5llrlll level5llrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrll_ok : everyKey (rowOK 4 level4) level5llrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrlll && everyKey (rowOK 4 level4) level5llrllr) = true
  rw [level5llrlll_ok, level5llrllr_ok]
  decide +kernel
def level5llrlrl : BinaryTree (List W) := (.node [v23, v124, v144, v169, v189, v260] (.node [v23, v112, v124, v169, v189, v204] (.node [v23, v60, v124, v169, v189, v204] .nil .nil) .nil) (.node [v23, v124, v169, v177, v204, v260] (.node [v23, v124, v155, v169, v189, v204] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrlrl_ok : everyKey (rowOK 4 level4) level5llrlrl = true := by decide +kernel
def level5llrlrr : BinaryTree (List W) := (.node [v23, v124, v169, v189, v204, v289] (.node [v23, v124, v169, v189, v204, v261] (.node [v23, v124, v169, v189, v204, v260] .nil .nil) .nil) (.node [v23, v124, v169, v189, v204, v295] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrlrr_ok : everyKey (rowOK 4 level4) level5llrlrr = true := by decide +kernel
def level5llrlr : BinaryTree (List W) := .node [v23, v124, v169, v189, v204, v239] level5llrlrl level5llrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrlr_ok : everyKey (rowOK 4 level4) level5llrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrlrl && everyKey (rowOK 4 level4) level5llrlrr) = true
  rw [level5llrlrl_ok, level5llrlrr_ok]
  decide +kernel
def level5llrl : BinaryTree (List W) := .node [v23, v57, v124, v169, v204, v260] level5llrll level5llrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrl_ok : everyKey (rowOK 4 level4) level5llrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrll && everyKey (rowOK 4 level4) level5llrlr) = true
  rw [level5llrll_ok, level5llrlr_ok]
  decide +kernel
def level5llrrll : BinaryTree (List W) := (.node [v29, v124, v169, v189, v204, v260] (.node [v28, v124, v169, v189, v204, v260] (.node [v26, v124, v169, v189, v204, v260] .nil .nil) .nil) (.node [v30, v85, v124, v189, v204, v260] (.node [v29, v124, v169, v189, v204, v289] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrll_ok : everyKey (rowOK 4 level4) level5llrrll = true := by decide +kernel
def level5llrrlr : BinaryTree (List W) := (.node [v34, v124, v169, v189, v204, v260] (.node [v33, v124, v169, v189, v204, v260] (.node [v32, v124, v169, v189, v204, v260] .nil .nil) .nil) (.node [v38, v39, v124, v169, v189, v234] (.node [v36, v124, v169, v189, v204, v234] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrlr_ok : everyKey (rowOK 4 level4) level5llrrlr = true := by decide +kernel
def level5llrrl : BinaryTree (List W) := .node [v31, v124, v169, v189, v204, v260] level5llrrll level5llrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrl_ok : everyKey (rowOK 4 level4) level5llrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrrll && everyKey (rowOK 4 level4) level5llrrlr) = true
  rw [level5llrrll_ok, level5llrrlr_ok]
  decide +kernel
def level5llrrrl : BinaryTree (List W) := (.node [v39, v78, v124, v189, v234, v260] (.node [v39, v60, v124, v169, v189, v234] (.node [v39, v45, v124, v169, v189, v234] .nil .nil) .nil) (.node [v39, v105, v124, v169, v189, v260] (.node [v39, v85, v124, v169, v189, v260] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrrl_ok : everyKey (rowOK 4 level4) level5llrrrl = true := by decide +kernel
def level5llrrrr : BinaryTree (List W) := (.node [v39, v124, v169, v177, v189, v260] (.node [v39, v124, v155, v169, v189, v234] (.node [v39, v124, v144, v189, v234, v260] .nil .nil) .nil) (.node [v39, v124, v169, v189, v212, v260] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrrr_ok : everyKey (rowOK 4 level4) level5llrrrr = true := by decide +kernel
def level5llrrr : BinaryTree (List W) := .node [v39, v112, v124, v169, v189, v234] level5llrrrl level5llrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrr_ok : everyKey (rowOK 4 level4) level5llrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrrrl && everyKey (rowOK 4 level4) level5llrrrr) = true
  rw [level5llrrrl_ok, level5llrrrr_ok]
  decide +kernel
def level5llrr : BinaryTree (List W) := .node [v38, v124, v169, v189, v204, v234] level5llrrl level5llrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrr_ok : everyKey (rowOK 4 level4) level5llrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrrl && everyKey (rowOK 4 level4) level5llrrr) = true
  rw [level5llrrl_ok, level5llrrr_ok]
  decide +kernel
def level5llr : BinaryTree (List W) := .node [v25, v43, v124, v169, v189, v260] level5llrl level5llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llr_ok : everyKey (rowOK 4 level4) level5llr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrl && everyKey (rowOK 4 level4) level5llrr) = true
  rw [level5llrl_ok, level5llrr_ok]
  decide +kernel
def level5ll : BinaryTree (List W) := .node [v22, v45, v124, v169, v189, v204] level5lll level5llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5ll_ok : everyKey (rowOK 4 level4) level5ll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lll && everyKey (rowOK 4 level4) level5llr) = true
  rw [level5lll_ok, level5llr_ok]
  decide +kernel
def level5lrllll : BinaryTree (List W) := (.node [v39, v124, v169, v189, v237, v260] (.node [v39, v124, v169, v189, v234, v295] (.node [v39, v124, v169, v189, v234, v289] .nil .nil) .nil) (.node [v40, v56, v124, v169, v234, v260] (.node [v39, v124, v169, v189, v260, v307] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrllll_ok : everyKey (rowOK 4 level4) level5lrllll = true := by decide +kernel
def level5lrlllr : BinaryTree (List W) := (.node [v45, v105, v124, v169, v189, v204] (.node [v45, v85, v124, v169, v189, v204] (.node [v44, v124, v169, v189, v204, v234] .nil .nil) .nil) (.node [v45, v124, v169, v177, v189, v204] (.node [v45, v124, v144, v169, v189, v234] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlllr_ok : everyKey (rowOK 4 level4) level5lrlllr = true := by decide +kernel
def level5lrlll : BinaryTree (List W) := .node [v40, v124, v169, v189, v234, v295] level5lrllll level5lrlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlll_ok : everyKey (rowOK 4 level4) level5lrlll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrllll && everyKey (rowOK 4 level4) level5lrlllr) = true
  rw [level5lrllll_ok, level5lrlllr_ok]
  decide +kernel
def level5lrllrl : BinaryTree (List W) := (.node [v46, v124, v169, v189, v234, v260] (.node [v45, v124, v169, v189, v234, v295] (.node [v45, v124, v169, v189, v204, v307] .nil .nil) .nil) (.node [v48, v124, v169, v189, v234, v260] (.node [v47, v131, v169, v189, v234, v260] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrllrl_ok : everyKey (rowOK 4 level4) level5lrllrl = true := by decide +kernel
def level5lrllrr : BinaryTree (List W) := (.node [v51, v124, v169, v189, v260, v307] (.node [v51, v124, v169, v189, v234, v260] (.node [v50, v124, v169, v189, v234, v260] .nil .nil) .nil) (.node [v52, v124, v169, v189, v204, v234] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrllrr_ok : everyKey (rowOK 4 level4) level5lrllrr = true := by decide +kernel
def level5lrllr : BinaryTree (List W) := .node [v49, v124, v169, v189, v234, v260] level5lrllrl level5lrllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrllr_ok : everyKey (rowOK 4 level4) level5lrllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrllrl && everyKey (rowOK 4 level4) level5lrllrr) = true
  rw [level5lrllrl_ok, level5lrllrr_ok]
  decide +kernel
def level5lrll : BinaryTree (List W) := .node [v45, v124, v169, v189, v204, v234] level5lrlll level5lrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrll_ok : everyKey (rowOK 4 level4) level5lrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrlll && everyKey (rowOK 4 level4) level5lrllr) = true
  rw [level5lrlll_ok, level5lrllr_ok]
  decide +kernel
def level5lrlrll : BinaryTree (List W) := (.node [v60, v85, v124, v169, v189, v204] (.node [v59, v124, v169, v189, v204, v234] (.node [v58, v124, v169, v189, v204, v234] .nil .nil) .nil) (.node [v60, v124, v144, v169, v189, v234] (.node [v60, v105, v124, v169, v189, v204] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrll_ok : everyKey (rowOK 4 level4) level5lrlrll = true := by decide +kernel
def level5lrlrlr : BinaryTree (List W) := (.node [v60, v124, v169, v189, v204, v234] (.node [v60, v124, v169, v180, v189, v204] (.node [v60, v124, v169, v177, v189, v204] .nil .nil) .nil) (.node [v60, v124, v169, v189, v204, v307] (.node [v60, v124, v169, v189, v204, v241] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrlr_ok : everyKey (rowOK 4 level4) level5lrlrlr = true := by decide +kernel
def level5lrlrl : BinaryTree (List W) := .node [v60, v124, v169, v174, v189, v234] level5lrlrll level5lrlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrl_ok : everyKey (rowOK 4 level4) level5lrlrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrlrll && everyKey (rowOK 4 level4) level5lrlrlr) = true
  rw [level5lrlrll_ok, level5lrlrlr_ok]
  decide +kernel
def level5lrlrrl : BinaryTree (List W) := (.node [v63, v83, v124, v204, v234, v260] (.node [v62, v130, v169, v204, v234, v260] (.node [v60, v124, v169, v204, v234, v289] .nil .nil) .nil) (.node [v64, v124, v169, v204, v234, v260] (.node [v63, v124, v169, v177, v204, v260] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrrl_ok : everyKey (rowOK 4 level4) level5lrlrrl = true := by decide +kernel
def level5lrlrrr : BinaryTree (List W) := (.node [v67, v124, v169, v204, v234, v260] (.node [v66, v124, v169, v189, v204, v234] (.node [v65, v124, v169, v204, v260, v307] .nil .nil) .nil) (.node [v69, v124, v169, v189, v204, v260] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrrr_ok : everyKey (rowOK 4 level4) level5lrlrrr = true := by decide +kernel
def level5lrlrr : BinaryTree (List W) := .node [v65, v124, v169, v204, v234, v260] level5lrlrrl level5lrlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrr_ok : everyKey (rowOK 4 level4) level5lrlrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrlrrl && everyKey (rowOK 4 level4) level5lrlrrr) = true
  rw [level5lrlrrl_ok, level5lrlrrr_ok]
  decide +kernel
def level5lrlr : BinaryTree (List W) := .node [v60, v124, v169, v189, v210, v234] level5lrlrl level5lrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlr_ok : everyKey (rowOK 4 level4) level5lrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrlrl && everyKey (rowOK 4 level4) level5lrlrr) = true
  rw [level5lrlrl_ok, level5lrlrr_ok]
  decide +kernel
def level5lrl : BinaryTree (List W) := .node [v55, v124, v169, v189, v204, v234] level5lrll level5lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrl_ok : everyKey (rowOK 4 level4) level5lrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrll && everyKey (rowOK 4 level4) level5lrlr) = true
  rw [level5lrll_ok, level5lrlr_ok]
  decide +kernel
def level5lrrlll : BinaryTree (List W) := (.node [v74, v105, v169, v189, v204, v260] (.node [v73, v124, v169, v189, v204, v234] (.node [v71, v124, v169, v189, v204, v234] .nil .nil) .nil) (.node [v74, v189, v204, v234, v260, v301] (.node [v74, v124, v144, v189, v234, v260] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrlll_ok : everyKey (rowOK 4 level4) level5lrrlll = true := by decide +kernel
def level5lrrllr : BinaryTree (List W) := (.node [v81, v124, v144, v189, v234, v260] (.node [v80, v124, v169, v189, v204, v260] (.node [v77, v124, v169, v189, v204, v234] .nil .nil) .nil) (.node [v82, v124, v169, v189, v204, v260] (.node [v81, v129, v189, v204, v234, v260] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrllr_ok : everyKey (rowOK 4 level4) level5lrrllr = true := by decide +kernel
def level5lrrll : BinaryTree (List W) := .node [v75, v124, v169, v189, v204, v260] level5lrrlll level5lrrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrll_ok : everyKey (rowOK 4 level4) level5lrrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrlll && everyKey (rowOK 4 level4) level5lrrllr) = true
  rw [level5lrrlll_ok, level5lrrllr_ok]
  decide +kernel
def level5lrrlrl : BinaryTree (List W) := (.node [v85, v124, v145, v169, v189, v260] (.node [v85, v124, v144, v169, v189, v260] (.node [v85, v112, v124, v169, v189, v204] .nil .nil) .nil) (.node [v85, v124, v156, v169, v189, v204] (.node [v85, v124, v155, v169, v189, v204] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrlrl_ok : everyKey (rowOK 4 level4) level5lrrlrl = true := by decide +kernel
def level5lrrlrr : BinaryTree (List W) := (.node [v85, v124, v169, v189, v204, v295] (.node [v85, v124, v169, v189, v204, v289] (.node [v85, v124, v169, v189, v204, v269] .nil .nil) .nil) (.node [v85, v124, v169, v189, v217, v260] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrlrr_ok : everyKey (rowOK 4 level4) level5lrrlrr = true := by decide +kernel
def level5lrrlr : BinaryTree (List W) := .node [v85, v124, v169, v189, v204, v260] level5lrrlrl level5lrrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrlr_ok : everyKey (rowOK 4 level4) level5lrrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrlrl && everyKey (rowOK 4 level4) level5lrrlrr) = true
  rw [level5lrrlrl_ok, level5lrrlrr_ok]
  decide +kernel
def level5lrrl : BinaryTree (List W) := .node [v84, v124, v189, v204, v234, v260] level5lrrll level5lrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrl_ok : everyKey (rowOK 4 level4) level5lrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrll && everyKey (rowOK 4 level4) level5lrrlr) = true
  rw [level5lrrll_ok, level5lrrlr_ok]
  decide +kernel
def level5lrrrll : BinaryTree (List W) := (.node [v89, v124, v155, v169, v189, v204] (.node [v87, v124, v169, v189, v204, v234] (.node [v86, v124, v189, v204, v234, v260] .nil .nil) .nil) (.node [v93, v124, v169, v189, v204, v260] (.node [v89, v124, v169, v189, v204, v260] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrll_ok : everyKey (rowOK 4 level4) level5lrrrll = true := by decide +kernel
def level5lrrrlr : BinaryTree (List W) := (.node [v96, v124, v169, v189, v204, v260] (.node [v96, v124, v144, v169, v189, v260] (.node [v95, v124, v169, v189, v204, v234] .nil .nil) .nil) (.node [v97, v124, v169, v189, v204, v234] (.node [v97, v124, v144, v169, v189, v234] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrlr_ok : everyKey (rowOK 4 level4) level5lrrrlr = true := by decide +kernel
def level5lrrrl : BinaryTree (List W) := .node [v94, v169, v204, v234, v260, v302] level5lrrrll level5lrrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrl_ok : everyKey (rowOK 4 level4) level5lrrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrrll && everyKey (rowOK 4 level4) level5lrrrlr) = true
  rw [level5lrrrll_ok, level5lrrrlr_ok]
  decide +kernel
def level5lrrrrl : BinaryTree (List W) := (.node [v102, v124, v169, v189, v204, v234] (.node [v101, v124, v169, v189, v204, v260] (.node [v100, v124, v169, v189, v204, v234] .nil .nil) .nil) (.node [v105, v124, v144, v169, v189, v260] (.node [v105, v112, v124, v169, v189, v204] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrrl_ok : everyKey (rowOK 4 level4) level5lrrrrl = true := by decide +kernel
def level5lrrrrr : BinaryTree (List W) := (.node [v105, v124, v169, v189, v204, v295] (.node [v105, v124, v169, v189, v204, v289] (.node [v105, v124, v169, v189, v204, v260] .nil .nil) .nil) (.node [v105, v129, v169, v189, v204, v260] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrrr_ok : everyKey (rowOK 4 level4) level5lrrrrr = true := by decide +kernel
def level5lrrrr : BinaryTree (List W) := .node [v105, v124, v155, v169, v189, v204] level5lrrrrl level5lrrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrr_ok : everyKey (rowOK 4 level4) level5lrrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrrrl && everyKey (rowOK 4 level4) level5lrrrrr) = true
  rw [level5lrrrrl_ok, level5lrrrrr_ok]
  decide +kernel
def level5lrrr : BinaryTree (List W) := .node [v99, v169, v189, v234, v260, v306] level5lrrrl level5lrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrr_ok : everyKey (rowOK 4 level4) level5lrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrrl && everyKey (rowOK 4 level4) level5lrrrr) = true
  rw [level5lrrrl_ok, level5lrrrr_ok]
  decide +kernel
def level5lrr : BinaryTree (List W) := .node [v85, v124, v189, v204, v260, v307] level5lrrl level5lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrr_ok : everyKey (rowOK 4 level4) level5lrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrl && everyKey (rowOK 4 level4) level5lrrr) = true
  rw [level5lrrl_ok, level5lrrr_ok]
  decide +kernel
def level5lr : BinaryTree (List W) := .node [v71, v124, v169, v177, v189, v204] level5lrl level5lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lr_ok : everyKey (rowOK 4 level4) level5lr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrl && everyKey (rowOK 4 level4) level5lrr) = true
  rw [level5lrl_ok, level5lrr_ok]
  decide +kernel
def level5l : BinaryTree (List W) := .node [v39, v124, v169, v189, v234, v260] level5ll level5lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5l_ok : everyKey (rowOK 4 level4) level5l = true := by
  change (_ && everyKey (rowOK 4 level4) level5ll && everyKey (rowOK 4 level4) level5lr) = true
  rw [level5ll_ok, level5lr_ok]
  decide +kernel
def level5rlllll : BinaryTree (List W) := (.node [v108, v124, v169, v189, v204, v260] (.node [v107, v124, v169, v189, v204, v260] (.node [v106, v124, v169, v189, v204, v260] .nil .nil) .nil) (.node [v110, v124, v169, v189, v204, v260] (.node [v109, v124, v169, v189, v204, v260] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlllll_ok : everyKey (rowOK 4 level4) level5rlllll = true := by decide +kernel
def level5rllllr : BinaryTree (List W) := (.node [v112, v124, v169, v189, v204, v234] (.node [v112, v124, v169, v177, v189, v204] (.node [v112, v124, v144, v169, v189, v234] .nil .nil) .nil) (.node [v112, v124, v169, v189, v234, v292] (.node [v112, v124, v169, v189, v204, v307] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllllr_ok : everyKey (rowOK 4 level4) level5rllllr = true := by decide +kernel
def level5rllll : BinaryTree (List W) := .node [v112, v124, v135, v169, v189, v234] level5rlllll level5rllllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllll_ok : everyKey (rowOK 4 level4) level5rllll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlllll && everyKey (rowOK 4 level4) level5rllllr) = true
  rw [level5rlllll_ok, level5rllllr_ok]
  decide +kernel
def level5rlllrl : BinaryTree (List W) := (.node [v115, v124, v169, v189, v204, v234] (.node [v114, v124, v169, v189, v204, v234] (.node [v113, v124, v169, v189, v204, v234] .nil .nil) .nil) (.node [v117, v124, v169, v189, v204, v234] (.node [v116, v124, v169, v189, v204, v234] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlllrl_ok : everyKey (rowOK 4 level4) level5rlllrl = true := by decide +kernel
def level5rlllrr : BinaryTree (List W) := (.node [v121, v169, v189, v204, v234, v260] (.node [v121, v124, v169, v189, v204, v260] (.node [v120, v169, v189, v204, v234, v260] .nil .nil) .nil) (.node [v121, v169, v189, v204, v260] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlllrr_ok : everyKey (rowOK 4 level4) level5rlllrr = true := by decide +kernel
def level5rlllr : BinaryTree (List W) := .node [v118, v124, v169, v189, v204, v234] level5rlllrl level5rlllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlllr_ok : everyKey (rowOK 4 level4) level5rlllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlllrl && everyKey (rowOK 4 level4) level5rlllrr) = true
  rw [level5rlllrl_ok, level5rlllrr_ok]
  decide +kernel
def level5rlll : BinaryTree (List W) := .node [v112, v169, v189, v204, v234, v272] level5rllll level5rlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlll_ok : everyKey (rowOK 4 level4) level5rlll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rllll && everyKey (rowOK 4 level4) level5rlllr) = true
  rw [level5rllll_ok, level5rlllr_ok]
  decide +kernel
def level5rllrll : BinaryTree (List W) := (.node [v124, v134, v169, v189, v204, v234] (.node [v124, v131, v169, v189, v234, v295] (.node [v124, v125, v169, v189, v204, v234] .nil .nil) .nil) (.node [v124, v137, v169, v189, v204, v260] (.node [v124, v135, v169, v189, v234, v260] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrll_ok : everyKey (rowOK 4 level4) level5rllrll = true := by decide +kernel
def level5rllrlr : BinaryTree (List W) := (.node [v124, v140, v169, v189, v204, v234] (.node [v124, v139, v169, v189, v204, v260] (.node [v124, v138, v204, v234, v260, v304] .nil .nil) .nil) (.node [v124, v143, v169, v189, v234, v260] (.node [v124, v141, v169, v189, v204, v234] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrlr_ok : everyKey (rowOK 4 level4) level5rllrlr = true := by decide +kernel
def level5rllrl : BinaryTree (List W) := .node [v124, v138, v169, v177, v204, v260] level5rllrll level5rllrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrl_ok : everyKey (rowOK 4 level4) level5rllrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rllrll && everyKey (rowOK 4 level4) level5rllrlr) = true
  rw [level5rllrll_ok, level5rllrlr_ok]
  decide +kernel
def level5rllrrl : BinaryTree (List W) := (.node [v124, v144, v169, v189, v234, v279] (.node [v124, v144, v169, v189, v234, v260] (.node [v124, v144, v169, v177, v189, v260] .nil .nil) .nil) (.node [v124, v144, v169, v189, v234, v295] (.node [v124, v144, v169, v189, v234, v289] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrrl_ok : everyKey (rowOK 4 level4) level5rllrrl = true := by decide +kernel
def level5rllrrr : BinaryTree (List W) := (.node [v124, v145, v169, v189, v234, v260] (.node [v124, v144, v189, v222, v234, v260] (.node [v124, v144, v169, v189, v260, v307] .nil .nil) .nil) (.node [v124, v146, v169, v189, v234, v260] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrrr_ok : everyKey (rowOK 4 level4) level5rllrrr = true := by decide +kernel
def level5rllrr : BinaryTree (List W) := .node [v124, v144, v169, v189, v253, v260] level5rllrrl level5rllrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrr_ok : everyKey (rowOK 4 level4) level5rllrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rllrrl && everyKey (rowOK 4 level4) level5rllrrr) = true
  rw [level5rllrrl_ok, level5rllrrr_ok]
  decide +kernel
def level5rllr : BinaryTree (List W) := .node [v124, v144, v155, v169, v189, v234] level5rllrl level5rllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllr_ok : everyKey (rowOK 4 level4) level5rllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rllrl && everyKey (rowOK 4 level4) level5rllrr) = true
  rw [level5rllrl_ok, level5rllrr_ok]
  decide +kernel
def level5rll : BinaryTree (List W) := .node [v121, v169, v189, v204, v260, v307] level5rlll level5rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rll_ok : everyKey (rowOK 4 level4) level5rll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlll && everyKey (rowOK 4 level4) level5rllr) = true
  rw [level5rlll_ok, level5rllr_ok]
  decide +kernel
def level5rlrlll : BinaryTree (List W) := (.node [v124, v150, v169, v189, v204, v234] (.node [v124, v149, v169, v189, v234, v260] (.node [v124, v148, v169, v189, v204, v234] .nil .nil) .nil) (.node [v124, v155, v169, v177, v189, v204] (.node [v124, v154, v189, v204, v260, v307] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrlll_ok : everyKey (rowOK 4 level4) level5rlrlll = true := by decide +kernel
def level5rlrllr : BinaryTree (List W) := (.node [v124, v155, v189, v204, v234, v280] (.node [v124, v155, v169, v189, v204, v307] (.node [v124, v155, v169, v189, v204, v297] .nil .nil) .nil) (.node [v124, v157, v169, v189, v204, v234] (.node [v124, v156, v169, v189, v204, v234] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrllr_ok : everyKey (rowOK 4 level4) level5rlrllr = true := by decide +kernel
def level5rlrll : BinaryTree (List W) := .node [v124, v155, v169, v189, v204, v234] level5rlrlll level5rlrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrll_ok : everyKey (rowOK 4 level4) level5rlrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrlll && everyKey (rowOK 4 level4) level5rlrllr) = true
  rw [level5rlrlll_ok, level5rlrllr_ok]
  decide +kernel
def level5rlrlrl : BinaryTree (List W) := (.node [v124, v164, v169, v189, v204, v234] (.node [v124, v161, v169, v189, v204, v234] (.node [v124, v160, v169, v189, v204, v234] .nil .nil) .nil) (.node [v124, v167, v189, v204, v234, v260] (.node [v124, v165, v189, v204, v234, v260] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrlrl_ok : everyKey (rowOK 4 level4) level5rlrlrl = true := by decide +kernel
def level5rlrlrr : BinaryTree (List W) := (.node [v124, v169, v173, v189, v234, v295] (.node [v124, v169, v172, v189, v204, v234] (.node [v124, v169, v171, v189, v204, v260] .nil .nil) .nil) (.node [v124, v169, v173, v225, v234, v260] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrlrr_ok : everyKey (rowOK 4 level4) level5rlrlrr = true := by decide +kernel
def level5rlrlr : BinaryTree (List W) := .node [v124, v169, v170, v189, v204, v260] level5rlrlrl level5rlrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrlr_ok : everyKey (rowOK 4 level4) level5rlrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrlrl && everyKey (rowOK 4 level4) level5rlrlrr) = true
  rw [level5rlrlrl_ok, level5rlrlrr_ok]
  decide +kernel
def level5rlrl : BinaryTree (List W) := .node [v124, v158, v169, v189, v204, v234] level5rlrll level5rlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrl_ok : everyKey (rowOK 4 level4) level5rlrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrll && everyKey (rowOK 4 level4) level5rlrlr) = true
  rw [level5rlrll_ok, level5rlrlr_ok]
  decide +kernel
def level5rlrrll : BinaryTree (List W) := (.node [v124, v169, v177, v189, v204, v283] (.node [v124, v169, v177, v189, v204, v260] (.node [v124, v169, v175, v189, v204, v260] .nil .nil) .nil) (.node [v124, v169, v177, v189, v204, v295] (.node [v124, v169, v177, v189, v204, v289] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrll_ok : everyKey (rowOK 4 level4) level5rlrrll = true := by decide +kernel
def level5rlrrlr : BinaryTree (List W) := (.node [v124, v169, v180, v189, v204, v260] (.node [v124, v169, v179, v189, v204, v260] (.node [v124, v169, v178, v189, v204, v260] .nil .nil) .nil) (.node [v124, v169, v183, v204, v234, v289] (.node [v124, v169, v182, v189, v204, v260] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrlr_ok : everyKey (rowOK 4 level4) level5rlrrlr = true := by decide +kernel
def level5rlrrl : BinaryTree (List W) := .node [v124, v169, v177, v204, v252, v260] level5rlrrll level5rlrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrl_ok : everyKey (rowOK 4 level4) level5rlrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrrll && everyKey (rowOK 4 level4) level5rlrrlr) = true
  rw [level5rlrrll_ok, level5rlrrlr_ok]
  decide +kernel
def level5rlrrrl : BinaryTree (List W) := (.node [v124, v169, v187, v204, v234, v260] (.node [v124, v169, v187, v189, v204, v260] (.node [v124, v169, v186, v204, v234, v260] .nil .nil) .nil) (.node [v124, v169, v187, v204, v260, v307] (.node [v124, v169, v187, v204, v260] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrrl_ok : everyKey (rowOK 4 level4) level5rlrrrl = true := by decide +kernel
def level5rlrrrr : BinaryTree (List W) := (.node [v124, v169, v189, v194, v204, v234] (.node [v124, v169, v189, v193, v204, v260] (.node [v124, v169, v189, v192, v204, v234] .nil .nil) .nil) (.node [v124, v169, v189, v196, v204, v234] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrrr_ok : everyKey (rowOK 4 level4) level5rlrrrr = true := by decide +kernel
def level5rlrrr : BinaryTree (List W) := .node [v124, v169, v189, v191, v204, v234] level5rlrrrl level5rlrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrr_ok : everyKey (rowOK 4 level4) level5rlrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrrrl && everyKey (rowOK 4 level4) level5rlrrrr) = true
  rw [level5rlrrrl_ok, level5rlrrrr_ok]
  decide +kernel
def level5rlrr : BinaryTree (List W) := .node [v124, v169, v185, v204, v234, v260] level5rlrrl level5rlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrr_ok : everyKey (rowOK 4 level4) level5rlrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrrl && everyKey (rowOK 4 level4) level5rlrrr) = true
  rw [level5rlrrl_ok, level5rlrrr_ok]
  decide +kernel
def level5rlr : BinaryTree (List W) := .node [v124, v169, v174, v189, v234, v260] level5rlrl level5rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlr_ok : everyKey (rowOK 4 level4) level5rlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrl && everyKey (rowOK 4 level4) level5rlrr) = true
  rw [level5rlrl_ok, level5rlrr_ok]
  decide +kernel
def level5rl : BinaryTree (List W) := .node [v124, v147, v169, v189, v234, v260] level5rll level5rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rl_ok : everyKey (rowOK 4 level4) level5rl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rll && everyKey (rowOK 4 level4) level5rlr) = true
  rw [level5rll_ok, level5rlr_ok]
  decide +kernel
def level5rrllll : BinaryTree (List W) := (.node [v124, v169, v189, v200, v234, v260] (.node [v124, v169, v189, v199, v234, v260] (.node [v124, v169, v189, v198, v234, v295] .nil .nil) .nil) (.node [v124, v169, v189, v202, v234, v260] (.node [v124, v169, v189, v201, v234, v260] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrllll_ok : everyKey (rowOK 4 level4) level5rrllll = true := by decide +kernel
def level5rrlllr : BinaryTree (List W) := (.node [v124, v169, v189, v204, v206, v234] (.node [v124, v169, v189, v204, v205, v234] (.node [v124, v169, v189, v203, v260, v307] .nil .nil) .nil) (.node [v124, v169, v189, v204, v210, v234] (.node [v124, v169, v189, v204, v207, v234] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlllr_ok : everyKey (rowOK 4 level4) level5rrlllr = true := by decide +kernel
def level5rrlll : BinaryTree (List W) := .node [v124, v169, v189, v203, v234, v260] level5rrllll level5rrlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlll_ok : everyKey (rowOK 4 level4) level5rrlll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrllll && everyKey (rowOK 4 level4) level5rrlllr) = true
  rw [level5rrllll_ok, level5rrlllr_ok]
  decide +kernel
def level5rrllrl : BinaryTree (List W) := (.node [v124, v169, v189, v204, v223, v260] (.node [v124, v169, v189, v204, v221, v234] (.node [v124, v169, v189, v204, v219, v234] .nil .nil) .nil) (.node [v124, v169, v189, v204, v227, v260] (.node [v124, v169, v189, v204, v226, v298] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrllrl_ok : everyKey (rowOK 4 level4) level5rrllrl = true := by decide +kernel
def level5rrllrr : BinaryTree (List W) := (.node [v124, v169, v189, v204, v230, v260] (.node [v124, v169, v189, v204, v229, v289] (.node [v124, v169, v189, v204, v229, v260] .nil .nil) .nil) (.node [v124, v169, v189, v204, v231, v260] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrllrr_ok : everyKey (rowOK 4 level4) level5rrllrr = true := by decide +kernel
def level5rrllr : BinaryTree (List W) := .node [v124, v169, v189, v204, v228, v260] level5rrllrl level5rrllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrllr_ok : everyKey (rowOK 4 level4) level5rrllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrllrl && everyKey (rowOK 4 level4) level5rrllrr) = true
  rw [level5rrllrl_ok, level5rrllrr_ok]
  decide +kernel
def level5rrll : BinaryTree (List W) := .node [v124, v169, v189, v204, v212, v260] level5rrlll level5rrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrll_ok : everyKey (rowOK 4 level4) level5rrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrlll && everyKey (rowOK 4 level4) level5rrllr) = true
  rw [level5rrlll_ok, level5rrllr_ok]
  decide +kernel
def level5rrlrll : BinaryTree (List W) := (.node [v124, v169, v189, v204, v234, v239] (.node [v124, v169, v189, v204, v234, v236] (.node [v124, v169, v189, v204, v233, v260] .nil .nil) .nil) (.node [v124, v169, v189, v204, v234, v255] (.node [v124, v169, v189, v204, v234, v248] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrll_ok : everyKey (rowOK 4 level4) level5rrlrll = true := by decide +kernel
def level5rrlrlr : BinaryTree (List W) := (.node [v124, v169, v189, v204, v234, v259] (.node [v124, v169, v189, v204, v234, v258] (.node [v124, v169, v189, v204, v234, v257] .nil .nil) .nil) (.node [v124, v169, v189, v204, v234, v261] (.node [v124, v169, v189, v204, v234, v260] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrlr_ok : everyKey (rowOK 4 level4) level5rrlrlr = true := by decide +kernel
def level5rrlrl : BinaryTree (List W) := .node [v124, v169, v189, v204, v234, v256] level5rrlrll level5rrlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrl_ok : everyKey (rowOK 4 level4) level5rrlrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrlrll && everyKey (rowOK 4 level4) level5rrlrlr) = true
  rw [level5rrlrll_ok, level5rrlrlr_ok]
  decide +kernel
def level5rrlrrl : BinaryTree (List W) := (.node [v124, v169, v189, v204, v234, v265] (.node [v124, v169, v189, v204, v234, v264] (.node [v124, v169, v189, v204, v234, v263] .nil .nil) .nil) (.node [v124, v169, v189, v204, v234, v268] (.node [v124, v169, v189, v204, v234, v267] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrrl_ok : everyKey (rowOK 4 level4) level5rrlrrl = true := by decide +kernel
def level5rrlrrr : BinaryTree (List W) := (.node [v124, v169, v189, v204, v234, v273] (.node [v124, v169, v189, v204, v234, v271] (.node [v124, v169, v189, v204, v234, v270] .nil .nil) .nil) (.node [v124, v169, v189, v204, v234, v274] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrrr_ok : everyKey (rowOK 4 level4) level5rrlrrr = true := by decide +kernel
def level5rrlrr : BinaryTree (List W) := .node [v124, v169, v189, v204, v234, v269] level5rrlrrl level5rrlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrr_ok : everyKey (rowOK 4 level4) level5rrlrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrlrrl && everyKey (rowOK 4 level4) level5rrlrrr) = true
  rw [level5rrlrrl_ok, level5rrlrrr_ok]
  decide +kernel
def level5rrlr : BinaryTree (List W) := .node [v124, v169, v189, v204, v234, v262] level5rrlrl level5rrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlr_ok : everyKey (rowOK 4 level4) level5rrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrlrl && everyKey (rowOK 4 level4) level5rrlrr) = true
  rw [level5rrlrl_ok, level5rrlrr_ok]
  decide +kernel
def level5rrl : BinaryTree (List W) := .node [v124, v169, v189, v204, v232, v260] level5rrll level5rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrl_ok : everyKey (rowOK 4 level4) level5rrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrll && everyKey (rowOK 4 level4) level5rrlr) = true
  rw [level5rrll_ok, level5rrlr_ok]
  decide +kernel
def level5rrrlll : BinaryTree (List W) := (.node [v124, v169, v189, v204, v234, v279] (.node [v124, v169, v189, v204, v234, v277] (.node [v124, v169, v189, v204, v234, v276] .nil .nil) .nil) (.node [v124, v169, v189, v204, v234, v283] (.node [v124, v169, v189, v204, v234, v281] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrlll_ok : everyKey (rowOK 4 level4) level5rrrlll = true := by decide +kernel
def level5rrrllr : BinaryTree (List W) := (.node [v124, v169, v189, v204, v234, v290] (.node [v124, v169, v189, v204, v234, v289] (.node [v124, v169, v189, v204, v234, v286] .nil .nil) .nil) (.node [v124, v169, v189, v204, v234, v295] (.node [v124, v169, v189, v204, v234, v292] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrllr_ok : everyKey (rowOK 4 level4) level5rrrllr = true := by decide +kernel
def level5rrrll : BinaryTree (List W) := .node [v124, v169, v189, v204, v234, v285] level5rrrlll level5rrrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrll_ok : everyKey (rowOK 4 level4) level5rrrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrlll && everyKey (rowOK 4 level4) level5rrrllr) = true
  rw [level5rrrlll_ok, level5rrrllr_ok]
  decide +kernel
def level5rrrlrl : BinaryTree (List W) := (.node [v124, v169, v189, v204, v238, v260] (.node [v124, v169, v189, v204, v237, v260] (.node [v124, v169, v189, v204, v235, v260] .nil .nil) .nil) (.node [v124, v169, v189, v204, v242, v260] (.node [v124, v169, v189, v204, v241, v260] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrlrl_ok : everyKey (rowOK 4 level4) level5rrrlrl = true := by decide +kernel
def level5rrrlrr : BinaryTree (List W) := (.node [v124, v169, v189, v204, v246, v260] (.node [v124, v169, v189, v204, v245, v260] (.node [v124, v169, v189, v204, v244, v260] .nil .nil) .nil) (.node [v124, v169, v189, v204, v247, v260] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrlrr_ok : everyKey (rowOK 4 level4) level5rrrlrr = true := by decide +kernel
def level5rrrlr : BinaryTree (List W) := .node [v124, v169, v189, v204, v243, v260] level5rrrlrl level5rrrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrlr_ok : everyKey (rowOK 4 level4) level5rrrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrlrl && everyKey (rowOK 4 level4) level5rrrlrr) = true
  rw [level5rrrlrl_ok, level5rrrlrr_ok]
  decide +kernel
def level5rrrl : BinaryTree (List W) := .node [v124, v169, v189, v204, v234, v308] level5rrrll level5rrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrl_ok : everyKey (rowOK 4 level4) level5rrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrll && everyKey (rowOK 4 level4) level5rrrlr) = true
  rw [level5rrrll_ok, level5rrrlr_ok]
  decide +kernel
def level5rrrrll : BinaryTree (List W) := (.node [v124, v169, v189, v204, v259, v307] (.node [v124, v169, v189, v204, v253, v260] (.node [v124, v169, v189, v204, v251, v260] .nil .nil) .nil) (.node [v124, v169, v189, v204, v260, v300] (.node [v124, v169, v189, v204, v260, v297] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrll_ok : everyKey (rowOK 4 level4) level5rrrrll = true := by decide +kernel
def level5rrrrlr : BinaryTree (List W) := (.node [v124, v169, v189, v204, v295, v307] (.node [v124, v169, v189, v204, v289, v307] (.node [v124, v169, v189, v204, v260, v307] .nil .nil) .nil) (.node [v124, v169, v189, v210, v234, v260] (.node [v124, v169, v189, v210, v234] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrlr_ok : everyKey (rowOK 4 level4) level5rrrrlr = true := by decide +kernel
def level5rrrrl : BinaryTree (List W) := .node [v124, v169, v189, v204, v260, v303] level5rrrrll level5rrrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrl_ok : everyKey (rowOK 4 level4) level5rrrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrrll && everyKey (rowOK 4 level4) level5rrrrlr) = true
  rw [level5rrrrll_ok, level5rrrrlr_ok]
  decide +kernel
def level5rrrrrl : BinaryTree (List W) := (.node [v124, v169, v189, v217, v234, v260] (.node [v124, v169, v189, v215, v234, v260] (.node [v124, v169, v189, v214, v234, v260] .nil .nil) .nil) (.node [v124, v169, v189, v234, v260, v292] (.node [v124, v169, v189, v224, v234, v260] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrrl_ok : everyKey (rowOK 4 level4) level5rrrrrl = true := by decide +kernel
def level5rrrrrr : BinaryTree (List W) := (.node [v132, v169, v189, v204, v260, v307] (.node [v132, v169, v189, v204, v234, v260] (.node [v124, v169, v189, v234, v295, v306] .nil .nil) .nil) (.node [v133, v169, v189, v204, v234, v260] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrrr_ok : everyKey (rowOK 4 level4) level5rrrrrr = true := by decide +kernel
def level5rrrrr : BinaryTree (List W) := .node [v124, v169, v189, v234, v292] level5rrrrrl level5rrrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrr_ok : everyKey (rowOK 4 level4) level5rrrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrrrl && everyKey (rowOK 4 level4) level5rrrrrr) = true
  rw [level5rrrrrl_ok, level5rrrrrr_ok]
  decide +kernel
def level5rrrr : BinaryTree (List W) := .node [v124, v169, v189, v213, v234, v260] level5rrrrl level5rrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrr_ok : everyKey (rowOK 4 level4) level5rrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrrl && everyKey (rowOK 4 level4) level5rrrrr) = true
  rw [level5rrrrl_ok, level5rrrrr_ok]
  decide +kernel
def level5rrr : BinaryTree (List W) := .node [v124, v169, v189, v204, v249, v260] level5rrrl level5rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrr_ok : everyKey (rowOK 4 level4) level5rrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrl && everyKey (rowOK 4 level4) level5rrrr) = true
  rw [level5rrrl_ok, level5rrrr_ok]
  decide +kernel
def level5rr : BinaryTree (List W) := .node [v124, v169, v189, v204, v234, v275] level5rrl level5rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rr_ok : everyKey (rowOK 4 level4) level5rr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrl && everyKey (rowOK 4 level4) level5rrr) = true
  rw [level5rrl_ok, level5rrr_ok]
  decide +kernel
def level5r : BinaryTree (List W) := .node [v124, v169, v189, v197, v254, v260] level5rl level5rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5r_ok : everyKey (rowOK 4 level4) level5r = true := by
  change (_ && everyKey (rowOK 4 level4) level5rl && everyKey (rowOK 4 level4) level5rr) = true
  rw [level5rl_ok, level5rr_ok]
  decide +kernel
def level5 : BinaryTree (List W) := .node [v105, v169, v189, v204, v250, v260] level5l level5r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5_ok : everyKey (rowOK 4 level4) level5 = true := by
  change (_ && everyKey (rowOK 4 level4) level5l && everyKey (rowOK 4 level4) level5r) = true
  rw [level5l_ok, level5r_ok]
  decide +kernel
theorem closed5 : Closed 5 level5 := closed_next 4 (by decide) level5 level4 closed4 level5_ok
def level6llll : BinaryTree (List W) := (.node [v10, v124, v169, v189, v204, v234] (.node [v9, v124, v169, v189, v204, v234, v260] (.node [v9, v124, v169, v189, v204, v234] .nil .nil) .nil) (.node [v10, v124, v169, v189, v204, v234, v260] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llll_ok : everyKey (rowOK 5 level5) level6llll = true := by decide +kernel
def level6lllr : BinaryTree (List W) := (.node [v22, v124, v169, v189, v204, v234, v260] (.node [v14, v124, v169, v189, v204, v234, v260] (.node [v12, v124, v169, v189, v204, v234, v260] .nil .nil) .nil) (.node [v22, v124, v169, v189, v204, v260] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllr_ok : everyKey (rowOK 5 level5) level6lllr = true := by decide +kernel
def level6lll : BinaryTree (List W) := .node [v11, v124, v169, v189, v204, v234, v260] level6llll level6lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lll_ok : everyKey (rowOK 5 level5) level6lll = true := by
  change (_ && everyKey (rowOK 5 level5) level6llll && everyKey (rowOK 5 level5) level6lllr) = true
  rw [level6llll_ok, level6lllr_ok]
  decide +kernel
def level6llrl : BinaryTree (List W) := (.node [v27, v124, v169, v189, v204, v234, v260] (.node [v25, v124, v169, v189, v204, v234, v260] (.node [v23, v124, v169, v189, v204, v260] .nil .nil) .nil) (.node [v30, v124, v169, v189, v204, v234, v260] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrl_ok : everyKey (rowOK 5 level5) level6llrl = true := by decide +kernel
def level6llrr : BinaryTree (List W) := (.node [v43, v124, v169, v189, v204, v234, v260] (.node [v40, v124, v169, v189, v204, v234, v260] (.node [v39, v124, v169, v189, v234, v260] .nil .nil) .nil) (.node [v45, v124, v169, v189, v204, v234] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrr_ok : everyKey (rowOK 5 level5) level6llrr = true := by decide +kernel
def level6llr : BinaryTree (List W) := .node [v39, v124, v169, v189, v204, v234, v260] level6llrl level6llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llr_ok : everyKey (rowOK 5 level5) level6llr = true := by
  change (_ && everyKey (rowOK 5 level5) level6llrl && everyKey (rowOK 5 level5) level6llrr) = true
  rw [level6llrl_ok, level6llrr_ok]
  decide +kernel
def level6ll : BinaryTree (List W) := .node [v23, v124, v169, v189, v204, v234, v260] level6lll level6llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6ll_ok : everyKey (rowOK 5 level5) level6ll = true := by
  change (_ && everyKey (rowOK 5 level5) level6lll && everyKey (rowOK 5 level5) level6llr) = true
  rw [level6lll_ok, level6llr_ok]
  decide +kernel
def level6lrll : BinaryTree (List W) := (.node [v57, v124, v169, v189, v204, v234, v260] (.node [v56, v124, v169, v189, v204, v234, v260] (.node [v47, v124, v169, v189, v204, v234, v260] .nil .nil) .nil) (.node [v60, v124, v169, v189, v204, v234] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrll_ok : everyKey (rowOK 5 level5) level6lrll = true := by decide +kernel
def level6lrlr : BinaryTree (List W) := (.node [v74, v124, v169, v189, v204, v234, v260] (.node [v63, v124, v169, v189, v204, v234, v260] (.node [v62, v124, v169, v189, v204, v234, v260] .nil .nil) .nil) (.node [v78, v124, v169, v189, v204, v234, v260] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlr_ok : everyKey (rowOK 5 level5) level6lrlr = true := by decide +kernel
def level6lrl : BinaryTree (List W) := .node [v60, v124, v169, v189, v204, v234, v260] level6lrll level6lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrl_ok : everyKey (rowOK 5 level5) level6lrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrll && everyKey (rowOK 5 level5) level6lrlr) = true
  rw [level6lrll_ok, level6lrlr_ok]
  decide +kernel
def level6lrrl : BinaryTree (List W) := (.node [v85, v124, v169, v189, v204, v234, v260] (.node [v83, v124, v169, v189, v204, v234, v260] (.node [v81, v124, v169, v189, v204, v234, v260] .nil .nil) .nil) (.node [v85, v124, v169, v189, v204, v260] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrl_ok : everyKey (rowOK 5 level5) level6lrrl = true := by decide +kernel
def level6lrrr : BinaryTree (List W) := (.node [v105, v124, v169, v189, v204, v234, v260] (.node [v99, v124, v169, v189, v204, v234, v260] .nil .nil) (.node [v105, v124, v169, v189, v204, v260] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrr_ok : everyKey (rowOK 5 level5) level6lrrr = true := by decide +kernel
def level6lrr : BinaryTree (List W) := .node [v94, v124, v169, v189, v204, v234, v260] level6lrrl level6lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrr_ok : everyKey (rowOK 5 level5) level6lrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrrl && everyKey (rowOK 5 level5) level6lrrr) = true
  rw [level6lrrl_ok, level6lrrr_ok]
  decide +kernel
def level6lr : BinaryTree (List W) := .node [v79, v124, v169, v189, v204, v234, v260] level6lrl level6lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lr_ok : everyKey (rowOK 5 level5) level6lr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrl && everyKey (rowOK 5 level5) level6lrr) = true
  rw [level6lrl_ok, level6lrr_ok]
  decide +kernel
def level6l : BinaryTree (List W) := .node [v45, v124, v169, v189, v204, v234, v260] level6ll level6lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6l_ok : everyKey (rowOK 5 level5) level6l = true := by
  change (_ && everyKey (rowOK 5 level5) level6ll && everyKey (rowOK 5 level5) level6lr) = true
  rw [level6ll_ok, level6lr_ok]
  decide +kernel
def level6rlll : BinaryTree (List W) := (.node [v124, v127, v169, v189, v204, v234, v260] (.node [v124, v126, v169, v189, v204, v234, v260] (.node [v112, v124, v169, v189, v204, v234, v260] .nil .nil) .nil) (.node [v124, v129, v169, v189, v204, v234, v260] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlll_ok : everyKey (rowOK 5 level5) level6rlll = true := by decide +kernel
def level6rllr : BinaryTree (List W) := (.node [v124, v144, v169, v189, v204, v234, v260] (.node [v124, v138, v169, v189, v204, v234, v260] (.node [v124, v131, v169, v189, v204, v234, v260] .nil .nil) .nil) (.node [v124, v144, v169, v189, v234, v260] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllr_ok : everyKey (rowOK 5 level5) level6rllr = true := by decide +kernel
def level6rll : BinaryTree (List W) := .node [v124, v130, v169, v189, v204, v234, v260] level6rlll level6rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rll_ok : everyKey (rowOK 5 level5) level6rll = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlll && everyKey (rowOK 5 level5) level6rllr) = true
  rw [level6rlll_ok, level6rllr_ok]
  decide +kernel
def level6rlrl : BinaryTree (List W) := (.node [v124, v169, v173, v189, v204, v234, v260] (.node [v124, v155, v169, v189, v204, v234, v260] (.node [v124, v155, v169, v189, v204, v234] .nil .nil) .nil) (.node [v124, v169, v177, v189, v204, v234, v260] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrl_ok : everyKey (rowOK 5 level5) level6rlrl = true := by decide +kernel
def level6rlrr : BinaryTree (List W) := (.node [v124, v169, v189, v197, v204, v234, v260] (.node [v124, v169, v183, v189, v204, v234, v260] .nil .nil) (.node [v124, v169, v189, v198, v204, v234, v260] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrr_ok : everyKey (rowOK 5 level5) level6rlrr = true := by decide +kernel
def level6rlr : BinaryTree (List W) := .node [v124, v169, v177, v189, v204, v260] level6rlrl level6rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlr_ok : everyKey (rowOK 5 level5) level6rlr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlrl && everyKey (rowOK 5 level5) level6rlrr) = true
  rw [level6rlrl_ok, level6rlrr_ok]
  decide +kernel
def level6rl : BinaryTree (List W) := .node [v124, v154, v169, v189, v204, v234, v260] level6rll level6rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rl_ok : everyKey (rowOK 5 level5) level6rl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rll && everyKey (rowOK 5 level5) level6rlr) = true
  rw [level6rll_ok, level6rlr_ok]
  decide +kernel
def level6rrll : BinaryTree (List W) := (.node [v124, v169, v189, v204, v234, v250, v260] (.node [v124, v169, v189, v204, v226, v234, v260] (.node [v124, v169, v189, v204, v225, v234, v260] .nil .nil) .nil) (.node [v124, v169, v189, v204, v234, v252, v260] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrll_ok : everyKey (rowOK 5 level5) level6rrll = true := by decide +kernel
def level6rrlr : BinaryTree (List W) := (.node [v124, v169, v189, v204, v234, v260, v289] (.node [v124, v169, v189, v204, v234, v260, v280] (.node [v124, v169, v189, v204, v234, v260, v272] .nil .nil) .nil) (.node [v124, v169, v189, v204, v234, v260, v295] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlr_ok : everyKey (rowOK 5 level5) level6rrlr = true := by decide +kernel
def level6rrl : BinaryTree (List W) := .node [v124, v169, v189, v204, v234, v254, v260] level6rrll level6rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrl_ok : everyKey (rowOK 5 level5) level6rrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrll && everyKey (rowOK 5 level5) level6rrlr) = true
  rw [level6rrll_ok, level6rrlr_ok]
  decide +kernel
def level6rrrl : BinaryTree (List W) := (.node [v124, v169, v189, v204, v234, v260, v304] (.node [v124, v169, v189, v204, v234, v260, v302] (.node [v124, v169, v189, v204, v234, v260, v301] .nil .nil) .nil) (.node [v124, v169, v189, v204, v234, v260, v306] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrl_ok : everyKey (rowOK 5 level5) level6rrrl = true := by decide +kernel
def level6rrrr : BinaryTree (List W) := (.node [v124, v169, v189, v204, v234, v295] (.node [v124, v169, v189, v204, v234, v289] .nil .nil) (.node [v124, v169, v189, v204, v260, v307] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrr_ok : everyKey (rowOK 5 level5) level6rrrr = true := by decide +kernel
def level6rrr : BinaryTree (List W) := .node [v124, v169, v189, v204, v234, v260, v307] level6rrrl level6rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrr_ok : everyKey (rowOK 5 level5) level6rrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrrl && everyKey (rowOK 5 level5) level6rrrr) = true
  rw [level6rrrl_ok, level6rrrr_ok]
  decide +kernel
def level6rr : BinaryTree (List W) := .node [v124, v169, v189, v204, v234, v260, v298] level6rrl level6rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rr_ok : everyKey (rowOK 5 level5) level6rr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrl && everyKey (rowOK 5 level5) level6rrr) = true
  rw [level6rrl_ok, level6rrr_ok]
  decide +kernel
def level6r : BinaryTree (List W) := .node [v124, v169, v189, v204, v222, v234, v260] level6rl level6rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6r_ok : everyKey (rowOK 5 level5) level6r = true := by
  change (_ && everyKey (rowOK 5 level5) level6rl && everyKey (rowOK 5 level5) level6rr) = true
  rw [level6rl_ok, level6rr_ok]
  decide +kernel
def level6 : BinaryTree (List W) := .node [v112, v124, v169, v189, v204, v234] level6l level6r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6_ok : everyKey (rowOK 5 level5) level6 = true := by
  change (_ && everyKey (rowOK 5 level5) level6l && everyKey (rowOK 5 level5) level6r) = true
  rw [level6l_ok, level6r_ok]
  decide +kernel
theorem closed6 : Closed 6 level6 := closed_next 5 (by decide) level6 level5 closed5 level6_ok
def level7 : BinaryTree (List W) := (.node [v124, v169, v189, v204, v234, v260] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7_ok : everyKey (rowOK 6 level6) level7 = true := by decide +kernel
theorem closed7 : Closed 7 level7 := closed_next 6 (by decide) level7 level6 closed6 level7_ok

theorem lower : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z 7 ins.toFinset :=
  @no_build 7 level7 ins (by decide +kernel) (by decide) closed7 (by decide +kernel)
def witness : List Gate := [⟨.and,[0,2]⟩, ⟨.or,[3,5]⟩, ⟨.and,[1,7]⟩, ⟨.and,[2,3]⟩, ⟨.or,[0,9]⟩, ⟨.or,[1,4]⟩, ⟨.or,[6,8]⟩, ⟨.and,[10,12]⟩, ⟨.and,[11,13]⟩]
theorem upper : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 9 ∧ ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xe8a8c888e8a0c880 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact ⟨witness,14,by simp [witness],rfl,by decide +kernel⟩
end PEqualNP.Outside.L_meta_13267_aux

open PEqualNP.Outside.L_meta_13267_aux in
theorem PEqualNP.Outside.L_meta_13267 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3903375496 * 2 ^ 32 + 3902851200) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3903375496 * 2 ^ 32 + 3902851200) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  have code : 3903375496 * 2 ^ 32 + 3902851200 = 0xe8a8c888e8a0c880 := by decide
  simp only [code] at h ⊢
  obtain ⟨C,legal,size,computes⟩ := h
  obtain ⟨gs,o,mono,bound,ev⟩ := replace 0xe8a8c888e8a0c880 9 ins (by decide +kernel) sampled rfl lower upper C.gates C.output legal computes
  exact ⟨⟨gs,o⟩,mono,bound.trans size,ev⟩
