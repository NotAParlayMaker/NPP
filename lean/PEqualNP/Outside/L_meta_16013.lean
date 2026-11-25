import PEqualNP.Defs

-- The live-wire search and circuit compiler are adapted from tacyon52 in L-meta-8639, pull request 12794 under Apache-2.0.
namespace PEqualNP.Outside.L_meta_16013_aux

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
def v1 : W := 0x100000000000000
def v2 : W := 0x593100000000038f3
def v3 : W := 0x8e3c00000000000fc
def v4 : W := 0xd315000000001c300
def v5 : W := 0xdc28000000001fc00
def v6 : W := 0x96015100000000e00f3
def v7 : W := 0x12082140000000000000
def v8 : W := 0x132025400000007000fc
def v9 : W := 0x1a403150000003800300
def v10 : W := 0x1b600400000003fe0000
def v11 : W := 0x560860c000000070000c
def v12 : W := 0xb218204000000381c300
def v13 : W := 0xe418408000000c01c400
def v14 : W := 0xf610000000000ff00000
def v15 : W := 0x100008200000000000000
def v16 : W := 0x1012086000000700e38f3
def v17 : W := 0x1012087000000000000f0
def v18 : W := 0x1012087000000700e38f3
def v19 : W := 0x1012597100000700e38f3
def v20 : W := 0x1096097100000700e38f3
def v21 : W := 0x14400c28000007c003c00
def v22 : W := 0x14408c280000000000000
def v23 : W := 0x14520040000007c7e0000
def v24 : W := 0x14520860000007c7e38f3
def v25 : W := 0x14520c6800000007000fc
def v26 : W := 0x14520c6800000707e38ff
def v27 : W := 0x14520c68000007c0e3cf3
def v28 : W := 0x157200400000000700000
def v29 : W := 0x15728e7c00000007000fc
def v30 : W := 0x15728e7c00000707e38ff
def v31 : W := 0x1b338a6400000738ffbf3
def v32 : W := 0x2084510100000700e3803
def v33 : W := 0x208451110000000000000
def v34 : W := 0x2084593100000700e38f3
def v35 : W := 0x2096515100000700e38f3
def v36 : W := 0x2a015000000007c01fc00
def v37 : W := 0x2a01d000000000001c000
def v38 : W := 0x2a850000000007f8e0000
def v39 : W := 0x2a855101000000381c300
def v40 : W := 0x2ba500000000003800000
def v41 : W := 0x2ba5d315000000381c300
def v42 : W := 0x300058200000070003800
def v43 : W := 0x3012586000000700e38f3
def v44 : W := 0x3096004000000700e0000
def v45 : W := 0x3096086000000700e38f3
def v46 : W := 0x3096596100000700e38f3
def v47 : W := 0x3096597100000700e38f3
def v48 : W := 0x3096db7500000700ffbf3
def v49 : W := 0x3096dd7900000700ffcf3
def v50 : W := 0x3096df7d00000700e38ff
def v51 : W := 0x31b659710000073fe38f3
def v52 : W := 0x31b65b7500000707e38ff
def v53 : W := 0x31b65b7500000738e3bf3
def v54 : W := 0x31b6db7500000700e38f3
def v55 : W := 0x34d65971000007c7e38f3
def v56 : W := 0x34d65d7900000707e38ff
def v57 : W := 0x34d65d79000007c0e3cf3
def v58 : W := 0x34d6dd7900000700e38f3
def v59 : W := 0x35f6597100000707e38f3
def v60 : W := 0x35f6df7d00000707e38ff
def v61 : W := 0x3a97597100000738ffbf3
def v62 : W := 0x3a975971000007c0ffcf3
def v63 : W := 0x3a975971000007f8e38f3
def v64 : W := 0x3a97d97100000700ff8f3
def v65 : W := 0x3bb7597100000738e38f3
def v66 : W := 0x3bb7db7500000738ffbf3
def v67 : W := 0x3e410000000007c000000
def v68 : W := 0x3e41dc28000007c01fc00
def v69 : W := 0x3e53dc68000007c0ffcf3
def v70 : W := 0x3ed75971000007c0e38f3
def v71 : W := 0x3ed7dd79000007c0ffcf3
def v72 : W := 0x3f73de7c000007c71fcfc
def v73 : W := 0x3fe5df3d000007f81ff00
def v74 : W := 0x3ff70040000007ffe0000
def v75 : W := 0x3ff70860000007ffe38f3
def v76 : W := 0x3ff75971000007ffe38f3
def v77 : W := 0x3ff78e7c000007ffe00fc
def v78 : W := 0x3ff7d355000007fffc300
def v79 : W := 0x3ff7db75000007ffffbf3
def v80 : W := 0x3ff7dc68000007ffffc00
def v81 : W := 0x3ff7dd79000007ffffcf3
def v82 : W := 0x3ff7df7d0000003f1c3fc
def v83 : W := 0x3ff7df7d0000073fffbff
def v84 : W := 0x3ff7df7d000007c7ffcff
def v85 : W := 0x3ff7df7d000007f8ffff3
def v86 : W := 0x3ff7df7d000007ffe38ff
def v87 : W := 0x1000008b000000000000f0
def v88 : W := 0x98000019300000000000f3
def v89 : W := 0x130000029400007000000fc
def v90 : W := 0x1a000003150001800000300
def v91 : W := 0x1b800000820001f80000000
def v92 : W := 0x21800028a200000000038f3
def v93 : W := 0x4500000ca800007000000fc
def v94 : W := 0x6400002c280006000003c00
def v95 : W := 0x65800020820006780000000
def v96 : W := 0x80200050000000000000000
def v97 : W := 0x803096597100000700e38f3
def v98 : W := 0x8800005101003980001c300
def v99 : W := 0x88000051110000000000000
def v100 : W := 0x883096597100000700e38f3
def v101 : W := 0xa000007000003e00001fc00
def v102 : W := 0xa0000078200000000003800
def v103 : W := 0xa880002002003f880000000
def v104 : W := 0xa8800071030000000003803
def v105 : W := 0xa9800020820000000000000
def v106 : W := 0xa9800079b300000000038f3
def v107 : W := 0xa9800079b3003980001fbf3
def v108 : W := 0xa9800079b3003e00001fcf3
def v109 : W := 0xa9b09679f300000700e38f3
def v110 : W := 0xb300007294003e70001fcfc
def v111 : W := 0xcd00005da90039f0001c3fc
def v112 : W := 0x100000080000000000000000
def v113 : W := 0x11200008204003980001c300
def v114 : W := 0x112000082140000000000000
def v115 : W := 0x1338000aaa6003980001fbf3
def v116 : W := 0x14400008408003e00001c400
def v117 : W := 0x14400008c280000000000000
def v118 : W := 0x14d8000859b003e00001c4f3
def v119 : W := 0x15600000000003ff80000000
def v120 : W := 0x1560000860c000070000000c
def v121 : W := 0x157000000800000700000000
def v122 : W := 0x15700008ebc00007000000fc
def v123 : W := 0x15700008ebc0039f0001c3fc
def v124 : W := 0x15700008ebc003e70001c4fc
def v125 : W := 0x15715728efc00007007000fc
def v126 : W := 0x1800000d000003800001c000
def v127 : W := 0x19a000000000039800000000
def v128 : W := 0x19a0000d315003980001c300
def v129 : W := 0x19a0000db35003980001fbf3
def v130 : W := 0x19a0000df3d003980001c3fc
def v131 : W := 0x19a2ba5d315003980381c300
def v132 : W := 0x19a3096db7500398700ffbf3
def v133 : W := 0x19b0000d3950039f0001c3fc
def v134 : W := 0x19b0000dbb5003980001c3f0
def v135 : W := 0x19b8000d397003980001c3f3
def v136 : W := 0x1a98000f9b3003800001f8f3
def v137 : W := 0x1bb8000f397003980001c300
def v138 : W := 0x1bb8000fbb7003980001fbf3
def v139 : W := 0x1d70000debc003870001c0fc
def v140 : W := 0x1df0000dfbd0039f0001c3fc
def v141 : W := 0x1e400002000003e000000000
def v142 : W := 0x1e40000fc28003e00001fc00
def v143 : W := 0x1e40000fd39003e00001fcf3
def v144 : W := 0x1e40000fe3c003e00001fcfc
def v145 : W := 0x1e43e41fc28003e07c01fc00
def v146 : W := 0x1e50000fca8003e70001fcfc
def v147 : W := 0x1e50000fcb8003e00001fcf0
def v148 : W := 0x1e58000fcaa003e00001fcf3
def v149 : W := 0x1ed8000fdbb003e00001fcf3
def v150 : W := 0x1f70000febc003e70001fcfc
def v151 : W := 0x1fe0000ff3d003f80001ff00
def v152 : W := 0x1ff0000ffbd003ff0001fffc
def v153 : W := 0x1ff80002082003ff80000000
def v154 : W := 0x1ff800079b3003ff800038f3
def v155 : W := 0x1ff8000aebe003ff800000fc
def v156 : W := 0x1ff8000f397003ff8001c300
def v157 : W := 0x1ff8000fbb7003ff8001fbf3
def v158 : W := 0x1ff8000fcaa003ff8001fc00
def v159 : W := 0x1ff8000fdbb003ff8001fcf3
def v160 : W := 0x1ff8000febe003ff8001fcfc
def v161 : W := 0x1ff8000ffbf00007000038ff
def v162 : W := 0x1ff8000ffbf0039f0001c3fc
def v163 : W := 0x1ff8000ffbf0039f0001fbff
def v164 : W := 0x1ff8000ffbf003e70001fcff
def v165 : W := 0x1ff8000ffbf003f80001fff3
def v166 : W := 0x1ff8000ffbf003ff8001c3fc
def v167 : W := 0x1ff9452f3d7003fffc7fc300
def v168 : W := 0x1ffbff720c2003fffffe0000
def v169 : W := 0x800101200400000000000000
def v170 : W := 0x8003096597100000700e38f3
def v171 : W := 0x801000000800000000000000
def v172 : W := 0x801001200c003807007000fc
def v173 : W := 0x801001200d000000000000f0
def v174 : W := 0x801101208e000000000000f0
def v175 : W := 0x801101208f000000000000f0
def v176 : W := 0x80115728efc00000007000fc
def v177 : W := 0x801309659f100000700e38f3
def v178 : W := 0x8a9901279f300000000038f3
def v179 : W := 0x95710128efc00007000000fc
def v180 : W := 0xc00001a004003c00007e0000
def v181 : W := 0xc018008008203c0780000000
def v182 : W := 0xc01801a00c200000000e00f3
def v183 : W := 0x4000208400000000000000000
def v184 : W := 0x40003096597100000700e38f3
def v185 : W := 0x4008008401011c01803800300
def v186 : W := 0x4008008401110000000000000
def v187 : W := 0x40083096597100000700e38f3
def v188 : W := 0x4088000000000000000000000
def v189 : W := 0x4088208451010000000000000
def v190 : W := 0x4088208451110000000000000
def v191 : W := 0x40882ba5d315000000381c300
def v192 : W := 0x40883096597100000700e38f3
def v193 : W := 0x40a9a08479b300000000038f3
def v194 : W := 0x419a2084d315003980001c300
def v195 : W := 0x4400008c00001c400038e0000
def v196 : W := 0x4408800800021c41880000000
def v197 : W := 0x4408808c010300000000e0003
def v198 : W := 0x4809009601c11f81f03f003fc
def v199 : W := 0x4889309659f100000000000f0
def v200 : W := 0x4c00009e004000000000e0000
def v201 : W := 0x4c09800800820000000000000
def v202 : W := 0x4c09809e01d300000000e00f3
def v203 : W := 0x4c09909e09f300000000e00f3
def v204 : W := 0x4c09b09e59f300000700e38f3
def v205 : W := 0x4c89a09e51d300000000e00f3
def v206 : W := 0x4ca9809e79f300000000e38f3
def v207 : W := 0x9000012000000000000000000
def v208 : W := 0x9000012000001fc0003f00000
def v209 : W := 0x9012000000001fc1f80000000
def v210 : W := 0x901201200204038070070000c
def v211 : W := 0x9012012002041c01803800300
def v212 : W := 0x9012012002140000000000000
def v213 : W := 0x9112000000000000000000000
def v214 : W := 0x9112012082040000000000000
def v215 : W := 0x9112012082140000000000000
def v216 : W := 0x911215728e7c00000007000fc
def v217 : W := 0x91122ba5d315000000381c300
def v218 : W := 0x911231b6db7500000700e38f3
def v219 : W := 0x915701208ebc00007000000fc
def v220 : W := 0x919a0120d315003980001c300
def v221 : W := 0x9800013200400380000700000
def v222 : W := 0x9813000000800380700000000
def v223 : W := 0x9813013202d403807007000fc
def v224 : W := 0x9813013202d41f81f03f003fc
def v225 : W := 0x9813013202d41fc0703f000fc
def v226 : W := 0x981311320af403807007000fc
def v227 : W := 0x981315728efc03807007000fc
def v228 : W := 0x9913012082940000000000000
def v229 : W := 0x9913013282d403807007000fc
def v230 : W := 0x991311328af400000000000f0
def v231 : W := 0x995701328efc03807007000fc
def v232 : W := 0xd00001a400001c00003800000
def v233 : W := 0xd01a000000001c01800000000
def v234 : W := 0xd01a01a403151c01803800300
def v235 : W := 0xd01a2ba5d3151c0180381c300
def v236 : W := 0xd01a31b65b751c018738e3bf3
def v237 : W := 0xd09a21a453151c01803800300
def v238 : W := 0xd11a01a483151c01803800300
def v239 : W := 0xd19a01a4d3151c3980381c300
def v240 : W := 0xd19a21a4d3150000000000000
def v241 : W := 0xd19a35f6df7d00000707e38ff
def v242 : W := 0xd81301b602d41f80703f000fc
def v243 : W := 0xd81b01b603d51f81f03f003fc
def v244 : W := 0xdc00000800001fc0000000000
def v245 : W := 0xdc0001be00401fc0003fe0000
def v246 : W := 0xdc003fff00401fc007ffe0000
def v247 : W := 0xdc0101be00c01fc0703fe00fc
def v248 : W := 0xdc0981be01d31fc0003fe00f3
def v249 : W := 0xdc1301be02d41fc0703fe00fc
def v250 : W := 0xdc1a01be03551fc1803fe0300
def v251 : W := 0xdc1b01be03d51fc1f03fe03fc
def v252 : W := 0xdc1b800800821fc1f80000000
def v253 : W := 0xdc1b809e01d31fc1f800e00f3
def v254 : W := 0xdc1b813a02d61fc1f807000fc
def v255 : W := 0xdc1b81ac03971c01803800300
def v256 : W := 0xdc1b81ac03971fc1f83800300
def v257 : W := 0xdc1b81be00c21fc1f83fe0000
def v258 : W := 0xdc1b81be02d61fc1f83fe00fc
def v259 : W := 0xdc1b81be03d703807007e00ff
def v260 : W := 0xdc1b81be03d71c018038e03f3
def v261 : W := 0xdc1b81be03d71f81f03f003fc
def v262 : W := 0xdc1b81be03d71f81f03fe03ff
def v263 : W := 0xdc1b81be03d71fc0703fe00ff
def v264 : W := 0xdc1b81be03d71fc1f83f003fc
def v265 : W := 0xdc1b95ec0fbf1fc1fff803f00
def v266 : W := 0xdc1bbe49dcaa1fc1ffc01fc00
def v267 : W := 0xdd9a01bed3551ff9803ffc300
def v268 : W := 0xdde401befc681ffe003fffc00
def v269 : W := 0xddfe01beff7d1fff803ffff00
def v270 : W := 0xddff800820821ffff80000000
def v271 : W := 0x20000700000000000070000000
def v272 : W := 0x2002040002000e00607c003c00
def v273 : W := 0x20020500028200000070003800
def v274 : W := 0x200a0400020000000000000000
def v275 : W := 0x200a0600070000000070003800
def v276 : W := 0x200a0700078200000070003800
def v277 : W := 0x200a07096797100000700e38f3
def v278 : W := 0x200a07e41fc28000007c01fc00
def v279 : W := 0x200a9f00079b300000700038f3
def v280 : W := 0x201e47000fc28003e07001fc00
def v281 : W := 0x2040040080000e04007c0e0000
def v282 : W := 0x20420c008200200000700e3803
def v283 : W := 0x20420c0082002e046080000000
def v284 : W := 0x20465c0082082e046780000000
def v285 : W := 0x205ffc0082082e07ff80000000
def v286 : W := 0x208a1701278f000000700038f0
def v287 : W := 0x20c00501a004000000700e0000
def v288 : W := 0x20c21c00820820000000000000
def v289 : W := 0x20c21c008208203c0780000000
def v290 : W := 0x20c21c0082082e046080000000
def v291 : W := 0x20c21c0082082e3c6780000000
def v292 : W := 0x20c21d01a28e200000700e38f3
def v293 : W := 0x20c21d01a28f200000700e38f3
def v294 : W := 0x20c21f09e79f300000700e38f3
def v295 : W := 0x20c65c00820820006780000000
def v296 : W := 0x20ca1c00820820000000000000
def v297 : W := 0x20ca1f01a78e200000700e38f3
def v298 : W := 0x20ca9c00820820000000000000
def v299 : W := 0x20ca9d01a79f300000700e38f3
def v300 : W := 0x20dffc0082082003ff80000000
def v301 : W := 0x240a8708479310000070003800
def v302 : W := 0x24400608c000000000700e0000
def v303 : W := 0x244a8c00820020000000000000
def v304 : W := 0x244a8e08c710300000700e3803
def v305 : W := 0x244a8e08c711300000700e3803
def v306 : W := 0x244a8f08c792300000700e3803
def v307 : W := 0x244a8f09e796300000700e38f3
def v308 : W := 0x244a8f09e797300000700e38f3
def v309 : W := 0x244a9c00820820000000000000
def v310 : W := 0x244a9e08c79b300000700e38f3
def v311 : W := 0x245ffc0082082003ff80000000
def v312 : W := 0x24c00400800000000000000000
def v313 : W := 0x24c00709e004000000700e0000
def v314 : W := 0x24c00709e597100000700e38f3
def v315 : W := 0x24c007fff0040000007ffe0000
def v316 : W := 0x24c01709e08f000000700e00f0
def v317 : W := 0x24c09f09e01d300000700e00f3
def v318 : W := 0x24c21c00820820000000000000
def v319 : W := 0x24c21f09e28e200000700e38f3
def v320 : W := 0x24c29c00820820000000000000
def v321 : W := 0x24c29d09e29f300000700e38f3
def v322 : W := 0x24c88709e515100000700e0000
def v323 : W := 0x24ca0709e786000000700e3800
def v324 : W := 0x24ca8f09e714300000700e3803
def v325 : W := 0x24ca9c00820820000000000000
def v326 : W := 0x24ca9c0082082003f880000000
def v327 : W := 0x24ca9c008208203c0780000000
def v328 : W := 0x24ca9c00820821c41880000000
def v329 : W := 0x24ca9c0082082e046080000000
def v330 : W := 0x24ca9c00820920000000000000
def v331 : W := 0x24ca9c00871930000000000000
def v332 : W := 0x24ca9c00879b300000000038f3
def v333 : W := 0x24ca9c08c21930000000000000
def v334 : W := 0x24ca9c09e21d300000000e00f3
def v335 : W := 0x24ca9c09e79f300000000e38f3
def v336 : W := 0x24ca9d00828a20000000000000
def v337 : W := 0x24ca9d01a20c20000000000000
def v338 : W := 0x24ca9d01a28e200000700e38f3
def v339 : W := 0x24ca9d01a28f200000000000f0
def v340 : W := 0x24ca9d09e79f300000700e38f3
def v341 : W := 0x24ca9e00870820000000000000
def v342 : W := 0x24ca9e08c20820000000000000
def v343 : W := 0x24ca9e08c71830000000000000
def v344 : W := 0x24ca9e08c718300000700e3803
def v345 : W := 0x24ca9e08c71930000000000000
def v346 : W := 0x24ca9e09e71c300000700e38f3
def v347 : W := 0x24ca9e09e71d300000000e00f3
def v348 : W := 0x24ca9e09e71d300000700e38f3
def v349 : W := 0x24ca9e09e79f300000700e38f3
def v350 : W := 0x24ca9ebadf397000000381c300
def v351 : W := 0x24ca9f00878a20000070003800
def v352 : W := 0x24ca9f09e20c200000700e0000
def v353 : W := 0x24ca9f09e71c300000700e3803
def v354 : W := 0x24ca9f09e71d30000000000000
def v355 : W := 0x24ca9f09e71d300000700e0000
def v356 : W := 0x24ca9f09e71d300000700e38f3
def v357 : W := 0x24ca9f09e79e300000700e38f3
def v358 : W := 0x24ca9f09e79f300000000000f0
def v359 : W := 0x24ca9f09e79f300000700e38f3
def v360 : W := 0x24ca9f09effff00000700e38ff
def v361 : W := 0x24ca9f1befbf700000700e38f3
def v362 : W := 0x24ca9f4de7dfb000007c0e3cf3
def v363 : W := 0x24ca9f4defdfb00000700e38f3
def v364 : W := 0x24ca9f5feffff00000707e38ff
def v365 : W := 0x24ca9fbbffbf700000738ffbf3
def v366 : W := 0x24ca9fedf79f3000007c0e38f3
def v367 : W := 0x24ca9fedffdfb000007c0ffcf3
def v368 : W := 0x24ca9ffff79f3000007ffe38f3
def v369 : W := 0x24cbbc00820820001f80000000
def v370 : W := 0x24cedc00820820006780000000
def v371 : W := 0x24d9a709ed35500398700fc300
def v372 : W := 0x24da9f09ef9f300000700e38f3
def v373 : W := 0x24dbbc00820820039800000000
def v374 : W := 0x24dbbc008f397003980001c300
def v375 : W := 0x24dbbf09efbf700000700e38f3
def v376 : W := 0x24dbbf09efbf700398700ffbf3
def v377 : W := 0x24de4709efc68003e0700ffc00
def v378 : W := 0x24dedc0082082003e000000000
def v379 : W := 0x24dedf09efdfb00000700e38f3
def v380 : W := 0x24dedf09efdfb003e0700ffcf3
def v381 : W := 0x24dffc00820820000700000000
def v382 : W := 0x24dffc0082082003ff80000000
def v383 : W := 0x24dffe08cf397003ff8001c300
def v384 : W := 0x24dfff09e79f3003fff00e38f3
def v385 : W := 0x24dfff09effff00007700e38ff
def v386 : W := 0x29532d57aae7ee0460807000fc
def v387 : W := 0x2dc0071be00401fc0073fe0000
def v388 : W := 0x2dc3bc00820821fc1f80000000
def v389 : W := 0x2dc3bc0082082ffc7f80000000
def v390 : W := 0x2dca9c00820821fc0000000000
def v391 : W := 0x2dca9f1be79f300000700e38f3
def v392 : W := 0x2dca9f1be79f31fc0073fe38f3
def v393 : W := 0x2dcbbc00820820380700000000
def v394 : W := 0x2dcbbc00820821c01800000000
def v395 : W := 0x2dcbbc00820821fc1f80000000
def v396 : W := 0x2dcbbc1ac23971c01803800300
def v397 : W := 0x2dcbbe1ac73971fc1f83800300
def v398 : W := 0x2dcbbf09e79f31fc1ff00e38f3
def v399 : W := 0x2dcbbf1be7bf700000700e38f3
def v400 : W := 0x2dcbbf1be7bf703807707e38ff
def v401 : W := 0x2dcbbf1be7bf71c018738e3bf3
def v402 : W := 0x2ddbbc00820820000000000000
def v403 : W := 0x2ddbbc128a2960000000000000
def v404 : W := 0x2ddbbf09e79f300000700e38f3
def v405 : W := 0x2ddbbf1befbf700000700e38f3
def v406 : W := 0x2dde471befc681ffe073fffc00
def v407 : W := 0x2ddffc00820821ffff80000000
def v408 : W := 0x4200004400000e3c000c700000
def v409 : W := 0x42000144000000000000000000
def v410 : W := 0x4200014520040e3c007c7e0000
def v411 : W := 0x4204400000000e3c6780000000
def v412 : W := 0x4204404400408038070070000c
def v413 : W := 0x4204404400408e00600c000400
def v414 : W := 0x4204414400c280000000000000
def v415 : W := 0x4204414400c28e00607c003c00
def v416 : W := 0x4204414520c6803807007000fc
def v417 : W := 0x42144000000000000000000000
def v418 : W := 0x42144044084080000000000000
def v419 : W := 0x4214414408c280000000000000
def v420 : W := 0x4214415728e7c00000007000fc
def v421 : W := 0x4214434d6dd7900000700e38f3
def v422 : W := 0x421443e41dc28000007c01fc00
def v423 : W := 0x4215714408ebc00007000000fc
def v424 : W := 0x421bb9452f3d7e3f987c7fc300
def v425 : W := 0x421e41440fc28003e00001fc00
def v426 : W := 0x42800145200400380000700000
def v427 : W := 0x42845000000800380700000000
def v428 : W := 0x4284514520ce803807007000fc
def v429 : W := 0x4284514520cf803807007000fc
def v430 : W := 0x4284515728efc03807007000fc
def v431 : W := 0x4294514528ce803807007000fc
def v432 : W := 0x4294514528cf800000000000f0
def v433 : W := 0x4295714528efc03807007000fc
def v434 : W := 0x460cc30965971e3c67f00e38f3
def v435 : W := 0x4b000056000000380000700000
def v436 : W := 0x4b156000000000380700000000
def v437 : W := 0x4b1560560860c038070070000c
def v438 : W := 0x4b1560560861c038070070000c
def v439 : W := 0x4b15615608e2c038070070000c
def v440 : W := 0x4b15615608e3c0000000000000
def v441 : W := 0x4b15615728e6c03807007000fc
def v442 : W := 0x4b15615728e7c00000007000fc
def v443 : W := 0x4b15615728e7c03807007000fc
def v444 : W := 0x4b15635f6df7d03807707e38ff
def v445 : W := 0x4b15705608ebc03807007000fc
def v446 : W := 0x4b15715728efc03807007000fc
def v447 : W := 0x4b800000000000380000000000
def v448 : W := 0x4b800157200400380000700000
def v449 : W := 0x4b80015728e7c03800007000fc
def v450 : W := 0x4b80035f6597103800707e38f3
def v451 : W := 0x4b8003ff70040038007ffe0000
def v452 : W := 0x4b801157208f003800007000f0
def v453 : W := 0x4b813157202d403807007000fc
def v454 : W := 0x4b84515720ce803807007000fc
def v455 : W := 0x4b85715720efc03807007000fc
def v456 : W := 0x4b912157282540380000700000
def v457 : W := 0x4b94415728c680380000700000
def v458 : W := 0x4b9561572864c038070070000c
def v459 : W := 0x4b95615728e6c038070070000c
def v460 : W := 0x4b95615728e7c0380000700000
def v461 : W := 0x4b95615728e7c03807007000fc
def v462 : W := 0x4b957000000800380700000000
def v463 : W := 0x4b95700008ebc03807000000fc
def v464 : W := 0x4b957012082940380700000000
def v465 : W := 0x4b957013202d403807007000fc
def v466 : W := 0x4b9570560868c038070070000c
def v467 : W := 0x4b957057286dc03807007000fc
def v468 : W := 0x4b957101208f003807000000f0
def v469 : W := 0x4b95714408ca80380700000000
def v470 : W := 0x4b95714520ce803807007000fc
def v471 : W := 0x4b957157200c00380700700000
def v472 : W := 0x4b95715728eec03807007000fc
def v473 : W := 0x4b95715728efc00000000000f0
def v474 : W := 0x4b95715728efc03807007000fc
def v475 : W := 0x4b95725e4d78d03807707e380f
def v476 : W := 0x4b95735f6dffd03807007000fc
def v477 : W := 0x4b95735f6dffd03807707e38ff
def v478 : W := 0x4b9573f73defc038077c71fcfc
def v479 : W := 0x4b9573ff78efc038077ffe00fc
def v480 : W := 0x4b9573ff7dffd0380703f1c3fc
def v481 : W := 0x4b95f95728fff03807007000ff
def v482 : W := 0x4b99a1572d35503b980071c300
def v483 : W := 0x4b9d73572defc03807007000fc
def v484 : W := 0x4b9df1572dffd03807007000fc
def v485 : W := 0x4b9df1572dffd03b9f0071c3fc
def v486 : W := 0x4b9e41572fc6803be00071fc00
def v487 : W := 0x4b9f71572fefc03be70071fcfc
def v488 : W := 0x4b9ff8000208203bff80000000
def v489 : W := 0x4b9ff9572aefe03807007000fc
def v490 : W := 0x4b9ff9572aefe03bff807000fc
def v491 : W := 0x4b9ff9572ffff03807007038ff
def v492 : W := 0x4b9ffbff720c203bfffffe0000
def v493 : W := 0x4bd57957a8efe03c07807000fc
def v494 : W := 0x4f15e15e48f3d1c01803800300
def v495 : W := 0x4f95735f68efc03807007000fc
def v496 : W := 0x4f95f15f68ffd03807007000fc
def v497 : W := 0x4f95f15f68ffd1f81f03f003fc
def v498 : W := 0x4f9df15728efc03807007000fc
def v499 : W := 0x4f9df35f6dffd03807007000fc
def v500 : W := 0x4fc0015fe00401fc0003fe0000
def v501 : W := 0x4fc5f95ec0fbffc0787f803f00
def v502 : W := 0x4fd5715fe8efc1fc0703fe00fc
def v503 : W := 0x4fd5f800800821fc1f80000000
def v504 : W := 0x4fd5f957a8efe03807007000fc
def v505 : W := 0x4fd5f957a8efe1fc1f807000fc
def v506 : W := 0x4fd5f95fe8fff03807007e00ff
def v507 : W := 0x6200054400000e00007c000000
def v508 : W := 0x6206440002000e006000000000
def v509 : W := 0x6206454402c28e00607c003c00
def v510 : W := 0x620647e41fc28e00607c01fc00
def v511 : W := 0x620e474407c28e00607c003c00
def v512 : W := 0x621645440ac28e00607c003c00
def v513 : W := 0x621e45440fc28e03e07c01fc00
def v514 : W := 0x621e47440fc280000070003800
def v515 : W := 0x6286554522ce8e38677c703cfc
def v516 : W := 0x62c0040080000e3c0000000000
def v517 : W := 0x62c00545a0040e3c007c7e0000
def v518 : W := 0x62c007fff0040e3c007ffe0000
def v519 : W := 0x62c21c0082082e3c0000000000
def v520 : W := 0x62c21d45a28e2e3c007c7e38f3
def v521 : W := 0x62c45545a0ce8e3c077c7e00fc
def v522 : W := 0x62c64545a2c68e3c607c7e3c00
def v523 : W := 0x62c65c00820820380700000000
def v524 : W := 0x62c65c0082082e006000000000
def v525 : W := 0x62c65c0082082e3c6780000000
def v526 : W := 0x62c65c4482082e3c678c700000
def v527 : W := 0x62c65c448248ae3c678070000c
def v528 : W := 0x62c65c448248ae3c678c000400
def v529 : W := 0x62c65d01a28e2e3c67f00e38f3
def v530 : W := 0x62c65d4482caae3c6780000000
def v531 : W := 0x62c65d4482caae3c67fc003c00
def v532 : W := 0x62c65d45a20c2e3c6780700000
def v533 : W := 0x62c65d45a20c2e3c67fc7e0000
def v534 : W := 0x62c65d45a2cea03807707e38ff
def v535 : W := 0x62c65d45a2ceae00607c0e3cf3
def v536 : W := 0x62c65d45a2ceae38677c7e3cff
def v537 : W := 0x62c65d45a2ceae3c077c7e38ff
def v538 : W := 0x62c65d45a2ceae3c67807000fc
def v539 : W := 0x62c65ebadf397e3c678381c300
def v540 : W := 0x62c7fc0082082e3c7f80000000
def v541 : W := 0x62ce5c0082082e3c6780000000
def v542 : W := 0x62cedc0082082e3c6780000000
def v543 : W := 0x62cedc0082082e3fff80000000
def v544 : W := 0x62d65c0082082e3c6780000000
def v545 : W := 0x62d65d448acaae3c6780000000
def v546 : W := 0x62d77c0082082e3c6780000000
def v547 : W := 0x62d77c0082082e3fff80000000
def v548 : W := 0x62d9a545ad355e3f987c7fc300
def v549 : W := 0x62de4545afc68e3fe07c7ffc00
def v550 : W := 0x62de5c0082082e3fe780000000
def v551 : W := 0x62dffc0082082e3fff80000000
def v552 : W := 0x62dffc008f397e3fff8001c300
def v553 : W := 0x66c0074de0040e3c007c7e0000
def v554 : W := 0x66c65c0082082e3c6780000000
def v555 : W := 0x66c6dc0082082e3c6780000000
def v556 : W := 0x66c6dc0082082ffc7f80000000
def v557 : W := 0x66ca9c0082082e3c0000000000
def v558 : W := 0x66ca9f4de79f300000700e38f3
def v559 : W := 0x66ca9f4de79f3e3c007c7e38f3
def v560 : W := 0x66cedc00820820380700000000
def v561 : W := 0x66cedc0082082e006000000000
def v562 : W := 0x66cedc0082082e3c6780000000
def v563 : W := 0x66cede08c7193e3c6780000000
def v564 : W := 0x66cedebadf397e3c678381c300
def v565 : W := 0x66cedf09e79f3e3c67f00e38f3
def v566 : W := 0x66cedf4de7dfb00000700e38f3
def v567 : W := 0x66cedf4de7dfb03807707e38ff
def v568 : W := 0x66cedf4de7dfbe00607c0e3cf3
def v569 : W := 0x66dedc00820820000000000000
def v570 : W := 0x66dedd448acaa0000000000000
def v571 : W := 0x66dedf09e79f300000700e38f3
def v572 : W := 0x66dedf4defdfb00000700e38f3
def v573 : W := 0x66dffc0082082e3fff80000000
def v574 : W := 0x6b9775572aefce38677c703cfc
def v575 : W := 0x6b9f75572aefc03807007000fc
def v576 : W := 0x6b9f77572fefc03807707038fc
def v577 : W := 0x6bc00557a0040e3c007c7e0000
def v578 : W := 0x6bc65c0082082e3c6780000000
def v579 : W := 0x6bc65d57a20c2e3c6780700000
def v580 : W := 0x6bc77c0082082e3c6780000000
def v581 : W := 0x6bc77c0082082ffc7f80000000
def v582 : W := 0x6bd57557a8efce3c077c7e00fc
def v583 : W := 0x6bd77c00820820380700000000
def v584 : W := 0x6bd77c0082082e3c6780000000
def v585 : W := 0x6bd77c128a296e3c6780000000
def v586 : W := 0x6bd77c568a68ee3c678070000c
def v587 : W := 0x6bd77d57aaefe03807007000fc
def v588 : W := 0x6bd77d57aaefe03807707e38ff
def v589 : W := 0x6bd77d57aaefee3c67807000fc
def v590 : W := 0x6bdffc0082082e3fff80000000
def v591 : W := 0x6f07e55e42f3dfc0787f803f00
def v592 : W := 0x6f17e55e4af3dfc0787f803f00
def v593 : W := 0x6f5fed57aae7e03807007000fc
def v594 : W := 0x6f5fee5ecf70f03807707e380f
def v595 : W := 0x6f5fee5ecf71f03807707e380f
def v596 : W := 0x6fc0055fe0040ffc007ffe0000
def v597 : W := 0x6fc0075fe004003800707e0000
def v598 : W := 0x6fc65c0082082ffc6780000000
def v599 : W := 0x6fc7fc0082082ffc7f80000000
def v600 : W := 0x6fc7fc1ac2397ffc7f83800300
def v601 : W := 0x6fca9c00820820380000000000
def v602 : W := 0x6fca9d57a20c20380000700000
def v603 : W := 0x6fca9f5fe79f303800707e38f3
def v604 : W := 0x6fcffc0082082ffc7f80000000
def v605 : W := 0x6fd57557a8efc03807007000fc
def v606 : W := 0x6fd5775fe8efc03807707e00fc
def v607 : W := 0x6fd7fc0082082ffc7f80000000
def v608 : W := 0x6fdffc00820820380700000000
def v609 : W := 0x6fdffc008208203bff80000000
def v610 : W := 0x6fdffc00820821fc1f80000000
def v611 : W := 0x6fdffc0082082e3c6780000000
def v612 : W := 0x6fdffc0082082fffff80000000
def v613 : W := 0x6fdffc568a68e038070070000c
def v614 : W := 0x6fdffd57aaefe03807007000fc
def v615 : W := 0x6fdffe1acf3970380700000000
def v616 : W := 0x6fdfff09e79f303807700e38f3
def v617 : W := 0x6fdfff5feffff00000700e38f3
def v618 : W := 0x6fdfff5feffff03807007000fc
def v619 : W := 0x6fdfff5feffff03807707e38ff
def v620 : W := 0x9020000000000fc7f880000000
def v621 : W := 0x902000a0100001c3980381c300
def v622 : W := 0x902000a010000e03e00c01c400
def v623 : W := 0x902000a010000fc4000f800000
def v624 : W := 0x902002a0100000000000000000
def v625 : W := 0x902003ff70040000007ffe0000
def v626 : W := 0x902003ff70040fc4007ffe0000
def v627 : W := 0x902802a015000003800001c000
def v628 : W := 0x903000a018000003800001c000
def v629 : W := 0x90380000000000038000000000
def v630 : W := 0x903802a01d000003800001c000
def v631 : W := 0x903802ba5d315003800381c300
def v632 : W := 0x903803a97d97100380700ff8f3
def v633 : W := 0x903803e41dc28003807c01fc00
def v634 : W := 0x9039a2a01d315003980001c300
def v635 : W := 0x903e42a01fc28003e00001fc00
def v636 : W := 0x90a001a130040fc4000f800000
def v637 : W := 0x90e002a1b004003c00007e0000
def v638 : W := 0x90f81be49dcaa03f87fc01fc00
def v639 : W := 0x942002a8500001c00003800000
def v640 : W := 0x942003ff700401c0007ffe0000
def v641 : W := 0x94288000000001c39800000000
def v642 : W := 0x942882a8551011c3980381c300
def v643 : W := 0x942882a8551111c3980381c300
def v644 : W := 0x942882ba5d3151c3980381c300
def v645 : W := 0x942883a9759711c398738ffbf3
def v646 : W := 0x943882a85d1011c3980381c300
def v647 : W := 0x943882a85d111003800001c000
def v648 : W := 0x943883ed7dd79003807c0ffcf3
def v649 : W := 0x9439a2a85d3151c3980381c300
def v650 : W := 0x992000b2100001c00003800000
def v651 : W := 0x992003ff700401c0007ffe0000
def v652 : W := 0x99312000000001c39800000000
def v653 : W := 0x993120b2182041c3980381c300
def v654 : W := 0x993120b2182141c3980381c300
def v655 : W := 0x993121b338a641c398738ffbf3
def v656 : W := 0x993122ba5d3151c3980381c300
def v657 : W := 0x993123bb7db751c398738ffbf3
def v658 : W := 0x993922b21d2041c3980381c300
def v659 : W := 0x993922b21d214003800001c000
def v660 : W := 0x993922ba5d315003800381c300
def v661 : W := 0x993922ba5d3151c3980381c300
def v662 : W := 0x9939a0b21d3151c3980381c300
def v663 : W := 0x9939a2ba5d3151c3980381c300
def v664 : W := 0x99b932b33d2d403b870071c0fc
def v665 : W := 0x9d200000000001c00000000000
def v666 : W := 0x9d2002ba500001c00003800000
def v667 : W := 0x9d2002ba5d3151c0000381c300
def v668 : W := 0x9d2002bb700401c00003fe0000
def v669 : W := 0x9d2003bb700401c000738e0000
def v670 : W := 0x9d2003bb759711c000738e38f3
def v671 : W := 0x9d2003ff700401c00003f00000
def v672 : W := 0x9d2003ff700401c0007ffe0000
def v673 : W := 0x9d21a2ba503151c01803800300
def v674 : W := 0x9d21a2ba5d3151c0180381c300
def v675 : W := 0x9d265bff720c21c067fffe0000
def v676 : W := 0x9d2882ba551011c3980381c300
def v677 : W := 0x9d2882ba551111c00003800000
def v678 : W := 0x9d2883ff759711c0007ffe38f3
def v679 : W := 0x9d29a2ba553151c01803800300
def v680 : W := 0x9d29a2ba553151c3980381c300
def v681 : W := 0x9d29a2ba5d3151c3980381c300
def v682 : W := 0x9d2a9aba579b31c000038038f3
def v683 : W := 0x9d3122ba582041c3980381c300
def v684 : W := 0x9d3122ba582141c00003800000
def v685 : W := 0x9d3122ba5d3151c0000381c300
def v686 : W := 0x9d3122ba5d3151c3980381c300
def v687 : W := 0x9d31a0ba583151c3980381c300
def v688 : W := 0x9d31a2ba5d3151c3980381c300
def v689 : W := 0x9d3572ba58ebc1c007038000fc
def v690 : W := 0x9d3802ba5d0001c3800381c000
def v691 : W := 0x9d39a000000001c39800000000
def v692 : W := 0x9d39a0000d3151c3980001c300
def v693 : W := 0x9d39a012082141c39800000000
def v694 : W := 0x9d39a01a403151c39803800300
def v695 : W := 0x9d39a0b2182041c3980381c300
def v696 : W := 0x9d39a1b338a641c398738ffbf3
def v697 : W := 0x9d39a208451111c39800000000
def v698 : W := 0x9d39a2a01d0001c3980001c000
def v699 : W := 0x9d39a2a8551011c3980381c300
def v700 : W := 0x9d39a2ba500001c39803800000
def v701 : W := 0x9d39a2ba553151c3980381c300
def v702 : W := 0x9d39a2ba5d3051c3980381c300
def v703 : W := 0x9d39a2ba5d315003800001c000
def v704 : W := 0x9d39a2ba5d3151c00003800000
def v705 : W := 0x9d39a2ba5d3151c3980381c300
def v706 : W := 0x9d39a309659711c398700e38f3
def v707 : W := 0x9d39a3ba5db351c3980381c300
def v708 : W := 0x9d39a3bb7db751c398738ffbf3
def v709 : W := 0x9d39a3fe5df3d1c3980381c300
def v710 : W := 0x9d39a3fe5df3d1c3987f81ff00
def v711 : W := 0x9d39a3ff7d3551c3987fffc300
def v712 : W := 0x9d39a3ff7db751c3987ffffbf3
def v713 : W := 0x9d39a3ff7df7d1c39803f1c3fc
def v714 : W := 0x9d39a3ff7df7d1c39873fffbff
def v715 : W := 0x9d39a3ff7df7d1c3987f8ffff3
def v716 : W := 0x9d3baaba5f3171c3f88381c300
def v717 : W := 0x9d3bbaba5f3971c3980381c300
def v718 : W := 0x9d3bbaba5fbb71c3980381fbf3
def v719 : W := 0x9d3de2ba5d71d1c3f80381c700
def v720 : W := 0x9d3de2ba5df3d1c3980381c300
def v721 : W := 0x9d3df2ba5dfbd1c39f0381c3fc
def v722 : W := 0x9d3fe2ba5f3151c3f80381c300
def v723 : W := 0x9d3fe2ba5ff3d1c3f80381ff00
def v724 : W := 0x9d3ff800020821c3ff80000000
def v725 : W := 0x9d3ffaba5f3971c3ff8381c300
def v726 : W := 0x9d79aabadd3171c7988381c300
def v727 : W := 0x9da002bb700401f80003f00000
def v728 : W := 0x9da003bb700401c00003800000
def v729 : W := 0x9db9a3bb7d3551c3980381c300
def v730 : W := 0x9db9b2ba5d3951c3980381c300
def v731 : W := 0x9db9b2bb7d3d51fb9f03f1c3fc
def v732 : W := 0x9db9b3bb7dbf51c3980381c3f0
def v733 : W := 0x9de000bbf00401fc0003fe0000
def v734 : W := 0x9de000bbf0040ffc000ffe0000
def v735 : W := 0x9de002bbf00401c000038e0000
def v736 : W := 0x9de002bbf00401fc0003fe0000
def v737 : W := 0x9de003fff00401fc007ffe0000
def v738 : W := 0x9df9a2bbfd3551ff9803ffc300
def v739 : W := 0x9df9b800800821ff9f80000000
def v740 : W := 0x9df9babadd3971c3980381c300
def v741 : W := 0x9df9babadd3971ff9f8381c300
def v742 : W := 0x9df9babbfd3d71c398038fc3f3
def v743 : W := 0xb02006a010000e00007c000000
def v744 : W := 0xb02007ff70040e00007ffe0000
def v745 : W := 0xb02a040002000e03e000000000
def v746 : W := 0xb02a06a017000e03e07c01fc00
def v747 : W := 0xb02a07a017820e03e07c01fc00
def v748 : W := 0xb02a07e41fc28e03e07c01fc00
def v749 : W := 0xb03a06a01f000003800001c000
def v750 : W := 0xb03a06a01f000e03e07c01fc00
def v751 : W := 0xb03a07a01f820003807001f800
def v752 : W := 0xb03e46a01fc28e03e07c01fc00
def v753 : W := 0xb42a86a857101fc3f87f81ff00
def v754 : W := 0xb460040080000fc40000000000
def v755 : W := 0xb46006a8d0000fc4007f8e0000
def v756 : W := 0xb46006bbf0040fc4007ffe0000
def v757 : W := 0xb46007a9f0040fc4007f8e0000
def v758 : W := 0xb46007edf0040fc4007ffe0000
def v759 : W := 0xb46007fff0040fc4007ffe0000
def v760 : W := 0xb46886a8d5101fc7987f8fc300
def v761 : W := 0xb46a06a8d7000fc7e07f8ffc00
def v762 : W := 0xb46a86a8d7101fc7f87f8fff00
def v763 : W := 0xb46a8c0082002fc7f880000000
def v764 : W := 0xb46a8d57aae7efc7f8807000fc
def v765 : W := 0xb46a8e08c7103fc7f8f00e3803
def v766 : W := 0xb46a8ea097002fc7f8fc01fc00
def v767 : W := 0xb46a8ea8d2002fc7f8ff8e0000
def v768 : W := 0xb46a8ea8d71031c3980381c300
def v769 : W := 0xb46a8ea8d71031c398738ffb03
def v770 : W := 0xb46a8ea8d7103e03e07c0ffc03
def v771 : W := 0xb46a8ea8d7103fc3f87f8fff03
def v772 : W := 0xb46a8ea8d7103fc4007f8e3803
def v773 : W := 0xb46a8ea8d7103fc7f88381c300
def v774 : W := 0xb46a8fedf7d6bfc7f883f1c3fc
def v775 : W := 0xb46a9c0082082fc7f880000000
def v776 : W := 0xb46a9ea8d79b3fc4007f8e38f3
def v777 : W := 0xb46bbc0082082fc7ff80000000
def v778 : W := 0xb46edc0082082fc7ff80000000
def v779 : W := 0xb47576a8d8ebcfc4077f8e00fc
def v780 : W := 0xb47ffc0082082fc7ff80000000
def v781 : W := 0xb47ffea8df397fc7ff8381c300
def v782 : W := 0xb4e006a9f0040fc4007f8e0000
def v783 : W := 0xb4e006a9f0040ffc007ffe0000
def v784 : W := 0xb4e007a9f004000000700e0000
def v785 : W := 0xb4e007a9f00401c000738e0000
def v786 : W := 0xb4e007a9f0040e00007c0e0000
def v787 : W := 0xb4e007a9f0040fc4007f8e0000
def v788 : W := 0xb4e007fff0040fc4007ffe0000
def v789 : W := 0xb4ea9c00820821c39800000000
def v790 : W := 0xb4ea9c0082082e03e000000000
def v791 : W := 0xb4ea9c0082082fc40000000000
def v792 : W := 0xb4ea9c0082082fc7f880000000
def v793 : W := 0xb4ea9c0082082fffff80000000
def v794 : W := 0xb4ea9ea8d71831c3980381c300
def v795 : W := 0xb4ea9ea8d7193fc7f88381c300
def v796 : W := 0xb4ea9f09e79f3fc7f8f00e38f3
def v797 : W := 0xb4ea9fa9f79f300000700e38f3
def v798 : W := 0xb4ea9fa9f79f31c398738ffbf3
def v799 : W := 0xb4ea9fa9f79f3e03e07c0ffcf3
def v800 : W := 0xb4ea9fa9f79f3fc4007f8e38f3
def v801 : W := 0xb4fa9c00820820038000000000
def v802 : W := 0xb4fa9ea09f082003800001c000
def v803 : W := 0xb4fa9fa9ff9f300380700ff8f3
def v804 : W := 0xb4fffc0082082fc7ff80000000
def v805 : W := 0xb9a006b330040e38007c700000
def v806 : W := 0xb9ab36b3372d4e3be77c71fcfc
def v807 : W := 0xb9e005b3b00401c000738e0000
def v808 : W := 0xb9f33c00820821c39800000000
def v809 : W := 0xb9f33cb29a2861c3980381c300
def v810 : W := 0xb9f33db3baae61c398738ffbf3
def v811 : W := 0xb9f33ebadf3971c3980381c300
def v812 : W := 0xbd3ba6ba5f3151c3980381c300
def v813 : W := 0xbd3ba6ba5f315fc3f87f81ff00
def v814 : W := 0xbd3ba7ba5fb351c3987381fb00
def v815 : W := 0xbd6006bad0000fc4007f8e0000
def v816 : W := 0xbd6007fff0040fc4007ffe0000
def v817 : W := 0xbd79a6badd315fc7987f8fc300
def v818 : W := 0xbd7bac0082002fc7f880000000
def v819 : W := 0xbd7baebadf3171c3980381c300
def v820 : W := 0xbd7baebadf3171c398738ffb03
def v821 : W := 0xbd7baebadf317fc7f88381c300
def v822 : W := 0xbd7bbebadf3971c3980381c300
def v823 : W := 0xbd7ffc0082082fc7ff80000000
def v824 : W := 0xbd7ffebadf397fc7ff8381c300
def v825 : W := 0xbde006bad00001c00003800000
def v826 : W := 0xbde006bbf00401fc0003fe0000
def v827 : W := 0xbde006bbf0040ffc007ffe0000
def v828 : W := 0xbde007bbf00401c000738e0000
def v829 : W := 0xbde007bbf00401fc0073fe0000
def v830 : W := 0xbde007bbf0040fc4007f8e0000
def v831 : W := 0xbde007bbf0040ffc007ffe0000
def v832 : W := 0xbde007fff00401c0007ffe0000
def v833 : W := 0xbde007fff0040ffc007ffe0000
def v834 : W := 0xbdea9c00820821c00000000000
def v835 : W := 0xbdea9ebad20821c00003800000
def v836 : W := 0xbdea9fbbf79f31c000738e38f3
def v837 : W := 0xbdebbc0082082fffff80000000
def v838 : W := 0xbdebbebad73971c3980381c300
def v839 : W := 0xbdebbebad7397fffff8381c300
def v840 : W := 0xbdf9a6badd3151c3980381c300
def v841 : W := 0xbdf9a7bbfd3551c398738fc300
def v842 : W := 0xbdfbbc00820821c39800000000
def v843 : W := 0xbdfbbc00820821ff9f80000000
def v844 : W := 0xbdfbbc0082082fc7f880000000
def v845 : W := 0xbdfbbc0082082fffff80000000
def v846 : W := 0xbdfbbcb29a2861c3980381c300
def v847 : W := 0xbdfbbebadf3971c3980381c300
def v848 : W := 0xbdfbbebadf3971c3f88381c300
def v849 : W := 0xbdfbbebadf3971c7988381c300
def v850 : W := 0xbdfbbebadf3971ff9f8381c300
def v851 : W := 0xbdfbbebadf397fc7f88381c300
def v852 : W := 0xbdfbbebadf397fffff8381c300
def v853 : W := 0xbdfbbf09e79f31c398700e38f3
def v854 : W := 0xbdfbbfbadfbb71c3980381c300
def v855 : W := 0xbdfbbfbbff3d71c3980381c300
def v856 : W := 0xbdfbbfbbffbf71c398738ffbf3
def v857 : W := 0xbdfffc00820821c3ff80000000
def v858 : W := 0xbdfffc0082082fffff80000000
def v859 : W := 0xbdfffebadf3971c3f80381c300
def v860 : W := 0xbdfffebadf3971c3ff8381c300
def v861 : W := 0xd22000e410000e00000c000000
def v862 : W := 0xd22003ff70040e00007ffe0000
def v863 : W := 0xd22c43e415c28003800001c000
def v864 : W := 0xd234400000000e03e000000000
def v865 : W := 0xd23440e418408e03e00c01c400
def v866 : W := 0xd23440e418c28e03e00c01c400
def v867 : W := 0xd23440e41dc28e03e00c01fc00
def v868 : W := 0xd23441e418c28003800001c000
def v869 : W := 0xd23441e418c28e00000c000000
def v870 : W := 0xd23441e418c28e03e00c01c400
def v871 : W := 0xd23441e418c28e03e07c01fc00
def v872 : W := 0xd23443e418c280000000000000
def v873 : W := 0xd23443e41dc28e03e07c01fc00
def v874 : W := 0xd23443ed7dd79e03e07c0ffcf3
def v875 : W := 0xd23640e41ac28e03e00c01fc00
def v876 : W := 0xd23c42e41d408e03e00c01c400
def v877 : W := 0xd23c43e41dc28003800001c000
def v878 : W := 0xd23c43e41dc28003807c01fc00
def v879 : W := 0xd23c43e41dc28e03e00c01c400
def v880 : W := 0xd23c43e41dc28e03e07c01fc00
def v881 : W := 0xd23e40e41fc28e03e00c01fc00
def v882 : W := 0xd23e41e41fc28e03e00c01fc00
def v883 : W := 0xd23e42e41fc28e03e00c01fc00
def v884 : W := 0xd23e43e41fc28003e00001fc00
def v885 : W := 0xd23e43e41fc28e03e07c01fc00
def v886 : W := 0xd6a003ed700401f80003f00000
def v887 : W := 0xd6acd3ed75de91fb9f03f1c3fc
def v888 : W := 0xd6e000edf0040e00000c0e0000
def v889 : W := 0xd6f4d8edf85dbe03e00c0fc4f3
def v890 : W := 0xd6f4dbe49dcaae03e07c01fc00
def v891 : W := 0xdb20000000000ffc0000000000
def v892 : W := 0xdb2000f610000ffc000ff00000
def v893 : W := 0xdb2000ff70040ffc000ffe0000
def v894 : W := 0xdb2001f730040ffc000ff00000
def v895 : W := 0xdb2001f730040ffc007ffe0000
def v896 : W := 0xdb2003ff70040ffc007ffe0000
def v897 : W := 0xdb2003ff75971ffc007ffe38f3
def v898 : W := 0xdb2a98f6179b3ffc000ff038f3
def v899 : W := 0xdb2a9bff720c2ffc007ffe0000
def v900 : W := 0xdb3120f618204fff980ff1c300
def v901 : W := 0xdb3440f618408fffe00ff1c400
def v902 : W := 0xdb35600000000fffff80000000
def v903 : W := 0xdb3560560860cfffff8070000c
def v904 : W := 0xdb3560b218204fffff8381c300
def v905 : W := 0xdb3560e418408fffff8c01c400
def v906 : W := 0xdb3560f610000fffff8ff00000
def v907 : W := 0xdb3560f618204fffff8ff1c300
def v908 : W := 0xdb3560f61860c1fb9f03f1c30c
def v909 : W := 0xdb3560f61860ce3be70c71c40c
def v910 : W := 0xdb3560f61860cfc3f80f81c700
def v911 : W := 0xdb3560f61860cffc070ff0000c
def v912 : W := 0xdb3560f61860cfffff83f1c30c
def v913 : W := 0xdb3561b338a64ffffff38ffbf3
def v914 : W := 0xdb35630965971ffffff00e38f3
def v915 : W := 0xdb3570f618ebcffc070ff000fc
def v916 : W := 0xdb3ff80002082fffff80000000
def v917 : W := 0xdba000f730040ffc000ff00000
def v918 : W := 0xdba001f7300401f80003f00000
def v919 : W := 0xdba001f730040e38000c700000
def v920 : W := 0xdba001f730040ffc000ff00000
def v921 : W := 0xdba003f7300400380000700000
def v922 : W := 0xdba003ff70040ffc007ffe0000
def v923 : W := 0xdbb5700000080fffff80000000
def v924 : W := 0xdbb5715728efcfffff807000fc
def v925 : W := 0xdbb571f738efc1fb9f03f1c3fc
def v926 : W := 0xdbb571f738efce3be70c71c4fc
def v927 : W := 0xdbb571f738efcffc070ff000fc
def v928 : W := 0xdbb573f738efc03807007000fc
def v929 : W := 0xdbbd73f73defc03b870071c0fc
def v930 : W := 0xdbe000f7b0040ffc000ffe0000
def v931 : W := 0xdf2002fe50000ffc000ff00000
def v932 : W := 0xdf2003ff70040ffc007ffe0000
def v933 : W := 0xdf39a2fe5d315fff980ff1c300
def v934 : W := 0xdf39a3fe5d3151c3980381c300
def v935 : W := 0xdf3de00000000fffff80000000
def v936 : W := 0xdf3de2ba5d3151c3980381c300
def v937 : W := 0xdf3de2ba5d315fffff8381c300
def v938 : W := 0xdf3de2fe5d71d1c3980381c300
def v939 : W := 0xdf3de2fe5d71d1fb9f03f1c30c
def v940 : W := 0xdf3de2fe5d71dfc3f80f81c700
def v941 : W := 0xdf3de3fe5df3d1c3980381c300
def v942 : W := 0xdfa003ff700401f80003f00000
def v943 : W := 0xdfa003ff700401f8007ffe0000
def v944 : W := 0xdfa003ff70040ffc000ff00000
def v945 : W := 0xdfb573ff78efc1f80703f000fc
def v946 : W := 0xdfb9a3ff7d3551fb9803f1c300
def v947 : W := 0xdfbdf000000801fb9f00000000
def v948 : W := 0xdfbdf15728efc1fb9f007000fc
def v949 : W := 0xdfbdf2ba5d3951fb9f0381c300
def v950 : W := 0xdfbdf3ff7dffd1fb9f03f1c3fc
def v951 : W := 0xdfe000fff0040ffc000ffe0000
def v952 : W := 0xdfe001fff0040ffc000ffe0000
def v953 : W := 0xdfe002fff0040ffc000ffe0000
def v954 : W := 0xdfe003fff00401fc0003fe0000
def v955 : W := 0xdfe003fff0040ffc007ffe0000
def v956 : W := 0xdff5f80080082fffff80000000
def v957 : W := 0xf220040000000e000000000000
def v958 : W := 0xf22007e410000e00007c000000
def v959 : W := 0xf22007e41dc28e00007c01fc00
def v960 : W := 0xf22007e530040e00007c7e0000
def v961 : W := 0xf22007e530040e3c007c7e0000
def v962 : W := 0xf22007ed70040e00007c0e0000
def v963 : W := 0xf22007f730040e00007c700000
def v964 : W := 0xf22007ff70040e00007ffe0000
def v965 : W := 0xf22137e410294e00077c0000fc
def v966 : W := 0xf22447e410c28e00007c000000
def v967 : W := 0xf22447e410c28e00607c003c00
def v968 : W := 0xf22645e412c28e00607c003c00
def v969 : W := 0xf22645e412c28e03e07c01fc00
def v970 : W := 0xf22647e412c28e00607c003c00
def v971 : W := 0xf22647e41fc28e00607c01fc00
def v972 : W := 0xf22a07e417000e03e07c01fc00
def v973 : W := 0xf22a07e417820e00007c003800
def v974 : W := 0xf22a9fe4179b3e00007c0038f3
def v975 : W := 0xf22e47e417c28e00607c003c00
def v976 : W := 0xf22e47e417c28e03e07c01fc00
def v977 : W := 0xf22e47e41fc28e03e07c01fc00
def v978 : W := 0xf23447e418408e03e07c01c400
def v979 : W := 0xf23447e418c28e00007c000000
def v980 : W := 0xf23447e418c28e03e07c01c400
def v981 : W := 0xf23447e41dc28e00007c01fc00
def v982 : W := 0xf23447e41dc28e03e07c01fc00
def v983 : W := 0xf23577e418ebce00077c0000fc
def v984 : W := 0xf23645e41ac28e03e07c01fc00
def v985 : W := 0xf23647e41ac28e00607c003c00
def v986 : W := 0xf23647e41ac28e03e07c01fc00
def v987 : W := 0xf23647e41fc28e03e07c01fc00
def v988 : W := 0xf23807e41d000e03807c01c000
def v989 : W := 0xf23c47e41dc28e03807c01c000
def v990 : W := 0xf23e440002000e03e000000000
def v991 : W := 0xf23e44000fc28e03e00001fc00
def v992 : W := 0xf23e44e41a408e03e00c01c400
def v993 : W := 0xf23e44e41fc28e03e00c01fc00
def v994 : W := 0xf23e44ed7a559e03e00c0fc4f3
def v995 : W := 0xf23e454402c28e03e07c003c00
def v996 : W := 0xf23e45440ac28e03e000000000
def v997 : W := 0xf23e45e41ac28e03e00c01c400
def v998 : W := 0xf23e45e41ac28e03e07c01fc00
def v999 : W := 0xf23e45e41fc28e03e07c01fc00
def v1000 : W := 0xf23e46a017000e03e07c01fc00
def v1001 : W := 0xf23e46a01f000e03e00001c000
def v1002 : W := 0xf23e46e41f408e03e07c01fc00
def v1003 : W := 0xf23e46e41fc28e03e07c01fc00
def v1004 : W := 0xf23e470007820e03e070003800
def v1005 : W := 0xf23e47e412000e03e07c000000
def v1006 : W := 0xf23e47e412c28e03e07c003c00
def v1007 : W := 0xf23e47e417c28e03e07c01fc00
def v1008 : W := 0xf23e47e41ac28e03e07c000000
def v1009 : W := 0xf23e47e41fc28003800001c000
def v1010 : W := 0xf23e47e41fc28003807001f800
def v1011 : W := 0xf23e47e41fc28e00007c003800
def v1012 : W := 0xf23e47e41fc28e03e00001c000
def v1013 : W := 0xf23e47e41fc28e03e07c01fc00
def v1014 : W := 0xf23e47e41fc38e03e07c01fc00
def v1015 : W := 0xf23e47e41ff3de03e07c01ff00
def v1016 : W := 0xf23e47ec5fd29e03e07c0ffc03
def v1017 : W := 0xf23e47ec5fd39e03e07c01fc00
def v1018 : W := 0xf23e47ed7fc68e03e07c0ffc00
def v1019 : W := 0xf23e47ed7fd79e03e07c0ffcf3
def v1020 : W := 0xf23e47f61fe3ce03e07c01fc00
def v1021 : W := 0xf23e47f73fe7ce03e07c71fcfc
def v1022 : W := 0xf23e47fe5ff3de03e07f81ff00
def v1023 : W := 0xf23e47ff7fc68e03e07ffffc00
def v1024 : W := 0xf23ec7e41fd29e03f87c01ff00
def v1025 : W := 0xf23ec7e41fd39e03e07c01fc00
def v1026 : W := 0xf23ecfe41fc2ae03f8fc01fc00
def v1027 : W := 0xf23ecfe41fd2be03e07c01fc03
def v1028 : W := 0xf23edfe41fcaae03e07c01fc00
def v1029 : W := 0xf23edfe41fdbbe03e07c01fcf3
def v1030 : W := 0xf23f67e41fe2ce03f87c01ff00
def v1031 : W := 0xf23f67e41fe3ce03e07c01fc00
def v1032 : W := 0xf23f77e41febce03e77c01fcfc
def v1033 : W := 0xf23fe7e41fc28e03f87c01fc00
def v1034 : W := 0xf23fe7e41ff3de03f87c01ff00
def v1035 : W := 0xf23ffc0002082e03ff80000000
def v1036 : W := 0xf23fffe41fcaae03fffc01fc00
def v1037 : W := 0xf23fffe41ffbfe03f87c01ff00
def v1038 : W := 0xf27e47e49fc28e07e07c0ffc00
def v1039 : W := 0xf27e4fe49fc2ae03e07c0ffc03
def v1040 : W := 0xf27e4fe49fc2ae07e0fc01fc00
def v1041 : W := 0xf2a007e530040e00007c000000
def v1042 : W := 0xf2a007e530040e38007c700000
def v1043 : W := 0xf2be47e53fc68e03e07c01fc00
def v1044 : W := 0xf2be57e41fca8e03e07c01fc00
def v1045 : W := 0xf2be57e53fce8e3be77c71fcfc
def v1046 : W := 0xf2be57e53fcf8e03e07c01fcf0
def v1047 : W := 0xf2e005e5b0040e3c007c7e0000
def v1048 : W := 0xf2e005e5b0040ffc007ffe0000
def v1049 : W := 0xf2e007e5b0040e00007c0e0000
def v1050 : W := 0xf2e007e5b0040e3c007c7e0000
def v1051 : W := 0xf2e007fff0040e3c007ffe0000
def v1052 : W := 0xf2e65c0082082e3c6780000000
def v1053 : W := 0xf2e65c0082082fffff80000000
def v1054 : W := 0xf2ee5c0082082e3fe780000000
def v1055 : W := 0xf2f65c0082082e3fe780000000
def v1056 : W := 0xf2f65ce49a48ae3fe78c01c400
def v1057 : W := 0xf2fe47e5bfc68e03e07c0ffc00
def v1058 : W := 0xf2fe47e5bfc68e3fe07c7ffc00
def v1059 : W := 0xf2fe5c0082082e03e000000000
def v1060 : W := 0xf2fe5c0082082e3fe780000000
def v1061 : W := 0xf2fe5ea09f082e3fe78001c000
def v1062 : W := 0xf2fe5fe49fcaae03e07c01fc00
def v1063 : W := 0xf2fe5fe49fcaae3fe7fc01fc00
def v1064 : W := 0xf2fe5fe5bfceae03e07c0ffcf3
def v1065 : W := 0xf2fffc0082082e3fff80000000
def v1066 : W := 0xf63e47ec5fc28e03e07c01fc00
def v1067 : W := 0xf63ec7e41fc28e03e07c01fc00
def v1068 : W := 0xf63ec7ec5fd29e03e07c01fc00
def v1069 : W := 0xf63ec7ec5fd29fc3f87f81ff00
def v1070 : W := 0xf63ec7ec5fd39e03e07c01fc00
def v1071 : W := 0xf63fe7ec5ff3de03f87c01ff00
def v1072 : W := 0xf66007ecd0000fc4007f8e0000
def v1073 : W := 0xf66007edf0040ffc007ffe0000
def v1074 : W := 0xf66007fff0040fc4007ffe0000
def v1075 : W := 0xf66ecfedf7d6b1fb9f03f1c3fc
def v1076 : W := 0xf67e47ecdfc28e03e07c0ffc00
def v1077 : W := 0xf67e47ecdfc28fc7e07f8ffc00
def v1078 : W := 0xf67ecc0082002fc7f880000000
def v1079 : W := 0xf67ecfe49fc2ae03e07c01fc00
def v1080 : W := 0xf67ecfe49fc2afc7f8fc01fc00
def v1081 : W := 0xf67ecfecdfd2be03e07c0ffc03
def v1082 : W := 0xf67ecfecdfd3be03e07c0ffc03
def v1083 : W := 0xf67ffc0082082fc7ff80000000
def v1084 : W := 0xf6e007edf0040e00007c0e0000
def v1085 : W := 0xf6e007edf0040e3c007c7e0000
def v1086 : W := 0xf6e007edf0040fc4007f8e0000
def v1087 : W := 0xf6e007edf0040ffc007ffe0000
def v1088 : W := 0xf6e007fff0040e00007ffe0000
def v1089 : W := 0xf6e007fff0040ffc007ffe0000
def v1090 : W := 0xf6e647edf2c68e00607c0e3c00
def v1091 : W := 0xf6e65c0082082ffc6780000000
def v1092 : W := 0xf6ea9c0082082e000000000000
def v1093 : W := 0xf6ea9fedf79f3e00007c0e38f3
def v1094 : W := 0xf6eedc0082082fffff80000000
def v1095 : W := 0xf6eedea8d7183fffff8381c300
def v1096 : W := 0xf6f447edf8c68e00007c0e0000
def v1097 : W := 0xf6fe47e49fc28e03e07c01fc00
def v1098 : W := 0xf6fe47edffc68e03e07c0ffc00
def v1099 : W := 0xf6fec7edffd79e03e07c0ffc00
def v1100 : W := 0xf6fecfedffd6be03e07c0ffc03
def v1101 : W := 0xf6fedc0082082e03e000000000
def v1102 : W := 0xf6fedc0082082e3fe780000000
def v1103 : W := 0xf6fedc0082082fc7f880000000
def v1104 : W := 0xf6fedc0082082fffff80000000
def v1105 : W := 0xf6fedce49a48ae03e00c01c400
def v1106 : W := 0xf6fedde49acaae03e00c01c400
def v1107 : W := 0xf6fedea8df193e03e00001c000
def v1108 : W := 0xf6fedf09e79f3e03e0700e38f3
def v1109 : W := 0xf6fedfe49fcaa003800001c000
def v1110 : W := 0xf6fedfe49fcaae03e07c01fc00
def v1111 : W := 0xf6fedfecdfdabe03e07c0ffc03
def v1112 : W := 0xf6fedfecdfdbbe03e07c01fc00
def v1113 : W := 0xf6fedfedffceae03e07c0ffc00
def v1114 : W := 0xf6fedfedffdfbe03e07c0ffcf3
def v1115 : W := 0xf6fffc0082082e03ff80000000
def v1116 : W := 0xf6fffc0082082fffff80000000
def v1117 : W := 0xfb2007f610000ffc007ff00000
def v1118 : W := 0xfb2007ff70040ffc007ffe0000
def v1119 : W := 0xfb3e47f61fc28e03e07c01fc00
def v1120 : W := 0xfb3e47f61fc28fffe07ff1fc00
def v1121 : W := 0xfb3f640002000fffff80000000
def v1122 : W := 0xfb3f67e41fc28e03e07c01fc00
def v1123 : W := 0xfb3f67e41fc28ffffffc01fc00
def v1124 : W := 0xfb3f67f61fe2ce03e07c01fc00
def v1125 : W := 0xfb3f67f61fe2ce3be77c71fc0c
def v1126 : W := 0xfb3f67f61fe2cfc3f87f81ff00
def v1127 : W := 0xfb3f67f61fe3ce03e07c01fc00
def v1128 : W := 0xfb3fe7f61ff3de03f87c01ff00
def v1129 : W := 0xfba007f730040e38007c700000
def v1130 : W := 0xfba007f730040ffc007ff00000
def v1131 : W := 0xfba007ff70040e38007ffe0000
def v1132 : W := 0xfbb577f738efce38077c7000fc
def v1133 : W := 0xfbbe47f73fc68e3be07c71fc00
def v1134 : W := 0xfbbf740002080e3be700000000
def v1135 : W := 0xfbbf75572aefce3be7007000fc
def v1136 : W := 0xfbbf77e41fca8e3be77c01fc00
def v1137 : W := 0xfbbf77f61febce03e07c01fc00
def v1138 : W := 0xfbbf77f73fefce3be77c71fcfc
def v1139 : W := 0xfbe005f7b0040ffc007ffe0000
def v1140 : W := 0xfbe007f7b0040e3c007c7e0000
def v1141 : W := 0xfbe007f7b0040ffc007ffe0000
def v1142 : W := 0xfbe007fff0040ffc007ffe0000
def v1143 : W := 0xfbe65c0082082ffc6780000000
def v1144 : W := 0xfbe65cf692082ffc678ff00000
def v1145 : W := 0xfbe65df7b20c2ffc678ff00000
def v1146 : W := 0xfbf77c0082082fffff80000000
def v1147 : W := 0xfbf77cb29a286fffff8381c300
def v1148 : W := 0xfbff7c0082082e3fe780000000
def v1149 : W := 0xfbff7c0082082fffff80000000
def v1150 : W := 0xfbfffc0082082fffff80000000
def v1151 : W := 0xff2007fe50000fc0007f800000
def v1152 : W := 0xff2007ff70040fc0007ffe0000
def v1153 : W := 0xff39a7fe5d315fc3987f81c300
def v1154 : W := 0xff3e47fe5fc28fc3e07f81fc00
def v1155 : W := 0xff3fe40002000fc3f800000000
def v1156 : W := 0xff3fe6ba5f315fc3f80381c300
def v1157 : W := 0xff3fe7e41fc28fc3f87c01fc00
def v1158 : W := 0xff3fe7fe5ff3de03e07c01fc00
def v1159 : W := 0xff3fe7fe5ff3dfc3f87f81ff00
def v1160 : W := 0xff6006fed0000ffc007ffe0000
def v1161 : W := 0xff6007fff0040ffc007ffe0000
def v1162 : W := 0xff7fec0082002fffff80000000
def v1163 : W := 0xff7ffc0082082fffff80000000
def v1164 : W := 0xffa007ff70040ff8007ff00000
def v1165 : W := 0xffbff7ff7fffdffbff7ff1fffc
def v1166 : W := 0xffe0040080000ffc0000000000
def v1167 : W := 0xffe0041be0040ffc0003fe0000
def v1168 : W := 0xffe004f690000ffc000ff00000
def v1169 : W := 0xffe004f695931ffc000ff038f3
def v1170 : W := 0xffe004fff0040ffc000ffe0000
def v1171 : W := 0xffe00545a0040ffc007c7e0000
def v1172 : W := 0xffe00557a0040ffc0000700000
def v1173 : W := 0xffe005f7b0040ffc000ff00000
def v1174 : W := 0xffe005f7b0040ffc007ffe0000
def v1175 : W := 0xffe005fff0040ffc007ffe0000
def v1176 : W := 0xffe006a8d0000ffc007f8e0000
def v1177 : W := 0xffe006bad0000ffc0003800000
def v1178 : W := 0xffe006bbf0040ffc0003fe0000
def v1179 : W := 0xffe006bbf0040ffc007ffe0000
def v1180 : W := 0xffe006fff0040ffc007ffe0000
def v1181 : W := 0xffe00709e0040ffc00700e0000
def v1182 : W := 0xffe007a9f0040ffc007f8e0000
def v1183 : W := 0xffe007bbf0040ffc00738e0000
def v1184 : W := 0xffe007e490000ffc007c000000
def v1185 : W := 0xffe007e5b0040ffc007c7e0000
def v1186 : W := 0xffe007edf0040ffc007c0e0000
def v1187 : W := 0xffe007edf0040ffc007ffe0000
def v1188 : W := 0xffe007f7b0040ffc007c700000
def v1189 : W := 0xffe007fff00401f80003f00000
def v1190 : W := 0xffe007fff00401f80073fe0000
def v1191 : W := 0xffe007fff0040e38007c7e0000
def v1192 : W := 0xffe007fff0040fc0007f8e0000
def v1193 : W := 0xffe007fff0040ffc0003f00000
def v1194 : W := 0xffe007fff0040ffc007ffe0000
def v1195 : W := 0xffe007fff0050ffc007ffe0000
def v1196 : W := 0xffe007fff0355ffc007ffe0300
def v1197 : W := 0xffe007fff0860ffc007ffe0000
def v1198 : W := 0xffe007fff0c68ffc007ffe3c00
def v1199 : W := 0xffe007fff5141ffc007ffe3803
def v1200 : W := 0xffe007fff5151ffc007ffe0000
def v1201 : W := 0xffe007fff5860ffc007ffe3800
def v1202 : W := 0xffe007fff5971ffc007ffe38f3
def v1203 : W := 0xffe007fff8254ffc007ffe0000
def v1204 : W := 0xffe007fff864cffc007ffe000c
def v1205 : W := 0xffe007fff8c68ffc007ffe0000
def v1206 : W := 0xffe007fff8e7cffc007ffe00fc
def v1207 : W := 0xffe007fffd355ffc007fffc300
def v1208 : W := 0xffe007fffdc68ffc007ffffc00
def v1209 : W := 0xffe017fff00c0ffc007ffe0000
def v1210 : W := 0xffe017fff08f0ffc007ffe00f0
def v1211 : W := 0xffe01ffff00c2ffc07fffe0000
def v1212 : W := 0xffe087fff0141ffc187ffe0300
def v1213 : W := 0xffe087fff0151ffc007ffe0000
def v1214 : W := 0xffe08ffff0042ffc18fffe0000
def v1215 : W := 0xffe08ffff0143ffc007ffe0003
def v1216 : W := 0xffe09ffff00c2ffc007ffe0000
def v1217 : W := 0xffe09ffff01d3ffc007ffe00f3
def v1218 : W := 0xffe127fff0040ffc1ffffe0000
def v1219 : W := 0xffe127fff0244ffc077ffe000c
def v1220 : W := 0xffe127fff0244ffc187ffe0300
def v1221 : W := 0xffe127fff0254ffc007ffe0000
def v1222 : W := 0xffe137fff00c0ffc077ffe0000
def v1223 : W := 0xffe137fff02d4ffc077ffe00fc
def v1224 : W := 0xffe1a7fff0040ffc187ffe0000
def v1225 : W := 0xffe1a7fff0355ffc187ffe0300
def v1226 : W := 0xffe1bc0080082ffc1f80000000
def v1227 : W := 0xffe1bffff00c2ffc1ffffe0000
def v1228 : W := 0xffe1bffff03d7ffc187ffe0300
def v1229 : W := 0xffe1bffff03d7ffc1ffffe0300
def v1230 : W := 0xffe207fff2040ffc607ffe3c00
def v1231 : W := 0xffe207fff2860ffc007ffe3800
def v1232 : W := 0xffe20ffff2042ffc007ffe3803
def v1233 : W := 0xffe20ffff2042ffc60fffe0000
def v1234 : W := 0xffe21c0082082ffc0000000000
def v1235 : W := 0xffe21ffff20c2ffc007ffe0000
def v1236 : W := 0xffe21ffff28e2ffc007ffe38f3
def v1237 : W := 0xffe447fff0040ffc67fffe0000
def v1238 : W := 0xffe447fff0448ffc077ffe000c
def v1239 : W := 0xffe447fff0448ffc607ffe0400
def v1240 : W := 0xffe447fff0c68ffc007ffe0000
def v1241 : W := 0xffe447fff0c68ffc607ffe3c00
def v1242 : W := 0xffe457fff00c0ffc077ffe0000
def v1243 : W := 0xffe457fff0ce8ffc077ffe00fc
def v1244 : W := 0xffe647fff2040ffc607ffe0000
def v1245 : W := 0xffe647fff2c68ffc607ffe3c00
def v1246 : W := 0xffe65c0082082ffc6780000000
def v1247 : W := 0xffe65ebad2082ffc6783800000
def v1248 : W := 0xffe65ffff20c2ffc6783f00000
def v1249 : W := 0xffe65ffff20c2ffc67fffe0000
def v1250 : W := 0xffe65ffff2ceaffc67fffe3c00
def v1251 : W := 0xffe7e7fff2f7dffc787ffe3f00
def v1252 : W := 0xffe7fc0082082ffc7f80000000
def v1253 : W := 0xffe7fffff20c2ffc7ffffe0000
def v1254 : W := 0xffe807fff5040ffc007ffe0000
def v1255 : W := 0xffe887fff0040ffc007ffe0000
def v1256 : W := 0xffe887fff5141ffc007ffe0000
def v1257 : W := 0xffe887fff5141fff987fffc300
def v1258 : W := 0xffe887fff5151ffc007ffe0000
def v1259 : W := 0xffe9a7fff5355ffc187ffe0300
def v1260 : W := 0xffea07fff2040ffc007ffe0000
def v1261 : W := 0xffea07fff7040ffc007ffe3800
def v1262 : W := 0xffea07fff7040fffe07ffffc00
def v1263 : W := 0xffea07fff7860ffc007ffe3800
def v1264 : W := 0xffea87fff7971ffc007ffe3800
def v1265 : W := 0xffea8c0082002ffff880000000
def v1266 : W := 0xffea8ffff2042ffc007ffe0000
def v1267 : W := 0xffea8ffff2042ffff8fffe0000
def v1268 : W := 0xffea8ffff7143ffc007ffe3803
def v1269 : W := 0xffea8ffff7153ffc007ffe3803
def v1270 : W := 0xffea8ffff7963ffc007ffe3803
def v1271 : W := 0xffea9c0082082ffc0000000000
def v1272 : W := 0xffea9c0082082ffff880000000
def v1273 : W := 0xffea9cf692082ffc000ff00000
def v1274 : W := 0xffea9df7b20c2ffc000ff00000
def v1275 : W := 0xffea9ebad7193ffc0003800000
def v1276 : W := 0xffea9f09e79f3ffc00700e38f3
def v1277 : W := 0xffea9ffff20c21f80003f00000
def v1278 : W := 0xffea9ffff20c2ffc007ffe0000
def v1279 : W := 0xffea9ffff71c3ffc007ffe3803
def v1280 : W := 0xffea9ffff71d3ffc007ffe0000
def v1281 : W := 0xffea9ffff78e2ffc007ffe3800
def v1282 : W := 0xffea9ffff79f3ffc007ffe38f3
def v1283 : W := 0xffebbc0082082ffc1f80000000
def v1284 : W := 0xffebbc0082082fffff80000000
def v1285 : W := 0xffebbffff20c2ffc1ffffe0000
def v1286 : W := 0xffee47fff7c68ffc607ffe3c00
def v1287 : W := 0xffeedc0082082ffc6780000000
def v1288 : W := 0xffeedc0082082fffff80000000
def v1289 : W := 0xffeedffff20c2ffc67fffe0000
def v1290 : W := 0xffeffc0082082fffff80000000
def v1291 : W := 0xfff007fff8040ffc007ffe0000
def v1292 : W := 0xfff127fff0040ffc007ffe0000
def v1293 : W := 0xfff127fff8244ffc007ffe0000
def v1294 : W := 0xfff127fff8244fff987fffc300
def v1295 : W := 0xfff127fff8254ffc007ffe0000
def v1296 : W := 0xfff137fff82d4ffc007ffe0000
def v1297 : W := 0xfff1a7fff8355ffc187ffe0300
def v1298 : W := 0xfff447fff0040ffc007ffe0000
def v1299 : W := 0xfff447fff8448ffc007ffe0000
def v1300 : W := 0xfff447fff8448fffe07fffc400
def v1301 : W := 0xfff447fff8c68ffc007ffe0000
def v1302 : W := 0xfff5640080000fffff80000000
def v1303 : W := 0xfff567fff0040ffc077ffe0000
def v1304 : W := 0xfff567fff0040ffffffffe0000
def v1305 : W := 0xfff567fff864cffc077ffe000c
def v1306 : W := 0xfff567fff865cffc077ffe000c
def v1307 : W := 0xfff567fff8e6cffc077ffe000c
def v1308 : W := 0xfff567fff8e7cffc007ffe0000
def v1309 : W := 0xfff5740080080ffc0700000000
def v1310 : W := 0xfff57557a8efcffc07007000fc
def v1311 : W := 0xfff577fff00c0ffc077ffe0000
def v1312 : W := 0xfff577fff82d4ffc077ffe0000
def v1313 : W := 0xfff577fff86ccffc077ffe000c
def v1314 : W := 0xfff577fff8ce8ffc077ffe0000
def v1315 : W := 0xfff577fff8efcffc077ffe00fc
def v1316 : W := 0xfff5fffff00c2ffc1ffffe0000
def v1317 : W := 0xfff647fffac68ffc607ffe3c00
def v1318 : W := 0xfff77c0082082ffc6780000000
def v1319 : W := 0xfff77c0082082fffff80000000
def v1320 : W := 0xfff77ffff20c2ffc67fffe0000
def v1321 : W := 0xfff7fc0082082fffff80000000
def v1322 : W := 0xfff807fffd040fff807fffc000
def v1323 : W := 0xfff9a40080000fff9800000000
def v1324 : W := 0xfff9a6badd315fff980381c300
def v1325 : W := 0xfff9a7fff0040fff987ffe0000
def v1326 : W := 0xfff9a7fffd355ffc007ffe0000
def v1327 : W := 0xfff9a7fffd355fff987fffc300
def v1328 : W := 0xfffbbc0082082fff9800000000
def v1329 : W := 0xfffbbebadf397fff980381c300
def v1330 : W := 0xfffbbfffff3d7fff987fffc300
def v1331 : W := 0xfffbbfffffbf7fff987ffffbf3
def v1332 : W := 0xfffdf7fffdffdfff9f7fffc3fc
def v1333 : W := 0xfffe440082000fffe000000000
def v1334 : W := 0xfffe47e49fc28fffe07c01fc00
def v1335 : W := 0xfffe47fff2040fffe07ffe0000
def v1336 : W := 0xfffe47ffffc68ffc007ffe3800
def v1337 : W := 0xfffe47ffffc68fffe07ffffc00
def v1338 : W := 0xfffe5c0082082fffe780000000
def v1339 : W := 0xfffedc0082082fffe000000000
def v1340 : W := 0xfffedfffffdfbfffe07ffffcf3
def v1341 : W := 0xffff77ffffefcfffe77ffffcfc
def v1342 : W := 0xffffe7fffff7dffff87fffff00
def v1343 : W := 0xffffefffff74fffc077ffe380f
def v1344 : W := 0xfffffc00820821fb9f00000000
def v1345 : W := 0xfffffc0082082e3be700000000
def v1346 : W := 0xfffffc0082082fc3f800000000
def v1347 : W := 0xfffffc0082082ffc0700000000
def v1348 : W := 0xfffffc0082082fffff80000000
def v1349 : W := 0xfffffc0082092fffff80000000
def v1350 : W := 0xfffffc0082397fffff80000300
def v1351 : W := 0xfffffc0087183fffff8001c300
def v1352 : W := 0xfffffc0087193fffff80000000
def v1353 : W := 0xfffffc00879b3fffff800038f3
def v1354 : W := 0xfffffc008a082fffff80000000
def v1355 : W := 0xfffffc008a286fffff8001c300
def v1356 : W := 0xfffffc008a296fffff80000000
def v1357 : W := 0xfffffc008a48afffff8001c400
def v1358 : W := 0xfffffc008a68efffff8000000c
def v1359 : W := 0xfffffc008acaafffff80000000
def v1360 : W := 0xfffffc008aebefffff800000fc
def v1361 : W := 0xfffffc008f082fffff8001c000
def v1362 : W := 0xfffffc008f397fffff8001c300
def v1363 : W := 0xfffffc008fcaafffff8001fc00
def v1364 : W := 0xfffffc08c2183fffff83800300
def v1365 : W := 0xfffffc08c2193fffff80000000
def v1366 : W := 0xfffffc09e21d3fffff800e00f3
def v1367 : W := 0xfffffc1282082fffff80000000
def v1368 : W := 0xfffffc1282082fffff83f00000
def v1369 : W := 0xfffffc1282286fffff8070000c
def v1370 : W := 0xfffffc1282286fffff83800300
def v1371 : W := 0xfffffc1282296fffff80000000
def v1372 : W := 0xfffffc128a286fffff80000000
def v1373 : W := 0xfffffc128a296fffff80000000
def v1374 : W := 0xfffffc128f397fffff8001c300
def v1375 : W := 0xfffffc13a20c2fffff80700000
def v1376 : W := 0xfffffc13a22d6fffff807000fc
def v1377 : W := 0xfffffc1ac2082fffff83800000
def v1378 : W := 0xfffffc1ac2397fffff83800300
def v1379 : W := 0xfffffc1aca397fffff83800300
def v1380 : W := 0xfffffc1acf397fffff8381c300
def v1381 : W := 0xfffffc1be20c2fffff83fe0000
def v1382 : W := 0xfffffc4482082fffff8c700000
def v1383 : W := 0xfffffc448248afffff8070000c
def v1384 : W := 0xfffffc448248afffff8c000400
def v1385 : W := 0xfffffc448a48afffff80000000
def v1386 : W := 0xfffffc5682082fffff80700000
def v1387 : W := 0xfffffc568a68efffff8070000c
def v1388 : W := 0xfffffc568a69efffff8070000c
def v1389 : W := 0xfffffca092082fffff8381c300
def v1390 : W := 0xfffffca092082fffff8c01c400
def v1391 : W := 0xfffffca092082fffff8f800000
def v1392 : W := 0xfffffca09a082fffff8001c000
def v1393 : W := 0xfffffcb292082fffff83800000
def v1394 : W := 0xfffffcb29a286fffff8381c300
def v1395 : W := 0xfffffcb29a296fffff8381c300
def v1396 : W := 0xfffffcb29f397fffff8381c300
def v1397 : W := 0xfffffcbada397fffff8381c300
def v1398 : W := 0xfffffce492082fffff8c000000
def v1399 : W := 0xfffffce49a48afffff8c01c400
def v1400 : W := 0xfffffcf692082fffff8ff00000
def v1401 : W := 0xfffffcf69a286fffff8ff1c300
def v1402 : W := 0xfffffcf69a48afffff8ff1c400
def v1403 : W := 0xfffffcf69a68efffff83f1c30c
def v1404 : W := 0xfffffcf69a68efffff8c71c40c
def v1405 : W := 0xfffffcf69a68efffff8f81c700
def v1406 : W := 0xfffffcf69a68efffff8ff0000c
def v1407 : W := 0xfffffd00828a2fffff80000000
def v1408 : W := 0xfffffd01a20c2fffff80000000
def v1409 : W := 0xfffffd01a28e2ffffff00e38f3
def v1410 : W := 0xfffffd01a28f2fffff800000f0
def v1411 : W := 0xfffffd4482082fffff80000000
def v1412 : W := 0xfffffd4482caafffff80000000
def v1413 : W := 0xfffffd4482caaffffffc003c00
def v1414 : W := 0xfffffd448acaafffff80000000
def v1415 : W := 0xfffffd45a20c2fffff80700000
def v1416 : W := 0xfffffd45a20c2ffffffc7e0000
def v1417 : W := 0xfffffd45a2ceafffff807000fc
def v1418 : W := 0xfffffd568aeaefffff8070000c
def v1419 : W := 0xfffffd568aebefffff80000000
def v1420 : W := 0xfffffd57a20c2fffff80700000
def v1421 : W := 0xfffffd57aa2d6fffff80700000
def v1422 : W := 0xfffffd57aa6cefffff8070000c
def v1423 : W := 0xfffffd57aaceafffff80700000
def v1424 : W := 0xfffffd57aaefefffff807000fc
def v1425 : W := 0xfffffde49acaafffff8c01c400
def v1426 : W := 0xfffffdf7b20c2fffff8ff00000
def v1427 : W := 0xfffffe0087082fffff80000000
def v1428 : W := 0xfffffe08c2082fffff80000000
def v1429 : W := 0xfffffe08c7183fffff80000000
def v1430 : W := 0xfffffe08c7183ffffff00e3803
def v1431 : W := 0xfffffe08c7193fffff80000000
def v1432 : W := 0xfffffe08cf397fffff8001c300
def v1433 : W := 0xfffffe1ac7397fffff83800300
def v1434 : W := 0xfffffe1acf397fffff80000000
def v1435 : W := 0xfffffea092082fffff80000000
def v1436 : W := 0xfffffea097082fffff8001c000
def v1437 : W := 0xfffffea097082ffffffc01fc00
def v1438 : W := 0xfffffea09f082fffff8001c000
def v1439 : W := 0xfffffea09f397fffff8001c300
def v1440 : W := 0xfffffea8d2082fffff83800000
def v1441 : W := 0xfffffea8d2082fffffff8e0000
def v1442 : W := 0xfffffea8d7183fffff8381c300
def v1443 : W := 0xfffffea8d7193fffff8381c300
def v1444 : W := 0xfffffea8df183fffff8381c300
def v1445 : W := 0xfffffea8df193fffff8001c000
def v1446 : W := 0xfffffea8df397fffff8381c300
def v1447 : W := 0xfffffeb29f286fffff8381c300
def v1448 : W := 0xfffffeb29f296fffff8001c000
def v1449 : W := 0xfffffebad2082fffff83800000
def v1450 : W := 0xfffffebad2397fffff83800300
def v1451 : W := 0xfffffebad7183fffff8381c300
def v1452 : W := 0xfffffebad7193fffff83800000
def v1453 : W := 0xfffffebad7397fffff8381c300
def v1454 : W := 0xfffffebada286fffff8381c300
def v1455 : W := 0xfffffebada296fffff83800000
def v1456 : W := 0xfffffebadf082fffff8381c000
def v1457 : W := 0xfffffebadf387fffff8381c300
def v1458 : W := 0xfffffebadf3971c3980381c300
def v1459 : W := 0xfffffebadf3971fb9f0381c300
def v1460 : W := 0xfffffebadf397fc3f80381c300
def v1461 : W := 0xfffffebadf397fffff8381c300
def v1462 : W := 0xfffffee49f48afffff8c01c400
def v1463 : W := 0xfffffefed2082fffff8ff00000
def v1464 : W := 0xfffffefedf397fffff8ff1c300
def v1465 : W := 0xfffffefedf79ffffff83f1c30c
def v1466 : W := 0xfffffefedf79ffffff8f81c700
def v1467 : W := 0xffffff00878a2ffffff0003800
def v1468 : W := 0xffffff09e20c2ffffff00e0000
def v1469 : W := 0xffffff09e79f3ffffff00e38f3
def v1470 : W := 0xffffff5feffffffffff07e38ff
def v1471 : W := 0xffffffbbffbf7ffffff38ffbf3
def v1472 : W := 0xffffffe492082ffffffc000000
def v1473 : W := 0xffffffe49fcaafffff8001c000
def v1474 : W := 0xffffffe49fcaaffffffc01fc00
def v1475 : W := 0xffffffedffdfbffffffc0ffcf3
def v1476 : W := 0xfffffff7bfefeffffffc71fcfc
def v1477 : W := 0xfffffffedffbf1c3980381c300
def v1478 : W := 0xfffffffedffbffc3f87f81ff00
def v1479 : W := 0xfffffffedffbffffff8381c300
def v1480 : W := 0xfffffffedffbffffffff81ff00
def v1481 : W := 0xfffffffff20c2ffc077ffe0000
def v1482 : W := 0xfffffffff20c2fffff83f00000
def v1483 : W := 0xfffffffff20c2ffffffffe0000
def v1484 : W := 0xfffffffff79f3ffffffffe38f3
def v1485 : W := 0xfffffffffaefeffffffffe00fc
def v1486 : W := 0xffffffffff3d7fffff83f1c300
def v1487 : W := 0xffffffffff3d7fffffffffc300
def v1488 : W := 0xffffffffffceaffffffffffc00
def v1489 : W := 0xfffffffffffff1fb9f03f1c3fc
def v1490 : W := 0xfffffffffffff1fb9f73fffbff
def v1491 : W := 0xfffffffffffffe3be77c7ffcff
def v1492 : W := 0xffffffffffffffc3f87f8ffff3
def v1493 : W := 0xfffffffffffffffc077ffe38ff
def v1494 : W := 0xffffffffffffffffff83f1c3fc

def ins : List W := [v359, v474, v705, v1013, v1194, v1348]
theorem sampled : ∀ j : Fin 104, Nat.testBit 0xfeeaeeeafce8ece0 (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
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
def level3 : BinaryTree (List W) := (.node [v474, v847, v898, v1013] (.node [v359, v779, v847, v1013] (.node [v359, v424, v474, v1013] (.node [v268, v359, v474, v847] .nil .nil) (.node [v359, v474, v501, v1194] .nil .nil)) (.node [v359, v1013, v1075, v1194] (.node [v359, v806, v847, v1194] .nil .nil) (.node [v474, v847, v889, v1194] .nil .nil))) (.node [v594, v847, v1013, v1194] (.node [v474, v847, v1098, v1282] (.node [v474, v847, v1093, v1337] .nil .nil) (.node [v474, v847, v1114, v1263] .nil .nil)) (.node [v618, v856, v1112, v1194] (.node [v618, v856, v1013, v1280] .nil .nil) .nil)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level3_ok : everyKey (rowOK 2 level2) level3 = true := by decide +kernel
theorem closed3 : Closed 3 level3 := closed_next 2 (by decide) level3 level2 closed2 level3_ok
def level4llll : BinaryTree (List W) := (.node [v60, v594, v705, v1013, v1194] (.node [v47, v359, v887, v1013, v1194] (.node [v47, v359, v474, v548, v1013] (.node [v31, v474, v810, v1013, v1194] (.node [v16, v474, v810, v1013, v1194] .nil .nil) (.node [v47, v268, v359, v474, v705] .nil .nil)) (.node [v47, v359, v705, v779, v1013] (.node [v47, v359, v474, v591, v1194] .nil .nil) (.node [v47, v359, v705, v806, v1194] .nil .nil))) (.node [v47, v594, v705, v1013, v1194] (.node [v47, v474, v705, v898, v1013] (.node [v47, v474, v705, v889, v1194] .nil .nil) (.node [v47, v474, v810, v1013, v1194] .nil .nil)) (.node [v47, v614, v847, v1013, v1194] (.node [v47, v614, v705, v1110, v1194] .nil .nil) .nil))) (.node [v118, v474, v705, v889, v1348] (.node [v106, v474, v847, v892, v1013] (.node [v71, v474, v705, v889, v1194] (.node [v66, v474, v810, v1013, v1194] .nil .nil) (.node [v76, v474, v705, v898, v1013] .nil .nil)) (.node [v111, v359, v887, v1013, v1348] (.node [v110, v359, v705, v806, v1348] .nil .nil) (.node [v115, v474, v810, v1013, v1348] .nil .nil))) (.node [v138, v359, v474, v847, v1013] (.node [v137, v359, v410, v474, v1013] (.node [v122, v359, v755, v847, v1013] .nil .nil) (.node [v138, v345, v474, v856, v1013] .nil .nil)) (.node [v140, v359, v474, v847, v1013] (.node [v138, v474, v810, v1013, v1348] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llll_ok : everyKey (rowOK 3 level3) level4llll = true := by decide +kernel
def level4lllr : BinaryTree (List W) := (.node [v206, v474, v847, v1013, v1194] (.node [v168, v359, v474, v705, v1013] (.node [v150, v359, v474, v847, v1013] (.node [v149, v359, v474, v847, v1013] (.node [v142, v245, v359, v474, v847] .nil .nil) (.node [v149, v474, v705, v889, v1348] .nil .nil)) (.node [v162, v359, v474, v847, v1013] (.node [v150, v359, v705, v806, v1348] .nil .nil) (.node [v167, v359, v474, v705, v1013] .nil .nil))) (.node [v199, v474, v847, v1013, v1194] (.node [v192, v474, v847, v1013, v1194] (.node [v175, v619, v847, v1013, v1194] .nil .nil) (.node [v198, v359, v887, v1194, v1348] .nil .nil)) (.node [v205, v474, v847, v1013, v1194] (.node [v202, v474, v847, v865, v1194] .nil .nil) .nil))) (.node [v255, v359, v415, v474, v1194] (.node [v243, v359, v887, v1194, v1348] (.node [v228, v359, v1013, v1194, v1489] (.node [v223, v359, v746, v847, v1194] .nil .nil) (.node [v243, v359, v474, v847, v1194] .nil .nil)) (.node [v249, v359, v705, v779, v1348] (.node [v249, v359, v474, v847, v1194] .nil .nil) .nil)) (.node [v266, v359, v474, v705, v1194] (.node [v265, v359, v474, v705, v1194] (.node [v261, v359, v474, v847, v1194] .nil .nil) (.node [v266, v359, v474, v705, v964] .nil .nil)) (.node [v268, v325, v359, v474, v705] (.node [v266, v359, v474, v705, v1227] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lllr_ok : everyKey (rowOK 3 level3) level4lllr = true := by decide +kernel
def level4lll : BinaryTree (List W) := .node [v140, v359, v887, v1013, v1348] level4llll level4lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lll_ok : everyKey (rowOK 3 level3) level4lll = true := by
  change (_ && everyKey (rowOK 3 level3) level4llll && everyKey (rowOK 3 level3) level4lllr) = true
  rw [level4llll_ok, level4lllr_ok]
  decide +kernel
def level4llrl : BinaryTree (List W) := (.node [v325, v359, v474, v548, v1013] (.node [v304, v437, v847, v1013, v1194] (.node [v276, v474, v847, v1114, v1194] (.node [v268, v359, v474, v705, v1461] (.node [v268, v359, v474, v705, v1348] .nil .nil) (.node [v269, v359, v474, v705, v1348] .nil .nil)) (.node [v292, v474, v655, v1013, v1194] (.node [v288, v474, v810, v1013, v1194] .nil .nil) (.node [v292, v474, v809, v1013, v1194] .nil .nil))) (.node [v313, v474, v847, v1013, v1282] (.node [v308, v474, v847, v1013, v1194] (.node [v307, v474, v847, v1013, v1194] .nil .nil) (.node [v313, v474, v705, v1013, v1275] .nil .nil)) (.node [v324, v474, v847, v1013, v1194] (.node [v322, v474, v847, v1013, v1194] .nil .nil) .nil))) (.node [v325, v474, v705, v1098, v1282] (.node [v325, v359, v887, v1013, v1194] (.node [v325, v359, v705, v779, v1013] (.node [v325, v359, v474, v591, v1194] .nil .nil) (.node [v325, v359, v705, v806, v1194] .nil .nil)) (.node [v325, v474, v705, v898, v1013] (.node [v325, v474, v705, v889, v1194] .nil .nil) (.node [v325, v474, v705, v1093, v1337] .nil .nil))) (.node [v345, v441, v856, v1013, v1194] (.node [v325, v474, v810, v1013, v1194] (.node [v325, v474, v705, v1114, v1263] .nil .nil) (.node [v325, v594, v705, v1013, v1194] .nil .nil)) (.node [v345, v474, v705, v787, v1013] (.node [v345, v474, v655, v1013, v1194] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llrl_ok : everyKey (rowOK 3 level3) level4llrl = true := by decide +kernel
def level4llrr : BinaryTree (List W) := (.node [v347, v474, v847, v1013, v1194] (.node [v345, v474, v841, v1013, v1194] (.node [v345, v474, v708, v1013, v1194] (.node [v345, v474, v705, v1013, v1183] (.node [v345, v474, v705, v1013, v1084] .nil .nil) (.node [v345, v474, v705, v1098, v1194] .nil .nil)) (.node [v345, v474, v742, v1013, v1194] (.node [v345, v474, v732, v1013, v1194] .nil .nil) (.node [v345, v474, v828, v856, v1013] .nil .nil))) (.node [v345, v474, v856, v1013, v1280] (.node [v345, v474, v856, v895, v1013] (.node [v345, v474, v856, v871, v1194] .nil .nil) (.node [v345, v474, v856, v1013, v1194] .nil .nil)) (.node [v345, v618, v856, v1013, v1194] (.node [v345, v474, v856, v1112, v1194] .nil .nil) .nil))) (.node [v357, v887, v1013, v1194, v1348] (.node [v355, v474, v705, v1013, v1177] (.node [v348, v705, v806, v1194, v1348] (.node [v348, v474, v847, v1013, v1194] .nil .nil) (.node [v354, v474, v705, v1013, v1194] .nil .nil)) (.node [v357, v474, v847, v1013, v1194] (.node [v355, v474, v847, v1013, v1194] .nil .nil) .nil)) (.node [v359, v396, v474, v509, v1194] (.node [v359, v374, v474, v517, v1013] (.node [v358, v474, v847, v1013, v1194] .nil .nil) (.node [v359, v386, v705, v1013, v1194] .nil .nil)) (.node [v359, v406, v474, v705, v1348] (.node [v359, v403, v950, v1013, v1194] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llrr_ok : everyKey (rowOK 3 level3) level4llrr = true := by decide +kernel
def level4llr : BinaryTree (List W) := .node [v345, v474, v705, v828, v1013] level4llrl level4llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llr_ok : everyKey (rowOK 3 level3) level4llr = true := by
  change (_ && everyKey (rowOK 3 level3) level4llrl && everyKey (rowOK 3 level3) level4llrr) = true
  rw [level4llrl_ok, level4llrr_ok]
  decide +kernel
def level4ll : BinaryTree (List W) := .node [v268, v359, v474, v525, v705] level4lll level4llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4ll_ok : everyKey (rowOK 3 level3) level4ll = true := by
  change (_ && everyKey (rowOK 3 level3) level4lll && everyKey (rowOK 3 level3) level4llr) = true
  rw [level4lll_ok, level4llr_ok]
  decide +kernel
def level4lrll : BinaryTree (List W) := (.node [v359, v460, v705, v958, v1348] (.node [v359, v443, v847, v1013, v1194] (.node [v359, v441, v847, v1013, v1194] (.node [v359, v428, v794, v1013, v1194] (.node [v359, v419, v847, v1138, v1194] .nil .nil) (.node [v359, v440, v705, v1129, v1348] .nil .nil)) (.node [v359, v443, v847, v873, v1194] (.node [v359, v443, v819, v1013, v1194] .nil .nil) (.node [v359, v443, v847, v896, v1013] .nil .nil))) (.node [v359, v448, v847, v1013, v1315] (.node [v359, v443, v847, v1110, v1194] (.node [v359, v443, v847, v1013, v1278] .nil .nil) (.node [v359, v446, v847, v1013, v1194] .nil .nil)) (.node [v359, v458, v705, v979, v1348] (.node [v359, v456, v705, v979, v1348] .nil .nil) .nil))) (.node [v359, v474, v539, v1013, v1249] (.node [v359, v474, v525, v548, v1013] (.node [v359, v472, v847, v1013, v1194] (.node [v359, v461, v847, v1013, v1194] .nil .nil) (.node [v359, v474, v492, v705, v1013] .nil .nil)) (.node [v359, v474, v539, v672, v1013] (.node [v359, v474, v525, v591, v1194] .nil .nil) (.node [v359, v474, v539, v1013, v1194] .nil .nil))) (.node [v359, v474, v548, v1013, v1348] (.node [v359, v474, v548, v970, v1348] (.node [v359, v474, v548, v551, v1013] .nil .nil) (.node [v359, v474, v548, v1013, v1246] .nil .nil)) (.node [v359, v474, v548, v1013, v1449] (.node [v359, v474, v548, v1013, v1362] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrll_ok : everyKey (rowOK 3 level3) level4lrll = true := by decide +kernel
def level4lrlr : BinaryTree (List W) := (.node [v359, v474, v592, v1194, v1348] (.node [v359, v474, v591, v1194, v1348] (.node [v359, v474, v591, v637, v1348] (.node [v359, v474, v564, v1013, v1194] (.node [v359, v474, v548, v1034, v1348] .nil .nil) (.node [v359, v474, v591, v599, v1194] .nil .nil)) (.node [v359, v474, v591, v1050, v1348] (.node [v359, v474, v591, v736, v1348] .nil .nil) (.node [v359, v474, v591, v1060, v1194] .nil .nil))) (.node [v359, v474, v591, v1225, v1348] (.node [v359, v474, v591, v1194, v1438] (.node [v359, v474, v591, v1194, v1378] .nil .nil) (.node [v359, v474, v591, v1194, v1461] .nil .nil)) (.node [v359, v474, v591, v1251, v1348] (.node [v359, v474, v591, v1245, v1348] .nil .nil) .nil))) (.node [v359, v474, v705, v899, v1013] (.node [v359, v474, v675, v705, v1013] (.node [v359, v474, v655, v1013, v1194] (.node [v359, v474, v638, v705, v1194] .nil .nil) (.node [v359, v474, v672, v847, v1013] .nil .nil)) (.node [v359, v474, v705, v890, v1194] (.node [v359, v474, v696, v1013, v1194] .nil .nil) .nil)) (.node [v359, v474, v705, v994, v1194] (.node [v359, v474, v705, v970, v1420] (.node [v359, v474, v705, v965, v1348] .nil .nil) (.node [v359, v474, v705, v979, v1420] .nil .nil)) (.node [v359, v474, v705, v1013, v1169] (.node [v359, v474, v705, v1013, v1145] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrlr_ok : everyKey (rowOK 3 level3) level4lrlr = true := by decide +kernel
def level4lrl : BinaryTree (List W) := .node [v359, v474, v548, v1013, v1461] level4lrll level4lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrl_ok : everyKey (rowOK 3 level3) level4lrl = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrll && everyKey (rowOK 3 level3) level4lrlr) = true
  rw [level4lrll_ok, level4lrlr_ok]
  decide +kernel
def level4lrrl : BinaryTree (List W) := (.node [v359, v474, v812, v1110, v1194] (.node [v359, v474, v736, v847, v1013] (.node [v359, v474, v705, v1096, v1348] (.node [v359, v474, v705, v1013, v1277] (.node [v359, v474, v705, v1013, v1274] .nil .nil) (.node [v359, v474, v705, v1090, v1348] .nil .nil)) (.node [v359, v474, v705, v1109, v1194] (.node [v359, v474, v705, v1106, v1194] .nil .nil) (.node [v359, v474, v717, v896, v1013] .nil .nil))) (.node [v359, v474, v787, v847, v1013] (.node [v359, v474, v749, v1194, v1478] (.node [v359, v474, v740, v873, v1194] .nil .nil) (.node [v359, v474, v759, v847, v1013] .nil .nil)) (.node [v359, v474, v811, v1013, v1194] (.node [v359, v474, v802, v1159, v1194] .nil .nil) .nil))) (.node [v359, v474, v828, v847, v1013] (.node [v359, v474, v825, v1013, v1330] (.node [v359, v474, v819, v1110, v1194] (.node [v359, v474, v819, v1013, v1278] .nil .nil) (.node [v359, v474, v822, v1013, v1194] .nil .nil)) (.node [v359, v474, v827, v847, v1013] (.node [v359, v474, v826, v847, v1013] .nil .nil) .nil)) (.node [v359, v474, v840, v1013, v1278] (.node [v359, v474, v835, v1013, v1327] (.node [v359, v474, v832, v847, v1013] .nil .nil) (.node [v359, v474, v838, v1013, v1194] .nil .nil)) (.node [v359, v474, v847, v871, v1194] (.node [v359, v474, v847, v870, v1194] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrrl_ok : everyKey (rowOK 3 level3) level4lrrl = true := by decide +kernel
def level4lrrr : BinaryTree (List W) := (.node [v359, v474, v847, v955, v1013] (.node [v359, v474, v847, v896, v1013] (.node [v359, v474, v847, v880, v1194] (.node [v359, v474, v847, v873, v1278] (.node [v359, v474, v847, v873, v1194] .nil .nil) (.node [v359, v474, v847, v877, v1194] .nil .nil)) (.node [v359, v474, v847, v885, v1194] (.node [v359, v474, v847, v881, v1194] .nil .nil) (.node [v359, v474, v847, v895, v1013] .nil .nil))) (.node [v359, v474, v847, v932, v1013] (.node [v359, v474, v847, v920, v1013] (.node [v359, v474, v847, v896, v1110] .nil .nil) (.node [v359, v474, v847, v922, v1013] .nil .nil)) (.node [v359, v474, v847, v951, v1013] (.node [v359, v474, v847, v942, v1013] .nil .nil) .nil))) (.node [v359, v474, v847, v979, v1194] (.node [v359, v474, v847, v967, v1194] (.node [v359, v474, v847, v961, v1013] (.node [v359, v474, v847, v958, v1337] .nil .nil) (.node [v359, v474, v847, v964, v1013] .nil .nil)) (.node [v359, v474, v847, v976, v1194] (.node [v359, v474, v847, v970, v1194] .nil .nil) .nil)) (.node [v359, v474, v847, v1009, v1194] (.node [v359, v474, v847, v984, v1194] (.node [v359, v474, v847, v982, v1194] .nil .nil) (.node [v359, v474, v847, v987, v1194] .nil .nil)) (.node [v359, v474, v847, v1013, v1073] (.node [v359, v474, v847, v1013, v1050] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrrr_ok : everyKey (rowOK 3 level3) level4lrrr = true := by decide +kernel
def level4lrr : BinaryTree (List W) := .node [v359, v474, v847, v873, v896] level4lrrl level4lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrr_ok : everyKey (rowOK 3 level3) level4lrr = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrrl && everyKey (rowOK 3 level3) level4lrrr) = true
  rw [level4lrrl_ok, level4lrrr_ok]
  decide +kernel
def level4lr : BinaryTree (List W) := .node [v359, v474, v705, v1013, v1248] level4lrl level4lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lr_ok : everyKey (rowOK 3 level3) level4lr = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrl && everyKey (rowOK 3 level3) level4lrr) = true
  rw [level4lrl_ok, level4lrr_ok]
  decide +kernel
def level4l : BinaryTree (List W) := .node [v359, v416, v768, v1013, v1194] level4ll level4lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4l_ok : everyKey (rowOK 3 level3) level4l = true := by
  change (_ && everyKey (rowOK 3 level3) level4ll && everyKey (rowOK 3 level3) level4lr) = true
  rw [level4ll_ok, level4lr_ok]
  decide +kernel
def level4rlll : BinaryTree (List W) := (.node [v359, v474, v847, v1013, v1237] (.node [v359, v474, v847, v1013, v1194] (.node [v359, v474, v847, v1013, v1139] (.node [v359, v474, v847, v1013, v1118] (.node [v359, v474, v847, v1013, v1087] .nil .nil) (.node [v359, v474, v847, v1013, v1129] .nil .nil)) (.node [v359, v474, v847, v1013, v1161] (.node [v359, v474, v847, v1013, v1142] .nil .nil) (.node [v359, v474, v847, v1013, v1189] .nil .nil))) (.node [v359, v474, v847, v1013, v1227] (.node [v359, v474, v847, v1013, v1216] (.node [v359, v474, v847, v1013, v1209] .nil .nil) (.node [v359, v474, v847, v1013, v1225] .nil .nil)) (.node [v359, v474, v847, v1013, v1235] (.node [v359, v474, v847, v1013, v1228] .nil .nil) .nil))) (.node [v359, v474, v847, v1013, v1266] (.node [v359, v474, v847, v1013, v1255] (.node [v359, v474, v847, v1013, v1245] (.node [v359, v474, v847, v1013, v1241] .nil .nil) (.node [v359, v474, v847, v1013, v1249] .nil .nil)) (.node [v359, v474, v847, v1013, v1260] (.node [v359, v474, v847, v1013, v1258] .nil .nil) (.node [v359, v474, v847, v1013, v1263] .nil .nil))) (.node [v359, v474, v847, v1013, v1295] (.node [v359, v474, v847, v1013, v1278] (.node [v359, v474, v847, v1013, v1268] .nil .nil) (.node [v359, v474, v847, v1013, v1280] .nil .nil)) (.node [v359, v474, v847, v1013, v1301] (.node [v359, v474, v847, v1013, v1296] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlll_ok : everyKey (rowOK 3 level3) level4rlll = true := by decide +kernel
def level4rllr : BinaryTree (List W) := (.node [v359, v474, v847, v1112, v1194] (.node [v359, v474, v847, v1070, v1194] (.node [v359, v474, v847, v1037, v1194] (.node [v359, v474, v847, v1028, v1194] (.node [v359, v474, v847, v1013, v1311] .nil .nil) (.node [v359, v474, v847, v1034, v1194] .nil .nil)) (.node [v359, v474, v847, v1062, v1194] (.node [v359, v474, v847, v1044, v1194] .nil .nil) (.node [v359, v474, v847, v1067, v1194] .nil .nil))) (.node [v359, v474, v847, v1098, v1194] (.node [v359, v474, v847, v1081, v1194] (.node [v359, v474, v847, v1079, v1194] .nil .nil) (.node [v359, v474, v847, v1097, v1194] .nil .nil)) (.node [v359, v474, v847, v1110, v1278] (.node [v359, v474, v847, v1110, v1194] .nil .nil) .nil))) (.node [v359, v474, v859, v1013, v1194] (.node [v359, v474, v849, v1013, v1194] (.node [v359, v474, v847, v1137, v1194] (.node [v359, v474, v847, v1127, v1194] .nil .nil) (.node [v359, v474, v848, v1013, v1194] .nil .nil)) (.node [v359, v474, v855, v1013, v1194] (.node [v359, v474, v854, v1013, v1194] .nil .nil) .nil)) (.node [v359, v474, v1013, v1194, v1458] (.node [v359, v474, v941, v1084, v1348] (.node [v359, v474, v941, v1050, v1348] .nil .nil) (.node [v359, v474, v941, v1129, v1348] .nil .nil)) (.node [v359, v475, v705, v1013, v1194] (.node [v359, v474, v1013, v1194, v1477] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rllr_ok : everyKey (rowOK 3 level3) level4rllr = true := by decide +kernel
def level4rll : BinaryTree (List W) := .node [v359, v474, v847, v1013, v1305] level4rlll level4rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rll_ok : everyKey (rowOK 3 level3) level4rll = true := by
  change (_ && everyKey (rowOK 3 level3) level4rlll && everyKey (rowOK 3 level3) level4rllr) = true
  rw [level4rlll_ok, level4rllr_ok]
  decide +kernel
def level4rlrl : BinaryTree (List W) := (.node [v359, v587, v705, v1110, v1194] (.node [v359, v575, v705, v1110, v1194] (.node [v359, v525, v705, v779, v1013] (.node [v359, v499, v847, v1013, v1194] (.node [v359, v498, v847, v1013, v1194] .nil .nil) (.node [v359, v504, v847, v1013, v1194] .nil .nil)) (.node [v359, v525, v887, v1013, v1194] (.node [v359, v525, v705, v806, v1194] .nil .nil) (.node [v359, v570, v705, v1138, v1194] .nil .nil))) (.node [v359, v587, v705, v1013, v1249] (.node [v359, v584, v887, v1013, v1194] (.node [v359, v575, v847, v1013, v1194] .nil .nil) (.node [v359, v587, v705, v1013, v1235] .nil .nil)) (.node [v359, v587, v705, v1062, v1194] (.node [v359, v587, v705, v1013, v1278] .nil .nil) .nil))) (.node [v359, v614, v656, v1110, v1194] (.node [v359, v605, v705, v1013, v1278] (.node [v359, v593, v705, v1013, v1194] (.node [v359, v587, v847, v1013, v1194] .nil .nil) (.node [v359, v602, v705, v1013, v1315] .nil .nil)) (.node [v359, v614, v656, v1013, v1278] (.node [v359, v605, v847, v1013, v1194] .nil .nil) .nil)) (.node [v359, v614, v705, v1013, v1216] (.node [v359, v614, v705, v896, v1110] (.node [v359, v614, v705, v873, v1278] .nil .nil) (.node [v359, v614, v705, v1013, v1209] .nil .nil)) (.node [v359, v614, v705, v1013, v1235] (.node [v359, v614, v705, v1013, v1227] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlrl_ok : everyKey (rowOK 3 level3) level4rlrl = true := by decide +kernel
def level4rlrr : BinaryTree (List W) := (.node [v359, v614, v847, v1013, v1278] (.node [v359, v614, v705, v1110, v1278] (.node [v359, v614, v705, v1028, v1194] (.node [v359, v614, v705, v1013, v1311] (.node [v359, v614, v705, v1013, v1278] .nil .nil) (.node [v359, v614, v705, v1013, v1481] .nil .nil)) (.node [v359, v614, v705, v1062, v1194] (.node [v359, v614, v705, v1044, v1194] .nil .nil) (.node [v359, v614, v705, v1110, v1194] .nil .nil))) (.node [v359, v614, v847, v873, v1194] (.node [v359, v614, v730, v1013, v1194] (.node [v359, v614, v717, v1013, v1194] .nil .nil) (.node [v359, v614, v740, v1013, v1194] .nil .nil)) (.node [v359, v614, v847, v1013, v1194] (.node [v359, v614, v847, v896, v1013] .nil .nil) .nil))) (.node [v359, v705, v764, v1013, v1194] (.node [v359, v618, v847, v1013, v1194] (.node [v359, v618, v705, v1013, v1280] (.node [v359, v614, v847, v1110, v1194] .nil .nil) (.node [v359, v618, v705, v1112, v1194] .nil .nil)) (.node [v359, v705, v759, v764, v1013] (.node [v359, v680, v806, v1194, v1348] .nil .nil) .nil)) (.node [v359, v705, v779, v979, v1348] (.node [v359, v705, v774, v1013, v1194] (.node [v359, v705, v764, v1013, v1311] .nil .nil) (.node [v359, v705, v779, v780, v1013] .nil .nil)) (.node [v359, v705, v779, v1013, v1420] (.node [v359, v705, v779, v1013, v1348] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlrr_ok : everyKey (rowOK 3 level3) level4rlrr = true := by decide +kernel
def level4rlr : BinaryTree (List W) := .node [v359, v614, v705, v1013, v1249] level4rlrl level4rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlr_ok : everyKey (rowOK 3 level3) level4rlr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rlrl && everyKey (rowOK 3 level3) level4rlrr) = true
  rw [level4rlrl_ok, level4rlrr_ok]
  decide +kernel
def level4rl : BinaryTree (List W) := .node [v359, v489, v847, v1013, v1194] level4rll level4rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rl_ok : everyKey (rowOK 3 level3) level4rl = true := by
  change (_ && everyKey (rowOK 3 level3) level4rll && everyKey (rowOK 3 level3) level4rlr) = true
  rw [level4rll_ok, level4rlr_ok]
  decide +kernel
def level4rrll : BinaryTree (List W) := (.node [v359, v887, v1013, v1087, v1348] (.node [v359, v705, v806, v1301, v1348] (.node [v359, v705, v806, v1129, v1348] (.node [v359, v705, v806, v827, v1348] (.node [v359, v705, v805, v806, v1348] .nil .nil) (.node [v359, v705, v806, v837, v1194] .nil .nil)) (.node [v359, v705, v806, v1194, v1414] (.node [v359, v705, v806, v1194, v1348] .nil .nil) (.node [v359, v705, v806, v1194, v1461] .nil .nil))) (.node [v359, v886, v887, v1013, v1348] (.node [v359, v863, v887, v1194, v1348] (.node [v359, v806, v941, v1194, v1348] .nil .nil) (.node [v359, v877, v887, v1194, v1348] .nil .nil)) (.node [v359, v887, v976, v1194, v1348] (.node [v359, v887, v942, v1013, v1348] .nil .nil) .nil))) (.node [v359, v941, v1132, v1194, v1348] (.node [v359, v887, v1013, v1194, v1442] (.node [v359, v887, v1013, v1194, v1348] (.node [v359, v887, v1013, v1094, v1194] .nil .nil) (.node [v359, v887, v1013, v1194, v1373] .nil .nil)) (.node [v359, v887, v1013, v1295, v1348] (.node [v359, v887, v1013, v1194, v1461] .nil .nil) (.node [v359, v887, v1127, v1194, v1348] .nil .nil))) (.node [v385, v474, v847, v1013, v1194] (.node [v359, v950, v1127, v1295, v1348] (.node [v359, v941, v1138, v1301, v1348] .nil .nil) (.node [v382, v474, v705, v898, v1013] .nil .nil)) (.node [v405, v474, v847, v1013, v1194] (.node [v395, v474, v705, v889, v1194] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrll_ok : everyKey (rowOK 3 level3) level4rrll = true := by decide +kernel
def level4rrlr : BinaryTree (List W) := (.node [v474, v572, v847, v1013, v1194] (.node [v474, v525, v705, v889, v1194] (.node [v405, v950, v1127, v1194, v1348] (.node [v405, v950, v1013, v1194, v1461] (.node [v405, v950, v1013, v1194, v1373] .nil .nil) (.node [v405, v950, v1013, v1295, v1348] .nil .nil)) (.node [v443, v705, v914, v1013, v1194] (.node [v434, v474, v705, v1013, v1194] .nil .nil) (.node [v472, v810, v1013, v1194, v1348] .nil .nil))) (.node [v474, v563, v856, v1013, v1194] (.node [v474, v525, v810, v1013, v1194] (.node [v474, v525, v705, v898, v1013] .nil .nil) (.node [v474, v562, v810, v1013, v1194] .nil .nil)) (.node [v474, v568, v847, v1013, v1194] (.node [v474, v565, v847, v1013, v1194] .nil .nil) .nil))) (.node [v474, v705, v873, v914, v1194] (.node [v474, v655, v856, v1013, v1194] (.node [v474, v615, v856, v1013, v1194] (.node [v474, v572, v1013, v1194, v1458] .nil .nil) (.node [v474, v616, v847, v1013, v1194] .nil .nil)) (.node [v474, v705, v836, v1098, v1348] (.node [v474, v656, v914, v1013, v1194] .nil .nil) .nil)) (.node [v474, v705, v889, v1084, v1348] (.node [v474, v705, v888, v889, v1348] (.node [v474, v705, v881, v898, v1348] .nil .nil) (.node [v474, v705, v889, v951, v1348] .nil .nil)) (.node [v474, v705, v889, v1194, v1348] (.node [v474, v705, v889, v1101, v1194] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrlr_ok : everyKey (rowOK 3 level3) level4rrlr = true := by decide +kernel
def level4rrl : BinaryTree (List W) := .node [v405, v887, v1013, v1194, v1348] level4rrll level4rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrl_ok : everyKey (rowOK 3 level3) level4rrl = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrll && everyKey (rowOK 3 level3) level4rrlr) = true
  rw [level4rrll_ok, level4rrlr_ok]
  decide +kernel
def level4rrrl : BinaryTree (List W) := (.node [v474, v810, v828, v1013, v1348] (.node [v474, v705, v898, v1098, v1348] (.node [v474, v705, v898, v1013, v1271] (.node [v474, v705, v889, v1263, v1348] (.node [v474, v705, v889, v1194, v1461] .nil .nil) (.node [v474, v705, v896, v914, v1013] .nil .nil)) (.node [v474, v705, v898, v1013, v1400] (.node [v474, v705, v898, v1013, v1348] .nil .nil) (.node [v474, v705, v898, v1013, v1461] .nil .nil))) (.node [v474, v705, v914, v1110, v1194] (.node [v474, v705, v914, v1013, v1194] (.node [v474, v705, v913, v1013, v1194] .nil .nil) (.node [v474, v705, v914, v1013, v1278] .nil .nil)) (.node [v474, v808, v810, v1013, v1194] (.node [v474, v807, v810, v1013, v1348] .nil .nil) .nil))) (.node [v474, v810, v1013, v1194, v1431] (.node [v474, v810, v1013, v1146, v1194] (.node [v474, v810, v984, v1194, v1348] (.node [v474, v810, v842, v1013, v1194] .nil .nil) (.node [v474, v810, v1013, v1139, v1348] .nil .nil)) (.node [v474, v810, v1013, v1194, v1394] (.node [v474, v810, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v474, v847, v900, v1013, v1194] (.node [v474, v810, v1013, v1258, v1348] (.node [v474, v810, v1013, v1194, v1461] .nil .nil) (.node [v474, v810, v1070, v1194, v1348] .nil .nil)) (.node [v474, v847, v914, v1013, v1194] (.node [v474, v847, v908, v1013, v1194] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrrl_ok : everyKey (rowOK 3 level3) level4rrrl = true := by decide +kernel
def level4rrrr : BinaryTree (List W) := (.node [v594, v705, v920, v1013, v1348] (.node [v572, v705, v1138, v1194, v1414] (.node [v499, v856, v1013, v1258, v1348] (.node [v499, v856, v1013, v1194, v1431] (.node [v499, v810, v1013, v1194, v1348] .nil .nil) (.node [v499, v856, v1013, v1194, v1461] .nil .nil)) (.node [v525, v594, v705, v1013, v1194] (.node [v499, v856, v1070, v1194, v1348] .nil .nil) (.node [v572, v705, v806, v1194, v1348] .nil .nil))) (.node [v594, v705, v787, v1013, v1348] (.node [v594, v608, v705, v1013, v1194] (.node [v572, v941, v1138, v1194, v1348] .nil .nil) (.node [v594, v636, v705, v1013, v1348] .nil .nil)) (.node [v594, v705, v870, v1194, v1348] (.node [v594, v705, v792, v1013, v1194] .nil .nil) .nil))) (.node [v594, v705, v1081, v1194, v1348] (.node [v594, v705, v1013, v1268, v1348] (.node [v594, v705, v1013, v1194, v1387] (.node [v594, v705, v1013, v1194, v1348] .nil .nil) (.node [v594, v705, v1013, v1194, v1461] .nil .nil)) (.node [v594, v705, v1013, v1343, v1348] (.node [v594, v705, v1013, v1305, v1348] .nil .nil) .nil)) (.node [v614, v847, v1013, v1194, v1469] (.node [v614, v705, v914, v1013, v1194] (.node [v595, v705, v1013, v1194, v1348] .nil .nil) (.node [v614, v705, v1110, v1194, v1469] .nil .nil)) (.node [v619, v732, v1013, v1194, v1461] (.node [v618, v856, v1013, v1194, v1461] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrrr_ok : everyKey (rowOK 3 level3) level4rrrr = true := by decide +kernel
def level4rrr : BinaryTree (List W) := .node [v474, v847, v1013, v1093, v1194] level4rrrl level4rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrr_ok : everyKey (rowOK 3 level3) level4rrr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrrl && everyKey (rowOK 3 level3) level4rrrr) = true
  rw [level4rrrl_ok, level4rrrr_ok]
  decide +kernel
def level4rr : BinaryTree (List W) := .node [v474, v705, v889, v1194, v1399] level4rrl level4rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rr_ok : everyKey (rowOK 3 level3) level4rr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrl && everyKey (rowOK 3 level3) level4rrr) = true
  rw [level4rrl_ok, level4rrr_ok]
  decide +kernel
def level4r : BinaryTree (List W) := .node [v359, v705, v779, v1013, v1461] level4rl level4rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4r_ok : everyKey (rowOK 3 level3) level4r = true := by
  change (_ && everyKey (rowOK 3 level3) level4rl && everyKey (rowOK 3 level3) level4rr) = true
  rw [level4rl_ok, level4rr_ok]
  decide +kernel
def level4 : BinaryTree (List W) := .node [v359, v474, v847, v1013, v1084] level4l level4r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4_ok : everyKey (rowOK 3 level3) level4 = true := by
  change (_ && everyKey (rowOK 3 level3) level4l && everyKey (rowOK 3 level3) level4r) = true
  rw [level4l_ok, level4r_ok]
  decide +kernel
theorem closed4 : Closed 4 level4 := closed_next 3 (by decide) level4 level3 closed3 level4_ok
def level5llllll : BinaryTree (List W) := (.node [v23, v156, v359, v474, v705, v1013] (.node [v16, v359, v474, v708, v1013, v1194] (.node [v16, v345, v474, v705, v1013, v1194] (.node [v6, v359, v474, v705, v992, v1194] (.node [v2, v359, v474, v705, v1013, v1168] (.node [v0, v359, v474, v847, v1013, v1194] .nil .nil) .nil) (.node [v16, v292, v474, v653, v1013, v1194] .nil .nil)) (.node [v16, v359, v474, v695, v1013, v1194] (.node [v16, v359, v474, v653, v1013, v1194] .nil .nil) (.node [v16, v359, v474, v705, v1013, v1194] .nil .nil))) (.node [v18, v359, v474, v705, v1013, v1194] (.node [v16, v474, v705, v904, v1013, v1194] (.node [v16, v359, v474, v856, v1013, v1194] (.node [v16, v359, v474, v847, v1013, v1194] .nil .nil) .nil) (.node [v17, v359, v477, v705, v1013, v1194] .nil .nil)) (.node [v20, v359, v474, v705, v1013, v1194] (.node [v19, v359, v474, v705, v1013, v1194] .nil .nil) (.node [v21, v256, v359, v474, v705, v1194] .nil .nil)))) (.node [v29, v359, v705, v763, v1013, v1194] (.node [v29, v359, v474, v847, v1013, v1194] (.node [v26, v359, v474, v705, v1013, v1194] (.node [v25, v359, v705, v773, v1013, v1194] (.node [v24, v359, v474, v705, v1013, v1194] .nil .nil) .nil) (.node [v27, v359, v474, v705, v1013, v1194] .nil .nil)) (.node [v29, v359, v608, v705, v1013, v1194] (.node [v29, v359, v477, v705, v1013, v1194] .nil .nil) (.node [v29, v359, v614, v705, v1013, v1194] .nil .nil))) (.node [v30, v359, v474, v705, v1013, v1194] (.node [v29, v359, v705, v773, v1013, v1194] (.node [v29, v359, v705, v764, v1013, v1194] .nil .nil) (.node [v29, v359, v705, v792, v1013, v1194] .nil .nil)) (.node [v33, v359, v474, v708, v1013, v1194] (.node [v32, v359, v466, v705, v1013, v1194] .nil .nil) (.node [v34, v359, v474, v705, v1013, v1194] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llllll_ok : everyKey (rowOK 4 level4) level5llllll = true := by decide +kernel
def level5lllllr : BinaryTree (List W) := (.node [v47, v128, v359, v474, v517, v1013] (.node [v41, v359, v474, v847, v1013, v1194] (.node [v41, v359, v474, v539, v1013, v1194] (.node [v41, v359, v474, v525, v1013, v1194] (.node [v41, v359, v474, v525, v672, v1013] (.node [v35, v359, v474, v705, v1013, v1194] .nil .nil) .nil) (.node [v41, v359, v474, v525, v1013, v1249] .nil .nil)) (.node [v41, v359, v474, v708, v1013, v1194] (.node [v41, v359, v474, v562, v1013, v1194] .nil .nil) (.node [v41, v359, v474, v842, v1013, v1194] .nil .nil))) (.node [v46, v357, v474, v705, v1013, v1194] (.node [v44, v359, v474, v705, v1013, v1202] (.node [v43, v359, v474, v705, v1013, v1194] (.node [v42, v359, v474, v705, v1019, v1194] .nil .nil) .nil) (.node [v45, v359, v474, v705, v1013, v1194] .nil .nil)) (.node [v47, v106, v474, v705, v892, v1013] (.node [v46, v359, v474, v705, v1013, v1194] .nil .nil) (.node [v47, v122, v359, v705, v755, v1013] .nil .nil)))) (.node [v47, v190, v474, v856, v1013, v1194] (.node [v47, v143, v359, v474, v705, v1013] (.node [v47, v140, v359, v474, v705, v1013] (.node [v47, v138, v359, v474, v705, v1013] (.node [v47, v129, v359, v474, v705, v1013] .nil .nil) .nil) (.node [v47, v142, v245, v359, v474, v705] .nil .nil)) (.node [v47, v150, v359, v474, v705, v1013] (.node [v47, v149, v359, v474, v705, v1013] .nil .nil) (.node [v47, v175, v619, v705, v1013, v1194] .nil .nil))) (.node [v47, v234, v359, v474, v509, v1194] (.node [v47, v215, v359, v950, v1013, v1194] (.node [v47, v202, v474, v705, v865, v1194] .nil .nil) (.node [v47, v223, v359, v705, v746, v1194] .nil .nil)) (.node [v47, v249, v359, v474, v705, v1194] (.node [v47, v243, v359, v474, v705, v1194] .nil .nil) (.node [v47, v276, v474, v705, v1114, v1194] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllllr_ok : everyKey (rowOK 4 level4) level5lllllr = true := by decide +kernel
def level5lllll : BinaryTree (List W) := .node [v35, v348, v474, v705, v1013, v1194] level5llllll level5lllllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllll_ok : everyKey (rowOK 4 level4) level5lllll = true := by
  change (_ && everyKey (rowOK 4 level4) level5llllll && everyKey (rowOK 4 level4) level5lllllr) = true
  rw [level5llllll_ok, level5lllllr_ok]
  decide +kernel
def level5llllrl : BinaryTree (List W) := (.node [v47, v348, v474, v705, v1013, v1194] (.node [v47, v325, v474, v705, v1110, v1194] (.node [v47, v325, v474, v705, v873, v1194] (.node [v47, v325, v443, v705, v1013, v1194] (.node [v47, v313, v474, v705, v1013, v1282] (.node [v47, v304, v437, v705, v1013, v1194] .nil .nil) .nil) (.node [v47, v325, v474, v656, v1013, v1194] .nil .nil)) (.node [v47, v325, v474, v705, v1013, v1194] (.node [v47, v325, v474, v705, v896, v1013] .nil .nil) (.node [v47, v325, v474, v705, v1013, v1278] .nil .nil))) (.node [v47, v338, v474, v705, v1013, v1194] (.node [v47, v332, v474, v705, v1013, v1194] (.node [v47, v325, v614, v705, v1013, v1194] (.node [v47, v325, v474, v847, v1013, v1194] .nil .nil) .nil) (.node [v47, v334, v474, v705, v1013, v1194] .nil .nil)) (.node [v47, v344, v474, v705, v1013, v1194] (.node [v47, v339, v474, v705, v1013, v1194] .nil .nil) (.node [v47, v345, v474, v705, v1013, v1194] .nil .nil)))) (.node [v47, v359, v474, v630, v1159, v1194] (.node [v47, v359, v428, v642, v1013, v1194] (.node [v47, v357, v474, v705, v1013, v1194] (.node [v47, v352, v474, v705, v1013, v1194] (.node [v47, v351, v474, v705, v1013, v1194] .nil .nil) .nil) (.node [v47, v359, v419, v705, v1138, v1194] .nil .nil)) (.node [v47, v359, v448, v705, v1013, v1315] (.node [v47, v359, v443, v705, v1013, v1194] .nil .nil) (.node [v47, v359, v472, v705, v1013, v1194] .nil .nil))) (.node [v47, v359, v474, v672, v705, v1013] (.node [v47, v359, v474, v666, v1013, v1327] (.node [v47, v359, v474, v656, v1013, v1194] .nil .nil) (.node [v47, v359, v474, v669, v705, v1013] .nil .nil)) (.node [v47, v359, v474, v705, v736, v1013] (.node [v47, v359, v474, v680, v1013, v1194] .nil .nil) (.node [v47, v359, v474, v705, v757, v1013] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llllrl_ok : everyKey (rowOK 4 level4) level5llllrl = true := by decide +kernel
def level5llllrr : BinaryTree (List W) := (.node [v47, v359, v474, v705, v979, v1194] (.node [v47, v359, v474, v705, v920, v1013] (.node [v47, v359, v474, v705, v873, v1194] (.node [v47, v359, v474, v705, v828, v1013] (.node [v47, v359, v474, v705, v827, v1013] (.node [v47, v359, v474, v705, v787, v1013] .nil .nil) .nil) (.node [v47, v359, v474, v705, v870, v1194] .nil .nil)) (.node [v47, v359, v474, v705, v881, v1194] (.node [v47, v359, v474, v705, v877, v1194] .nil .nil) (.node [v47, v359, v474, v705, v896, v1013] .nil .nil))) (.node [v47, v359, v474, v705, v962, v1013] (.node [v47, v359, v474, v705, v951, v1013] (.node [v47, v359, v474, v705, v942, v1013] .nil .nil) (.node [v47, v359, v474, v705, v958, v1337] .nil .nil)) (.node [v47, v359, v474, v705, v970, v1194] (.node [v47, v359, v474, v705, v964, v1013] .nil .nil) (.node [v47, v359, v474, v705, v976, v1194] .nil .nil)))) (.node [v47, v359, v474, v705, v1013, v1139] (.node [v47, v359, v474, v705, v1013, v1050] (.node [v47, v359, v474, v705, v997, v1194] (.node [v47, v359, v474, v705, v993, v1194] (.node [v47, v359, v474, v705, v984, v1194] .nil .nil) .nil) (.node [v47, v359, v474, v705, v998, v1194] .nil .nil)) (.node [v47, v359, v474, v705, v1013, v1087] (.node [v47, v359, v474, v705, v1013, v1084] .nil .nil) (.node [v47, v359, v474, v705, v1013, v1129] .nil .nil))) (.node [v47, v359, v474, v705, v1013, v1194] (.node [v47, v359, v474, v705, v1013, v1173] (.node [v47, v359, v474, v705, v1013, v1170] .nil .nil) (.node [v47, v359, v474, v705, v1013, v1174] .nil .nil)) (.node [v47, v359, v474, v705, v1013, v1200] (.node [v47, v359, v474, v705, v1013, v1199] .nil .nil) (.node [v47, v359, v474, v705, v1013, v1201] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llllrr_ok : everyKey (rowOK 4 level4) level5llllrr = true := by decide +kernel
def level5llllr : BinaryTree (List W) := .node [v47, v359, v474, v705, v759, v1013] level5llllrl level5llllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llllr_ok : everyKey (rowOK 4 level4) level5llllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llllrl && everyKey (rowOK 4 level4) level5llllrr) = true
  rw [level5llllrl_ok, level5llllrr_ok]
  decide +kernel
def level5llll : BinaryTree (List W) := .node [v47, v292, v474, v653, v1013, v1194] level5lllll level5llllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llll_ok : everyKey (rowOK 4 level4) level5llll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lllll && everyKey (rowOK 4 level4) level5llllr) = true
  rw [level5lllll_ok, level5llllr_ok]
  decide +kernel
def level5lllrll : BinaryTree (List W) := (.node [v47, v359, v474, v705, v1081, v1194] (.node [v47, v359, v474, v705, v1013, v1301] (.node [v47, v359, v474, v705, v1013, v1263] (.node [v47, v359, v474, v705, v1013, v1249] (.node [v47, v359, v474, v705, v1013, v1245] (.node [v47, v359, v474, v705, v1013, v1227] .nil .nil) .nil) (.node [v47, v359, v474, v705, v1013, v1258] .nil .nil)) (.node [v47, v359, v474, v705, v1013, v1278] (.node [v47, v359, v474, v705, v1013, v1268] .nil .nil) (.node [v47, v359, v474, v705, v1013, v1295] .nil .nil))) (.node [v47, v359, v474, v705, v1017, v1194] (.node [v47, v359, v474, v705, v1013, v1313] (.node [v47, v359, v474, v705, v1013, v1311] (.node [v47, v359, v474, v705, v1013, v1305] .nil .nil) .nil) (.node [v47, v359, v474, v705, v1016, v1194] .nil .nil)) (.node [v47, v359, v474, v705, v1034, v1194] (.node [v47, v359, v474, v705, v1018, v1194] .nil .nil) (.node [v47, v359, v474, v705, v1070, v1194] .nil .nil)))) (.node [v47, v364, v474, v705, v1013, v1194] (.node [v47, v359, v474, v941, v1013, v1194] (.node [v47, v359, v474, v705, v1127, v1194] (.node [v47, v359, v474, v705, v1110, v1194] (.node [v47, v359, v474, v705, v1098, v1194] .nil .nil) .nil) (.node [v47, v359, v474, v847, v1013, v1194] .nil .nil)) (.node [v47, v359, v499, v705, v1013, v1194] (.node [v47, v359, v476, v705, v1013, v1194] .nil .nil) (.node [v47, v359, v614, v705, v1013, v1194] .nil .nil))) (.node [v47, v405, v474, v705, v1013, v1194] (.node [v47, v367, v474, v705, v1013, v1194] (.node [v47, v365, v474, v705, v1013, v1194] .nil .nil) (.node [v47, v368, v474, v705, v1013, v1194] .nil .nil)) (.node [v47, v474, v705, v902, v1013, v1194] (.node [v47, v474, v572, v705, v1013, v1194] .nil .nil) (.node [v47, v474, v705, v903, v1013, v1194] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrll_ok : everyKey (rowOK 4 level4) level5lllrll = true := by decide +kernel
def level5lllrlr : BinaryTree (List W) := (.node [v60, v175, v619, v705, v1013, v1194] (.node [v53, v359, v474, v705, v1013, v1194] (.node [v49, v359, v474, v705, v1013, v1194] (.node [v47, v474, v705, v914, v1013, v1194] (.node [v47, v474, v705, v906, v1013, v1194] (.node [v47, v474, v705, v905, v1013, v1194] .nil .nil) .nil) (.node [v48, v359, v474, v705, v1013, v1194] .nil .nil)) (.node [v51, v359, v474, v705, v1013, v1194] (.node [v50, v359, v474, v705, v1013, v1194] .nil .nil) (.node [v52, v359, v474, v705, v1013, v1194] .nil .nil))) (.node [v57, v359, v474, v705, v1013, v1194] (.node [v55, v359, v474, v705, v1013, v1194] (.node [v54, v405, v474, v705, v1013, v1194] (.node [v54, v359, v474, v705, v1013, v1194] .nil .nil) .nil) (.node [v56, v359, v474, v705, v1013, v1194] .nil .nil)) (.node [v58, v474, v572, v705, v1013, v1194] (.node [v58, v359, v474, v705, v1013, v1194] .nil .nil) (.node [v59, v359, v474, v705, v1013, v1194] .nil .nil)))) (.node [v66, v359, v474, v705, v828, v1013] (.node [v64, v359, v474, v705, v1013, v1194] (.node [v62, v359, v474, v705, v1013, v1194] (.node [v61, v359, v474, v705, v1013, v1194] (.node [v60, v359, v474, v705, v1013, v1194] .nil .nil) .nil) (.node [v63, v359, v474, v705, v1013, v1194] .nil .nil)) (.node [v66, v138, v359, v474, v705, v1013] (.node [v65, v359, v474, v705, v1013, v1194] .nil .nil) (.node [v66, v190, v474, v856, v1013, v1194] .nil .nil))) (.node [v68, v252, v359, v474, v705, v1227] (.node [v68, v252, v359, v474, v705, v964] (.node [v66, v359, v474, v705, v1013, v1194] .nil .nil) (.node [v68, v252, v359, v474, v705, v1194] .nil .nil)) (.node [v68, v266, v359, v474, v705, v1194] (.node [v68, v256, v359, v474, v705, v1194] .nil .nil) (.node [v68, v359, v395, v474, v705, v1194] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrlr_ok : everyKey (rowOK 4 level4) level5lllrlr = true := by decide +kernel
def level5lllrl : BinaryTree (List W) := .node [v47, v474, v705, v904, v1013, v1194] level5lllrll level5lllrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrl_ok : everyKey (rowOK 4 level4) level5lllrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lllrll && everyKey (rowOK 4 level4) level5lllrlr) = true
  rw [level5lllrll_ok, level5lllrlr_ok]
  decide +kernel
def level5lllrrl : BinaryTree (List W) := (.node [v74, v359, v474, v705, v979, v1348] (.node [v71, v359, v474, v705, v1013, v1194] (.node [v70, v359, v474, v705, v1013, v1194] (.node [v68, v359, v474, v847, v1013, v1194] (.node [v68, v359, v474, v705, v1110, v1194] (.node [v68, v359, v474, v705, v1101, v1194] .nil .nil) .nil) (.node [v69, v359, v474, v705, v1013, v1194] .nil .nil)) (.node [v71, v276, v474, v705, v1114, v1194] (.node [v71, v149, v359, v474, v705, v1013] .nil .nil) (.node [v71, v359, v474, v705, v1013, v1084] .nil .nil))) (.node [v74, v359, v382, v474, v705, v1013] (.node [v74, v168, v359, v474, v705, v1013] (.node [v74, v156, v359, v474, v705, v1013] (.node [v74, v153, v359, v474, v705, v1013] .nil .nil) .nil) (.node [v74, v270, v359, v474, v705, v1013] .nil .nil)) (.node [v74, v359, v474, v551, v705, v1013] (.node [v74, v359, v474, v488, v705, v1013] .nil .nil) (.node [v74, v359, v474, v705, v970, v1348] .nil .nil)))) (.node [v76, v359, v474, v705, v1013, v1194] (.node [v74, v359, v474, v705, v1013, v1278] (.node [v74, v359, v474, v705, v1013, v1249] (.node [v74, v359, v474, v705, v1013, v1246] (.node [v74, v359, v474, v705, v1013, v1202] .nil .nil) .nil) (.node [v74, v359, v474, v705, v1013, v1271] .nil .nil)) (.node [v75, v359, v474, v705, v1013, v1194] (.node [v74, v359, v474, v847, v1013, v1194] .nil .nil) (.node [v76, v313, v474, v705, v1013, v1282] .nil .nil))) (.node [v84, v359, v474, v705, v1013, v1194] (.node [v81, v359, v474, v705, v1013, v1194] (.node [v79, v359, v474, v705, v1013, v1194] .nil .nil) (.node [v83, v359, v474, v705, v1013, v1194] .nil .nil)) (.node [v86, v359, v474, v705, v1013, v1194] (.node [v85, v359, v474, v705, v1013, v1194] .nil .nil) (.node [v89, v359, v474, v705, v958, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrrl_ok : everyKey (rowOK 4 level4) level5lllrrl = true := by decide +kernel
def level5lllrrr : BinaryTree (List W) := (.node [v106, v474, v705, v898, v1013, v1348] (.node [v106, v359, v474, v847, v1013, v1194] (.node [v105, v359, v614, v705, v1013, v1194] (.node [v105, v359, v474, v705, v896, v1013] (.node [v100, v359, v474, v705, v1013, v1194] (.node [v97, v359, v474, v705, v1013, v1194] .nil .nil) .nil) (.node [v105, v359, v474, v847, v1013, v1194] .nil .nil)) (.node [v106, v359, v474, v705, v970, v1348] (.node [v106, v325, v474, v705, v892, v1013] .nil .nil) (.node [v106, v359, v474, v705, v979, v1348] .nil .nil))) (.node [v106, v474, v525, v705, v892, v1013] (.node [v106, v380, v474, v705, v1013, v1348] (.node [v106, v376, v474, v705, v1013, v1348] .nil .nil) (.node [v106, v382, v474, v705, v892, v1013] .nil .nil)) (.node [v106, v474, v705, v892, v1013, v1400] (.node [v106, v474, v705, v892, v1013, v1348] .nil .nil) (.node [v106, v474, v705, v892, v1013, v1461] .nil .nil)))) (.node [v122, v359, v485, v705, v1013, v1348] (.node [v122, v325, v359, v705, v755, v1013] (.node [v108, v359, v474, v705, v1013, v1348] (.node [v107, v359, v474, v705, v1013, v1348] (.node [v106, v474, v705, v911, v1013, v1348] .nil .nil) .nil) (.node [v109, v325, v474, v705, v1013, v1194] .nil .nil)) (.node [v122, v359, v474, v705, v979, v1348] (.node [v122, v359, v474, v705, v970, v1348] .nil .nil) (.node [v122, v359, v474, v847, v1013, v1194] .nil .nil))) (.node [v122, v359, v705, v755, v1013, v1461] (.node [v122, v359, v525, v705, v755, v1013] (.node [v122, v359, v487, v705, v1013, v1348] .nil .nil) (.node [v122, v359, v705, v755, v1013, v1348] .nil .nil)) (.node [v122, v359, v705, v779, v1013, v1348] (.node [v122, v359, v705, v772, v1013, v1348] .nil .nil) (.node [v123, v359, v474, v705, v1013, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrrr_ok : everyKey (rowOK 4 level4) level5lllrrr = true := by decide +kernel
def level5lllrr : BinaryTree (List W) := .node [v95, v359, v474, v672, v705, v1013] level5lllrrl level5lllrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrr_ok : everyKey (rowOK 4 level4) level5lllrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lllrrl && everyKey (rowOK 4 level4) level5lllrrr) = true
  rw [level5lllrrl_ok, level5lllrrr_ok]
  decide +kernel
def level5lllr : BinaryTree (List W) := .node [v68, v359, v474, v705, v1019, v1194] level5lllrl level5lllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllr_ok : everyKey (rowOK 4 level4) level5lllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lllrl && everyKey (rowOK 4 level4) level5lllrr) = true
  rw [level5lllrl_ok, level5lllrr_ok]
  decide +kernel
def level5lll : BinaryTree (List W) := .node [v47, v359, v474, v705, v1013, v1225] level5llll level5lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lll_ok : everyKey (rowOK 4 level4) level5lll = true := by
  change (_ && everyKey (rowOK 4 level4) level5llll && everyKey (rowOK 4 level4) level5lllr) = true
  rw [level5llll_ok, level5lllr_ok]
  decide +kernel
def level5llrlll : BinaryTree (List W) := (.node [v129, v359, v474, v705, v1013, v1348] (.node [v128, v359, v474, v522, v1013, v1348] (.node [v128, v359, v474, v517, v1013, v1348] (.node [v128, v359, v474, v517, v970, v1348] (.node [v128, v359, v474, v517, v525, v1013] (.node [v128, v325, v359, v474, v517, v1013] .nil .nil) .nil) (.node [v128, v359, v474, v517, v1013, v1246] .nil .nil)) (.node [v128, v359, v474, v517, v1013, v1461] (.node [v128, v359, v474, v517, v1013, v1362] .nil .nil) (.node [v128, v359, v474, v517, v1034, v1348] .nil .nil))) (.node [v128, v359, v474, v718, v1013, v1348] (.node [v128, v359, v474, v705, v1013, v1420] (.node [v128, v359, v474, v548, v1013, v1348] (.node [v128, v359, v474, v533, v1013, v1348] .nil .nil) .nil) (.node [v128, v359, v474, v705, v1098, v1348] .nil .nil)) (.node [v128, v359, v474, v847, v1013, v1194] (.node [v128, v359, v474, v721, v1013, v1348] .nil .nil) (.node [v129, v359, v474, v705, v708, v1013] .nil .nil)))) (.node [v138, v190, v474, v856, v1013, v1348] (.node [v134, v359, v474, v705, v1013, v1348] (.node [v132, v359, v474, v705, v1013, v1194] (.node [v131, v359, v474, v525, v1013, v1194] (.node [v130, v359, v474, v705, v1013, v1348] .nil .nil) .nil) (.node [v133, v359, v474, v705, v1013, v1348] .nil .nil)) (.node [v136, v359, v474, v705, v1013, v1348] (.node [v135, v359, v474, v705, v1013, v1348] .nil .nil) (.node [v137, v359, v474, v847, v1013, v1194] .nil .nil))) (.node [v138, v359, v474, v705, v1013, v1348] (.node [v138, v359, v474, v525, v705, v1013] (.node [v138, v325, v359, v474, v705, v1013] .nil .nil) (.node [v138, v359, v474, v705, v842, v1013] .nil .nil)) (.node [v138, v359, v474, v856, v1013, v1461] (.node [v138, v359, v474, v705, v1013, v1461] .nil .nil) (.node [v139, v359, v474, v705, v1013, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrlll_ok : everyKey (rowOK 4 level4) level5llrlll = true := by decide +kernel
def level5llrllr : BinaryTree (List W) := (.node [v142, v359, v474, v705, v1084, v1348] (.node [v142, v245, v359, v474, v705, v1348] (.node [v140, v359, v474, v705, v1013, v1348] (.node [v140, v359, v474, v525, v705, v1013] (.node [v140, v325, v359, v474, v705, v1013] (.node [v140, v243, v359, v474, v705, v1348] .nil .nil) .nil) (.node [v140, v359, v474, v705, v877, v1348] .nil .nil)) (.node [v142, v245, v325, v359, v474, v705] (.node [v140, v359, v474, v705, v1013, v1461] .nil .nil) (.node [v142, v245, v359, v474, v525, v705] .nil .nil))) (.node [v142, v359, v387, v474, v705, v1348] (.node [v142, v257, v359, v474, v705, v1348] (.node [v142, v250, v359, v474, v705, v1348] (.node [v142, v245, v359, v474, v705, v1461] .nil .nil) .nil) (.node [v142, v268, v359, v474, v705, v1348] .nil .nil)) (.node [v142, v359, v474, v705, v1029, v1348] (.node [v142, v359, v474, v705, v1013, v1420] .nil .nil) (.node [v142, v359, v474, v705, v1032, v1348] .nil .nil)))) (.node [v149, v325, v359, v474, v705, v1013] (.node [v146, v359, v474, v705, v1013, v1348] (.node [v143, v359, v474, v705, v1013, v1348] (.node [v142, v359, v474, v847, v1013, v1194] (.node [v142, v359, v474, v705, v1098, v1348] .nil .nil) .nil) (.node [v144, v359, v474, v705, v1013, v1348] .nil .nil)) (.node [v148, v359, v474, v705, v1013, v1348] (.node [v147, v359, v474, v705, v1013, v1348] .nil .nil) (.node [v149, v276, v474, v705, v1114, v1348] .nil .nil))) (.node [v149, v359, v474, v705, v1013, v1461] (.node [v149, v359, v474, v705, v1013, v1101] (.node [v149, v359, v474, v525, v705, v1013] .nil .nil) (.node [v149, v359, v474, v705, v1013, v1348] .nil .nil)) (.node [v150, v359, v419, v705, v1138, v1348] (.node [v150, v325, v359, v474, v705, v1013] .nil .nil) (.node [v150, v359, v474, v525, v705, v1013] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrllr_ok : everyKey (rowOK 4 level4) level5llrllr = true := by decide +kernel
def level5llrll : BinaryTree (List W) := .node [v140, v215, v359, v950, v1013, v1348] level5llrlll level5llrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrll_ok : everyKey (rowOK 4 level4) level5llrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrlll && everyKey (rowOK 4 level4) level5llrllr) = true
  rw [level5llrlll_ok, level5llrllr_ok]
  decide +kernel
def level5llrlrl : BinaryTree (List W) := (.node [v166, v359, v474, v705, v1013, v1461] (.node [v153, v359, v614, v705, v1013, v1194] (.node [v153, v359, v451, v474, v705, v1013] (.node [v152, v359, v474, v705, v1013, v1348] (.node [v151, v245, v359, v474, v705, v1348] (.node [v150, v359, v474, v705, v1013, v1461] .nil .nil) .nil) (.node [v153, v168, v359, v474, v705, v1013] .nil .nil)) (.node [v153, v359, v474, v705, v896, v1013] (.node [v153, v359, v474, v672, v705, v1013] .nil .nil) (.node [v153, v359, v474, v847, v1013, v1194] .nil .nil))) (.node [v163, v359, v474, v705, v1013, v1348] (.node [v159, v359, v474, v705, v1013, v1348] (.node [v157, v359, v474, v705, v1013, v1461] (.node [v157, v359, v474, v705, v1013, v1348] .nil .nil) .nil) (.node [v160, v359, v474, v705, v1013, v1348] .nil .nil)) (.node [v165, v359, v474, v705, v1013, v1348] (.node [v164, v359, v474, v705, v1013, v1348] .nil .nil) (.node [v166, v359, v474, v705, v1013, v1348] .nil .nil)))) (.node [v174, v619, v705, v1013, v1194, v1348] (.node [v168, v359, v474, v705, v1013, v1483] (.node [v168, v359, v474, v705, v1013, v1194] (.node [v168, v359, v474, v705, v1013, v1166] (.node [v168, v359, v474, v705, v1013] .nil .nil) .nil) (.node [v168, v359, v474, v705, v1013, v1348] .nil .nil)) (.node [v171, v359, v474, v847, v1013, v1194] (.node [v170, v359, v474, v705, v1013, v1194] .nil .nil) (.node [v171, v359, v614, v705, v1013, v1194] .nil .nil))) (.node [v175, v525, v619, v705, v1013, v1194] (.node [v175, v345, v474, v705, v1013, v1194] (.node [v175, v325, v619, v705, v1013, v1194] .nil .nil) (.node [v175, v359, v474, v847, v1013, v1194] .nil .nil)) (.node [v175, v608, v619, v705, v1013, v1194] (.node [v175, v594, v705, v1013, v1194, v1348] .nil .nil) (.node [v175, v619, v705, v1013, v1194, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrlrl_ok : everyKey (rowOK 4 level4) level5llrlrl = true := by decide +kernel
def level5llrlrr : BinaryTree (List W) := (.node [v190, v474, v856, v1013, v1194, v1348] (.node [v190, v472, v856, v1013, v1194, v1348] (.node [v188, v359, v474, v847, v1013, v1194] (.node [v184, v359, v474, v705, v1013, v1194] (.node [v181, v359, v474, v633, v705, v1194] (.node [v177, v325, v474, v705, v1013, v1194] .nil .nil) .nil) (.node [v187, v359, v474, v705, v1013, v1194] .nil .nil)) (.node [v190, v359, v474, v708, v1013, v1194] (.node [v190, v325, v474, v856, v1013, v1194] .nil .nil) (.node [v190, v359, v474, v847, v1013, v1194] .nil .nil))) (.node [v190, v474, v842, v856, v1013, v1194] (.node [v190, v474, v810, v1013, v1194, v1348] (.node [v190, v474, v525, v856, v1013, v1194] .nil .nil) (.node [v190, v474, v828, v856, v1013, v1348] .nil .nil)) (.node [v190, v474, v856, v1013, v1139, v1348] (.node [v190, v474, v856, v984, v1194, v1348] .nil .nil) (.node [v190, v474, v856, v1013, v1146, v1194] .nil .nil)))) (.node [v192, v325, v474, v705, v1013, v1194] (.node [v190, v499, v856, v1013, v1194, v1348] (.node [v190, v474, v856, v1013, v1258, v1348] (.node [v190, v474, v856, v1013, v1194, v1461] (.node [v190, v474, v856, v1013, v1194, v1431] .nil .nil) .nil) (.node [v190, v474, v856, v1070, v1194, v1348] .nil .nil)) (.node [v192, v288, v474, v705, v1013, v1194] (.node [v191, v359, v474, v525, v1013, v1194] .nil .nil) (.node [v192, v292, v474, v705, v1013, v1194] .nil .nil))) (.node [v192, v411, v474, v705, v1013, v1194] (.node [v192, v359, v474, v705, v1013, v1194] (.node [v192, v359, v474, v672, v705, v1013] .nil .nil) (.node [v192, v359, v474, v705, v1013, v1249] .nil .nil)) (.node [v192, v474, v705, v902, v1013, v1194] (.node [v192, v474, v705, v856, v1013, v1194] .nil .nil) (.node [v193, v474, v705, v892, v1013, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrlrr_ok : everyKey (rowOK 4 level4) level5llrlrr = true := by decide +kernel
def level5llrlr : BinaryTree (List W) := .node [v175, v619, v705, v1013, v1194, v1461] level5llrlrl level5llrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrlr_ok : everyKey (rowOK 4 level4) level5llrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrlrl && everyKey (rowOK 4 level4) level5llrlrr) = true
  rw [level5llrlrl_ok, level5llrlrr_ok]
  decide +kernel
def level5llrl : BinaryTree (List W) := .node [v150, v359, v474, v705, v1013, v1348] level5llrll level5llrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrl_ok : everyKey (rowOK 4 level4) level5llrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrll && everyKey (rowOK 4 level4) level5llrlr) = true
  rw [level5llrll_ok, level5llrlr_ok]
  decide +kernel
def level5llrrll : BinaryTree (List W) := (.node [v205, v474, v705, v865, v1194, v1348] (.node [v202, v395, v474, v705, v865, v1194] (.node [v201, v359, v614, v705, v1013, v1194] (.node [v201, v359, v474, v705, v873, v1194] (.node [v199, v619, v705, v1013, v1194, v1348] (.node [v199, v325, v474, v705, v1013, v1194] .nil .nil) .nil) (.node [v201, v359, v474, v847, v1013, v1194] .nil .nil)) (.node [v202, v345, v474, v705, v1013, v1194] (.node [v202, v325, v474, v705, v865, v1194] .nil .nil) (.node [v202, v359, v474, v847, v1013, v1194] .nil .nil))) (.node [v202, v474, v705, v870, v1194, v1348] (.node [v202, v474, v705, v865, v1194, v1399] (.node [v202, v474, v705, v865, v1194, v1348] (.node [v202, v474, v525, v705, v865, v1194] .nil .nil) .nil) (.node [v202, v474, v705, v865, v1194, v1461] .nil .nil)) (.node [v204, v325, v474, v705, v1013, v1194] (.node [v202, v474, v705, v889, v1194, v1348] .nil .nil) (.node [v205, v325, v474, v705, v1013, v1194] .nil .nil)))) (.node [v215, v359, v942, v950, v1013, v1348] (.node [v215, v359, v474, v847, v1013, v1194] (.node [v215, v325, v359, v950, v1013, v1194] (.node [v215, v243, v359, v950, v1194, v1348] (.node [v206, v325, v474, v705, v1013, v1194] .nil .nil) .nil) (.node [v215, v357, v950, v1013, v1194, v1348] .nil .nil)) (.node [v215, v359, v877, v950, v1194, v1348] (.node [v215, v359, v525, v950, v1013, v1194] .nil .nil) (.node [v215, v359, v887, v1013, v1194, v1348] .nil .nil))) (.node [v215, v359, v950, v1013, v1194, v1348] (.node [v215, v359, v950, v1013, v1087, v1348] (.node [v215, v359, v950, v976, v1194, v1348] .nil .nil) (.node [v215, v359, v950, v1013, v1094, v1194] .nil .nil)) (.node [v215, v359, v950, v1013, v1194, v1461] (.node [v215, v359, v950, v1013, v1194, v1373] .nil .nil) (.node [v215, v359, v950, v1013, v1295, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrll_ok : everyKey (rowOK 4 level4) level5llrrll = true := by decide +kernel
def level5llrrlr : BinaryTree (List W) := (.node [v223, v359, v705, v746, v1194, v1461] (.node [v223, v359, v474, v705, v1050, v1348] (.node [v218, v359, v474, v705, v1013, v1194] (.node [v216, v359, v705, v763, v1013, v1194] (.node [v216, v283, v359, v705, v1013, v1194] (.node [v215, v405, v950, v1013, v1194, v1348] .nil .nil) .nil) (.node [v217, v359, v474, v525, v1013, v1194] .nil .nil)) (.node [v220, v359, v474, v517, v1013, v1348] (.node [v219, v359, v705, v755, v1013, v1348] .nil .nil) (.node [v223, v325, v359, v705, v746, v1194] .nil .nil))) (.node [v223, v359, v497, v705, v1194, v1348] (.node [v223, v359, v474, v705, v1129, v1348] (.node [v223, v359, v474, v705, v1084, v1348] .nil .nil) (.node [v223, v359, v474, v847, v1013, v1194] .nil .nil)) (.node [v223, v359, v525, v705, v746, v1194] (.node [v223, v359, v502, v705, v1194, v1348] .nil .nil) (.node [v223, v359, v705, v746, v1194, v1348] .nil .nil)))) (.node [v234, v359, v474, v509, v525, v1194] (.node [v228, v359, v474, v847, v1013, v1194] (.node [v224, v359, v474, v705, v1194, v1348] (.node [v223, v359, v705, v806, v1194, v1348] (.node [v223, v359, v705, v770, v1194, v1348] .nil .nil) .nil) (.node [v225, v359, v474, v705, v1194, v1348] .nil .nil)) (.node [v230, v619, v705, v1013, v1194, v1348] (.node [v229, v359, v705, v746, v1194, v1348] .nil .nil) (.node [v234, v325, v359, v474, v509, v1194] .nil .nil))) (.node [v234, v359, v474, v509, v1194, v1348] (.node [v234, v359, v474, v509, v1050, v1348] (.node [v234, v359, v474, v509, v736, v1348] .nil .nil) (.node [v234, v359, v474, v509, v1060, v1194] .nil .nil)) (.node [v234, v359, v474, v509, v1194, v1461] (.node [v234, v359, v474, v509, v1194, v1378] .nil .nil) (.node [v234, v359, v474, v509, v1225, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrlr_ok : everyKey (rowOK 4 level4) level5llrrlr = true := by decide +kernel
def level5llrrl : BinaryTree (List W) := .node [v215, v359, v950, v1127, v1194, v1348] level5llrrll level5llrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrl_ok : everyKey (rowOK 4 level4) level5llrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrrll && everyKey (rowOK 4 level4) level5llrrlr) = true
  rw [level5llrrll_ok, level5llrrlr_ok]
  decide +kernel
def level5llrrrl : BinaryTree (List W) := (.node [v243, v359, v474, v525, v705, v1194] (.node [v237, v359, v474, v509, v1194, v1348] (.node [v234, v359, v474, v877, v1194, v1348] (.node [v234, v359, v474, v731, v1194, v1348] (.node [v234, v359, v474, v591, v1194, v1348] (.node [v234, v359, v474, v512, v1194, v1348] .nil .nil) .nil) (.node [v234, v359, v474, v847, v1013, v1194] .nil .nil)) (.node [v235, v359, v474, v525, v1013, v1194] (.node [v234, v359, v474, v941, v1194, v1348] .nil .nil) (.node [v236, v359, v474, v705, v1013, v1194] .nil .nil))) (.node [v240, v474, v856, v1013, v1194, v1348] (.node [v239, v359, v474, v517, v1013, v1348] (.node [v239, v359, v474, v509, v1194, v1348] (.node [v238, v359, v474, v509, v1194, v1348] .nil .nil) .nil) (.node [v240, v359, v950, v1013, v1194, v1348] .nil .nil)) (.node [v242, v359, v474, v705, v1194, v1348] (.node [v241, v359, v474, v705, v1013, v1194] .nil .nil) (.node [v243, v325, v359, v474, v705, v1194] .nil .nil)))) (.node [v245, v359, v474, v705, v979, v1348] (.node [v245, v280, v359, v474, v705, v1348] (.node [v243, v359, v474, v705, v1194, v1461] (.node [v243, v359, v474, v705, v1194, v1348] (.node [v243, v359, v474, v705, v942, v1348] .nil .nil) .nil) (.node [v245, v268, v359, v474, v705, v1348] .nil .nil)) (.node [v245, v359, v474, v513, v705, v1348] (.node [v245, v359, v425, v474, v705, v1348] .nil .nil) (.node [v245, v359, v474, v705, v970, v1348] .nil .nil))) (.node [v245, v359, v474, v847, v1013, v1194] (.node [v245, v359, v474, v705, v1245, v1348] (.node [v245, v359, v474, v705, v1223, v1348] .nil .nil) (.node [v245, v359, v474, v705, v1301, v1348] .nil .nil)) (.node [v247, v359, v474, v705, v1194, v1348] (.node [v245, v359, v474, v941, v1194, v1348] .nil .nil) (.node [v249, v325, v359, v474, v705, v1194] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrrl_ok : everyKey (rowOK 4 level4) level5llrrrl = true := by decide +kernel
def level5llrrrr : BinaryTree (List W) := (.node [v266, v359, v474, v705, v990, v1194] (.node [v252, v359, v474, v847, v1013, v1194] (.node [v252, v266, v359, v474, v705, v1194] (.node [v249, v359, v474, v705, v1194, v1461] (.node [v249, v359, v474, v705, v1194, v1348] (.node [v249, v359, v474, v525, v705, v1194] .nil .nil) .nil) (.node [v251, v359, v474, v705, v1194, v1348] .nil .nil)) (.node [v252, v359, v474, v633, v705, v1194] (.node [v252, v359, v422, v474, v705, v1194] .nil .nil) (.node [v252, v359, v474, v705, v873, v1194] .nil .nil))) (.node [v262, v359, v474, v705, v1194, v1348] (.node [v255, v359, v474, v847, v1013, v1194] (.node [v252, v359, v614, v705, v1013, v1194] .nil .nil) (.node [v258, v359, v474, v705, v1194, v1348] .nil .nil)) (.node [v264, v359, v474, v705, v1194, v1348] (.node [v263, v359, v474, v705, v1194, v1348] .nil .nil) (.node [v264, v359, v474, v705, v1194, v1461] .nil .nil)))) (.node [v268, v359, v474, v705, v1337, v1348] (.node [v267, v359, v474, v705, v1013, v1348] (.node [v266, v359, v474, v705, v1194, v1348] (.node [v266, v359, v474, v705, v1194] (.node [v266, v359, v474, v705, v1013, v1194] .nil .nil) .nil) (.node [v266, v359, v474, v705, v1194, v1474] .nil .nil)) (.node [v268, v359, v474, v705, v1013, v1348] (.node [v268, v359, v474, v705, v958, v1348] .nil .nil) (.node [v268, v359, v474, v705, v1194, v1348] .nil .nil))) (.node [v276, v325, v474, v705, v1114, v1194] (.node [v274, v359, v474, v705, v1110, v1194] (.node [v268, v359, v474, v705, v1348] .nil .nil) (.node [v274, v359, v474, v847, v1013, v1194] .nil .nil)) (.node [v276, v474, v525, v705, v1114, v1194] (.node [v276, v359, v474, v847, v1013, v1194] .nil .nil) (.node [v276, v474, v705, v889, v1194, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrrr_ok : everyKey (rowOK 4 level4) level5llrrrr = true := by decide +kernel
def level5llrrr : BinaryTree (List W) := .node [v249, v359, v448, v705, v1315, v1348] level5llrrrl level5llrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrr_ok : everyKey (rowOK 4 level4) level5llrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrrrl && everyKey (rowOK 4 level4) level5llrrrr) = true
  rw [level5llrrrl_ok, level5llrrrr_ok]
  decide +kernel
def level5llrr : BinaryTree (List W) := .node [v234, v359, v474, v509, v1245, v1348] level5llrrl level5llrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrr_ok : everyKey (rowOK 4 level4) level5llrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrrl && everyKey (rowOK 4 level4) level5llrrr) = true
  rw [level5llrrl_ok, level5llrrr_ok]
  decide +kernel
def level5llr : BinaryTree (List W) := .node [v194, v359, v474, v517, v1013, v1348] level5llrl level5llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llr_ok : everyKey (rowOK 4 level4) level5llr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrl && everyKey (rowOK 4 level4) level5llrr) = true
  rw [level5llrl_ok, level5llrr_ok]
  decide +kernel
def level5ll : BinaryTree (List W) := .node [v124, v359, v474, v705, v1013, v1348] level5lll level5llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5ll_ok : everyKey (rowOK 4 level4) level5ll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lll && everyKey (rowOK 4 level4) level5llr) = true
  rw [level5lll_ok, level5llr_ok]
  decide +kernel
def level5lrllll : BinaryTree (List W) := (.node [v288, v359, v474, v705, v896, v1013] (.node [v284, v359, v474, v705, v1013, v1194] (.node [v276, v474, v705, v1114, v1263, v1348] (.node [v276, v474, v705, v1114, v1194, v1348] (.node [v276, v474, v705, v1101, v1114, v1194] (.node [v276, v474, v705, v1084, v1114, v1348] .nil .nil) .nil) (.node [v276, v474, v705, v1114, v1194, v1461] .nil .nil)) (.node [v279, v474, v705, v892, v1013, v1348] (.node [v277, v325, v474, v705, v1013, v1194] .nil .nil) (.node [v283, v359, v474, v705, v1013, v1249] .nil .nil))) (.node [v288, v359, v474, v656, v1013, v1194] (.node [v288, v292, v474, v653, v1013, v1194] (.node [v285, v359, v474, v705, v1013, v1194] (.node [v285, v359, v474, v705, v942, v1013] .nil .nil) .nil) (.node [v288, v359, v443, v705, v1013, v1194] .nil .nil)) (.node [v288, v359, v474, v705, v873, v1194] (.node [v288, v359, v474, v672, v705, v1013] .nil .nil) (.node [v288, v359, v474, v705, v880, v1194] .nil .nil)))) (.node [v288, v359, v587, v705, v1013, v1194] (.node [v288, v359, v474, v705, v1013, v1278] (.node [v288, v359, v474, v705, v1013, v1235] (.node [v288, v359, v474, v705, v1013, v1194] (.node [v288, v359, v474, v705, v932, v1013] .nil .nil) .nil) (.node [v288, v359, v474, v705, v1013, v1249] .nil .nil)) (.node [v288, v359, v474, v705, v1110, v1194] (.node [v288, v359, v474, v705, v1062, v1194] .nil .nil) (.node [v288, v359, v474, v847, v1013, v1194] .nil .nil))) (.node [v290, v359, v474, v705, v1013, v1194] (.node [v288, v474, v565, v705, v1013, v1194] (.node [v288, v359, v614, v705, v1013, v1194] .nil .nil) (.node [v289, v359, v474, v705, v1013, v1194] .nil .nil)) (.node [v291, v359, v474, v941, v1013, v1194] (.node [v291, v359, v474, v705, v1013, v1194] .nil .nil) (.node [v292, v325, v474, v653, v1013, v1194] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrllll_ok : everyKey (rowOK 4 level4) level5lrllll = true := by decide +kernel
def level5lrlllr : BinaryTree (List W) := (.node [v303, v359, v474, v705, v1013, v1278] (.node [v292, v474, v810, v1013, v1194, v1348] (.node [v292, v474, v653, v1013, v1194, v1348] (.node [v292, v474, v525, v653, v1013, v1194] (.node [v292, v359, v474, v847, v1013, v1194] (.node [v292, v359, v474, v708, v1013, v1194] .nil .nil) .nil) (.node [v292, v474, v562, v653, v1013, v1194] .nil .nil)) (.node [v292, v474, v653, v1013, v1194, v1461] (.node [v292, v474, v653, v1013, v1194, v1394] .nil .nil) (.node [v292, v474, v654, v1013, v1194, v1348] .nil .nil))) (.node [v298, v359, v474, v705, v1013, v1194] (.node [v295, v359, v474, v705, v1013, v1194] (.node [v294, v325, v474, v705, v1013, v1194] (.node [v292, v499, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v296, v359, v474, v705, v1013, v1194] .nil .nil)) (.node [v301, v474, v705, v1114, v1194, v1348] (.node [v300, v359, v474, v705, v1013, v1194] .nil .nil) (.node [v303, v359, v443, v705, v1013, v1194] .nil .nil)))) (.node [v304, v437, v705, v920, v1013, v1348] (.node [v304, v437, v525, v705, v1013, v1194] (.node [v304, v325, v437, v705, v1013, v1194] (.node [v303, v359, v474, v847, v1013, v1194] (.node [v303, v359, v474, v705, v1110, v1194] .nil .nil) .nil) (.node [v304, v359, v474, v847, v1013, v1194] .nil .nil)) (.node [v304, v437, v705, v792, v1013, v1194] (.node [v304, v437, v705, v787, v1013, v1348] .nil .nil) (.node [v304, v437, v705, v870, v1194, v1348] .nil .nil))) (.node [v304, v437, v705, v1013, v1268, v1348] (.node [v304, v437, v705, v1013, v1194, v1387] (.node [v304, v437, v705, v1013, v1194, v1348] .nil .nil) (.node [v304, v437, v705, v1013, v1194, v1461] .nil .nil)) (.node [v304, v437, v705, v1081, v1194, v1348] (.node [v304, v437, v705, v1013, v1305, v1348] .nil .nil) (.node [v304, v438, v705, v1013, v1194, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlllr_ok : everyKey (rowOK 4 level4) level5lrlllr = true := by decide +kernel
def level5lrlll : BinaryTree (List W) := .node [v292, v345, v474, v705, v1013, v1194] level5lrllll level5lrlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlll_ok : everyKey (rowOK 4 level4) level5lrlll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrllll && everyKey (rowOK 4 level4) level5lrlllr) = true
  rw [level5lrllll_ok, level5lrlllr_ok]
  decide +kernel
def level5lrllrl : BinaryTree (List W) := (.node [v313, v474, v705, v800, v1013, v1348] (.node [v311, v359, v474, v705, v1013, v1194] (.node [v308, v325, v474, v705, v1013, v1194] (.node [v305, v437, v705, v1013, v1194, v1348] (.node [v304, v594, v705, v1013, v1194, v1348] (.node [v304, v474, v856, v1013, v1194, v1461] .nil .nil) .nil) (.node [v306, v474, v705, v1114, v1194, v1348] .nil .nil)) (.node [v310, v474, v705, v892, v1013, v1348] (.node [v309, v359, v474, v705, v1013, v1194] .nil .nil) (.node [v311, v359, v474, v705, v920, v1013] .nil .nil))) (.node [v313, v359, v474, v705, v970, v1348] (.node [v313, v325, v474, v705, v1013, v1282] (.node [v312, v359, v474, v847, v1013, v1194] (.node [v312, v359, v474, v705, v1013, v1278] .nil .nil) .nil) (.node [v313, v345, v474, v705, v1013, v1194] .nil .nil)) (.node [v313, v359, v474, v847, v1013, v1194] (.node [v313, v359, v474, v705, v979, v1348] .nil .nil) (.node [v313, v474, v525, v705, v1013, v1282] .nil .nil)))) (.node [v314, v325, v474, v705, v1013, v1194] (.node [v313, v474, v705, v1013, v1271, v1282] (.node [v313, v474, v705, v898, v1013, v1348] (.node [v313, v474, v705, v881, v1282, v1348] (.node [v313, v474, v705, v836, v1013, v1348] .nil .nil) .nil) (.node [v313, v474, v705, v1013, v1093, v1348] .nil .nil)) (.node [v313, v474, v705, v1013, v1282, v1461] (.node [v313, v474, v705, v1013, v1282, v1348] .nil .nil) (.node [v313, v474, v705, v1098, v1282, v1348] .nil .nil))) (.node [v322, v325, v474, v705, v1013, v1194] (.node [v318, v359, v474, v705, v1013, v1194] (.node [v317, v474, v705, v865, v1194, v1348] .nil .nil) (.node [v320, v359, v474, v705, v1013, v1194] .nil .nil)) (.node [v323, v474, v705, v1013, v1282, v1348] (.node [v322, v474, v705, v1013, v1282, v1348] .nil .nil) (.node [v323, v474, v705, v1114, v1194, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrllrl_ok : everyKey (rowOK 4 level4) level5lrllrl = true := by decide +kernel
def level5lrllrr : BinaryTree (List W) := (.node [v325, v359, v474, v630, v1159, v1194] (.node [v325, v359, v443, v705, v1013, v1194] (.node [v325, v359, v428, v642, v1013, v1194] (.node [v325, v357, v474, v705, v1013, v1194] (.node [v325, v348, v474, v705, v1013, v1194] (.node [v324, v474, v705, v1013, v1282, v1348] .nil .nil) .nil) (.node [v325, v359, v419, v705, v1138, v1194] .nil .nil)) (.node [v325, v359, v443, v705, v873, v1194] (.node [v325, v359, v443, v656, v1013, v1194] .nil .nil) (.node [v325, v359, v443, v705, v896, v1013] .nil .nil))) (.node [v325, v359, v446, v705, v1013, v1194] (.node [v325, v359, v443, v705, v1110, v1194] (.node [v325, v359, v443, v705, v1013, v1278] .nil .nil) (.node [v325, v359, v443, v847, v1013, v1194] .nil .nil)) (.node [v325, v359, v461, v705, v1013, v1194] (.node [v325, v359, v448, v705, v1013, v1315] .nil .nil) (.node [v325, v359, v472, v705, v1013, v1194] .nil .nil)))) (.node [v325, v359, v474, v672, v705, v1013] (.node [v325, v359, v474, v656, v1110, v1194] (.node [v325, v359, v474, v656, v1013, v1194] (.node [v325, v359, v474, v656, v896, v1013] (.node [v325, v359, v474, v656, v873, v1194] .nil .nil) .nil) (.node [v325, v359, v474, v656, v1013, v1278] .nil .nil)) (.node [v325, v359, v474, v663, v1013, v1194] (.node [v325, v359, v474, v661, v1013, v1194] .nil .nil) (.node [v325, v359, v474, v666, v1013, v1327] .nil .nil))) (.node [v325, v359, v474, v705, v736, v1013] (.node [v325, v359, v474, v686, v1013, v1194] (.node [v325, v359, v474, v680, v1013, v1194] .nil .nil) (.node [v325, v359, v474, v688, v1013, v1194] .nil .nil)) (.node [v325, v359, v474, v705, v787, v1013] (.node [v325, v359, v474, v705, v759, v1013] .nil .nil) (.node [v325, v359, v474, v705, v827, v1013] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrllrr_ok : everyKey (rowOK 4 level4) level5lrllrr = true := by decide +kernel
def level5lrllr : BinaryTree (List W) := .node [v324, v325, v474, v705, v1013, v1194] level5lrllrl level5lrllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrllr_ok : everyKey (rowOK 4 level4) level5lrllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrllrl && everyKey (rowOK 4 level4) level5lrllrr) = true
  rw [level5lrllrl_ok, level5lrllrr_ok]
  decide +kernel
def level5lrll : BinaryTree (List W) := .node [v304, v439, v705, v1013, v1194, v1348] level5lrlll level5lrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrll_ok : everyKey (rowOK 4 level4) level5lrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrlll && everyKey (rowOK 4 level4) level5lrllr) = true
  rw [level5lrlll_ok, level5lrllr_ok]
  decide +kernel
def level5lrlrll : BinaryTree (List W) := (.node [v325, v359, v474, v705, v964, v1013] (.node [v325, v359, v474, v705, v896, v1013] (.node [v325, v359, v474, v705, v877, v1194] (.node [v325, v359, v474, v705, v873, v1194] (.node [v325, v359, v474, v705, v873, v896] (.node [v325, v359, v474, v705, v870, v1194] .nil .nil) .nil) (.node [v325, v359, v474, v705, v873, v1278] .nil .nil)) (.node [v325, v359, v474, v705, v881, v1194] (.node [v325, v359, v474, v705, v880, v1194] .nil .nil) (.node [v325, v359, v474, v705, v885, v1194] .nil .nil))) (.node [v325, v359, v474, v705, v942, v1013] (.node [v325, v359, v474, v705, v922, v1013] (.node [v325, v359, v474, v705, v920, v1013] (.node [v325, v359, v474, v705, v896, v1110] .nil .nil) .nil) (.node [v325, v359, v474, v705, v932, v1013] .nil .nil)) (.node [v325, v359, v474, v705, v955, v1013] (.node [v325, v359, v474, v705, v951, v1013] .nil .nil) (.node [v325, v359, v474, v705, v958, v1337] .nil .nil)))) (.node [v325, v359, v474, v705, v1013, v1087] (.node [v325, v359, v474, v705, v984, v1194] (.node [v325, v359, v474, v705, v979, v1194] (.node [v325, v359, v474, v705, v976, v1194] (.node [v325, v359, v474, v705, v970, v1194] .nil .nil) .nil) (.node [v325, v359, v474, v705, v982, v1194] .nil .nil)) (.node [v325, v359, v474, v705, v1013, v1050] (.node [v325, v359, v474, v705, v987, v1194] .nil .nil) (.node [v325, v359, v474, v705, v1013, v1084] .nil .nil))) (.node [v325, v359, v474, v705, v1013, v1142] (.node [v325, v359, v474, v705, v1013, v1129] (.node [v325, v359, v474, v705, v1013, v1118] .nil .nil) (.node [v325, v359, v474, v705, v1013, v1139] .nil .nil)) (.node [v325, v359, v474, v705, v1013, v1194] (.node [v325, v359, v474, v705, v1013, v1161] .nil .nil) (.node [v325, v359, v474, v705, v1013, v1209] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrll_ok : everyKey (rowOK 4 level4) level5lrlrll = true := by decide +kernel
def level5lrlrlr : BinaryTree (List W) := (.node [v325, v359, v474, v705, v1028, v1194] (.node [v325, v359, v474, v705, v1013, v1263] (.node [v325, v359, v474, v705, v1013, v1249] (.node [v325, v359, v474, v705, v1013, v1235] (.node [v325, v359, v474, v705, v1013, v1227] (.node [v325, v359, v474, v705, v1013, v1225] .nil .nil) .nil) (.node [v325, v359, v474, v705, v1013, v1245] .nil .nil)) (.node [v325, v359, v474, v705, v1013, v1258] (.node [v325, v359, v474, v705, v1013, v1255] .nil .nil) (.node [v325, v359, v474, v705, v1013, v1260] .nil .nil))) (.node [v325, v359, v474, v705, v1013, v1295] (.node [v325, v359, v474, v705, v1013, v1268] (.node [v325, v359, v474, v705, v1013, v1266] .nil .nil) (.node [v325, v359, v474, v705, v1013, v1278] .nil .nil)) (.node [v325, v359, v474, v705, v1013, v1305] (.node [v325, v359, v474, v705, v1013, v1301] .nil .nil) (.node [v325, v359, v474, v705, v1013, v1311] .nil .nil)))) (.node [v325, v359, v474, v705, v1098, v1194] (.node [v325, v359, v474, v705, v1070, v1194] (.node [v325, v359, v474, v705, v1062, v1194] (.node [v325, v359, v474, v705, v1044, v1194] (.node [v325, v359, v474, v705, v1034, v1194] .nil .nil) .nil) (.node [v325, v359, v474, v705, v1067, v1194] .nil .nil)) (.node [v325, v359, v474, v705, v1081, v1194] (.node [v325, v359, v474, v705, v1079, v1194] .nil .nil) (.node [v325, v359, v474, v705, v1097, v1194] .nil .nil))) (.node [v325, v359, v474, v717, v1013, v1194] (.node [v325, v359, v474, v705, v1110, v1278] (.node [v325, v359, v474, v705, v1110, v1194] .nil .nil) (.node [v325, v359, v474, v705, v1127, v1194] .nil .nil)) (.node [v325, v359, v474, v740, v1013, v1194] (.node [v325, v359, v474, v730, v1013, v1194] .nil .nil) (.node [v325, v359, v474, v812, v1013, v1194] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrlr_ok : everyKey (rowOK 4 level4) level5lrlrlr = true := by decide +kernel
def level5lrlrl : BinaryTree (List W) := .node [v325, v359, v474, v705, v1013, v1216] level5lrlrll level5lrlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrl_ok : everyKey (rowOK 4 level4) level5lrlrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrlrll && everyKey (rowOK 4 level4) level5lrlrlr) = true
  rw [level5lrlrll_ok, level5lrlrlr_ok]
  decide +kernel
def level5lrlrrl : BinaryTree (List W) := (.node [v325, v359, v614, v705, v1013, v1194] (.node [v325, v359, v498, v705, v1013, v1194] (.node [v325, v359, v474, v847, v1013, v1278] (.node [v325, v359, v474, v847, v896, v1013] (.node [v325, v359, v474, v847, v873, v1194] (.node [v325, v359, v474, v840, v1013, v1194] .nil .nil) .nil) (.node [v325, v359, v474, v847, v1013, v1194] .nil .nil)) (.node [v325, v359, v474, v941, v1013, v1194] (.node [v325, v359, v474, v847, v1110, v1194] .nil .nil) (.node [v325, v359, v489, v705, v1013, v1194] .nil .nil))) (.node [v325, v359, v605, v705, v1013, v1194] (.node [v325, v359, v575, v705, v1013, v1194] (.node [v325, v359, v504, v705, v1013, v1194] (.node [v325, v359, v499, v705, v1013, v1194] .nil .nil) .nil) (.node [v325, v359, v587, v705, v1013, v1194] .nil .nil)) (.node [v325, v359, v614, v705, v873, v1194] (.node [v325, v359, v614, v656, v1013, v1194] .nil .nil) (.node [v325, v359, v614, v705, v896, v1013] .nil .nil)))) (.node [v325, v474, v565, v705, v1013, v1194] (.node [v325, v385, v474, v705, v1013, v1194] (.node [v325, v359, v614, v847, v1013, v1194] (.node [v325, v359, v614, v705, v1110, v1194] (.node [v325, v359, v614, v705, v1013, v1278] .nil .nil) .nil) (.node [v325, v384, v474, v705, v1013, v1194] .nil .nil)) (.node [v325, v405, v474, v705, v1013, v1194] (.node [v325, v398, v474, v705, v1013, v1194] .nil .nil) (.node [v325, v443, v705, v1013, v1194, v1469] .nil .nil))) (.node [v325, v474, v656, v1013, v1194, v1469] (.node [v325, v474, v572, v705, v1013, v1194] (.node [v325, v474, v568, v705, v1013, v1194] .nil .nil) (.node [v325, v474, v616, v705, v1013, v1194] .nil .nil)) (.node [v325, v474, v705, v853, v1013, v1194] (.node [v325, v474, v705, v796, v1013, v1194] .nil .nil) (.node [v325, v474, v705, v873, v1194, v1469] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrrl_ok : everyKey (rowOK 4 level4) level5lrlrrl = true := by decide +kernel
def level5lrlrrr : BinaryTree (List W) := (.node [v331, v359, v474, v705, v1013, v1194] (.node [v325, v474, v705, v1110, v1194, v1469] (.node [v325, v474, v705, v1013, v1108, v1194] (.node [v325, v474, v705, v914, v1013, v1194] (.node [v325, v474, v705, v908, v1013, v1194] (.node [v325, v474, v705, v900, v1013, v1194] .nil .nil) .nil) (.node [v325, v474, v705, v1013, v1093, v1194] .nil .nil)) (.node [v325, v474, v705, v1013, v1194, v1469] (.node [v325, v474, v705, v1013, v1194, v1276] .nil .nil) (.node [v325, v474, v705, v1013, v1278, v1469] .nil .nil))) (.node [v327, v359, v474, v705, v1013, v1194] (.node [v325, v614, v705, v1013, v1194, v1469] (.node [v325, v474, v847, v1013, v1194, v1469] .nil .nil) (.node [v326, v359, v474, v705, v1013, v1194] .nil .nil)) (.node [v329, v359, v474, v705, v1013, v1194] (.node [v328, v359, v474, v705, v1013, v1194] .nil .nil) (.node [v330, v359, v474, v705, v1013, v1194] .nil .nil)))) (.node [v340, v474, v705, v1013, v1194, v1348] (.node [v336, v359, v474, v705, v1013, v1194] (.node [v334, v474, v705, v865, v1194, v1348] (.node [v333, v359, v474, v705, v1013, v1194] (.node [v332, v474, v705, v892, v1013, v1348] .nil .nil) .nil) (.node [v335, v474, v705, v1013, v1194, v1348] .nil .nil)) (.node [v338, v474, v653, v1013, v1194, v1348] (.node [v337, v359, v474, v705, v1013, v1194] .nil .nil) (.node [v339, v619, v705, v1013, v1194, v1348] .nil .nil))) (.node [v344, v437, v705, v1013, v1194, v1348] (.node [v342, v359, v474, v705, v1013, v1194] (.node [v341, v359, v474, v705, v1013, v1194] .nil .nil) (.node [v343, v359, v474, v705, v1013, v1194] .nil .nil)) (.node [v345, v359, v474, v653, v1013, v1194] (.node [v345, v359, v441, v705, v1013, v1194] .nil .nil) (.node [v345, v359, v474, v705, v871, v1194] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrrr_ok : everyKey (rowOK 4 level4) level5lrlrrr = true := by decide +kernel
def level5lrlrr : BinaryTree (List W) := .node [v325, v474, v705, v896, v1013, v1469] level5lrlrrl level5lrlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrr_ok : everyKey (rowOK 4 level4) level5lrlrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrlrrl && everyKey (rowOK 4 level4) level5lrlrrr) = true
  rw [level5lrlrrl_ok, level5lrlrrr_ok]
  decide +kernel
def level5lrlr : BinaryTree (List W) := .node [v325, v359, v474, v819, v1013, v1194] level5lrlrl level5lrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlr_ok : everyKey (rowOK 4 level4) level5lrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrlrl && everyKey (rowOK 4 level4) level5lrlrr) = true
  rw [level5lrlrl_ok, level5lrlrr_ok]
  decide +kernel
def level5lrl : BinaryTree (List W) := .node [v325, v359, v474, v705, v828, v1013] level5lrll level5lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrl_ok : everyKey (rowOK 4 level4) level5lrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrll && everyKey (rowOK 4 level4) level5lrlr) = true
  rw [level5lrll_ok, level5lrlr_ok]
  decide +kernel
def level5lrrlll : BinaryTree (List W) := (.node [v347, v474, v705, v1013, v1194, v1461] (.node [v345, v474, v705, v892, v1013, v1194] (.node [v345, v359, v474, v856, v1013, v1194] (.node [v345, v359, v474, v705, v1112, v1194] (.node [v345, v359, v474, v705, v1013, v1280] (.node [v345, v359, v474, v705, v1013, v1194] .nil .nil) .nil) (.node [v345, v359, v474, v847, v1013, v1194] .nil .nil)) (.node [v345, v437, v474, v705, v1013, v1194] (.node [v345, v359, v618, v705, v1013, v1194] .nil .nil) (.node [v345, v474, v705, v856, v1013, v1194] .nil .nil))) (.node [v345, v474, v856, v1013, v1194, v1348] (.node [v345, v474, v705, v1013, v1194, v1471] (.node [v345, v474, v705, v1013, v1194, v1469] (.node [v345, v474, v705, v1013, v1114, v1194] .nil .nil) .nil) (.node [v345, v474, v856, v1013, v1194] .nil .nil)) (.node [v346, v474, v705, v1013, v1194, v1348] (.node [v345, v474, v856, v1013, v1194, v1461] .nil .nil) (.node [v347, v474, v705, v1013, v1194, v1348] .nil .nil)))) (.node [v348, v474, v705, v1013, v1194, v1414] (.node [v348, v474, v705, v837, v1013, v1194] (.node [v348, v474, v680, v1013, v1194, v1348] (.node [v348, v474, v525, v705, v1013, v1194] (.node [v348, v419, v705, v1138, v1194, v1348] .nil .nil) .nil) (.node [v348, v474, v705, v827, v1013, v1348] .nil .nil)) (.node [v348, v474, v705, v870, v1194, v1348] (.node [v348, v474, v705, v865, v1194, v1348] .nil .nil) (.node [v348, v474, v705, v1013, v1194, v1348] .nil .nil))) (.node [v348, v474, v941, v1013, v1194, v1348] (.node [v348, v474, v705, v1013, v1301, v1348] (.node [v348, v474, v705, v1013, v1194, v1461] .nil .nil) (.node [v348, v474, v705, v1114, v1194, v1348] .nil .nil)) (.node [v350, v359, v474, v705, v1013, v1194] (.node [v349, v474, v705, v1013, v1194, v1348] .nil .nil) (.node [v351, v474, v705, v1114, v1194, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrlll_ok : everyKey (rowOK 4 level4) level5lrrlll = true := by decide +kernel
def level5lrrllr : BinaryTree (List W) := (.node [v359, v370, v474, v705, v1013, v1194] (.node [v357, v474, v705, v1013, v1194, v1348] (.node [v357, v474, v525, v705, v1013, v1194] (.node [v355, v474, v705, v1013, v1194, v1461] (.node [v355, v474, v705, v1013, v1194, v1348] (.node [v353, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v356, v474, v705, v1013, v1194, v1348] .nil .nil)) (.node [v357, v474, v705, v1013, v1087, v1348] (.node [v357, v474, v705, v976, v1194, v1348] .nil .nil) (.node [v357, v474, v705, v1013, v1094, v1194] .nil .nil))) (.node [v358, v474, v705, v1013, v1194, v1348] (.node [v357, v474, v705, v1013, v1295, v1348] (.node [v357, v474, v705, v1013, v1194, v1461] (.node [v357, v474, v705, v1013, v1194, v1373] .nil .nil) .nil) (.node [v357, v474, v705, v1127, v1194, v1348] .nil .nil)) (.node [v359, v359, v474, v847, v1013, v1194] (.node [v358, v474, v705, v1013, v1194, v1461] .nil .nil) (.node [v359, v369, v474, v705, v1013, v1194] .nil .nil)))) (.node [v359, v382, v474, v705, v1013, v1483] (.node [v359, v378, v474, v705, v1013, v1194] (.node [v359, v374, v474, v705, v1013, v1194] (.node [v359, v373, v474, v705, v1013, v1194] (.node [v359, v371, v474, v705, v1013, v1348] .nil .nil) .nil) (.node [v359, v377, v474, v705, v1013, v1348] .nil .nil)) (.node [v359, v382, v474, v705, v896, v1013] (.node [v359, v381, v474, v705, v1013, v1194] .nil .nil) (.node [v359, v382, v474, v705, v1013, v1194] .nil .nil))) (.node [v359, v389, v474, v705, v1013, v1194] (.node [v359, v388, v474, v705, v1013, v1194] (.node [v359, v383, v474, v705, v1013, v1194] .nil .nil) (.node [v359, v389, v474, v705, v877, v1194] .nil .nil)) (.node [v359, v393, v474, v705, v1013, v1194] (.node [v359, v390, v474, v705, v1013, v1194] .nil .nil) (.node [v359, v394, v474, v705, v1013, v1194] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrllr_ok : everyKey (rowOK 4 level4) level5lrrllr = true := by decide +kernel
def level5lrrll : BinaryTree (List W) := .node [v352, v474, v705, v1013, v1282, v1348] level5lrrlll level5lrrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrll_ok : everyKey (rowOK 4 level4) level5lrrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrlll && everyKey (rowOK 4 level4) level5lrrllr) = true
  rw [level5lrrlll_ok, level5lrrllr_ok]
  decide +kernel
def level5lrrlrl : BinaryTree (List W) := (.node [v359, v419, v474, v705, v1129, v1348] (.node [v359, v403, v474, v705, v1013, v1194] (.node [v359, v395, v474, v705, v1194, v1474] (.node [v359, v395, v474, v705, v1013, v1194] (.node [v359, v395, v474, v705, v873, v1194] (.node [v359, v395, v474, v705, v870, v1194] .nil .nil) .nil) (.node [v359, v395, v474, v705, v1013, v1285] .nil .nil)) (.node [v359, v397, v474, v705, v1013, v1194] (.node [v359, v396, v474, v705, v1013, v1194] .nil .nil) (.node [v359, v402, v474, v705, v1013, v1194] .nil .nil))) (.node [v359, v415, v474, v847, v1013, v1194] (.node [v359, v411, v474, v847, v1013, v1194] (.node [v359, v410, v474, v847, v1013, v1194] (.node [v359, v407, v474, v705, v1013, v1194] .nil .nil) .nil) (.node [v359, v411, v474, v1013, v1194, v1461] .nil .nil)) (.node [v359, v419, v474, v705, v1050, v1348] (.node [v359, v416, v474, v847, v1013, v1194] .nil .nil) (.node [v359, v419, v474, v705, v1084, v1348] .nil .nil)))) (.node [v359, v419, v705, v1129, v1138, v1348] (.node [v359, v419, v705, v827, v1138, v1348] (.node [v359, v419, v680, v1138, v1194, v1348] (.node [v359, v419, v525, v705, v1138, v1194] (.node [v359, v419, v474, v847, v1013, v1194] .nil .nil) .nil) (.node [v359, v419, v705, v806, v1194, v1348] .nil .nil)) (.node [v359, v419, v705, v926, v1194, v1348] (.node [v359, v419, v705, v837, v1138, v1194] .nil .nil) (.node [v359, v419, v705, v929, v1194, v1348] .nil .nil))) (.node [v359, v419, v705, v1138, v1194, v1461] (.node [v359, v419, v705, v1138, v1194, v1348] (.node [v359, v419, v705, v1132, v1194, v1348] .nil .nil) (.node [v359, v419, v705, v1138, v1194, v1414] .nil .nil)) (.node [v359, v419, v941, v1138, v1194, v1348] (.node [v359, v419, v705, v1138, v1301, v1348] .nil .nil) (.node [v359, v420, v705, v763, v1013, v1194] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrlrl_ok : everyKey (rowOK 4 level4) level5lrrlrl = true := by decide +kernel
def level5lrrlrr : BinaryTree (List W) := (.node [v359, v442, v525, v705, v1013, v1194] (.node [v359, v428, v643, v1013, v1194, v1348] (.node [v359, v428, v584, v642, v1013, v1194] (.node [v359, v428, v474, v847, v1013, v1194] (.node [v359, v427, v589, v705, v1013, v1194] (.node [v359, v423, v705, v755, v1013, v1348] .nil .nil) .nil) (.node [v359, v428, v525, v642, v1013, v1194] .nil .nil)) (.node [v359, v428, v642, v1013, v1194, v1442] (.node [v359, v428, v642, v1013, v1194, v1348] .nil .nil) (.node [v359, v428, v642, v1013, v1194, v1461] .nil .nil))) (.node [v359, v440, v705, v1138, v1194, v1348] (.node [v359, v431, v642, v1013, v1194, v1348] (.node [v359, v428, v887, v1013, v1194, v1348] .nil .nil) (.node [v359, v437, v474, v847, v1013, v1194] .nil .nil)) (.node [v359, v441, v705, v1013, v1194, v1348] (.node [v359, v440, v950, v1013, v1194, v1348] .nil .nil) (.node [v359, v441, v705, v1013, v1194, v1461] .nil .nil)))) (.node [v359, v443, v705, v873, v1194, v1348] (.node [v359, v443, v656, v1013, v1194, v1348] (.node [v359, v443, v525, v705, v1013, v1194] (.node [v359, v443, v474, v847, v1013, v1194] (.node [v359, v442, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v443, v614, v705, v1013, v1194] .nil .nil)) (.node [v359, v443, v705, v792, v1013, v1194] (.node [v359, v443, v705, v763, v1013, v1194] .nil .nil) (.node [v359, v443, v705, v847, v1013, v1194] .nil .nil))) (.node [v359, v443, v705, v1013, v1194, v1461] (.node [v359, v443, v705, v1013, v1194, v1348] (.node [v359, v443, v705, v896, v1013, v1348] .nil .nil) (.node [v359, v443, v705, v1013, v1194, v1424] .nil .nil)) (.node [v359, v443, v705, v1110, v1194, v1348] (.node [v359, v443, v705, v1013, v1278, v1348] .nil .nil) (.node [v359, v443, v847, v1013, v1194] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrlrr_ok : everyKey (rowOK 4 level4) level5lrrlrr = true := by decide +kernel
def level5lrrlr : BinaryTree (List W) := .node [v359, v421, v474, v705, v1013, v1194] level5lrrlrl level5lrrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrlr_ok : everyKey (rowOK 4 level4) level5lrrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrlrl && everyKey (rowOK 4 level4) level5lrrlrr) = true
  rw [level5lrrlrl_ok, level5lrrlrr_ok]
  decide +kernel
def level5lrrl : BinaryTree (List W) := .node [v359, v395, v474, v705, v862, v1013] level5lrrll level5lrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrl_ok : everyKey (rowOK 4 level4) level5lrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrll && everyKey (rowOK 4 level4) level5lrrlr) = true
  rw [level5lrrll_ok, level5lrrlr_ok]
  decide +kernel
def level5lrrrll : BinaryTree (List W) := (.node [v359, v450, v474, v705, v1013, v1194] (.node [v359, v448, v705, v780, v1013, v1315] (.node [v359, v448, v474, v705, v979, v1348] (.node [v359, v446, v705, v1013, v1194, v1348] (.node [v359, v445, v705, v755, v1013, v1348] (.node [v359, v444, v474, v705, v1013, v1194] .nil .nil) .nil) (.node [v359, v448, v474, v705, v970, v1348] .nil .nil)) (.node [v359, v448, v525, v705, v1013, v1315] (.node [v359, v448, v474, v847, v1013, v1194] .nil .nil) (.node [v359, v448, v705, v779, v1013, v1348] .nil .nil))) (.node [v359, v448, v705, v1013, v1315, v1348] (.node [v359, v448, v705, v979, v1315, v1348] (.node [v359, v448, v705, v945, v1013, v1348] (.node [v359, v448, v705, v927, v1013, v1348] .nil .nil) .nil) (.node [v359, v448, v705, v1013, v1132, v1348] .nil .nil)) (.node [v359, v448, v705, v1013, v1315, v1461] (.node [v359, v448, v705, v1013, v1315, v1420] .nil .nil) (.node [v359, v449, v705, v763, v1013, v1194] .nil .nil)))) (.node [v359, v462, v589, v705, v1013, v1194] (.node [v359, v459, v705, v1013, v1194, v1348] (.node [v359, v457, v705, v1013, v1315, v1348] (.node [v359, v457, v474, v705, v958, v1348] (.node [v359, v456, v705, v1013, v1315, v1348] .nil .nil) .nil) (.node [v359, v458, v705, v1013, v1315, v1348] .nil .nil)) (.node [v359, v461, v705, v1013, v1194, v1348] (.node [v359, v460, v705, v1013, v1194, v1348] .nil .nil) (.node [v359, v462, v474, v847, v1013, v1194] .nil .nil))) (.node [v359, v462, v705, v1013, v1194, v1424] (.node [v359, v462, v705, v759, v1013, v1424] (.node [v359, v462, v614, v705, v1013, v1194] .nil .nil) (.node [v359, v462, v705, v764, v1013, v1194] .nil .nil)) (.node [v359, v463, v705, v755, v1013, v1348] (.node [v359, v462, v705, v1013, v1311, v1424] .nil .nil) (.node [v359, v464, v705, v1013, v1194, v1424] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrll_ok : everyKey (rowOK 4 level4) level5lrrrll = true := by decide +kernel
def level5lrrrlr : BinaryTree (List W) := (.node [v359, v474, v494, v705, v1194, v1348] (.node [v359, v472, v705, v1013, v1194, v1348] (.node [v359, v472, v525, v705, v1013, v1194] (.node [v359, v471, v705, v1013, v1194, v1424] (.node [v359, v469, v705, v1013, v1194, v1424] (.node [v359, v466, v705, v1013, v1194, v1424] .nil .nil) .nil) (.node [v359, v471, v705, v1013, v1315, v1348] .nil .nil)) (.node [v359, v472, v705, v1013, v1139, v1348] (.node [v359, v472, v705, v984, v1194, v1348] .nil .nil) (.node [v359, v472, v705, v1013, v1146, v1194] .nil .nil))) (.node [v359, v472, v705, v1070, v1194, v1348] (.node [v359, v472, v705, v1013, v1194, v1461] (.node [v359, v472, v705, v1013, v1194, v1431] .nil .nil) (.node [v359, v472, v705, v1013, v1258, v1348] .nil .nil)) (.node [v359, v474, v482, v705, v1013, v1348] (.node [v359, v473, v705, v1013, v1194, v1348] .nil .nil) (.node [v359, v474, v486, v705, v1013, v1348] .nil .nil)))) (.node [v359, v474, v517, v548, v1013, v1348] (.node [v359, v474, v509, v705, v1129, v1348] (.node [v359, v474, v509, v705, v1050, v1348] (.node [v359, v474, v509, v591, v1194, v1348] (.node [v359, v474, v508, v705, v1063, v1194] .nil .nil) .nil) (.node [v359, v474, v509, v705, v1084, v1348] .nil .nil)) (.node [v359, v474, v515, v1013, v1194, v1461] (.node [v359, v474, v509, v847, v1013, v1194] .nil .nil) (.node [v359, v474, v516, v705, v1013, v1249] .nil .nil))) (.node [v359, v474, v519, v705, v1013, v1194] (.node [v359, v474, v517, v705, v979, v1348] (.node [v359, v474, v517, v705, v970, v1348] .nil .nil) (.node [v359, v474, v517, v847, v1013, v1194] .nil .nil)) (.node [v359, v474, v522, v705, v958, v1348] (.node [v359, v474, v521, v1013, v1194, v1461] .nil .nil) (.node [v359, v474, v523, v705, v1013, v1194] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrlr_ok : everyKey (rowOK 4 level4) level5lrrrlr = true := by decide +kernel
def level5lrrrl : BinaryTree (List W) := .node [v359, v464, v705, v1013, v1194, v1494] level5lrrrll level5lrrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrl_ok : everyKey (rowOK 4 level4) level5lrrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrrll && everyKey (rowOK 4 level4) level5lrrrlr) = true
  rw [level5lrrrll_ok, level5lrrrlr_ok]
  decide +kernel
def level5lrrrrl : BinaryTree (List W) := (.node [v359, v474, v525, v705, v832, v1013] (.node [v359, v474, v525, v672, v1013, v1461] (.node [v359, v474, v525, v656, v1013, v1194] (.node [v359, v474, v525, v631, v1013, v1194] (.node [v359, v474, v525, v630, v1159, v1194] (.node [v359, v474, v525, v539, v1013, v1194] .nil .nil) .nil) (.node [v359, v474, v525, v644, v1013, v1194] .nil .nil)) (.node [v359, v474, v525, v667, v1013, v1194] (.node [v359, v474, v525, v666, v1013, v1327] .nil .nil) (.node [v359, v474, v525, v672, v705, v1013] .nil .nil))) (.node [v359, v474, v525, v705, v787, v1013] (.node [v359, v474, v525, v705, v737, v1013] (.node [v359, v474, v525, v705, v736, v1013] (.node [v359, v474, v525, v680, v1013, v1194] .nil .nil) .nil) (.node [v359, v474, v525, v705, v759, v1013] .nil .nil)) (.node [v359, v474, v525, v705, v827, v1013] (.node [v359, v474, v525, v705, v816, v1013] .nil .nil) (.node [v359, v474, v525, v705, v828, v1013] .nil .nil)))) (.node [v359, v474, v525, v705, v932, v1013] (.node [v359, v474, v525, v705, v880, v1194] (.node [v359, v474, v525, v705, v877, v1194] (.node [v359, v474, v525, v705, v873, v1194] (.node [v359, v474, v525, v705, v870, v1194] .nil .nil) .nil) (.node [v359, v474, v525, v705, v878, v1194] .nil .nil)) (.node [v359, v474, v525, v705, v896, v1013] (.node [v359, v474, v525, v705, v881, v1194] .nil .nil) (.node [v359, v474, v525, v705, v920, v1013] .nil .nil))) (.node [v359, v474, v525, v705, v958, v1337] (.node [v359, v474, v525, v705, v943, v1013] (.node [v359, v474, v525, v705, v942, v1013] .nil .nil) (.node [v359, v474, v525, v705, v951, v1013] .nil .nil)) (.node [v359, v474, v525, v705, v970, v1194] (.node [v359, v474, v525, v705, v964, v1013] .nil .nil) (.node [v359, v474, v525, v705, v976, v1194] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrrl_ok : everyKey (rowOK 4 level4) level5lrrrrl = true := by decide +kernel
def level5lrrrrr : BinaryTree (List W) := (.node [v359, v474, v525, v705, v1013, v1245] (.node [v359, v474, v525, v705, v1013, v1211] (.node [v359, v474, v525, v705, v1013, v1129] (.node [v359, v474, v525, v705, v1013, v1084] (.node [v359, v474, v525, v705, v1013, v1050] (.node [v359, v474, v525, v705, v984, v1194] .nil .nil) .nil) (.node [v359, v474, v525, v705, v1013, v1087] .nil .nil)) (.node [v359, v474, v525, v705, v1013, v1152] (.node [v359, v474, v525, v705, v1013, v1139] .nil .nil) (.node [v359, v474, v525, v705, v1013, v1194] .nil .nil))) (.node [v359, v474, v525, v705, v1013, v1235] (.node [v359, v474, v525, v705, v1013, v1227] (.node [v359, v474, v525, v705, v1013, v1225] .nil .nil) (.node [v359, v474, v525, v705, v1013, v1233] .nil .nil)) (.node [v359, v474, v525, v705, v1013, v1242] (.node [v359, v474, v525, v705, v1013, v1237] .nil .nil) (.node [v359, v474, v525, v705, v1013, v1244] .nil .nil)))) (.node [v359, v474, v525, v705, v1013, v1311] (.node [v359, v474, v525, v705, v1013, v1278] (.node [v359, v474, v525, v705, v1013, v1263] (.node [v359, v474, v525, v705, v1013, v1258] (.node [v359, v474, v525, v705, v1013, v1249] .nil .nil) .nil) (.node [v359, v474, v525, v705, v1013, v1268] .nil .nil)) (.node [v359, v474, v525, v705, v1013, v1301] (.node [v359, v474, v525, v705, v1013, v1295] .nil .nil) (.node [v359, v474, v525, v705, v1013, v1305] .nil .nil))) (.node [v359, v474, v525, v705, v1070, v1194] (.node [v359, v474, v525, v705, v1040, v1194] (.node [v359, v474, v525, v705, v1034, v1194] .nil .nil) (.node [v359, v474, v525, v705, v1062, v1194] .nil .nil)) (.node [v359, v474, v525, v705, v1098, v1194] (.node [v359, v474, v525, v705, v1081, v1194] .nil .nil) (.node [v359, v474, v525, v705, v1110, v1194] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrrr_ok : everyKey (rowOK 4 level4) level5lrrrrr = true := by decide +kernel
def level5lrrrr : BinaryTree (List W) := .node [v359, v474, v525, v705, v979, v1194] level5lrrrrl level5lrrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrr_ok : everyKey (rowOK 4 level4) level5lrrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrrrl && everyKey (rowOK 4 level4) level5lrrrrr) = true
  rw [level5lrrrrl_ok, level5lrrrrr_ok]
  decide +kernel
def level5lrrr : BinaryTree (List W) := .node [v359, v474, v524, v705, v1013, v1194] level5lrrrl level5lrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrr_ok : everyKey (rowOK 4 level4) level5lrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrrl && everyKey (rowOK 4 level4) level5lrrrr) = true
  rw [level5lrrrl_ok, level5lrrrr_ok]
  decide +kernel
def level5lrr : BinaryTree (List W) := .node [v359, v443, v847, v1013, v1194, v1348] level5lrrl level5lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrr_ok : everyKey (rowOK 4 level4) level5lrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrl && everyKey (rowOK 4 level4) level5lrrr) = true
  rw [level5lrrl_ok, level5lrrr_ok]
  decide +kernel
def level5lr : BinaryTree (List W) := .node [v345, v359, v474, v705, v895, v1013] level5lrl level5lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lr_ok : everyKey (rowOK 4 level4) level5lr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrl && everyKey (rowOK 4 level4) level5lrr) = true
  rw [level5lrl_ok, level5lrr_ok]
  decide +kernel
def level5l : BinaryTree (List W) := .node [v276, v474, v705, v951, v1114, v1348] level5ll level5lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5l_ok : everyKey (rowOK 4 level4) level5l = true := by
  change (_ && everyKey (rowOK 4 level4) level5ll && everyKey (rowOK 4 level4) level5lr) = true
  rw [level5ll_ok, level5lr_ok]
  decide +kernel
def level5rlllll : BinaryTree (List W) := (.node [v359, v474, v532, v705, v1013, v1194] (.node [v359, v474, v525, v1013, v1194, v1324] (.node [v359, v474, v525, v937, v1013, v1194] (.node [v359, v474, v525, v821, v1013, v1194] (.node [v359, v474, v525, v741, v1013, v1194] (.node [v359, v474, v525, v725, v1013, v1194] .nil .nil) .nil) (.node [v359, v474, v525, v847, v1013, v1194] .nil .nil)) (.node [v359, v474, v525, v949, v1013, v1194] (.node [v359, v474, v525, v941, v1013, v1194] .nil .nil) (.node [v359, v474, v525, v1013, v1156, v1194] .nil .nil))) (.node [v359, v474, v528, v705, v1013, v1194] (.node [v359, v474, v526, v705, v1013, v1194] (.node [v359, v474, v525, v1013, v1249, v1461] (.node [v359, v474, v525, v1013, v1194, v1461] .nil .nil) .nil) (.node [v359, v474, v527, v705, v1013, v1194] .nil .nil)) (.node [v359, v474, v530, v705, v1013, v1194] (.node [v359, v474, v529, v1013, v1194, v1461] .nil .nil) (.node [v359, v474, v531, v1013, v1194, v1461] .nil .nil)))) (.node [v359, v474, v539, v1013, v1194, v1461] (.node [v359, v474, v539, v691, v1013, v1194] (.node [v359, v474, v537, v1013, v1194, v1348] (.node [v359, v474, v536, v1013, v1194, v1348] (.node [v359, v474, v533, v1013, v1194, v1461] .nil .nil) .nil) (.node [v359, v474, v538, v1013, v1194, v1461] .nil .nil)) (.node [v359, v474, v539, v1013, v1194] (.node [v359, v474, v539, v705, v1013, v1194] .nil .nil) (.node [v359, v474, v539, v1013, v1194, v1348] .nil .nil))) (.node [v359, v474, v543, v705, v1013, v1194] (.node [v359, v474, v541, v705, v1013, v1194] (.node [v359, v474, v540, v705, v1013, v1194] .nil .nil) (.node [v359, v474, v542, v705, v1013, v1194] .nil .nil)) (.node [v359, v474, v544, v705, v1013, v1194] (.node [v359, v474, v544, v680, v1013, v1194] .nil .nil) (.node [v359, v474, v545, v705, v1013, v1194] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlllll_ok : everyKey (rowOK 4 level4) level5rlllll = true := by decide +kernel
def level5rllllr : BinaryTree (List W) := (.node [v359, v474, v560, v705, v1013, v1194] (.node [v359, v474, v551, v666, v1013, v1327] (.node [v359, v474, v548, v1013, v1327, v1348] (.node [v359, v474, v548, v705, v1013, v1348] (.node [v359, v474, v548, v666, v1013, v1348] (.node [v359, v474, v547, v705, v1013, v1194] .nil .nil) .nil) (.node [v359, v474, v548, v1013, v1194, v1348] .nil .nil)) (.node [v359, v474, v549, v705, v1013, v1348] (.node [v359, v474, v548, v1013, v1348] .nil .nil) (.node [v359, v474, v550, v705, v1013, v1194] .nil .nil))) (.node [v359, v474, v554, v705, v1013, v1194] (.node [v359, v474, v551, v705, v1013, v1483] (.node [v359, v474, v551, v705, v1013, v1194] (.node [v359, v474, v551, v672, v705, v1013] .nil .nil) .nil) (.node [v359, v474, v552, v705, v1013, v1194] .nil .nil)) (.node [v359, v474, v556, v705, v1013, v1194] (.node [v359, v474, v555, v705, v1013, v1194] .nil .nil) (.node [v359, v474, v557, v705, v1013, v1194] .nil .nil)))) (.node [v359, v474, v563, v1013, v1194, v1461] (.node [v359, v474, v562, v705, v1013, v1289] (.node [v359, v474, v562, v656, v1013, v1194] (.node [v359, v474, v562, v651, v705, v1013] (.node [v359, v474, v561, v705, v1013, v1194] .nil .nil) .nil) (.node [v359, v474, v562, v705, v1013, v1194] .nil .nil)) (.node [v359, v474, v563, v653, v1013, v1194] (.node [v359, v474, v562, v1013, v1194, v1461] .nil .nil) (.node [v359, v474, v563, v705, v1013, v1194] .nil .nil))) (.node [v359, v474, v573, v705, v1013, v1194] (.node [v359, v474, v569, v705, v1013, v1194] (.node [v359, v474, v565, v1013, v1194, v1461] .nil .nil) (.node [v359, v474, v570, v705, v1013, v1194] .nil .nil)) (.node [v359, v474, v579, v705, v1013, v1194] (.node [v359, v474, v578, v705, v1013, v1194] .nil .nil) (.node [v359, v474, v580, v705, v1013, v1194] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllllr_ok : everyKey (rowOK 4 level4) level5rllllr = true := by decide +kernel
def level5rllll : BinaryTree (List W) := .node [v359, v474, v546, v705, v1013, v1194] level5rlllll level5rllllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllll_ok : everyKey (rowOK 4 level4) level5rllll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlllll && everyKey (rowOK 4 level4) level5rllllr) = true
  rw [level5rlllll_ok, level5rllllr_ok]
  decide +kernel
def level5rlllrl : BinaryTree (List W) := (.node [v359, v474, v599, v705, v1013, v1253] (.node [v359, v474, v591, v630, v1194, v1348] (.node [v359, v474, v585, v705, v1013, v1194] (.node [v359, v474, v584, v705, v1013, v1194] (.node [v359, v474, v584, v640, v705, v1013] (.node [v359, v474, v583, v705, v1013, v1194] .nil .nil) .nil) (.node [v359, v474, v584, v705, v1013, v1320] .nil .nil)) (.node [v359, v474, v589, v705, v1013, v1249] (.node [v359, v474, v586, v705, v1013, v1194] .nil .nil) (.node [v359, v474, v590, v705, v1013, v1194] .nil .nil))) (.node [v359, v474, v598, v705, v1013, v1194] (.node [v359, v474, v591, v1159, v1194, v1348] (.node [v359, v474, v591, v1013, v1194, v1348] (.node [v359, v474, v591, v705, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v591, v1194, v1348] .nil .nil)) (.node [v359, v474, v599, v630, v1159, v1194] (.node [v359, v474, v599, v625, v705, v1013] .nil .nil) (.node [v359, v474, v599, v705, v1013, v1194] .nil .nil)))) (.node [v359, v474, v609, v705, v1013, v1194] (.node [v359, v474, v607, v705, v1013, v1194] (.node [v359, v474, v602, v705, v1013, v1194] (.node [v359, v474, v601, v705, v1013, v1194] (.node [v359, v474, v600, v705, v1013, v1194] .nil .nil) .nil) (.node [v359, v474, v604, v705, v1013, v1194] .nil .nil)) (.node [v359, v474, v608, v705, v1013, v1194] (.node [v359, v474, v608, v626, v705, v1013] .nil .nil) (.node [v359, v474, v608, v705, v1013, v1481] .nil .nil))) (.node [v359, v474, v613, v705, v1013, v1194] (.node [v359, v474, v611, v705, v1013, v1194] (.node [v359, v474, v610, v705, v1013, v1194] .nil .nil) (.node [v359, v474, v612, v705, v1013, v1194] .nil .nil)) (.node [v359, v474, v614, v705, v1110, v1194] (.node [v359, v474, v614, v705, v1013, v1278] .nil .nil) (.node [v359, v474, v614, v847, v1013, v1194] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlllrl_ok : everyKey (rowOK 4 level4) level5rlllrl = true := by decide +kernel
def level5rlllrr : BinaryTree (List W) := (.node [v359, v474, v648, v705, v1013, v1194] (.node [v359, v474, v630, v1159, v1194, v1461] (.node [v359, v474, v630, v847, v1013, v1194] (.node [v359, v474, v626, v705, v1013, v1348] (.node [v359, v474, v625, v705, v1013, v1348] (.node [v359, v474, v619, v847, v1013, v1194] .nil .nil) .nil) (.node [v359, v474, v627, v1159, v1194, v1348] .nil .nil)) (.node [v359, v474, v630, v1159, v1194, v1348] (.node [v359, v474, v630, v941, v1194, v1348] .nil .nil) (.node [v359, v474, v630, v1159, v1194, v1438] .nil .nil))) (.node [v359, v474, v642, v847, v1013, v1194] (.node [v359, v474, v634, v1159, v1194, v1348] (.node [v359, v474, v632, v705, v1013, v1194] .nil .nil) (.node [v359, v474, v640, v705, v1013, v1348] .nil .nil)) (.node [v359, v474, v645, v705, v1013, v1194] (.node [v359, v474, v642, v1127, v1194, v1348] .nil .nil) (.node [v359, v474, v647, v1159, v1194, v1348] .nil .nil)))) (.node [v359, v474, v656, v896, v1013, v1348] (.node [v359, v474, v653, v1013, v1194, v1461] (.node [v359, v474, v653, v847, v1013, v1194] (.node [v359, v474, v652, v1013, v1194, v1461] (.node [v359, v474, v651, v705, v1013, v1348] .nil .nil) .nil) (.node [v359, v474, v653, v1013, v1194, v1431] .nil .nil)) (.node [v359, v474, v656, v847, v1013, v1194] (.node [v359, v474, v654, v1013, v1194, v1461] .nil .nil) (.node [v359, v474, v656, v873, v1194, v1348] .nil .nil))) (.node [v359, v474, v656, v1110, v1194, v1348] (.node [v359, v474, v656, v1013, v1194, v1461] (.node [v359, v474, v656, v1013, v1194, v1348] .nil .nil) (.node [v359, v474, v656, v1013, v1278, v1348] .nil .nil)) (.node [v359, v474, v658, v1013, v1194, v1461] (.node [v359, v474, v657, v705, v1013, v1194] .nil .nil) (.node [v359, v474, v659, v1013, v1194, v1461] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlllrr_ok : everyKey (rowOK 4 level4) level5rlllrr = true := by decide +kernel
def level5rlllr : BinaryTree (List W) := .node [v359, v474, v615, v705, v1013, v1194] level5rlllrl level5rlllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlllr_ok : everyKey (rowOK 4 level4) level5rlllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlllrl && everyKey (rowOK 4 level4) level5rlllrr) = true
  rw [level5rlllrl_ok, level5rlllrr_ok]
  decide +kernel
def level5rlll : BinaryTree (List W) := .node [v359, v474, v581, v705, v1013, v1194] level5rllll level5rlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlll_ok : everyKey (rowOK 4 level4) level5rlll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rllll && everyKey (rowOK 4 level4) level5rlllr) = true
  rw [level5rllll_ok, level5rlllr_ok]
  decide +kernel
def level5rllrll : BinaryTree (List W) := (.node [v359, v474, v669, v705, v1013, v1348] (.node [v359, v474, v666, v738, v1013, v1348] (.node [v359, v474, v664, v705, v1194, v1348] (.node [v359, v474, v662, v1013, v1194, v1461] (.node [v359, v474, v661, v1013, v1194, v1348] (.node [v359, v474, v660, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v663, v1013, v1194, v1348] .nil .nil)) (.node [v359, v474, v666, v705, v1098, v1348] (.node [v359, v474, v666, v705, v1013, v1420] .nil .nil) (.node [v359, v474, v666, v711, v1013, v1348] .nil .nil))) (.node [v359, v474, v666, v1013, v1327, v1449] (.node [v359, v474, v666, v946, v1013, v1348] (.node [v359, v474, v666, v847, v1013, v1194] (.node [v359, v474, v666, v841, v1013, v1348] .nil .nil) .nil) (.node [v359, v474, v666, v1013, v1327, v1348] .nil .nil)) (.node [v359, v474, v668, v705, v1013, v1348] (.node [v359, v474, v666, v1013, v1327, v1461] .nil .nil) (.node [v359, v474, v669, v705, v708, v1013] .nil .nil)))) (.node [v359, v474, v674, v1013, v1194, v1348] (.node [v359, v474, v672, v705, v1013, v1461] (.node [v359, v474, v672, v705, v1013, v1249] (.node [v359, v474, v671, v705, v1013, v1348] (.node [v359, v474, v670, v705, v1013, v1194] .nil .nil) .nil) (.node [v359, v474, v672, v705, v1013, v1348] .nil .nil)) (.node [v359, v474, v673, v1013, v1194, v1461] (.node [v359, v474, v672, v705, v1013, v1483] .nil .nil) (.node [v359, v474, v673, v1013, v1327, v1348] .nil .nil))) (.node [v359, v474, v680, v827, v1013, v1348] (.node [v359, v474, v678, v705, v1013, v1194] (.node [v359, v474, v677, v1013, v1327, v1348] .nil .nil) (.node [v359, v474, v679, v1013, v1194, v1348] .nil .nil)) (.node [v359, v474, v680, v1013, v1194, v1348] (.node [v359, v474, v680, v837, v1013, v1194] .nil .nil) (.node [v359, v474, v680, v1013, v1194, v1414] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrll_ok : everyKey (rowOK 4 level4) level5rllrll = true := by decide +kernel
def level5rllrlr : BinaryTree (List W) := (.node [v359, v474, v694, v1013, v1194, v1461] (.node [v359, v474, v686, v1013, v1194, v1348] (.node [v359, v474, v683, v1013, v1194, v1461] (.node [v359, v474, v681, v1013, v1194, v1348] (.node [v359, v474, v680, v1013, v1301, v1348] (.node [v359, v474, v680, v1013, v1194, v1461] .nil .nil) .nil) (.node [v359, v474, v682, v705, v1013, v1348] .nil .nil)) (.node [v359, v474, v684, v1013, v1327, v1348] (.node [v359, v474, v684, v1013, v1194, v1461] .nil .nil) (.node [v359, v474, v685, v1013, v1194, v1348] .nil .nil))) (.node [v359, v474, v691, v847, v1013, v1194] (.node [v359, v474, v688, v1013, v1194, v1348] (.node [v359, v474, v687, v1013, v1194, v1461] .nil .nil) (.node [v359, v474, v689, v705, v1013, v1348] .nil .nil)) (.node [v359, v474, v692, v1013, v1194, v1461] (.node [v359, v474, v691, v1013, v1194, v1461] .nil .nil) (.node [v359, v474, v693, v1013, v1194, v1461] .nil .nil)))) (.node [v359, v474, v704, v1013, v1194, v1348] (.node [v359, v474, v700, v1013, v1194, v1461] (.node [v359, v474, v698, v1013, v1194, v1461] (.node [v359, v474, v697, v1013, v1194, v1461] (.node [v359, v474, v695, v1013, v1194, v1461] .nil .nil) .nil) (.node [v359, v474, v699, v1013, v1194, v1461] .nil .nil)) (.node [v359, v474, v702, v1013, v1194, v1461] (.node [v359, v474, v701, v1013, v1194, v1348] .nil .nil) (.node [v359, v474, v703, v1013, v1194, v1348] .nil .nil))) (.node [v359, v474, v705, v714, v1013, v1194] (.node [v359, v474, v705, v708, v1013, v1194] (.node [v359, v474, v705, v706, v1013, v1194] .nil .nil) (.node [v359, v474, v705, v712, v1013, v1194] .nil .nil)) (.node [v359, v474, v705, v727, v1013, v1348] (.node [v359, v474, v705, v715, v1013, v1194] .nil .nil) (.node [v359, v474, v705, v728, v1013, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrlr_ok : everyKey (rowOK 4 level4) level5rllrlr = true := by decide +kernel
def level5rllrl : BinaryTree (List W) := .node [v359, v474, v680, v1013, v1194, v1453] level5rllrll level5rllrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrl_ok : everyKey (rowOK 4 level4) level5rllrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rllrll && everyKey (rowOK 4 level4) level5rllrlr) = true
  rw [level5rllrll_ok, level5rllrlr_ok]
  decide +kernel
def level5rllrrl : BinaryTree (List W) := (.node [v359, v474, v705, v763, v1013, v1278] (.node [v359, v474, v705, v755, v1098, v1348] (.node [v359, v474, v705, v737, v1013, v1348] (.node [v359, v474, v705, v736, v1013, v1348] (.node [v359, v474, v705, v735, v1013, v1348] (.node [v359, v474, v705, v734, v1013, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v736, v1013, v1461] .nil .nil)) (.node [v359, v474, v705, v754, v1013, v1483] (.node [v359, v474, v705, v744, v1013, v1348] .nil .nil) (.node [v359, v474, v705, v755, v1013, v1420] .nil .nil))) (.node [v359, v474, v705, v759, v1013, v1348] (.node [v359, v474, v705, v758, v1013, v1348] (.node [v359, v474, v705, v757, v1013, v1348] (.node [v359, v474, v705, v756, v1013, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v758, v1013, v1461] .nil .nil)) (.node [v359, v474, v705, v763, v1013, v1227] (.node [v359, v474, v705, v759, v1013, v1461] .nil .nil) (.node [v359, v474, v705, v763, v1013, v1249] .nil .nil)))) (.node [v359, v474, v705, v780, v1013, v1194] (.node [v359, v474, v705, v776, v1013, v1348] (.node [v359, v474, v705, v764, v1013, v1194] (.node [v359, v474, v705, v763, v1110, v1194] (.node [v359, v474, v705, v763, v1013, v1311] .nil .nil) .nil) (.node [v359, v474, v705, v775, v1013, v1194] .nil .nil)) (.node [v359, v474, v705, v778, v1013, v1194] (.node [v359, v474, v705, v777, v1013, v1194] .nil .nil) (.node [v359, v474, v705, v779, v1013, v1348] .nil .nil))) (.node [v359, v474, v705, v784, v1013, v1348] (.node [v359, v474, v705, v782, v1013, v1348] (.node [v359, v474, v705, v781, v1013, v1194] .nil .nil) (.node [v359, v474, v705, v783, v1013, v1348] .nil .nil)) (.node [v359, v474, v705, v786, v1013, v1348] (.node [v359, v474, v705, v785, v1013, v1348] .nil .nil) (.node [v359, v474, v705, v787, v792, v1013] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrrl_ok : everyKey (rowOK 4 level4) level5rllrrl = true := by decide +kernel
def level5rllrrr : BinaryTree (List W) := (.node [v359, v474, v705, v823, v1013, v1194] (.node [v359, v474, v705, v793, v1013, v1194] (.node [v359, v474, v705, v790, v1013, v1194] (.node [v359, v474, v705, v788, v1013, v1348] (.node [v359, v474, v705, v787, v1013, v1461] (.node [v359, v474, v705, v787, v1013, v1387] .nil .nil) .nil) (.node [v359, v474, v705, v789, v1013, v1194] .nil .nil)) (.node [v359, v474, v705, v792, v1013, v1194] (.node [v359, v474, v705, v791, v1013, v1194] .nil .nil) (.node [v359, v474, v705, v792, v1013, v1305] .nil .nil))) (.node [v359, v474, v705, v802, v1013, v1194] (.node [v359, v474, v705, v795, v1013, v1194] (.node [v359, v474, v705, v794, v1013, v1194] .nil .nil) (.node [v359, v474, v705, v801, v1013, v1194] .nil .nil)) (.node [v359, v474, v705, v806, v1194, v1348] (.node [v359, v474, v705, v804, v1013, v1194] .nil .nil) (.node [v359, v474, v705, v816, v1013, v1348] .nil .nil)))) (.node [v359, v474, v705, v829, v1013, v1348] (.node [v359, v474, v705, v827, v1013, v1461] (.node [v359, v474, v705, v827, v1013, v1348] (.node [v359, v474, v705, v827, v837, v1013] (.node [v359, v474, v705, v824, v1013, v1194] .nil .nil) .nil) (.node [v359, v474, v705, v827, v1013, v1414] .nil .nil)) (.node [v359, v474, v705, v828, v1013, v1348] (.node [v359, v474, v705, v828, v842, v1013] .nil .nil) (.node [v359, v474, v705, v828, v1013, v1461] .nil .nil))) (.node [v359, v474, v705, v833, v1013, v1348] (.node [v359, v474, v705, v831, v1013, v1348] (.node [v359, v474, v705, v830, v1013, v1348] .nil .nil) (.node [v359, v474, v705, v832, v1013, v1348] .nil .nil)) (.node [v359, v474, v705, v835, v1013, v1194] (.node [v359, v474, v705, v834, v1013, v1194] .nil .nil) (.node [v359, v474, v705, v837, v1013, v1194] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrrr_ok : everyKey (rowOK 4 level4) level5rllrrr = true := by decide +kernel
def level5rllrr : BinaryTree (List W) := .node [v359, v474, v705, v787, v1013, v1348] level5rllrrl level5rllrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrr_ok : everyKey (rowOK 4 level4) level5rllrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rllrrl && everyKey (rowOK 4 level4) level5rllrrr) = true
  rw [level5rllrrl_ok, level5rllrrr_ok]
  decide +kernel
def level5rllr : BinaryTree (List W) := .node [v359, v474, v705, v733, v1013, v1348] level5rllrl level5rllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllr_ok : everyKey (rowOK 4 level4) level5rllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rllrl && everyKey (rowOK 4 level4) level5rllrr) = true
  rw [level5rllrl_ok, level5rllrr_ok]
  decide +kernel
def level5rll : BinaryTree (List W) := .node [v359, v474, v659, v1159, v1194, v1348] level5rlll level5rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rll_ok : everyKey (rowOK 4 level4) level5rll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlll && everyKey (rowOK 4 level4) level5rllr) = true
  rw [level5rlll_ok, level5rllr_ok]
  decide +kernel
def level5rlrlll : BinaryTree (List W) := (.node [v359, v474, v705, v861, v1337, v1348] (.node [v359, v474, v705, v847, v1013, v1194] (.node [v359, v474, v705, v845, v1013, v1194] (.node [v359, v474, v705, v843, v1013, v1194] (.node [v359, v474, v705, v842, v1013, v1194] (.node [v359, v474, v705, v839, v1013, v1194] .nil .nil) .nil) (.node [v359, v474, v705, v844, v1013, v1194] .nil .nil)) (.node [v359, v474, v705, v847, v873, v1194] (.node [v359, v474, v705, v846, v1013, v1194] .nil .nil) (.node [v359, v474, v705, v847, v896, v1013] .nil .nil))) (.node [v359, v474, v705, v852, v1013, v1194] (.node [v359, v474, v705, v850, v1013, v1194] (.node [v359, v474, v705, v847, v1110, v1194] (.node [v359, v474, v705, v847, v1013, v1278] .nil .nil) .nil) (.node [v359, v474, v705, v851, v1013, v1194] .nil .nil)) (.node [v359, v474, v705, v858, v1013, v1194] (.node [v359, v474, v705, v857, v1013, v1194] .nil .nil) (.node [v359, v474, v705, v860, v1013, v1194] .nil .nil)))) (.node [v359, v474, v705, v869, v1194, v1348] (.node [v359, v474, v705, v865, v1301, v1348] (.node [v359, v474, v705, v865, v1245, v1348] (.node [v359, v474, v705, v865, v1194, v1414] (.node [v359, v474, v705, v862, v1013, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v865, v1263, v1348] .nil .nil)) (.node [v359, v474, v705, v867, v1194, v1348] (.node [v359, v474, v705, v866, v1194, v1348] .nil .nil) (.node [v359, v474, v705, v868, v1194, v1348] .nil .nil))) (.node [v359, v474, v705, v870, v1194, v1461] (.node [v359, v474, v705, v870, v1194, v1348] (.node [v359, v474, v705, v870, v920, v1348] .nil .nil) (.node [v359, v474, v705, v870, v1194, v1425] .nil .nil)) (.node [v359, v474, v705, v871, v1194, v1348] (.node [v359, v474, v705, v870, v1268, v1348] .nil .nil) (.node [v359, v474, v705, v871, v1194, v1461] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrlll_ok : everyKey (rowOK 4 level4) level5rlrlll = true := by decide +kernel
def level5rlrllr : BinaryTree (List W) := (.node [v359, v474, v705, v882, v1194, v1348] (.node [v359, v474, v705, v877, v942, v1348] (.node [v359, v474, v705, v873, v1194, v1474] (.node [v359, v474, v705, v873, v1194, v1348] (.node [v359, v474, v705, v873, v1110, v1194] (.node [v359, v474, v705, v873, v896, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v873, v1194, v1461] .nil .nil)) (.node [v359, v474, v705, v874, v1013, v1194] (.node [v359, v474, v705, v873, v1278, v1348] .nil .nil) (.node [v359, v474, v705, v875, v1194, v1348] .nil .nil))) (.node [v359, v474, v705, v879, v1194, v1348] (.node [v359, v474, v705, v877, v1194, v1473] (.node [v359, v474, v705, v877, v1194, v1461] (.node [v359, v474, v705, v877, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v878, v1194, v1348] .nil .nil)) (.node [v359, v474, v705, v881, v1194, v1348] (.node [v359, v474, v705, v880, v1194, v1348] .nil .nil) (.node [v359, v474, v705, v881, v1194, v1461] .nil .nil)))) (.node [v359, v474, v705, v895, v1013, v1348] (.node [v359, v474, v705, v892, v1013, v1420] (.node [v359, v474, v705, v885, v1194, v1348] (.node [v359, v474, v705, v884, v1194, v1348] (.node [v359, v474, v705, v883, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v889, v1194, v1348] .nil .nil)) (.node [v359, v474, v705, v893, v1013, v1348] (.node [v359, v474, v705, v892, v1098, v1348] .nil .nil) (.node [v359, v474, v705, v894, v1013, v1348] .nil .nil))) (.node [v359, v474, v705, v896, v1013, v1461] (.node [v359, v474, v705, v896, v1013, v1278] (.node [v359, v474, v705, v895, v1013, v1461] .nil .nil) (.node [v359, v474, v705, v896, v1013, v1348] .nil .nil)) (.node [v359, v474, v705, v896, v1110, v1348] (.node [v359, v474, v705, v896, v1013, v1483] .nil .nil) (.node [v359, v474, v705, v897, v1013, v1194] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrllr_ok : everyKey (rowOK 4 level4) level5rlrllr = true := by decide +kernel
def level5rlrll : BinaryTree (List W) := .node [v359, v474, v705, v872, v1194, v1348] level5rlrlll level5rlrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrll_ok : everyKey (rowOK 4 level4) level5rlrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrlll && everyKey (rowOK 4 level4) level5rlrllr) = true
  rw [level5rlrlll_ok, level5rlrllr_ok]
  decide +kernel
def level5rlrlrl : BinaryTree (List W) := (.node [v359, v474, v705, v944, v1013, v1348] (.node [v359, v474, v705, v920, v1081, v1348] (.node [v359, v474, v705, v919, v1013, v1348] (.node [v359, v474, v705, v917, v1013, v1348] (.node [v359, v474, v705, v915, v1013, v1348] (.node [v359, v474, v705, v914, v1013, v1194] .nil .nil) .nil) (.node [v359, v474, v705, v918, v1013, v1348] .nil .nil)) (.node [v359, v474, v705, v920, v1013, v1426] (.node [v359, v474, v705, v920, v1013, v1348] .nil .nil) (.node [v359, v474, v705, v920, v1013, v1461] .nil .nil))) (.node [v359, v474, v705, v942, v1013, v1348] (.node [v359, v474, v705, v930, v1013, v1348] (.node [v359, v474, v705, v922, v1013, v1348] (.node [v359, v474, v705, v921, v1013, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v932, v1013, v1348] .nil .nil)) (.node [v359, v474, v705, v942, v1013, v1482] (.node [v359, v474, v705, v942, v1013, v1461] .nil .nil) (.node [v359, v474, v705, v943, v1013, v1348] .nil .nil)))) (.node [v359, v474, v705, v958, v1058, v1348] (.node [v359, v474, v705, v954, v1013, v1348] (.node [v359, v474, v705, v952, v1013, v1348] (.node [v359, v474, v705, v951, v1013, v1461] (.node [v359, v474, v705, v951, v1013, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v953, v1013, v1348] .nil .nil)) (.node [v359, v474, v705, v958, v1013, v1420] (.node [v359, v474, v705, v955, v1013, v1348] .nil .nil) (.node [v359, v474, v705, v958, v1023, v1348] .nil .nil))) (.node [v359, v474, v705, v958, v1301, v1348] (.node [v359, v474, v705, v958, v1133, v1348] (.node [v359, v474, v705, v958, v1098, v1348] .nil .nil) (.node [v359, v474, v705, v958, v1245, v1348] .nil .nil)) (.node [v359, v474, v705, v958, v1337, v1461] (.node [v359, v474, v705, v958, v1337, v1348] .nil .nil) (.node [v359, v474, v705, v958, v1342, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrlrl_ok : everyKey (rowOK 4 level4) level5rlrlrl = true := by decide +kernel
def level5rlrlrr : BinaryTree (List W) := (.node [v359, v474, v705, v971, v1194, v1348] (.node [v359, v474, v705, v970, v1194, v1246] (.node [v359, v474, v705, v964, v1013, v1461] (.node [v359, v474, v705, v963, v1013, v1348] (.node [v359, v474, v705, v962, v1013, v1348] (.node [v359, v474, v705, v960, v1013, v1461] .nil .nil) .nil) (.node [v359, v474, v705, v964, v1013, v1348] .nil .nil)) (.node [v359, v474, v705, v968, v1194, v1348] (.node [v359, v474, v705, v966, v1194, v1348] .nil .nil) (.node [v359, v474, v705, v969, v1194, v1348] .nil .nil))) (.node [v359, v474, v705, v970, v1245, v1348] (.node [v359, v474, v705, v970, v1194, v1362] (.node [v359, v474, v705, v970, v1194, v1348] .nil .nil) (.node [v359, v474, v705, v970, v1194, v1461] .nil .nil)) (.node [v359, v474, v705, v970, v1337, v1348] (.node [v359, v474, v705, v970, v1327, v1348] .nil .nil) (.node [v359, v474, v705, v970, v1348, v1483] .nil .nil)))) (.node [v359, v474, v705, v976, v1295, v1348] (.node [v359, v474, v705, v976, v1094, v1194] (.node [v359, v474, v705, v975, v1194, v1348] (.node [v359, v474, v705, v974, v1013, v1348] (.node [v359, v474, v705, v973, v1337, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v976, v1087, v1348] .nil .nil)) (.node [v359, v474, v705, v976, v1194, v1373] (.node [v359, v474, v705, v976, v1194, v1348] .nil .nil) (.node [v359, v474, v705, v976, v1194, v1461] .nil .nil))) (.node [v359, v474, v705, v979, v1301, v1348] (.node [v359, v474, v705, v979, v1194, v1348] (.node [v359, v474, v705, v977, v1194, v1348] .nil .nil) (.node [v359, v474, v705, v979, v1194, v1461] .nil .nil)) (.node [v359, v474, v705, v979, v1337, v1348] (.node [v359, v474, v705, v979, v1327, v1348] .nil .nil) (.node [v359, v474, v705, v979, v1348, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrlrr_ok : everyKey (rowOK 4 level4) level5rlrlrr = true := by decide +kernel
def level5rlrlr : BinaryTree (List W) := .node [v359, v474, v705, v960, v1013, v1348] level5rlrlrl level5rlrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrlr_ok : everyKey (rowOK 4 level4) level5rlrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrlrl && everyKey (rowOK 4 level4) level5rlrlrr) = true
  rw [level5rlrlrl_ok, level5rlrlrr_ok]
  decide +kernel
def level5rlrl : BinaryTree (List W) := .node [v359, v474, v705, v898, v1013, v1348] level5rlrll level5rlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrl_ok : everyKey (rowOK 4 level4) level5rlrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrll && everyKey (rowOK 4 level4) level5rlrlr) = true
  rw [level5rlrll_ok, level5rlrlr_ok]
  decide +kernel
def level5rlrrll : BinaryTree (List W) := (.node [v359, v474, v705, v993, v1194, v1348] (.node [v359, v474, v705, v984, v1258, v1348] (.node [v359, v474, v705, v984, v1146, v1194] (.node [v359, v474, v705, v983, v1013, v1348] (.node [v359, v474, v705, v982, v1194, v1348] (.node [v359, v474, v705, v981, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v984, v1139, v1348] .nil .nil)) (.node [v359, v474, v705, v984, v1194, v1431] (.node [v359, v474, v705, v984, v1194, v1348] .nil .nil) (.node [v359, v474, v705, v984, v1194, v1461] .nil .nil))) (.node [v359, v474, v705, v990, v1063, v1194] (.node [v359, v474, v705, v987, v1194, v1348] (.node [v359, v474, v705, v986, v1194, v1348] (.node [v359, v474, v705, v985, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v989, v1194, v1348] .nil .nil)) (.node [v359, v474, v705, v990, v1194, v1474] (.node [v359, v474, v705, v990, v1110, v1194] .nil .nil) (.node [v359, v474, v705, v992, v1194, v1474] .nil .nil)))) (.node [v359, v474, v705, v1007, v1194, v1348] (.node [v359, v474, v705, v1001, v1194, v1474] (.node [v359, v474, v705, v998, v1194, v1348] (.node [v359, v474, v705, v997, v1194, v1348] (.node [v359, v474, v705, v996, v1194, v1474] .nil .nil) .nil) (.node [v359, v474, v705, v999, v1194, v1348] .nil .nil)) (.node [v359, v474, v705, v1003, v1194, v1348] (.node [v359, v474, v705, v1001, v1194, v1480] .nil .nil) (.node [v359, v474, v705, v1006, v1194, v1348] .nil .nil))) (.node [v359, v474, v705, v1012, v1194, v1348] (.node [v359, v474, v705, v1010, v1194, v1348] (.node [v359, v474, v705, v1008, v1194, v1348] .nil .nil) (.node [v359, v474, v705, v1011, v1194, v1348] .nil .nil)) (.node [v359, v474, v705, v1013, v1041, v1348] (.node [v359, v474, v705, v1012, v1194, v1461] .nil .nil) (.node [v359, v474, v705, v1013, v1042, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrll_ok : everyKey (rowOK 4 level4) level5rlrrll = true := by decide +kernel
def level5rlrrlr : BinaryTree (List W) := (.node [v359, v474, v705, v1013, v1065, v1194] (.node [v359, v474, v705, v1013, v1053, v1194] (.node [v359, v474, v705, v1013, v1050, v1378] (.node [v359, v474, v705, v1013, v1050, v1060] (.node [v359, v474, v705, v1013, v1049, v1348] (.node [v359, v474, v705, v1013, v1048, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1050, v1348] .nil .nil)) (.node [v359, v474, v705, v1013, v1051, v1348] (.node [v359, v474, v705, v1013, v1050, v1461] .nil .nil) (.node [v359, v474, v705, v1013, v1052, v1194] .nil .nil))) (.node [v359, v474, v705, v1013, v1059, v1194] (.node [v359, v474, v705, v1013, v1055, v1194] (.node [v359, v474, v705, v1013, v1054, v1194] .nil .nil) (.node [v359, v474, v705, v1013, v1056, v1194] .nil .nil)) (.node [v359, v474, v705, v1013, v1060, v1225] (.node [v359, v474, v705, v1013, v1060, v1194] .nil .nil) (.node [v359, v474, v705, v1013, v1061, v1194] .nil .nil)))) (.node [v359, v474, v705, v1013, v1087, v1348] (.node [v359, v474, v705, v1013, v1084, v1461] (.node [v359, v474, v705, v1013, v1084, v1101] (.node [v359, v474, v705, v1013, v1083, v1194] (.node [v359, v474, v705, v1013, v1074, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1084, v1348] .nil .nil)) (.node [v359, v474, v705, v1013, v1086, v1348] (.node [v359, v474, v705, v1013, v1085, v1348] .nil .nil) (.node [v359, v474, v705, v1013, v1087, v1094] .nil .nil))) (.node [v359, v474, v705, v1013, v1089, v1348] (.node [v359, v474, v705, v1013, v1087, v1461] (.node [v359, v474, v705, v1013, v1087, v1373] .nil .nil) (.node [v359, v474, v705, v1013, v1088, v1348] .nil .nil)) (.node [v359, v474, v705, v1013, v1092, v1194] (.node [v359, v474, v705, v1013, v1091, v1194] .nil .nil) (.node [v359, v474, v705, v1013, v1094, v1194] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrlr_ok : everyKey (rowOK 4 level4) level5rlrrlr = true := by decide +kernel
def level5rlrrl : BinaryTree (List W) := .node [v359, v474, v705, v1013, v1047, v1348] level5rlrrll level5rlrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrl_ok : everyKey (rowOK 4 level4) level5rlrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrrll && everyKey (rowOK 4 level4) level5rlrrlr) = true
  rw [level5rlrrll_ok, level5rlrrlr_ok]
  decide +kernel
def level5rlrrrl : BinaryTree (List W) := (.node [v359, v474, v705, v1013, v1139, v1461] (.node [v359, v474, v705, v1013, v1116, v1194] (.node [v359, v474, v705, v1013, v1104, v1194] (.node [v359, v474, v705, v1013, v1102, v1194] (.node [v359, v474, v705, v1013, v1101, v1194] (.node [v359, v474, v705, v1013, v1095, v1194] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1103, v1194] .nil .nil)) (.node [v359, v474, v705, v1013, v1107, v1194] (.node [v359, v474, v705, v1013, v1105, v1194] .nil .nil) (.node [v359, v474, v705, v1013, v1115, v1194] .nil .nil))) (.node [v359, v474, v705, v1013, v1131, v1348] (.node [v359, v474, v705, v1013, v1129, v1461] (.node [v359, v474, v705, v1013, v1129, v1348] (.node [v359, v474, v705, v1013, v1118, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1130, v1348] .nil .nil)) (.node [v359, v474, v705, v1013, v1139, v1348] (.node [v359, v474, v705, v1013, v1139, v1146] .nil .nil) (.node [v359, v474, v705, v1013, v1139, v1431] .nil .nil)))) (.node [v359, v474, v705, v1013, v1148, v1194] (.node [v359, v474, v705, v1013, v1144, v1194] (.node [v359, v474, v705, v1013, v1142, v1348] (.node [v359, v474, v705, v1013, v1141, v1348] (.node [v359, v474, v705, v1013, v1140, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1143, v1194] .nil .nil)) (.node [v359, v474, v705, v1013, v1146, v1258] (.node [v359, v474, v705, v1013, v1146, v1194] .nil .nil) (.node [v359, v474, v705, v1013, v1147, v1194] .nil .nil))) (.node [v359, v474, v705, v1013, v1161, v1348] (.node [v359, v474, v705, v1013, v1150, v1194] (.node [v359, v474, v705, v1013, v1149, v1194] .nil .nil) (.node [v359, v474, v705, v1013, v1152, v1348] .nil .nil)) (.node [v359, v474, v705, v1013, v1164, v1348] (.node [v359, v474, v705, v1013, v1163, v1194] .nil .nil) (.node [v359, v474, v705, v1013, v1166, v1249] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrrl_ok : everyKey (rowOK 4 level4) level5rlrrrl = true := by decide +kernel
def level5rlrrrr : BinaryTree (List W) := (.node [v359, v474, v705, v1013, v1185, v1348] (.node [v359, v474, v705, v1013, v1177, v1487] (.node [v359, v474, v705, v1013, v1173, v1348] (.node [v359, v474, v705, v1013, v1170, v1348] (.node [v359, v474, v705, v1013, v1168, v1483] (.node [v359, v474, v705, v1013, v1166, v1483] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1172, v1483] .nil .nil)) (.node [v359, v474, v705, v1013, v1175, v1348] (.node [v359, v474, v705, v1013, v1174, v1348] .nil .nil) (.node [v359, v474, v705, v1013, v1177, v1483] .nil .nil))) (.node [v359, v474, v705, v1013, v1180, v1348] (.node [v359, v474, v705, v1013, v1178, v1461] (.node [v359, v474, v705, v1013, v1178, v1348] .nil .nil) (.node [v359, v474, v705, v1013, v1179, v1348] .nil .nil)) (.node [v359, v474, v705, v1013, v1183, v1348] (.node [v359, v474, v705, v1013, v1182, v1348] .nil .nil) (.node [v359, v474, v705, v1013, v1183, v1461] .nil .nil)))) (.node [v359, v474, v705, v1013, v1194, v1234] (.node [v359, v474, v705, v1013, v1191, v1348] (.node [v359, v474, v705, v1013, v1188, v1348] (.node [v359, v474, v705, v1013, v1187, v1348] (.node [v359, v474, v705, v1013, v1186, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1190, v1348] .nil .nil)) (.node [v359, v474, v705, v1013, v1193, v1348] (.node [v359, v474, v705, v1013, v1192, v1348] .nil .nil) (.node [v359, v474, v705, v1013, v1193, v1461] .nil .nil))) (.node [v359, v474, v705, v1013, v1194, v1271] (.node [v359, v474, v705, v1013, v1194, v1247] (.node [v359, v474, v705, v1013, v1194, v1246] .nil .nil) (.node [v359, v474, v705, v1013, v1194, v1252] .nil .nil)) (.node [v359, v474, v705, v1013, v1194, v1273] (.node [v359, v474, v705, v1013, v1194, v1272] .nil .nil) (.node [v359, v474, v705, v1013, v1194, v1275] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrrr_ok : everyKey (rowOK 4 level4) level5rlrrrr = true := by decide +kernel
def level5rlrrr : BinaryTree (List W) := .node [v359, v474, v705, v1013, v1166, v1278] level5rlrrrl level5rlrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrr_ok : everyKey (rowOK 4 level4) level5rlrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrrrl && everyKey (rowOK 4 level4) level5rlrrrr) = true
  rw [level5rlrrrl_ok, level5rlrrrr_ok]
  decide +kernel
def level5rlrr : BinaryTree (List W) := .node [v359, v474, v705, v1013, v1094, v1295] level5rlrrl level5rlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrr_ok : everyKey (rowOK 4 level4) level5rlrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrrl && everyKey (rowOK 4 level4) level5rlrrr) = true
  rw [level5rlrrl_ok, level5rlrrr_ok]
  decide +kernel
def level5rlr : BinaryTree (List W) := .node [v359, v474, v705, v980, v1194, v1348] level5rlrl level5rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlr_ok : everyKey (rowOK 4 level4) level5rlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrl && everyKey (rowOK 4 level4) level5rlrr) = true
  rw [level5rlrl_ok, level5rlrr_ok]
  decide +kernel
def level5rl : BinaryTree (List W) := .node [v359, v474, v705, v837, v1013, v1301] level5rll level5rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rl_ok : everyKey (rowOK 4 level4) level5rl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rll && everyKey (rowOK 4 level4) level5rlr) = true
  rw [level5rll_ok, level5rlr_ok]
  decide +kernel
def level5rrllll : BinaryTree (List W) := (.node [v359, v474, v705, v1013, v1194, v1350] (.node [v359, v474, v705, v1013, v1194, v1329] (.node [v359, v474, v705, v1013, v1194, v1318] (.node [v359, v474, v705, v1013, v1194, v1288] (.node [v359, v474, v705, v1013, v1194, v1287] (.node [v359, v474, v705, v1013, v1194, v1284] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1194, v1290] .nil .nil)) (.node [v359, v474, v705, v1013, v1194, v1321] (.node [v359, v474, v705, v1013, v1194, v1319] .nil .nil) (.node [v359, v474, v705, v1013, v1194, v1328] .nil .nil))) (.node [v359, v474, v705, v1013, v1194, v1346] (.node [v359, v474, v705, v1013, v1194, v1344] (.node [v359, v474, v705, v1013, v1194, v1339] (.node [v359, v474, v705, v1013, v1194, v1338] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1194, v1345] .nil .nil)) (.node [v359, v474, v705, v1013, v1194, v1348] (.node [v359, v474, v705, v1013, v1194, v1347] .nil .nil) (.node [v359, v474, v705, v1013, v1194, v1349] .nil .nil)))) (.node [v359, v474, v705, v1013, v1194, v1361] (.node [v359, v474, v705, v1013, v1194, v1356] (.node [v359, v474, v705, v1013, v1194, v1354] (.node [v359, v474, v705, v1013, v1194, v1352] (.node [v359, v474, v705, v1013, v1194, v1351] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1194, v1355] .nil .nil)) (.node [v359, v474, v705, v1013, v1194, v1358] (.node [v359, v474, v705, v1013, v1194, v1357] .nil .nil) (.node [v359, v474, v705, v1013, v1194, v1359] .nil .nil))) (.node [v359, v474, v705, v1013, v1194, v1367] (.node [v359, v474, v705, v1013, v1194, v1364] (.node [v359, v474, v705, v1013, v1194, v1362] .nil .nil) (.node [v359, v474, v705, v1013, v1194, v1365] .nil .nil)) (.node [v359, v474, v705, v1013, v1194, v1369] (.node [v359, v474, v705, v1013, v1194, v1368] .nil .nil) (.node [v359, v474, v705, v1013, v1194, v1370] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrllll_ok : everyKey (rowOK 4 level4) level5rrllll = true := by decide +kernel
def level5rrlllr : BinaryTree (List W) := (.node [v359, v474, v705, v1013, v1194, v1391] (.node [v359, v474, v705, v1013, v1194, v1382] (.node [v359, v474, v705, v1013, v1194, v1377] (.node [v359, v474, v705, v1013, v1194, v1374] (.node [v359, v474, v705, v1013, v1194, v1373] (.node [v359, v474, v705, v1013, v1194, v1372] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1194, v1375] .nil .nil)) (.node [v359, v474, v705, v1013, v1194, v1379] (.node [v359, v474, v705, v1013, v1194, v1378] .nil .nil) (.node [v359, v474, v705, v1013, v1194, v1380] .nil .nil))) (.node [v359, v474, v705, v1013, v1194, v1387] (.node [v359, v474, v705, v1013, v1194, v1385] (.node [v359, v474, v705, v1013, v1194, v1384] (.node [v359, v474, v705, v1013, v1194, v1383] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1194, v1386] .nil .nil)) (.node [v359, v474, v705, v1013, v1194, v1389] (.node [v359, v474, v705, v1013, v1194, v1388] .nil .nil) (.node [v359, v474, v705, v1013, v1194, v1390] .nil .nil)))) (.node [v359, v474, v705, v1013, v1194, v1400] (.node [v359, v474, v705, v1013, v1194, v1396] (.node [v359, v474, v705, v1013, v1194, v1394] (.node [v359, v474, v705, v1013, v1194, v1393] (.node [v359, v474, v705, v1013, v1194, v1392] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1194, v1395] .nil .nil)) (.node [v359, v474, v705, v1013, v1194, v1398] (.node [v359, v474, v705, v1013, v1194, v1397] .nil .nil) (.node [v359, v474, v705, v1013, v1194, v1399] .nil .nil))) (.node [v359, v474, v705, v1013, v1194, v1404] (.node [v359, v474, v705, v1013, v1194, v1402] (.node [v359, v474, v705, v1013, v1194, v1401] .nil .nil) (.node [v359, v474, v705, v1013, v1194, v1403] .nil .nil)) (.node [v359, v474, v705, v1013, v1194, v1406] (.node [v359, v474, v705, v1013, v1194, v1405] .nil .nil) (.node [v359, v474, v705, v1013, v1194, v1407] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlllr_ok : everyKey (rowOK 4 level4) level5rrlllr = true := by decide +kernel
def level5rrlll : BinaryTree (List W) := .node [v359, v474, v705, v1013, v1194, v1371] level5rrllll level5rrlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlll_ok : everyKey (rowOK 4 level4) level5rrlll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrllll && everyKey (rowOK 4 level4) level5rrlllr) = true
  rw [level5rrllll_ok, level5rrlllr_ok]
  decide +kernel
def level5rrllrl : BinaryTree (List W) := (.node [v359, v474, v705, v1013, v1194, v1433] (.node [v359, v474, v705, v1013, v1194, v1422] (.node [v359, v474, v705, v1013, v1194, v1418] (.node [v359, v474, v705, v1013, v1194, v1414] (.node [v359, v474, v705, v1013, v1194, v1412] (.node [v359, v474, v705, v1013, v1194, v1411] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1194, v1415] .nil .nil)) (.node [v359, v474, v705, v1013, v1194, v1420] (.node [v359, v474, v705, v1013, v1194, v1419] .nil .nil) (.node [v359, v474, v705, v1013, v1194, v1421] .nil .nil))) (.node [v359, v474, v705, v1013, v1194, v1428] (.node [v359, v474, v705, v1013, v1194, v1426] (.node [v359, v474, v705, v1013, v1194, v1425] (.node [v359, v474, v705, v1013, v1194, v1423] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1194, v1427] .nil .nil)) (.node [v359, v474, v705, v1013, v1194, v1431] (.node [v359, v474, v705, v1013, v1194, v1429] .nil .nil) (.node [v359, v474, v705, v1013, v1194, v1432] .nil .nil)))) (.node [v359, v474, v705, v1013, v1194, v1444] (.node [v359, v474, v705, v1013, v1194, v1439] (.node [v359, v474, v705, v1013, v1194, v1436] (.node [v359, v474, v705, v1013, v1194, v1435] (.node [v359, v474, v705, v1013, v1194, v1434] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1194, v1438] .nil .nil)) (.node [v359, v474, v705, v1013, v1194, v1442] (.node [v359, v474, v705, v1013, v1194, v1440] .nil .nil) (.node [v359, v474, v705, v1013, v1194, v1443] .nil .nil))) (.node [v359, v474, v705, v1013, v1194, v1448] (.node [v359, v474, v705, v1013, v1194, v1446] (.node [v359, v474, v705, v1013, v1194, v1445] .nil .nil) (.node [v359, v474, v705, v1013, v1194, v1447] .nil .nil)) (.node [v359, v474, v705, v1013, v1194, v1450] (.node [v359, v474, v705, v1013, v1194, v1449] .nil .nil) (.node [v359, v474, v705, v1013, v1194, v1451] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrllrl_ok : everyKey (rowOK 4 level4) level5rrllrl = true := by decide +kernel
def level5rrllrr : BinaryTree (List W) := (.node [v359, v474, v705, v1013, v1194, v1486] (.node [v359, v474, v705, v1013, v1194, v1462] (.node [v359, v474, v705, v1013, v1194, v1457] (.node [v359, v474, v705, v1013, v1194, v1455] (.node [v359, v474, v705, v1013, v1194, v1454] (.node [v359, v474, v705, v1013, v1194, v1453] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1194, v1456] .nil .nil)) (.node [v359, v474, v705, v1013, v1194, v1460] (.node [v359, v474, v705, v1013, v1194, v1459] .nil .nil) (.node [v359, v474, v705, v1013, v1194, v1461] .nil .nil))) (.node [v359, v474, v705, v1013, v1194, v1466] (.node [v359, v474, v705, v1013, v1194, v1464] (.node [v359, v474, v705, v1013, v1194, v1463] .nil .nil) (.node [v359, v474, v705, v1013, v1194, v1465] .nil .nil)) (.node [v359, v474, v705, v1013, v1194, v1479] (.node [v359, v474, v705, v1013, v1194, v1473] .nil .nil) (.node [v359, v474, v705, v1013, v1194, v1482] .nil .nil)))) (.node [v359, v474, v705, v1013, v1203, v1348] (.node [v359, v474, v705, v1013, v1198, v1461] (.node [v359, v474, v705, v1013, v1197, v1348] (.node [v359, v474, v705, v1013, v1196, v1348] (.node [v359, v474, v705, v1013, v1195, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1198, v1348] .nil .nil)) (.node [v359, v474, v705, v1013, v1200, v1348] (.node [v359, v474, v705, v1013, v1199, v1348] .nil .nil) (.node [v359, v474, v705, v1013, v1201, v1348] .nil .nil))) (.node [v359, v474, v705, v1013, v1211, v1348] (.node [v359, v474, v705, v1013, v1205, v1348] (.node [v359, v474, v705, v1013, v1204, v1348] .nil .nil) (.node [v359, v474, v705, v1013, v1209, v1348] .nil .nil)) (.node [v359, v474, v705, v1013, v1213, v1348] (.node [v359, v474, v705, v1013, v1212, v1348] .nil .nil) (.node [v359, v474, v705, v1013, v1214, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrllrr_ok : everyKey (rowOK 4 level4) level5rrllrr = true := by decide +kernel
def level5rrllr : BinaryTree (List W) := .node [v359, v474, v705, v1013, v1194, v1452] level5rrllrl level5rrllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrllr_ok : everyKey (rowOK 4 level4) level5rrllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrllrl && everyKey (rowOK 4 level4) level5rrllrr) = true
  rw [level5rrllrl_ok, level5rrllrr_ok]
  decide +kernel
def level5rrll : BinaryTree (List W) := .node [v359, v474, v705, v1013, v1194, v1408] level5rrlll level5rrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrll_ok : everyKey (rowOK 4 level4) level5rrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrlll && everyKey (rowOK 4 level4) level5rrllr) = true
  rw [level5rrlll_ok, level5rrllr_ok]
  decide +kernel
def level5rrlrll : BinaryTree (List W) := (.node [v359, v474, v705, v1013, v1231, v1348] (.node [v359, v474, v705, v1013, v1225, v1378] (.node [v359, v474, v705, v1013, v1221, v1348] (.node [v359, v474, v705, v1013, v1219, v1348] (.node [v359, v474, v705, v1013, v1218, v1348] (.node [v359, v474, v705, v1013, v1216, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1220, v1348] .nil .nil)) (.node [v359, v474, v705, v1013, v1224, v1348] (.node [v359, v474, v705, v1013, v1222, v1348] .nil .nil) (.node [v359, v474, v705, v1013, v1225, v1348] .nil .nil))) (.node [v359, v474, v705, v1013, v1227, v1461] (.node [v359, v474, v705, v1013, v1227, v1348] (.node [v359, v474, v705, v1013, v1226, v1483] (.node [v359, v474, v705, v1013, v1225, v1461] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1227, v1424] .nil .nil)) (.node [v359, v474, v705, v1013, v1229, v1461] (.node [v359, v474, v705, v1013, v1229, v1348] .nil .nil) (.node [v359, v474, v705, v1013, v1230, v1348] .nil .nil)))) (.node [v359, v474, v705, v1013, v1244, v1348] (.node [v359, v474, v705, v1013, v1238, v1348] (.node [v359, v474, v705, v1013, v1235, v1348] (.node [v359, v474, v705, v1013, v1233, v1348] (.node [v359, v474, v705, v1013, v1232, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1237, v1348] .nil .nil)) (.node [v359, v474, v705, v1013, v1240, v1348] (.node [v359, v474, v705, v1013, v1239, v1348] .nil .nil) (.node [v359, v474, v705, v1013, v1242, v1348] .nil .nil))) (.node [v359, v474, v705, v1013, v1246, v1483] (.node [v359, v474, v705, v1013, v1245, v1461] (.node [v359, v474, v705, v1013, v1245, v1348] .nil .nil) (.node [v359, v474, v705, v1013, v1246, v1249] .nil .nil)) (.node [v359, v474, v705, v1013, v1249, v1424] (.node [v359, v474, v705, v1013, v1249, v1348] .nil .nil) (.node [v359, v474, v705, v1013, v1249, v1461] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrll_ok : everyKey (rowOK 4 level4) level5rrlrll = true := by decide +kernel
def level5rrlrlr : BinaryTree (List W) := (.node [v359, v474, v705, v1013, v1269, v1348] (.node [v359, v474, v705, v1013, v1260, v1348] (.node [v359, v474, v705, v1013, v1258, v1348] (.node [v359, v474, v705, v1013, v1255, v1348] (.node [v359, v474, v705, v1013, v1254, v1348] (.node [v359, v474, v705, v1013, v1253, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1256, v1348] .nil .nil)) (.node [v359, v474, v705, v1013, v1258, v1461] (.node [v359, v474, v705, v1013, v1258, v1431] .nil .nil) (.node [v359, v474, v705, v1013, v1259, v1348] .nil .nil))) (.node [v359, v474, v705, v1013, v1264, v1348] (.node [v359, v474, v705, v1013, v1263, v1348] (.node [v359, v474, v705, v1013, v1261, v1348] .nil .nil) (.node [v359, v474, v705, v1013, v1263, v1461] .nil .nil)) (.node [v359, v474, v705, v1013, v1268, v1348] (.node [v359, v474, v705, v1013, v1266, v1348] .nil .nil) (.node [v359, v474, v705, v1013, v1268, v1461] .nil .nil)))) (.node [v359, v474, v705, v1013, v1280, v1461] (.node [v359, v474, v705, v1013, v1278, v1424] (.node [v359, v474, v705, v1013, v1271, v1483] (.node [v359, v474, v705, v1013, v1271, v1278] (.node [v359, v474, v705, v1013, v1270, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1278, v1348] .nil .nil)) (.node [v359, v474, v705, v1013, v1279, v1348] (.node [v359, v474, v705, v1013, v1278, v1461] .nil .nil) (.node [v359, v474, v705, v1013, v1280, v1348] .nil .nil))) (.node [v359, v474, v705, v1013, v1286, v1348] (.node [v359, v474, v705, v1013, v1282, v1420] (.node [v359, v474, v705, v1013, v1281, v1348] .nil .nil) (.node [v359, v474, v705, v1013, v1285, v1348] .nil .nil)) (.node [v359, v474, v705, v1013, v1291, v1348] (.node [v359, v474, v705, v1013, v1289, v1348] .nil .nil) (.node [v359, v474, v705, v1013, v1292, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrlr_ok : everyKey (rowOK 4 level4) level5rrlrlr = true := by decide +kernel
def level5rrlrl : BinaryTree (List W) := .node [v359, v474, v705, v1013, v1250, v1348] level5rrlrll level5rrlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrl_ok : everyKey (rowOK 4 level4) level5rrlrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrlrll && everyKey (rowOK 4 level4) level5rrlrlr) = true
  rw [level5rrlrll_ok, level5rrlrlr_ok]
  decide +kernel
def level5rrlrrl : BinaryTree (List W) := (.node [v359, v474, v705, v1013, v1310, v1483] (.node [v359, v474, v705, v1013, v1301, v1461] (.node [v359, v474, v705, v1013, v1298, v1348] (.node [v359, v474, v705, v1013, v1295, v1461] (.node [v359, v474, v705, v1013, v1295, v1373] (.node [v359, v474, v705, v1013, v1295, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1297, v1348] .nil .nil)) (.node [v359, v474, v705, v1013, v1301, v1348] (.node [v359, v474, v705, v1013, v1299, v1348] .nil .nil) (.node [v359, v474, v705, v1013, v1301, v1414] .nil .nil))) (.node [v359, v474, v705, v1013, v1306, v1348] (.node [v359, v474, v705, v1013, v1305, v1387] (.node [v359, v474, v705, v1013, v1305, v1348] (.node [v359, v474, v705, v1013, v1303, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1305, v1461] .nil .nil)) (.node [v359, v474, v705, v1013, v1308, v1348] (.node [v359, v474, v705, v1013, v1307, v1348] .nil .nil) (.node [v359, v474, v705, v1013, v1309, v1483] .nil .nil)))) (.node [v359, v474, v705, v1013, v1316, v1348] (.node [v359, v474, v705, v1013, v1312, v1461] (.node [v359, v474, v705, v1013, v1311, v1461] (.node [v359, v474, v705, v1013, v1311, v1424] (.node [v359, v474, v705, v1013, v1311, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1312, v1348] .nil .nil)) (.node [v359, v474, v705, v1013, v1314, v1348] (.node [v359, v474, v705, v1013, v1313, v1348] .nil .nil) (.node [v359, v474, v705, v1013, v1315, v1420] .nil .nil))) (.node [v359, v474, v705, v1013, v1336, v1348] (.node [v359, v474, v705, v1013, v1320, v1348] (.node [v359, v474, v705, v1013, v1317, v1348] .nil .nil) (.node [v359, v474, v705, v1013, v1326, v1348] .nil .nil)) (.node [v359, v474, v705, v1014, v1194, v1348] (.node [v359, v474, v705, v1013, v1348, v1481] .nil .nil) (.node [v359, v474, v705, v1015, v1194, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrrl_ok : everyKey (rowOK 4 level4) level5rrlrrl = true := by decide +kernel
def level5rrlrrr : BinaryTree (List W) := (.node [v359, v474, v705, v1039, v1194, v1348] (.node [v359, v474, v705, v1030, v1194, v1348] (.node [v359, v474, v705, v1025, v1194, v1348] (.node [v359, v474, v705, v1020, v1194, v1348] (.node [v359, v474, v705, v1018, v1194, v1348] (.node [v359, v474, v705, v1017, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1024, v1194, v1348] .nil .nil)) (.node [v359, v474, v705, v1027, v1194, v1348] (.node [v359, v474, v705, v1026, v1194, v1348] .nil .nil) (.node [v359, v474, v705, v1028, v1194, v1348] .nil .nil))) (.node [v359, v474, v705, v1034, v1194, v1348] (.node [v359, v474, v705, v1033, v1194, v1348] (.node [v359, v474, v705, v1031, v1194, v1348] .nil .nil) (.node [v359, v474, v705, v1034, v1194, v1246] .nil .nil)) (.node [v359, v474, v705, v1034, v1194, v1461] (.node [v359, v474, v705, v1034, v1194, v1362] .nil .nil) (.node [v359, v474, v705, v1038, v1194, v1348] .nil .nil)))) (.node [v359, v474, v705, v1068, v1194, v1348] (.node [v359, v474, v705, v1057, v1194, v1348] (.node [v359, v474, v705, v1044, v1194, v1348] (.node [v359, v474, v705, v1043, v1194, v1348] (.node [v359, v474, v705, v1040, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1050, v1159, v1348] .nil .nil)) (.node [v359, v474, v705, v1066, v1194, v1348] (.node [v359, v474, v705, v1062, v1194, v1348] .nil .nil) (.node [v359, v474, v705, v1067, v1194, v1348] .nil .nil))) (.node [v359, v474, v705, v1070, v1194, v1431] (.node [v359, v474, v705, v1070, v1146, v1194] (.node [v359, v474, v705, v1070, v1139, v1348] .nil .nil) (.node [v359, v474, v705, v1070, v1194, v1348] .nil .nil)) (.node [v359, v474, v705, v1070, v1258, v1348] (.node [v359, v474, v705, v1070, v1194, v1461] .nil .nil) (.node [v359, v474, v705, v1071, v1194, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrrr_ok : everyKey (rowOK 4 level4) level5rrlrrr = true := by decide +kernel
def level5rrlrr : BinaryTree (List W) := .node [v359, v474, v705, v1016, v1194, v1348] level5rrlrrl level5rrlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrr_ok : everyKey (rowOK 4 level4) level5rrlrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrlrrl && everyKey (rowOK 4 level4) level5rrlrrr) = true
  rw [level5rrlrrl_ok, level5rrlrrr_ok]
  decide +kernel
def level5rrlr : BinaryTree (List W) := .node [v359, v474, v705, v1013, v1293, v1348] level5rrlrl level5rrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlr_ok : everyKey (rowOK 4 level4) level5rrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrlrl && everyKey (rowOK 4 level4) level5rrlrr) = true
  rw [level5rrlrl_ok, level5rrlrr_ok]
  decide +kernel
def level5rrl : BinaryTree (List W) := .node [v359, v474, v705, v1013, v1215, v1348] level5rrll level5rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrl_ok : everyKey (rowOK 4 level4) level5rrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrll && everyKey (rowOK 4 level4) level5rrlr) = true
  rw [level5rrll_ok, level5rrlr_ok]
  decide +kernel
def level5rrrlll : BinaryTree (List W) := (.node [v359, v474, v705, v1100, v1194, v1348] (.node [v359, v474, v705, v1087, v1127, v1348] (.node [v359, v474, v705, v1082, v1194, v1348] (.node [v359, v474, v705, v1081, v1194, v1461] (.node [v359, v474, v705, v1081, v1194, v1348] (.node [v359, v474, v705, v1079, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1081, v1268, v1348] .nil .nil)) (.node [v359, v474, v705, v1084, v1159, v1348] (.node [v359, v474, v705, v1084, v1098, v1348] .nil .nil) (.node [v359, v474, v705, v1084, v1337, v1348] .nil .nil))) (.node [v359, v474, v705, v1098, v1194, v1461] (.node [v359, v474, v705, v1097, v1194, v1348] (.node [v359, v474, v705, v1094, v1127, v1194] (.node [v359, v474, v705, v1093, v1337, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1098, v1194, v1348] .nil .nil)) (.node [v359, v474, v705, v1098, v1315, v1348] (.node [v359, v474, v705, v1098, v1282, v1348] .nil .nil) (.node [v359, v474, v705, v1099, v1194, v1348] .nil .nil)))) (.node [v359, v474, v705, v1112, v1194, v1461] (.node [v359, v474, v705, v1110, v1194, v1461] (.node [v359, v474, v705, v1110, v1194, v1348] (.node [v359, v474, v705, v1101, v1194, v1474] (.node [v359, v474, v705, v1101, v1110, v1194] .nil .nil) .nil) (.node [v359, v474, v705, v1110, v1194, v1424] .nil .nil)) (.node [v359, v474, v705, v1111, v1194, v1348] (.node [v359, v474, v705, v1110, v1278, v1348] .nil .nil) (.node [v359, v474, v705, v1112, v1194, v1348] .nil .nil))) (.node [v359, v474, v705, v1114, v1263, v1348] (.node [v359, v474, v705, v1114, v1194, v1414] (.node [v359, v474, v705, v1113, v1194, v1348] .nil .nil) (.node [v359, v474, v705, v1114, v1245, v1348] .nil .nil)) (.node [v359, v474, v705, v1119, v1194, v1348] (.node [v359, v474, v705, v1114, v1301, v1348] .nil .nil) (.node [v359, v474, v705, v1122, v1194, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrlll_ok : everyKey (rowOK 4 level4) level5rrrlll = true := by decide +kernel
def level5rrrllr : BinaryTree (List W) := (.node [v359, v474, v720, v1013, v1194, v1348] (.node [v359, v474, v708, v1013, v1194, v1461] (.node [v359, v474, v705, v1128, v1194, v1348] (.node [v359, v474, v705, v1127, v1194, v1461] (.node [v359, v474, v705, v1127, v1194, v1373] (.node [v359, v474, v705, v1127, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1127, v1295, v1348] .nil .nil)) (.node [v359, v474, v705, v1158, v1194, v1348] (.node [v359, v474, v705, v1129, v1159, v1348] .nil .nil) (.node [v359, v474, v707, v1013, v1194, v1348] .nil .nil))) (.node [v359, v474, v716, v1013, v1194, v1348] (.node [v359, v474, v711, v1013, v1194, v1461] (.node [v359, v474, v710, v1013, v1194, v1461] (.node [v359, v474, v709, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v713, v1013, v1194, v1461] .nil .nil)) (.node [v359, v474, v718, v1013, v1194, v1461] (.node [v359, v474, v717, v1013, v1194, v1348] .nil .nil) (.node [v359, v474, v719, v1013, v1194, v1348] .nil .nil)))) (.node [v359, v474, v746, v847, v1013, v1194] (.node [v359, v474, v730, v1013, v1194, v1348] (.node [v359, v474, v726, v1013, v1194, v1348] (.node [v359, v474, v723, v1013, v1194, v1461] (.node [v359, v474, v722, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v729, v1013, v1194, v1348] .nil .nil)) (.node [v359, v474, v740, v1013, v1194, v1348] (.node [v359, v474, v732, v1013, v1194, v1461] .nil .nil) (.node [v359, v474, v742, v1013, v1194, v1461] .nil .nil))) (.node [v359, v474, v763, v847, v1013, v1194] (.node [v359, v474, v749, v847, v1013, v1194] (.node [v359, v474, v746, v941, v1194, v1348] .nil .nil) (.node [v359, v474, v755, v847, v1013, v1194] .nil .nil)) (.node [v359, v474, v810, v1013, v1194, v1348] (.node [v359, v474, v768, v847, v1013, v1194] .nil .nil) (.node [v359, v474, v812, v1013, v1194, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrllr_ok : everyKey (rowOK 4 level4) level5rrrllr = true := by decide +kernel
def level5rrrll : BinaryTree (List W) := .node [v359, v474, v705, v1124, v1194, v1348] level5rrrlll level5rrrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrll_ok : everyKey (rowOK 4 level4) level5rrrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrlll && everyKey (rowOK 4 level4) level5rrrllr) = true
  rw [level5rrrlll_ok, level5rrrllr_ok]
  decide +kernel
def level5rrrlrl : BinaryTree (List W) := (.node [v359, v474, v847, v896, v1013] (.node [v359, v474, v842, v847, v1013, v1194] (.node [v359, v474, v828, v856, v1013, v1461] (.node [v359, v474, v825, v847, v1013, v1194] (.node [v359, v474, v820, v1013, v1194, v1461] (.node [v359, v474, v819, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v827, v941, v1013, v1348] .nil .nil)) (.node [v359, v474, v840, v1013, v1194, v1348] (.node [v359, v474, v837, v941, v1013, v1194] .nil .nil) (.node [v359, v474, v841, v1013, v1194, v1461] .nil .nil))) (.node [v359, v474, v847, v873, v1013, v1194] (.node [v359, v474, v847, v856, v1013, v1194] (.node [v359, v474, v847, v847, v1013, v1194] (.node [v359, v474, v842, v1013, v1194, v1461] .nil .nil) .nil) (.node [v359, v474, v847, v865, v1013, v1194] .nil .nil)) (.node [v359, v474, v847, v873, v1194, v1348] (.node [v359, v474, v847, v873, v1194] .nil .nil) (.node [v359, v474, v847, v892, v1013, v1194] .nil .nil)))) (.node [v359, v474, v847, v1013, v1138, v1194] (.node [v359, v474, v847, v958, v1013, v1194] (.node [v359, v474, v847, v902, v1013, v1194] (.node [v359, v474, v847, v896, v1013, v1348] (.node [v359, v474, v847, v896, v1013, v1194] .nil .nil) .nil) (.node [v359, v474, v847, v950, v1013, v1194] .nil .nil)) (.node [v359, v474, v847, v1013, v1110, v1194] (.node [v359, v474, v847, v990, v1013, v1194] .nil .nil) (.node [v359, v474, v847, v1013, v1114, v1194] .nil .nil))) (.node [v359, v474, v847, v1013, v1194, v1278] (.node [v359, v474, v847, v1013, v1166, v1194] (.node [v359, v474, v847, v1013, v1159, v1194] .nil .nil) (.node [v359, v474, v847, v1013, v1194] .nil .nil)) (.node [v359, v474, v847, v1013, v1194, v1315] (.node [v359, v474, v847, v1013, v1194, v1282] .nil .nil) (.node [v359, v474, v847, v1013, v1194, v1327] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrlrl_ok : everyKey (rowOK 4 level4) level5rrrlrl = true := by decide +kernel
def level5rrrlrr : BinaryTree (List W) := (.node [v359, v474, v865, v941, v1194, v1348] (.node [v359, v474, v847, v1013, v1194, v1489] (.node [v359, v474, v847, v1013, v1194, v1469] (.node [v359, v474, v847, v1013, v1194, v1424] (.node [v359, v474, v847, v1013, v1194, v1348] (.node [v359, v474, v847, v1013, v1194, v1337] .nil .nil) .nil) (.node [v359, v474, v847, v1013, v1194, v1461] .nil .nil)) (.node [v359, v474, v847, v1013, v1194, v1478] (.node [v359, v474, v847, v1013, v1194, v1474] .nil .nil) (.node [v359, v474, v847, v1013, v1194, v1483] .nil .nil))) (.node [v359, v474, v847, v1110, v1194, v1348] (.node [v359, v474, v847, v1013, v1278, v1348] (.node [v359, v474, v847, v1013, v1278] .nil .nil) (.node [v359, v474, v847, v1110, v1194] .nil .nil)) (.node [v359, v474, v856, v1013, v1194, v1431] (.node [v359, v474, v853, v1013, v1194, v1461] .nil .nil) (.node [v359, v474, v856, v1013, v1194, v1461] .nil .nil)))) (.node [v359, v474, v941, v1013, v1194, v1348] (.node [v359, v474, v934, v1013, v1194, v1348] (.node [v359, v474, v887, v1013, v1194, v1348] (.node [v359, v474, v877, v1159, v1194, v1348] (.node [v359, v474, v877, v941, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v929, v1159, v1194, v1348] .nil .nil)) (.node [v359, v474, v938, v1013, v1194, v1348] (.node [v359, v474, v936, v1013, v1194, v1348] .nil .nil) (.node [v359, v474, v941, v958, v1194, v1348] .nil .nil))) (.node [v359, v474, v941, v1013, v1301, v1348] (.node [v359, v474, v941, v1013, v1194, v1461] (.node [v359, v474, v941, v1013, v1194, v1414] .nil .nil) (.node [v359, v474, v941, v1013, v1194, v1479] .nil .nil)) (.node [v359, v474, v941, v1138, v1194, v1348] (.node [v359, v474, v941, v1114, v1194, v1348] .nil .nil) (.node [v359, v474, v950, v1127, v1194, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrlrr_ok : everyKey (rowOK 4 level4) level5rrrlrr = true := by decide +kernel
def level5rrrlr : BinaryTree (List W) := .node [v359, v474, v847, v1013, v1194, v1330] level5rrrlrl level5rrrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrlr_ok : everyKey (rowOK 4 level4) level5rrrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrlrl && everyKey (rowOK 4 level4) level5rrrlrr) = true
  rw [level5rrrlrl_ok, level5rrrlrr_ok]
  decide +kernel
def level5rrrl : BinaryTree (List W) := .node [v359, v474, v814, v1013, v1194, v1461] level5rrrll level5rrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrl_ok : everyKey (rowOK 4 level4) level5rrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrll && everyKey (rowOK 4 level4) level5rrrlr) = true
  rw [level5rrrll_ok, level5rrrlr_ok]
  decide +kernel
def level5rrrrll : BinaryTree (List W) := (.node [v359, v499, v705, v1070, v1194, v1348] (.node [v359, v498, v705, v1013, v1194, v1348] (.node [v359, v493, v525, v705, v1013, v1194] (.node [v359, v484, v705, v1013, v1194, v1348] (.node [v359, v483, v705, v1013, v1194, v1348] (.node [v359, v481, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v489, v705, v1013, v1194, v1348] .nil .nil)) (.node [v359, v495, v705, v1013, v1194, v1348] (.node [v359, v493, v705, v1013, v1194, v1348] .nil .nil) (.node [v359, v496, v705, v1013, v1194, v1348] .nil .nil))) (.node [v359, v499, v705, v1013, v1194, v1348] (.node [v359, v499, v705, v1013, v1139, v1348] (.node [v359, v499, v705, v984, v1194, v1348] (.node [v359, v499, v525, v705, v1013, v1194] .nil .nil) .nil) (.node [v359, v499, v705, v1013, v1146, v1194] .nil .nil)) (.node [v359, v499, v705, v1013, v1194, v1461] (.node [v359, v499, v705, v1013, v1194, v1431] .nil .nil) (.node [v359, v499, v705, v1013, v1258, v1348] .nil .nil)))) (.node [v359, v608, v705, v1013, v1194, v1424] (.node [v359, v587, v705, v1013, v1194, v1348] (.node [v359, v525, v614, v705, v1013, v1194] (.node [v359, v525, v587, v705, v1013, v1194] (.node [v359, v504, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v575, v705, v1013, v1194, v1348] .nil .nil)) (.node [v359, v605, v705, v1013, v1194, v1348] (.node [v359, v594, v705, v1013, v1194, v1348] .nil .nil) (.node [v359, v608, v614, v705, v1013, v1194] .nil .nil))) (.node [v359, v614, v705, v896, v1013, v1348] (.node [v359, v614, v705, v847, v1013, v1194] (.node [v359, v614, v656, v1013, v1194, v1348] .nil .nil) (.node [v359, v614, v705, v873, v1194, v1348] .nil .nil)) (.node [v359, v614, v705, v1013, v1194, v1278] (.node [v359, v614, v705, v1013, v1110, v1194] .nil .nil) (.node [v359, v614, v705, v1013, v1194, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrll_ok : everyKey (rowOK 4 level4) level5rrrrll = true := by decide +kernel
def level5rrrrlr : BinaryTree (List W) := (.node [v359, v705, v764, v1013, v1194, v1348] (.node [v359, v618, v705, v1013, v1194, v1348] (.node [v359, v614, v705, v1110, v1194] (.node [v359, v614, v705, v1013, v1278] (.node [v359, v614, v705, v1013, v1194, v1483] (.node [v359, v614, v705, v1013, v1194, v1474] .nil .nil) .nil) (.node [v359, v614, v705, v1013, v1278, v1348] .nil .nil)) (.node [v359, v614, v847, v1013, v1194] (.node [v359, v614, v705, v1110, v1194, v1348] .nil .nil) (.node [v359, v614, v847, v1013, v1194, v1348] .nil .nil))) (.node [v359, v705, v755, v779, v1013, v1348] (.node [v359, v642, v887, v1013, v1194, v1348] (.node [v359, v618, v705, v1013, v1194, v1461] .nil .nil) (.node [v359, v705, v746, v806, v1194, v1348] .nil .nil)) (.node [v359, v705, v763, v764, v1013, v1194] (.node [v359, v705, v762, v1013, v1194, v1348] .nil .nil) (.node [v359, v705, v764, v1013, v1194] .nil .nil)))) (.node [v359, v705, v806, v1194, v1348] (.node [v359, v705, v779, v1013, v1348] (.node [v359, v705, v779, v1013, v1194, v1348] (.node [v359, v705, v771, v1013, v1194, v1348] (.node [v359, v705, v764, v1013, v1194, v1424] .nil .nil) .nil) (.node [v359, v705, v779, v1013, v1315, v1348] .nil .nil)) (.node [v359, v705, v806, v1013, v1194, v1348] (.node [v359, v705, v792, v1013, v1194, v1424] .nil .nil) (.node [v359, v705, v806, v1138, v1194, v1348] .nil .nil))) (.node [v359, v887, v1013, v1194, v1348] (.node [v359, v705, v928, v1013, v1194, v1348] (.node [v359, v705, v887, v1013, v1194, v1348] .nil .nil) (.node [v359, v887, v950, v1013, v1194, v1348] .nil .nil)) (.node [v361, v474, v705, v1013, v1194, v1348] (.node [v360, v474, v705, v1013, v1194, v1348] .nil .nil) (.node [v362, v474, v705, v1013, v1194, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrlr_ok : everyKey (rowOK 4 level4) level5rrrrlr = true := by decide +kernel
def level5rrrrl : BinaryTree (List W) := .node [v359, v614, v705, v1013, v1194, v1461] level5rrrrll level5rrrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrl_ok : everyKey (rowOK 4 level4) level5rrrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrrll && everyKey (rowOK 4 level4) level5rrrrlr) = true
  rw [level5rrrrll_ok, level5rrrrlr_ok]
  decide +kernel
def level5rrrrrl : BinaryTree (List W) := (.node [v405, v474, v705, v1013, v1295, v1348] (.node [v404, v474, v705, v1013, v1194, v1348] (.node [v379, v474, v705, v1013, v1194, v1348] (.node [v372, v474, v705, v1013, v1194, v1348] (.node [v366, v474, v705, v1013, v1194, v1348] (.node [v363, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v375, v474, v705, v1013, v1194, v1348] .nil .nil)) (.node [v399, v474, v705, v1013, v1194, v1348] (.node [v391, v474, v705, v1013, v1194, v1348] .nil .nil) (.node [v402, v405, v474, v705, v1013, v1194] .nil .nil))) (.node [v405, v474, v705, v1013, v1094, v1194] (.node [v405, v474, v705, v976, v1194, v1348] (.node [v405, v474, v525, v705, v1013, v1194] (.node [v405, v428, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v405, v474, v705, v1013, v1087, v1348] .nil .nil)) (.node [v405, v474, v705, v1013, v1194, v1373] (.node [v405, v474, v705, v1013, v1194, v1348] .nil .nil) (.node [v405, v474, v705, v1013, v1194, v1461] .nil .nil)))) (.node [v474, v566, v705, v1013, v1194, v1348] (.node [v437, v594, v705, v1013, v1194, v1348] (.node [v419, v572, v705, v1138, v1194, v1348] (.node [v405, v705, v950, v1013, v1194, v1348] (.node [v405, v474, v705, v1127, v1194, v1348] .nil .nil) .nil) (.node [v432, v619, v705, v1013, v1194, v1348] .nil .nil)) (.node [v474, v525, v572, v705, v1013, v1194] (.node [v474, v514, v705, v1114, v1194, v1348] .nil .nil) (.node [v474, v558, v705, v1013, v1194, v1348] .nil .nil))) (.node [v474, v572, v705, v827, v1013, v1348] (.node [v474, v571, v705, v1013, v1194, v1348] (.node [v474, v569, v572, v705, v1013, v1194] .nil .nil) (.node [v474, v572, v680, v1013, v1194, v1348] .nil .nil)) (.node [v474, v572, v705, v1013, v1194, v1348] (.node [v474, v572, v705, v837, v1013, v1194] .nil .nil) (.node [v474, v572, v705, v1013, v1194, v1414] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrrl_ok : everyKey (rowOK 4 level4) level5rrrrrl = true := by decide +kernel
def level5rrrrrr : BinaryTree (List W) := (.node [v474, v705, v898, v1013, v1282, v1348] (.node [v474, v705, v810, v1013, v1194, v1348] (.node [v474, v619, v856, v1013, v1194, v1461] (.node [v474, v594, v705, v1013, v1194, v1348] (.node [v474, v572, v941, v1013, v1194, v1348] (.node [v474, v572, v705, v1013, v1301, v1348] .nil .nil) .nil) (.node [v474, v617, v705, v1013, v1194, v1348] .nil .nil)) (.node [v474, v653, v856, v1013, v1194, v1461] (.node [v474, v653, v810, v1013, v1194, v1348] .nil .nil) (.node [v474, v705, v797, v1013, v1194, v1348] .nil .nil))) (.node [v474, v705, v889, v1114, v1194, v1348] (.node [v474, v705, v870, v1114, v1194, v1348] (.node [v474, v705, v865, v889, v1194, v1348] .nil .nil) (.node [v474, v705, v889, v1013, v1194, v1348] .nil .nil)) (.node [v474, v705, v892, v898, v1013, v1348] (.node [v474, v705, v889, v1194, v1348] .nil .nil) (.node [v474, v705, v898, v1013, v1194, v1348] .nil .nil)))) (.node [v474, v705, v914, v1013, v1194, v1469] (.node [v474, v705, v912, v1013, v1194, v1348] (.node [v474, v705, v907, v1013, v1194, v1348] (.node [v474, v705, v902, v914, v1013, v1194] (.node [v474, v705, v898, v1013, v1348] .nil .nil) .nil) (.node [v474, v705, v907, v1013, v1194, v1461] .nil .nil)) (.node [v474, v705, v914, v1013, v1194] (.node [v474, v705, v912, v1013, v1194, v1461] .nil .nil) (.node [v474, v705, v914, v1013, v1194, v1348] .nil .nil))) (.node [v499, v705, v856, v1013, v1194, v1348] (.node [v474, v810, v1013, v1194, v1348] (.node [v474, v810, v856, v1013, v1194, v1348] .nil .nil) (.node [v474, v856, v904, v1013, v1194, v1461] .nil .nil)) (.node [v594, v705, v1013, v1194, v1348] (.node [v594, v619, v705, v1013, v1194, v1348] .nil .nil) (.node [v619, v705, v732, v1013, v1194, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrrr_ok : everyKey (rowOK 4 level4) level5rrrrrr = true := by decide +kernel
def level5rrrrr : BinaryTree (List W) := .node [v474, v572, v705, v1013, v1194, v1461] level5rrrrrl level5rrrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrr_ok : everyKey (rowOK 4 level4) level5rrrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrrrl && everyKey (rowOK 4 level4) level5rrrrrr) = true
  rw [level5rrrrrl_ok, level5rrrrrr_ok]
  decide +kernel
def level5rrrr : BinaryTree (List W) := .node [v362, v474, v705, v1013, v1194, v1461] level5rrrrl level5rrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrr_ok : everyKey (rowOK 4 level4) level5rrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrrl && everyKey (rowOK 4 level4) level5rrrrr) = true
  rw [level5rrrrl_ok, level5rrrrr_ok]
  decide +kernel
def level5rrr : BinaryTree (List W) := .node [v359, v476, v705, v1013, v1194, v1348] level5rrrl level5rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrr_ok : everyKey (rowOK 4 level4) level5rrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrl && everyKey (rowOK 4 level4) level5rrrr) = true
  rw [level5rrrl_ok, level5rrrr_ok]
  decide +kernel
def level5rr : BinaryTree (List W) := .node [v359, v474, v705, v1076, v1194, v1348] level5rrl level5rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rr_ok : everyKey (rowOK 4 level4) level5rr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrl && everyKey (rowOK 4 level4) level5rrr) = true
  rw [level5rrl_ok, level5rrr_ok]
  decide +kernel
def level5r : BinaryTree (List W) := .node [v359, v474, v705, v1013, v1194, v1283] level5rl level5rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5r_ok : everyKey (rowOK 4 level4) level5r = true := by
  change (_ && everyKey (rowOK 4 level4) level5rl && everyKey (rowOK 4 level4) level5rr) = true
  rw [level5rl_ok, level5rr_ok]
  decide +kernel
def level5 : BinaryTree (List W) := .node [v359, v474, v525, v705, v1127, v1194] level5l level5r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5_ok : everyKey (rowOK 4 level4) level5 = true := by
  change (_ && everyKey (rowOK 4 level4) level5l && everyKey (rowOK 4 level4) level5r) = true
  rw [level5l_ok, level5r_ok]
  decide +kernel
theorem closed5 : Closed 5 level5 := closed_next 4 (by decide) level5 level4 closed4 level5_ok
def level6lllll : BinaryTree (List W) := (.node [v16, v292, v359, v474, v705, v1013, v1194] (.node [v6, v47, v359, v474, v705, v1013, v1194] (.node [v1, v359, v474, v705, v1013, v1194, v1348] (.node [v0, v359, v474, v525, v705, v1013, v1194] (.node [v0, v325, v359, v474, v705, v1013, v1194] (.node [v0, v47, v359, v474, v705, v1013, v1194] .nil .nil) .nil) (.node [v0, v359, v474, v705, v1013, v1194, v1461] (.node [v0, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v3, v359, v474, v705, v1013, v1194, v1348] (.node [v2, v359, v474, v705, v1013, v1194, v1348] (.node [v2, v47, v359, v474, v705, v1013, v1194] .nil .nil) .nil) (.node [v5, v359, v474, v705, v1013, v1194, v1348] (.node [v4, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil))) (.node [v11, v359, v474, v705, v1013, v1194, v1348] (.node [v8, v359, v474, v705, v1013, v1194, v1348] (.node [v7, v359, v474, v705, v1013, v1194, v1348] (.node [v6, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v10, v359, v474, v705, v1013, v1194, v1348] (.node [v9, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v14, v359, v474, v705, v1013, v1194, v1348] (.node [v13, v359, v474, v705, v1013, v1194, v1348] (.node [v12, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v16, v47, v359, v474, v705, v1013, v1194] (.node [v15, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil)))) (.node [v25, v359, v474, v705, v1013, v1194, v1461] (.node [v21, v359, v474, v705, v1013, v1194, v1348] (.node [v16, v359, v474, v705, v1013, v1194, v1461] (.node [v16, v359, v474, v705, v1013, v1194, v1348] (.node [v16, v359, v474, v705, v1013, v1194] .nil .nil) .nil) (.node [v17, v359, v474, v705, v1013, v1194, v1348] (.node [v17, v47, v359, v474, v705, v1013, v1194] .nil .nil) .nil)) (.node [v23, v359, v474, v705, v1013, v1194, v1348] (.node [v22, v359, v474, v705, v1013, v1194, v1348] (.node [v21, v359, v474, v705, v1013, v1194, v1461] .nil .nil) .nil) (.node [v25, v359, v474, v705, v1013, v1194, v1348] (.node [v23, v359, v474, v705, v1013, v1194, v1461] .nil .nil) .nil))) (.node [v29, v359, v474, v525, v705, v1013, v1194] (.node [v29, v325, v359, v474, v705, v1013, v1194] (.node [v29, v47, v359, v474, v705, v1013, v1194] (.node [v28, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v29, v359, v462, v705, v1013, v1194, v1348] (.node [v29, v359, v437, v705, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v29, v359, v474, v705, v1013, v1194, v1424] (.node [v29, v359, v474, v705, v1013, v1194, v1348] (.node [v29, v359, v474, v705, v763, v1013, v1194] .nil .nil) .nil) (.node [v29, v359, v474, v705, v1013, v1194, v1461] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllll_ok : everyKey (rowOK 5 level5) level6lllll = true := by decide +kernel
def level6llllr : BinaryTree (List W) := (.node [v44, v47, v359, v474, v705, v1013, v1194] (.node [v41, v47, v359, v474, v705, v1013, v1194] (.node [v33, v359, v474, v705, v1013, v1194, v1348] (.node [v32, v47, v359, v474, v705, v1013, v1194] (.node [v29, v359, v705, v763, v1013, v1194, v1348] (.node [v29, v359, v705, v763, v1013, v1194] .nil .nil) .nil) (.node [v33, v47, v359, v474, v705, v1013, v1194] (.node [v32, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v38, v359, v474, v705, v1013, v1194, v1348] (.node [v37, v359, v474, v705, v1013, v1194, v1348] (.node [v36, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v40, v359, v474, v705, v1013, v1194, v1348] (.node [v39, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil))) (.node [v41, v359, v474, v691, v1013, v1194, v1348] (.node [v41, v359, v474, v525, v1013, v1194] (.node [v41, v359, v474, v525, v705, v1013, v1194] (.node [v41, v325, v359, v474, v705, v1013, v1194] .nil .nil) .nil) (.node [v41, v359, v474, v653, v1013, v1194, v1348] (.node [v41, v359, v474, v525, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v41, v359, v474, v856, v1013, v1194, v1348] (.node [v41, v359, v474, v705, v1013, v1194, v1461] (.node [v41, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v42, v359, v474, v705, v1013, v1194, v1348] (.node [v42, v47, v359, v474, v705, v1013, v1194] .nil .nil) .nil)))) (.node [v47, v202, v359, v474, v705, v1013, v1194] (.node [v47, v122, v359, v474, v705, v1013, v1194] (.node [v47, v68, v359, v474, v705, v1013, v1194] (.node [v47, v47, v359, v474, v705, v1013, v1194] (.node [v44, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v47, v106, v359, v474, v705, v1013, v1194] (.node [v47, v74, v359, v474, v705, v1013, v1194] .nil .nil) .nil)) (.node [v47, v153, v359, v474, v705, v1013, v1194] (.node [v47, v142, v359, v474, v705, v1013, v1194] (.node [v47, v128, v359, v474, v705, v1013, v1194] .nil .nil) .nil) (.node [v47, v190, v359, v474, v705, v1013, v1194] (.node [v47, v175, v359, v474, v705, v1013, v1194] .nil .nil) .nil))) (.node [v47, v276, v359, v474, v705, v1013, v1194] (.node [v47, v234, v359, v474, v705, v1013, v1194] (.node [v47, v223, v359, v474, v705, v1013, v1194] (.node [v47, v215, v359, v474, v705, v1013, v1194] .nil .nil) .nil) (.node [v47, v252, v359, v474, v705, v1013, v1194] (.node [v47, v245, v359, v474, v705, v1013, v1194] .nil .nil) .nil)) (.node [v47, v313, v359, v474, v705, v1013, v1194] (.node [v47, v304, v359, v474, v705, v1013, v1194] (.node [v47, v292, v359, v474, v705, v1013, v1194] .nil .nil) .nil) (.node [v47, v325, v359, v474, v705, v1013, v1194] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llllr_ok : everyKey (rowOK 5 level5) level6llllr = true := by decide +kernel
def level6llll : BinaryTree (List W) := .node [v29, v359, v619, v705, v1013, v1194, v1348] level6lllll level6llllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llll_ok : everyKey (rowOK 5 level5) level6llll = true := by
  change (_ && everyKey (rowOK 5 level5) level6lllll && everyKey (rowOK 5 level5) level6llllr) = true
  rw [level6lllll_ok, level6llllr_ok]
  decide +kernel
def level6lllrl : BinaryTree (List W) := (.node [v47, v359, v474, v705, v856, v1013, v1194] (.node [v47, v359, v474, v525, v705, v1013, v1194] (.node [v47, v359, v448, v474, v705, v1013, v1194] (.node [v47, v359, v419, v474, v705, v1013, v1194] (.node [v47, v359, v359, v474, v705, v1013, v1194] (.node [v47, v325, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v47, v359, v437, v474, v705, v1013, v1194] (.node [v47, v359, v428, v474, v705, v1013, v1194] .nil .nil) .nil)) (.node [v47, v359, v474, v477, v705, v1013, v1194] (.node [v47, v359, v466, v474, v705, v1013, v1194] (.node [v47, v359, v462, v474, v705, v1013, v1194] .nil .nil) .nil) (.node [v47, v359, v474, v517, v705, v1013, v1194] (.node [v47, v359, v474, v509, v705, v1013, v1194] .nil .nil) .nil))) (.node [v47, v359, v474, v691, v705, v1013, v1194] (.node [v47, v359, v474, v642, v705, v1013, v1194] (.node [v47, v359, v474, v630, v705, v1013, v1194] (.node [v47, v359, v474, v619, v705, v1013, v1194] .nil .nil) .nil) (.node [v47, v359, v474, v666, v705, v1013, v1194] (.node [v47, v359, v474, v653, v705, v1013, v1194] .nil .nil) .nil)) (.node [v47, v359, v474, v705, v746, v1013, v1194] (.node [v47, v359, v474, v705, v708, v1013, v1194] (.node [v47, v359, v474, v695, v705, v1013, v1194] .nil .nil) .nil) (.node [v47, v359, v474, v705, v763, v1013, v1194] (.node [v47, v359, v474, v705, v755, v1013, v1194] .nil .nil) .nil)))) (.node [v47, v359, v474, v705, v1013, v1166, v1194] (.node [v47, v359, v474, v705, v990, v1013, v1194] (.node [v47, v359, v474, v705, v902, v1013, v1194] (.node [v47, v359, v474, v705, v892, v1013, v1194] (.node [v47, v359, v474, v705, v865, v1013, v1194] .nil .nil) .nil) (.node [v47, v359, v474, v705, v958, v1013, v1194] (.node [v47, v359, v474, v705, v950, v1013, v1194] .nil .nil) .nil)) (.node [v47, v359, v474, v705, v1013, v1114, v1194] (.node [v47, v359, v474, v705, v1013, v1019, v1194] (.node [v47, v359, v474, v705, v992, v1013, v1194] .nil .nil) .nil) (.node [v47, v359, v474, v705, v1013, v1159, v1194] (.node [v47, v359, v474, v705, v1013, v1138, v1194] .nil .nil) .nil))) (.node [v47, v359, v474, v705, v1013, v1194, v1327] (.node [v47, v359, v474, v705, v1013, v1194, v1202] (.node [v47, v359, v474, v705, v1013, v1194] (.node [v47, v359, v474, v705, v1013, v1168, v1194] .nil .nil) .nil) (.node [v47, v359, v474, v705, v1013, v1194, v1315] (.node [v47, v359, v474, v705, v1013, v1194, v1282] .nil .nil) .nil)) (.node [v47, v359, v474, v705, v1013, v1194, v1424] (.node [v47, v359, v474, v705, v1013, v1194, v1348] (.node [v47, v359, v474, v705, v1013, v1194, v1337] .nil .nil) .nil) (.node [v47, v359, v474, v705, v1013, v1194, v1461] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllrl_ok : everyKey (rowOK 5 level5) level6lllrl = true := by decide +kernel
def level6lllrr : BinaryTree (List W) := (.node [v71, v359, v474, v705, v1013, v1194] (.node [v68, v252, v359, v474, v705, v1013, v1194] (.node [v60, v359, v474, v705, v1013, v1194] (.node [v47, v474, v705, v902, v1013, v1194] (.node [v47, v359, v474, v705, v1013, v1194, v1483] (.node [v47, v359, v474, v705, v1013, v1194, v1474] .nil .nil) .nil) (.node [v60, v359, v474, v619, v705, v1013, v1194] (.node [v47, v474, v705, v902, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v66, v359, v474, v705, v1013, v1194] (.node [v66, v359, v474, v705, v856, v1013, v1194] (.node [v60, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v67, v359, v474, v705, v1013, v1194, v1348] (.node [v66, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil))) (.node [v68, v359, v474, v705, v990, v1194, v1348] (.node [v68, v325, v359, v474, v705, v1013, v1194] (.node [v68, v252, v359, v474, v705, v1194, v1348] (.node [v68, v252, v359, v474, v705, v1194] .nil .nil) .nil) (.node [v68, v359, v474, v705, v865, v1194, v1348] (.node [v68, v359, v474, v525, v705, v1013, v1194] .nil .nil) .nil)) (.node [v68, v359, v474, v705, v1013, v1194, v1474] (.node [v68, v359, v474, v705, v1013, v1194, v1461] (.node [v68, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v71, v359, v474, v705, v1013, v1114, v1194] (.node [v68, v359, v474, v705, v1114, v1194, v1348] .nil .nil) .nil)))) (.node [v74, v359, v474, v705, v755, v1013, v1348] (.node [v74, v153, v359, v474, v705, v1013] (.node [v73, v359, v474, v705, v1013, v1194, v1348] (.node [v72, v359, v474, v705, v1013, v1194, v1348] (.node [v71, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v74, v142, v359, v474, v705, v1013, v1348] (.node [v74, v128, v359, v474, v705, v1013, v1348] .nil .nil) .nil)) (.node [v74, v325, v359, v474, v705, v1013, v1194] (.node [v74, v153, v359, v474, v705, v1013, v1348] (.node [v74, v153, v359, v474, v705, v1013, v1194] .nil .nil) .nil) (.node [v74, v359, v474, v666, v705, v1013, v1348] (.node [v74, v359, v474, v525, v705, v1013, v1194] .nil .nil) .nil))) (.node [v74, v359, v474, v705, v1013, v1194, v1483] (.node [v74, v359, v474, v705, v1013, v1166, v1348] (.node [v74, v359, v474, v705, v958, v1013, v1348] (.node [v74, v359, v474, v705, v892, v1013, v1348] .nil .nil) .nil) (.node [v74, v359, v474, v705, v1013, v1194, v1461] (.node [v74, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v76, v359, v474, v705, v1013, v1194] (.node [v74, v359, v474, v705, v1013, v1315, v1348] (.node [v74, v359, v474, v705, v1013, v1282, v1348] .nil .nil) .nil) (.node [v76, v359, v474, v705, v1013, v1194, v1282] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllrr_ok : everyKey (rowOK 5 level5) level6lllrr = true := by decide +kernel
def level6lllr : BinaryTree (List W) := .node [v47, v359, v474, v705, v1013, v1194, v1469] level6lllrl level6lllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllr_ok : everyKey (rowOK 5 level5) level6lllr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lllrl && everyKey (rowOK 5 level5) level6lllrr) = true
  rw [level6lllrl_ok, level6lllrr_ok]
  decide +kernel
def level6lll : BinaryTree (List W) := .node [v47, v325, v474, v705, v1013, v1194] level6llll level6lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lll_ok : everyKey (rowOK 5 level5) level6lll = true := by
  change (_ && everyKey (rowOK 5 level5) level6llll && everyKey (rowOK 5 level5) level6lllr) = true
  rw [level6llll_ok, level6lllr_ok]
  decide +kernel
def level6llrll : BinaryTree (List W) := (.node [v106, v128, v359, v474, v705, v1013, v1348] (.node [v94, v359, v474, v705, v1013, v1194, v1348] (.node [v88, v359, v474, v705, v1013, v1194, v1348] (.node [v80, v359, v474, v705, v1013, v1194, v1348] (.node [v78, v359, v474, v705, v1013, v1194, v1348] (.node [v77, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v87, v359, v474, v705, v1013, v1194, v1348] (.node [v82, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v91, v359, v474, v705, v1013, v1194, v1348] (.node [v90, v359, v474, v705, v1013, v1194, v1348] (.node [v89, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v93, v359, v474, v705, v1013, v1194, v1348] (.node [v92, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil))) (.node [v101, v359, v474, v705, v1013, v1194, v1348] (.node [v96, v359, v474, v705, v1013, v1194, v1348] (.node [v95, v359, v474, v705, v1013, v1194, v1348] (.node [v95, v359, v474, v525, v705, v1013, v1194] .nil .nil) .nil) (.node [v99, v359, v474, v705, v1013, v1194, v1348] (.node [v98, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v104, v359, v474, v705, v1013, v1194, v1348] (.node [v103, v359, v474, v705, v1013, v1194, v1348] (.node [v102, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v105, v359, v474, v705, v1013, v1194, v1348] (.node [v105, v325, v359, v474, v705, v1013, v1194] .nil .nil) .nil)))) (.node [v106, v359, v474, v705, v1013, v1315, v1348] (.node [v106, v359, v474, v705, v755, v1013, v1348] (.node [v106, v325, v359, v474, v705, v1013, v1194] (.node [v106, v313, v474, v705, v1013, v1194, v1348] (.node [v106, v142, v359, v474, v705, v1013, v1348] .nil .nil) .nil) (.node [v106, v359, v474, v666, v705, v1013, v1348] (.node [v106, v359, v474, v525, v705, v1013, v1194] .nil .nil) .nil)) (.node [v106, v359, v474, v705, v1013, v1194, v1348] (.node [v106, v359, v474, v705, v958, v1013, v1348] (.node [v106, v359, v474, v705, v892, v1013, v1348] .nil .nil) .nil) (.node [v106, v359, v474, v705, v1013, v1282, v1348] (.node [v106, v359, v474, v705, v1013, v1194, v1461] .nil .nil) .nil))) (.node [v114, v359, v474, v705, v1013, v1194, v1348] (.node [v109, v359, v474, v705, v1013, v1194, v1348] (.node [v106, v474, v705, v892, v1013, v1348] (.node [v106, v474, v705, v892, v1013, v1194, v1348] .nil .nil) .nil) (.node [v113, v359, v474, v705, v1013, v1194, v1348] (.node [v112, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v119, v359, v474, v705, v1013, v1194, v1348] (.node [v117, v359, v474, v705, v1013, v1194, v1348] (.node [v116, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v120, v359, v474, v705, v1013, v1194, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrll_ok : everyKey (rowOK 5 level5) level6llrll = true := by decide +kernel
def level6llrlr : BinaryTree (List W) := (.node [v128, v359, v474, v517, v1013, v1194, v1348] (.node [v122, v359, v474, v705, v1013, v1282, v1348] (.node [v122, v359, v474, v666, v705, v1013, v1348] (.node [v122, v325, v359, v474, v705, v1013, v1194] (.node [v122, v142, v359, v474, v705, v1013, v1348] (.node [v122, v128, v359, v474, v705, v1013, v1348] .nil .nil) .nil) (.node [v122, v359, v474, v525, v705, v1013, v1194] (.node [v122, v359, v448, v705, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v122, v359, v474, v705, v958, v1013, v1348] (.node [v122, v359, v474, v705, v892, v1013, v1348] (.node [v122, v359, v474, v705, v755, v1013, v1348] .nil .nil) .nil) (.node [v122, v359, v474, v705, v1013, v1194, v1461] (.node [v122, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil))) (.node [v127, v359, v474, v705, v1013, v1194, v1348] (.node [v122, v359, v705, v755, v1013, v1348] (.node [v122, v359, v705, v755, v1013, v1194, v1348] (.node [v122, v359, v474, v705, v1013, v1315, v1348] .nil .nil) .nil) (.node [v126, v359, v474, v705, v1013, v1194, v1348] (.node [v125, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v128, v325, v359, v474, v705, v1013, v1194] (.node [v128, v313, v359, v474, v705, v1013, v1348] (.node [v128, v245, v359, v474, v705, v1013, v1348] .nil .nil) .nil) (.node [v128, v359, v474, v517, v705, v1013, v1348] (.node [v128, v359, v448, v474, v705, v1013, v1348] .nil .nil) .nil)))) (.node [v128, v359, v474, v705, v1034, v1194, v1348] (.node [v128, v359, v474, v705, v1013, v1194, v1348] (.node [v128, v359, v474, v666, v1013, v1194, v1348] (.node [v128, v359, v474, v525, v705, v1013, v1194] (.node [v128, v359, v474, v517, v1013, v1348] .nil .nil) .nil) (.node [v128, v359, v474, v705, v1013, v1194, v1246] (.node [v128, v359, v474, v705, v970, v1194, v1348] .nil .nil) .nil)) (.node [v128, v359, v474, v705, v1013, v1327, v1348] (.node [v128, v359, v474, v705, v1013, v1194, v1461] (.node [v128, v359, v474, v705, v1013, v1194, v1362] .nil .nil) .nil) (.node [v128, v359, v474, v705, v1013, v1348, v1483] (.node [v128, v359, v474, v705, v1013, v1337, v1348] .nil .nil) .nil))) (.node [v140, v359, v474, v705, v1013, v1194, v1348] (.node [v138, v359, v474, v705, v1013, v1194, v1348] (.node [v138, v359, v474, v705, v856, v1013, v1348] (.node [v131, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v140, v359, v474, v705, v950, v1013, v1348] (.node [v138, v359, v474, v705, v1013, v1348] .nil .nil) .nil)) (.node [v142, v245, v359, v474, v705, v1013, v1348] (.node [v141, v359, v474, v705, v1013, v1194, v1348] (.node [v140, v359, v474, v705, v1013, v1348] .nil .nil) .nil) (.node [v142, v245, v359, v474, v705, v1194, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrlr_ok : everyKey (rowOK 5 level5) level6llrlr = true := by decide +kernel
def level6llrl : BinaryTree (List W) := .node [v121, v359, v474, v705, v1013, v1194, v1348] level6llrll level6llrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrl_ok : everyKey (rowOK 5 level5) level6llrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6llrll && everyKey (rowOK 5 level5) level6llrlr) = true
  rw [level6llrll_ok, level6llrlr_ok]
  decide +kernel
def level6llrrl : BinaryTree (List W) := (.node [v153, v359, v474, v705, v763, v1013, v1194] (.node [v142, v359, v474, v705, v1013, v1348, v1483] (.node [v142, v359, v474, v705, v865, v1194, v1348] (.node [v142, v359, v448, v474, v705, v1013, v1348] (.node [v142, v325, v359, v474, v705, v1013, v1194] (.node [v142, v313, v359, v474, v705, v1013, v1348] .nil .nil) .nil) (.node [v142, v359, v474, v525, v705, v1013, v1194] (.node [v142, v359, v474, v517, v705, v1013, v1348] .nil .nil) .nil)) (.node [v142, v359, v474, v705, v1013, v1194, v1461] (.node [v142, v359, v474, v705, v1013, v1194, v1348] (.node [v142, v359, v474, v705, v958, v1194, v1348] .nil .nil) .nil) (.node [v142, v359, v474, v705, v1013, v1337, v1348] (.node [v142, v359, v474, v705, v1013, v1327, v1348] .nil .nil) .nil))) (.node [v150, v359, v474, v705, v1013, v1138, v1348] (.node [v149, v359, v474, v705, v1013, v1114, v1348] (.node [v145, v359, v474, v705, v1013, v1194, v1348] (.node [v142, v359, v474, v705, v1114, v1194, v1348] .nil .nil) .nil) (.node [v149, v359, v474, v705, v1013, v1348] (.node [v149, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v151, v359, v474, v705, v1013, v1194, v1348] (.node [v150, v359, v474, v705, v1013, v1348] (.node [v150, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v153, v359, v474, v525, v705, v1013, v1194] (.node [v153, v325, v359, v474, v705, v1013, v1194] .nil .nil) .nil)))) (.node [v169, v359, v474, v705, v1013, v1194, v1348] (.node [v154, v359, v474, v705, v1013, v1194, v1348] (.node [v153, v359, v474, v705, v1013, v1194, v1424] (.node [v153, v359, v474, v705, v1013, v1194, v1348] (.node [v153, v359, v474, v705, v1013, v1166, v1194] .nil .nil) .nil) (.node [v153, v359, v474, v705, v1013, v1348, v1483] (.node [v153, v359, v474, v705, v1013, v1194, v1461] .nil .nil) .nil)) (.node [v156, v359, v474, v705, v1013, v1194, v1461] (.node [v156, v359, v474, v705, v1013, v1194, v1348] (.node [v155, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v161, v359, v474, v705, v1013, v1194, v1348] (.node [v158, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil))) (.node [v175, v304, v474, v705, v1013, v1194, v1348] (.node [v172, v359, v474, v705, v1013, v1194, v1348] (.node [v171, v359, v474, v705, v1013, v1194, v1348] (.node [v171, v325, v359, v474, v705, v1013, v1194] .nil .nil) .nil) (.node [v174, v359, v474, v705, v1013, v1194, v1348] (.node [v173, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v175, v359, v474, v525, v705, v1013, v1194] (.node [v175, v359, v437, v705, v1013, v1194, v1348] (.node [v175, v325, v359, v474, v705, v1013, v1194] .nil .nil) .nil) (.node [v175, v359, v474, v705, v1013, v1194, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrrl_ok : everyKey (rowOK 5 level5) level6llrrl = true := by decide +kernel
def level6llrrr : BinaryTree (List W) := (.node [v190, v359, v474, v705, v984, v1194, v1348] (.node [v183, v359, v474, v705, v1013, v1194, v1348] (.node [v178, v359, v474, v705, v1013, v1194, v1348] (.node [v175, v619, v705, v1013, v1194, v1348] (.node [v175, v474, v619, v705, v1013, v1194, v1348] (.node [v175, v359, v619, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v177, v359, v474, v705, v1013, v1194, v1348] (.node [v176, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v181, v359, v474, v525, v705, v1013, v1194] (.node [v180, v359, v474, v705, v1013, v1194, v1348] (.node [v179, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v182, v359, v474, v705, v1013, v1194, v1348] (.node [v181, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil))) (.node [v190, v292, v474, v705, v1013, v1194, v1348] (.node [v188, v325, v359, v474, v705, v1013, v1194] (.node [v186, v359, v474, v705, v1013, v1194, v1348] (.node [v185, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v189, v359, v474, v705, v1013, v1194, v1348] (.node [v188, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v190, v359, v474, v525, v705, v1013, v1194] (.node [v190, v359, v472, v705, v1013, v1194, v1348] (.node [v190, v325, v359, v474, v705, v1013, v1194] .nil .nil) .nil) (.node [v190, v359, v474, v653, v1013, v1194, v1348] .nil .nil)))) (.node [v191, v359, v474, v705, v1013, v1194, v1348] (.node [v190, v359, v474, v705, v1013, v1258, v1348] (.node [v190, v359, v474, v705, v1013, v1194, v1348] (.node [v190, v359, v474, v705, v1013, v1146, v1194] (.node [v190, v359, v474, v705, v1013, v1139, v1348] .nil .nil) .nil) (.node [v190, v359, v474, v705, v1013, v1194, v1461] (.node [v190, v359, v474, v705, v1013, v1194, v1431] .nil .nil) .nil)) (.node [v190, v359, v499, v705, v1013, v1194, v1348] (.node [v190, v359, v474, v856, v1013, v1194, v1348] (.node [v190, v359, v474, v705, v1070, v1194, v1348] .nil .nil) .nil) (.node [v190, v474, v856, v1013, v1194, v1348] (.node [v190, v474, v705, v856, v1013, v1194, v1348] .nil .nil) .nil))) (.node [v195, v359, v474, v705, v1013, v1194, v1348] (.node [v192, v359, v474, v705, v1013, v1194, v1348] (.node [v192, v359, v474, v705, v1013, v1194] (.node [v192, v359, v474, v525, v705, v1013, v1194] .nil .nil) .nil) (.node [v194, v359, v474, v705, v1013, v1194, v1348] (.node [v193, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v199, v359, v474, v705, v1013, v1194, v1348] (.node [v197, v359, v474, v705, v1013, v1194, v1348] (.node [v196, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v200, v359, v474, v705, v1013, v1194, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrrr_ok : everyKey (rowOK 5 level5) level6llrrr = true := by decide +kernel
def level6llrr : BinaryTree (List W) := .node [v175, v359, v474, v705, v1013, v1194, v1461] level6llrrl level6llrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrr_ok : everyKey (rowOK 5 level5) level6llrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6llrrl && everyKey (rowOK 5 level5) level6llrrr) = true
  rw [level6llrrl_ok, level6llrrr_ok]
  decide +kernel
def level6llr : BinaryTree (List W) := .node [v142, v245, v359, v474, v705, v1348] level6llrl level6llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llr_ok : everyKey (rowOK 5 level5) level6llr = true := by
  change (_ && everyKey (rowOK 5 level5) level6llrl && everyKey (rowOK 5 level5) level6llrr) = true
  rw [level6llrl_ok, level6llrr_ok]
  decide +kernel
def level6ll : BinaryTree (List W) := .node [v76, v359, v474, v705, v1013, v1194, v1348] level6lll level6llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6ll_ok : everyKey (rowOK 5 level5) level6ll = true := by
  change (_ && everyKey (rowOK 5 level5) level6lll && everyKey (rowOK 5 level5) level6llr) = true
  rw [level6lll_ok, level6llr_ok]
  decide +kernel
def level6lrlll : BinaryTree (List W) := (.node [v214, v359, v474, v705, v1013, v1194, v1348] (.node [v202, v474, v705, v865, v1194, v1348] (.node [v202, v359, v474, v705, v865, v1194, v1348] (.node [v202, v304, v474, v705, v1013, v1194, v1348] (.node [v202, v276, v474, v705, v1013, v1194, v1348] (.node [v201, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v202, v359, v474, v525, v705, v1013, v1194] (.node [v202, v325, v359, v474, v705, v1013, v1194] .nil .nil) .nil)) (.node [v202, v359, v474, v705, v1114, v1194, v1348] (.node [v202, v359, v474, v705, v1013, v1194, v1461] (.node [v202, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v202, v474, v705, v865, v1013, v1194, v1348] (.node [v202, v474, v619, v705, v1013, v1194, v1348] .nil .nil) .nil))) (.node [v208, v359, v474, v705, v1013, v1194, v1348] (.node [v205, v359, v474, v705, v1013, v1194, v1348] (.node [v204, v359, v474, v705, v1013, v1194, v1348] (.node [v203, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v207, v359, v474, v705, v1013, v1194, v1348] (.node [v206, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v211, v359, v474, v705, v1013, v1194, v1348] (.node [v210, v359, v474, v705, v1013, v1194, v1348] (.node [v209, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v213, v359, v474, v705, v1013, v1194, v1348] (.node [v212, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil)))) (.node [v215, v359, v474, v705, v1013, v1295, v1348] (.node [v215, v359, v474, v705, v976, v1194, v1348] (.node [v215, v359, v428, v705, v1013, v1194, v1348] (.node [v215, v357, v474, v705, v1013, v1194, v1348] (.node [v215, v325, v359, v474, v705, v1013, v1194] .nil .nil) .nil) (.node [v215, v359, v474, v642, v1013, v1194, v1348] (.node [v215, v359, v474, v525, v705, v1013, v1194] .nil .nil) .nil)) (.node [v215, v359, v474, v705, v1013, v1194, v1348] (.node [v215, v359, v474, v705, v1013, v1094, v1194] (.node [v215, v359, v474, v705, v1013, v1087, v1348] .nil .nil) .nil) (.node [v215, v359, v474, v705, v1013, v1194, v1461] (.node [v215, v359, v474, v705, v1013, v1194, v1373] .nil .nil) .nil))) (.node [v216, v359, v474, v525, v705, v1013, v1194] (.node [v215, v359, v705, v950, v1013, v1194, v1348] (.node [v215, v359, v474, v950, v1013, v1194, v1348] (.node [v215, v359, v474, v705, v1127, v1194, v1348] .nil .nil) .nil) (.node [v215, v405, v474, v705, v1013, v1194, v1348] (.node [v215, v359, v950, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v219, v359, v474, v705, v1013, v1194, v1348] (.node [v217, v359, v474, v705, v1013, v1194, v1348] (.node [v216, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v220, v359, v474, v705, v1013, v1194, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlll_ok : everyKey (rowOK 5 level5) level6lrlll = true := by decide +kernel
def level6lrllr : BinaryTree (List W) := (.node [v234, v325, v359, v474, v705, v1013, v1194] (.node [v223, v359, v474, v705, v1013, v1194, v1461] (.node [v223, v359, v474, v525, v705, v1013, v1194] (.node [v223, v245, v359, v474, v705, v1194, v1348] (.node [v223, v234, v359, v474, v705, v1194, v1348] (.node [v222, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v223, v359, v419, v705, v1013, v1194, v1348] (.node [v223, v325, v359, v474, v705, v1013, v1194] .nil .nil) .nil)) (.node [v223, v359, v474, v705, v865, v1194, v1348] (.node [v223, v359, v474, v705, v746, v1194, v1348] (.node [v223, v359, v474, v630, v705, v1194, v1348] .nil .nil) .nil) (.node [v223, v359, v474, v705, v1013, v1194, v1348] (.node [v223, v359, v474, v705, v958, v1194, v1348] .nil .nil) .nil))) (.node [v227, v359, v474, v705, v1013, v1194, v1348] (.node [v223, v359, v705, v746, v1013, v1194, v1348] (.node [v223, v359, v474, v705, v1138, v1194, v1348] (.node [v223, v359, v474, v705, v1114, v1194, v1348] .nil .nil) .nil) (.node [v226, v359, v474, v705, v1013, v1194, v1348] (.node [v223, v359, v705, v746, v1194, v1348] .nil .nil) .nil)) (.node [v231, v359, v474, v705, v1013, v1194, v1348] (.node [v230, v359, v474, v705, v1013, v1194, v1348] (.node [v229, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v233, v359, v474, v705, v1013, v1194, v1348] (.node [v232, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil)))) (.node [v234, v359, v474, v705, v1013, v1194, v1461] (.node [v234, v359, v474, v630, v1013, v1194, v1348] (.node [v234, v359, v474, v509, v1013, v1194, v1348] (.node [v234, v359, v474, v509, v705, v1194, v1348] (.node [v234, v359, v419, v474, v705, v1194, v1348] .nil .nil) .nil) (.node [v234, v359, v474, v525, v705, v1013, v1194] (.node [v234, v359, v474, v509, v1194, v1348] .nil .nil) .nil)) (.node [v234, v359, v474, v705, v1013, v1060, v1194] (.node [v234, v359, v474, v705, v1013, v1050, v1348] (.node [v234, v359, v474, v642, v1013, v1194, v1348] .nil .nil) .nil) (.node [v234, v359, v474, v705, v1013, v1194, v1378] (.node [v234, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil))) (.node [v238, v359, v474, v705, v1013, v1194, v1348] (.node [v234, v359, v474, v950, v1013, v1194, v1348] (.node [v234, v359, v474, v705, v1159, v1194, v1348] (.node [v234, v359, v474, v705, v1013, v1225, v1348] .nil .nil) .nil) (.node [v237, v359, v474, v705, v1013, v1194, v1348] (.node [v235, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v243, v359, v474, v705, v950, v1194, v1348] (.node [v240, v359, v474, v705, v1013, v1194, v1348] (.node [v239, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v243, v359, v474, v705, v1013, v1194, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrllr_ok : everyKey (rowOK 5 level5) level6lrllr = true := by decide +kernel
def level6lrll : BinaryTree (List W) := .node [v221, v359, v474, v705, v1013, v1194, v1348] level6lrlll level6lrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrll_ok : everyKey (rowOK 5 level5) level6lrll = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrlll && everyKey (rowOK 5 level5) level6lrllr) = true
  rw [level6lrlll_ok, level6lrllr_ok]
  decide +kernel
def level6lrlrl : BinaryTree (List W) := (.node [v252, v359, v474, v705, v763, v1013, v1194] (.node [v245, v359, v474, v705, v1013, v1282, v1348] (.node [v245, v359, v474, v666, v705, v1013, v1348] (.node [v245, v359, v419, v474, v705, v1194, v1348] (.node [v245, v325, v359, v474, v705, v1013, v1194] (.node [v244, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v245, v359, v474, v525, v705, v1013, v1194] (.node [v245, v359, v474, v509, v705, v1194, v1348] .nil .nil) .nil)) (.node [v245, v359, v474, v705, v958, v1013, v1348] (.node [v245, v359, v474, v705, v892, v1013, v1348] (.node [v245, v359, v474, v705, v755, v1013, v1348] .nil .nil) .nil) (.node [v245, v359, v474, v705, v1013, v1194, v1461] (.node [v245, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil))) (.node [v249, v359, v474, v705, v1013, v1194, v1348] (.node [v245, v359, v474, v705, v1194, v1337, v1348] (.node [v245, v359, v474, v705, v1159, v1194, v1348] (.node [v245, v359, v474, v705, v1013, v1315, v1348] .nil .nil) .nil) (.node [v248, v359, v474, v705, v1013, v1194, v1348] (.node [v246, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v250, v359, v474, v705, v1013, v1194, v1348] (.node [v249, v359, v474, v705, v1194, v1348] (.node [v249, v359, v474, v705, v1194, v1315, v1348] .nil .nil) .nil) (.node [v252, v359, v474, v525, v705, v1013, v1194] (.node [v252, v325, v359, v474, v705, v1013, v1194] .nil .nil) .nil)))) (.node [v257, v359, v474, v705, v1013, v1194, v1348] (.node [v252, v359, v474, v705, v1013, v1227, v1348] (.node [v252, v359, v474, v705, v1013, v1194, v1348] (.node [v252, v359, v474, v705, v990, v1013, v1194] (.node [v252, v359, v474, v705, v964, v1013, v1348] .nil .nil) .nil) (.node [v252, v359, v474, v705, v1013, v1194, v1461] (.node [v252, v359, v474, v705, v1013, v1194, v1424] .nil .nil) .nil)) (.node [v254, v359, v474, v705, v1013, v1194, v1348] (.node [v253, v359, v474, v705, v1013, v1194, v1348] (.node [v252, v359, v474, v705, v1194, v1348, v1474] .nil .nil) .nil) (.node [v256, v359, v474, v705, v1013, v1194, v1461] (.node [v256, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil))) (.node [v273, v359, v474, v705, v1013, v1194, v1348] (.node [v270, v359, v474, v705, v1013, v1194, v1348] (.node [v260, v359, v474, v705, v1013, v1194, v1348] (.node [v259, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v272, v359, v474, v705, v1013, v1194, v1348] (.node [v271, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v275, v359, v474, v705, v1013, v1194, v1348] (.node [v274, v359, v474, v705, v1013, v1194, v1348] (.node [v274, v325, v359, v474, v705, v1013, v1194] .nil .nil) .nil) (.node [v276, v325, v359, v474, v705, v1013, v1194] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlrl_ok : everyKey (rowOK 5 level5) level6lrlrl = true := by decide +kernel
def level6lrlrr : BinaryTree (List W) := (.node [v292, v304, v474, v705, v1013, v1194, v1348] (.node [v280, v359, v474, v705, v1013, v1194, v1348] (.node [v276, v359, v474, v705, v1114, v1194, v1348] (.node [v276, v359, v474, v705, v1013, v1194, v1348] (.node [v276, v359, v474, v705, v951, v1013, v1348] (.node [v276, v359, v474, v705, v865, v1194, v1348] .nil .nil) .nil) (.node [v276, v359, v474, v705, v1013, v1263, v1348] (.node [v276, v359, v474, v705, v1013, v1194, v1461] .nil .nil) .nil)) (.node [v277, v359, v474, v705, v1013, v1194, v1348] (.node [v276, v474, v705, v1114, v1194, v1348] (.node [v276, v474, v705, v1013, v1114, v1194, v1348] .nil .nil) .nil) (.node [v279, v359, v474, v705, v1013, v1194, v1348] (.node [v278, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil))) (.node [v287, v359, v474, v705, v1013, v1194, v1348] (.node [v283, v359, v474, v525, v705, v1013, v1194] (.node [v282, v359, v474, v705, v1013, v1194, v1348] (.node [v281, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v286, v359, v474, v705, v1013, v1194, v1348] (.node [v283, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v288, v359, v474, v525, v705, v1013, v1194] (.node [v288, v325, v359, v474, v705, v1013, v1194] (.node [v288, v292, v359, v474, v705, v1013, v1194] .nil .nil) .nil) (.node [v288, v359, v474, v705, v1013, v1194, v1348] (.node [v288, v359, v474, v705, v1013, v1194] .nil .nil) .nil)))) (.node [v297, v359, v474, v705, v1013, v1194, v1348] (.node [v292, v359, v474, v856, v1013, v1194, v1348] (.node [v292, v359, v474, v653, v1013, v1194, v1348] (.node [v292, v359, v474, v525, v705, v1013, v1194] (.node [v292, v325, v359, v474, v705, v1013, v1194] .nil .nil) .nil) (.node [v292, v359, v474, v705, v1013, v1194, v1461] (.node [v292, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v292, v474, v653, v1013, v1194, v1348] (.node [v292, v474, v653, v705, v1013, v1194, v1348] (.node [v292, v474, v619, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v294, v359, v474, v705, v1013, v1194, v1348] (.node [v293, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil))) (.node [v304, v325, v359, v474, v705, v1013, v1194] (.node [v302, v359, v474, v705, v1013, v1194, v1348] (.node [v301, v359, v474, v705, v1013, v1194, v1348] (.node [v299, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v303, v359, v474, v705, v1013, v1194, v1348] (.node [v303, v325, v359, v474, v705, v1013, v1194] .nil .nil) .nil)) (.node [v304, v359, v474, v705, v870, v1194, v1348] (.node [v304, v359, v474, v525, v705, v1013, v1194] (.node [v304, v359, v437, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v304, v359, v474, v705, v920, v1013, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlrr_ok : everyKey (rowOK 5 level5) level6lrlrr = true := by decide +kernel
def level6lrlr : BinaryTree (List W) := .node [v276, v359, v474, v525, v705, v1013, v1194] level6lrlrl level6lrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlr_ok : everyKey (rowOK 5 level5) level6lrlr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrlrl && everyKey (rowOK 5 level5) level6lrlrr) = true
  rw [level6lrlrl_ok, level6lrlrr_ok]
  decide +kernel
def level6lrl : BinaryTree (List W) := .node [v243, v359, v474, v705, v1194, v1348] level6lrll level6lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrl_ok : everyKey (rowOK 5 level5) level6lrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrll && everyKey (rowOK 5 level5) level6lrlr) = true
  rw [level6lrll_ok, level6lrlr_ok]
  decide +kernel
def level6lrrll : BinaryTree (List W) := (.node [v313, v359, v474, v705, v1013, v1282, v1348] (.node [v310, v359, v474, v705, v1013, v1194, v1348] (.node [v304, v437, v705, v1013, v1194, v1348] (.node [v304, v359, v474, v705, v1081, v1194, v1348] (.node [v304, v359, v474, v705, v1013, v1268, v1348] (.node [v304, v359, v474, v705, v1013, v1194, v1461] .nil .nil) .nil) (.node [v304, v437, v474, v705, v1013, v1194, v1348] (.node [v304, v359, v619, v705, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v305, v359, v474, v705, v1013, v1194, v1348] (.node [v304, v474, v705, v1013, v1114, v1194, v1348] (.node [v304, v474, v705, v856, v1013, v1194, v1348] .nil .nil) .nil) (.node [v308, v359, v474, v705, v1013, v1194, v1348] (.node [v306, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil))) (.node [v313, v359, v474, v705, v755, v1013, v1348] (.node [v313, v325, v359, v474, v705, v1013, v1194] (.node [v312, v359, v474, v705, v1013, v1194, v1348] (.node [v312, v325, v359, v474, v705, v1013, v1194] .nil .nil) .nil) (.node [v313, v359, v474, v666, v705, v1013, v1348] (.node [v313, v359, v474, v525, v705, v1013, v1194] .nil .nil) .nil)) (.node [v313, v359, v474, v705, v958, v1013, v1348] (.node [v313, v359, v474, v705, v892, v1013, v1348] (.node [v313, v359, v474, v705, v881, v1194, v1348] .nil .nil) .nil) (.node [v313, v359, v474, v705, v1013, v1194, v1461] (.node [v313, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil)))) (.node [v323, v359, v474, v705, v1013, v1194, v1348] (.node [v315, v359, v474, v705, v1013, v1194, v1348] (.node [v313, v474, v705, v1013, v1194, v1282, v1348] (.node [v313, v359, v474, v705, v1098, v1194, v1348] (.node [v313, v359, v474, v705, v1013, v1315, v1348] .nil .nil) .nil) (.node [v314, v359, v474, v705, v1013, v1194, v1348] (.node [v313, v474, v705, v1013, v1282, v1348] .nil .nil) .nil)) (.node [v319, v359, v474, v705, v1013, v1194, v1348] (.node [v317, v359, v474, v705, v1013, v1194, v1348] (.node [v316, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v322, v359, v474, v705, v1013, v1194, v1348] (.node [v321, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil))) (.node [v325, v359, v437, v474, v705, v1013, v1194] (.node [v325, v359, v359, v474, v705, v1013, v1194] (.node [v325, v325, v359, v474, v705, v1013, v1194] (.node [v324, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v325, v359, v428, v474, v705, v1013, v1194] (.node [v325, v359, v419, v474, v705, v1013, v1194] .nil .nil) .nil)) (.node [v325, v359, v443, v705, v1013, v1194, v1348] (.node [v325, v359, v443, v705, v1013, v1194] (.node [v325, v359, v443, v474, v705, v1013, v1194] .nil .nil) .nil) (.node [v325, v359, v448, v474, v705, v1013, v1194] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrll_ok : everyKey (rowOK 5 level5) level6lrrll = true := by decide +kernel
def level6lrrlr : BinaryTree (List W) := (.node [v325, v359, v474, v705, v896, v1013] (.node [v325, v359, v474, v666, v705, v1013, v1194] (.node [v325, v359, v474, v630, v705, v1013, v1194] (.node [v325, v359, v474, v525, v705, v1013, v1194] (.node [v325, v359, v474, v517, v705, v1013, v1194] (.node [v325, v359, v474, v509, v705, v1013, v1194] .nil .nil) .nil) (.node [v325, v359, v474, v619, v705, v1013, v1194] (.node [v325, v359, v474, v614, v705, v1013, v1194] .nil .nil) .nil)) (.node [v325, v359, v474, v656, v705, v1013, v1194] (.node [v325, v359, v474, v653, v705, v1013, v1194] (.node [v325, v359, v474, v642, v705, v1013, v1194] .nil .nil) .nil) (.node [v325, v359, v474, v656, v1013, v1194, v1348] (.node [v325, v359, v474, v656, v1013, v1194] .nil .nil) .nil))) (.node [v325, v359, v474, v705, v856, v1013, v1194] (.node [v325, v359, v474, v705, v755, v1013, v1194] (.node [v325, v359, v474, v705, v746, v1013, v1194] (.node [v325, v359, v474, v691, v705, v1013, v1194] .nil .nil) .nil) (.node [v325, v359, v474, v705, v847, v1013, v1194] (.node [v325, v359, v474, v705, v763, v1013, v1194] .nil .nil) .nil)) (.node [v325, v359, v474, v705, v873, v1194] (.node [v325, v359, v474, v705, v873, v1013, v1194] (.node [v325, v359, v474, v705, v865, v1013, v1194] .nil .nil) .nil) (.node [v325, v359, v474, v705, v892, v1013, v1194] (.node [v325, v359, v474, v705, v873, v1194, v1348] .nil .nil) .nil)))) (.node [v325, v359, v474, v705, v1013, v1194] (.node [v325, v359, v474, v705, v990, v1013, v1194] (.node [v325, v359, v474, v705, v902, v1013, v1194] (.node [v325, v359, v474, v705, v896, v1013, v1348] (.node [v325, v359, v474, v705, v896, v1013, v1194] .nil .nil) .nil) (.node [v325, v359, v474, v705, v958, v1013, v1194] (.node [v325, v359, v474, v705, v950, v1013, v1194] .nil .nil) .nil)) (.node [v325, v359, v474, v705, v1013, v1138, v1194] (.node [v325, v359, v474, v705, v1013, v1114, v1194] (.node [v325, v359, v474, v705, v1013, v1110, v1194] .nil .nil) .nil) (.node [v325, v359, v474, v705, v1013, v1166, v1194] (.node [v325, v359, v474, v705, v1013, v1159, v1194] .nil .nil) .nil))) (.node [v325, v359, v474, v705, v1013, v1194, v1348] (.node [v325, v359, v474, v705, v1013, v1194, v1315] (.node [v325, v359, v474, v705, v1013, v1194, v1282] (.node [v325, v359, v474, v705, v1013, v1194, v1278] .nil .nil) .nil) (.node [v325, v359, v474, v705, v1013, v1194, v1337] (.node [v325, v359, v474, v705, v1013, v1194, v1327] .nil .nil) .nil)) (.node [v325, v359, v474, v705, v1013, v1194, v1469] (.node [v325, v359, v474, v705, v1013, v1194, v1461] (.node [v325, v359, v474, v705, v1013, v1194, v1424] .nil .nil) .nil) (.node [v325, v359, v474, v705, v1013, v1194, v1474] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrlr_ok : everyKey (rowOK 5 level5) level6lrrlr = true := by decide +kernel
def level6lrrl : BinaryTree (List W) := .node [v325, v359, v462, v474, v705, v1013, v1194] level6lrrll level6lrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrl_ok : everyKey (rowOK 5 level5) level6lrrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrrll && everyKey (rowOK 5 level5) level6lrrlr) = true
  rw [level6lrrll_ok, level6lrrlr_ok]
  decide +kernel
def level6lrrrl : BinaryTree (List W) := (.node [v357, v359, v474, v705, v1013, v1194, v1348] (.node [v334, v359, v474, v705, v1013, v1194, v1348] (.node [v325, v359, v474, v847, v1013, v1194, v1348] (.node [v325, v359, v474, v705, v1110, v1194] (.node [v325, v359, v474, v705, v1013, v1278, v1348] (.node [v325, v359, v474, v705, v1013, v1278] .nil .nil) .nil) (.node [v325, v359, v474, v847, v1013, v1194] (.node [v325, v359, v474, v705, v1110, v1194, v1348] .nil .nil) .nil)) (.node [v325, v474, v705, v1013, v1194, v1348, v1469] (.node [v325, v359, v614, v705, v1013, v1194, v1348] (.node [v325, v359, v614, v705, v1013, v1194] .nil .nil) .nil) (.node [v332, v359, v474, v705, v1013, v1194, v1348] (.node [v325, v474, v705, v1013, v1194, v1469] .nil .nil) .nil))) (.node [v345, v359, v474, v705, v1013, v1194, v1461] (.node [v344, v359, v474, v705, v1013, v1194, v1348] (.node [v339, v359, v474, v705, v1013, v1194, v1348] (.node [v338, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v345, v359, v474, v705, v1013, v1194, v1348] (.node [v345, v359, v474, v705, v1013, v1194] .nil .nil) .nil)) (.node [v348, v474, v705, v1013, v1194, v1348] (.node [v348, v419, v474, v705, v1013, v1194, v1348] (.node [v348, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v352, v359, v474, v705, v1013, v1194, v1348] (.node [v351, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil)))) (.node [v359, v384, v474, v705, v1013, v1194, v1348] (.node [v359, v368, v474, v705, v1013, v1194, v1348] (.node [v359, v364, v474, v705, v1013, v1194, v1348] (.node [v359, v359, v474, v705, v1013, v1194, v1348] (.node [v357, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v367, v474, v705, v1013, v1194, v1348] (.node [v359, v365, v474, v705, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v359, v382, v474, v705, v892, v1013, v1194] (.node [v359, v380, v474, v705, v1013, v1194, v1348] (.node [v359, v376, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v382, v474, v705, v1013, v1194, v1348] (.node [v359, v382, v474, v705, v1013, v1194] .nil .nil) .nil))) (.node [v359, v395, v474, v705, v1013, v1194, v1348] (.node [v359, v392, v474, v705, v1013, v1194, v1348] (.node [v359, v387, v474, v705, v1013, v1194, v1348] (.node [v359, v385, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v395, v474, v705, v1013, v1194] (.node [v359, v395, v474, v705, v865, v1013, v1194] .nil .nil) .nil)) (.node [v359, v401, v474, v705, v1013, v1194, v1348] (.node [v359, v400, v474, v705, v1013, v1194, v1348] (.node [v359, v398, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v405, v474, v705, v1013, v1194, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrrl_ok : everyKey (rowOK 5 level5) level6lrrrl = true := by decide +kernel
def level6lrrrr : BinaryTree (List W) := (.node [v359, v419, v474, v941, v1013, v1194, v1348] (.node [v359, v419, v474, v705, v746, v1194, v1348] (.node [v359, v414, v474, v705, v1013, v1194, v1348] (.node [v359, v411, v474, v705, v1013, v1194, v1348] (.node [v359, v411, v474, v525, v705, v1013, v1194] (.node [v359, v409, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v413, v474, v705, v1013, v1194, v1348] (.node [v359, v412, v474, v705, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v359, v419, v474, v525, v705, v1013, v1194] (.node [v359, v418, v474, v705, v1013, v1194, v1348] (.node [v359, v417, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v419, v474, v680, v1013, v1194, v1348] (.node [v359, v419, v474, v630, v705, v1194, v1348] .nil .nil) .nil))) (.node [v359, v419, v474, v705, v1013, v1194, v1414] (.node [v359, v419, v474, v705, v865, v1194, v1348] (.node [v359, v419, v474, v705, v837, v1013, v1194] (.node [v359, v419, v474, v705, v827, v1013, v1348] .nil .nil) .nil) (.node [v359, v419, v474, v705, v1013, v1194, v1348] (.node [v359, v419, v474, v705, v958, v1194, v1348] .nil .nil) .nil)) (.node [v359, v419, v474, v705, v1114, v1194, v1348] (.node [v359, v419, v474, v705, v1013, v1301, v1348] (.node [v359, v419, v474, v705, v1013, v1194, v1461] .nil .nil) .nil) (.node [v359, v419, v474, v705, v1138, v1194, v1348] .nil .nil)))) (.node [v359, v428, v474, v642, v1013, v1194, v1348] (.node [v359, v425, v474, v705, v1013, v1194, v1348] (.node [v359, v420, v474, v705, v1013, v1194, v1348] (.node [v359, v419, v705, v1138, v1194, v1348] (.node [v359, v419, v705, v1013, v1138, v1194, v1348] .nil .nil) .nil) (.node [v359, v423, v474, v705, v1013, v1194, v1348] (.node [v359, v422, v474, v705, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v359, v427, v474, v705, v1013, v1194, v1348] (.node [v359, v427, v474, v525, v705, v1013, v1194] (.node [v359, v426, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v428, v474, v525, v705, v1013, v1194] (.node [v359, v428, v437, v705, v1013, v1194, v1348] .nil .nil) .nil))) (.node [v359, v428, v642, v1013, v1194, v1348] (.node [v359, v428, v474, v950, v1013, v1194, v1348] (.node [v359, v428, v474, v705, v1013, v1194, v1461] (.node [v359, v428, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v428, v642, v705, v1013, v1194, v1348] (.node [v359, v428, v619, v705, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v359, v431, v474, v705, v1013, v1194, v1348] (.node [v359, v430, v474, v705, v1013, v1194, v1348] (.node [v359, v429, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v432, v474, v705, v1013, v1194, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrrr_ok : everyKey (rowOK 5 level5) level6lrrrr = true := by decide +kernel
def level6lrrr : BinaryTree (List W) := .node [v359, v408, v474, v705, v1013, v1194, v1348] level6lrrrl level6lrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrr_ok : everyKey (rowOK 5 level5) level6lrrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrrrl && everyKey (rowOK 5 level5) level6lrrrr) = true
  rw [level6lrrrl_ok, level6lrrrr_ok]
  decide +kernel
def level6lrr : BinaryTree (List W) := .node [v325, v359, v474, v705, v1013, v1194, v1483] level6lrrl level6lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrr_ok : everyKey (rowOK 5 level5) level6lrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrrl && everyKey (rowOK 5 level5) level6lrrr) = true
  rw [level6lrrl_ok, level6lrrr_ok]
  decide +kernel
def level6lr : BinaryTree (List W) := .node [v304, v359, v474, v705, v1013, v1194, v1348] level6lrl level6lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lr_ok : everyKey (rowOK 5 level5) level6lr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrl && everyKey (rowOK 5 level5) level6lrr) = true
  rw [level6lrl_ok, level6lrr_ok]
  decide +kernel
def level6l : BinaryTree (List W) := .node [v201, v325, v359, v474, v705, v1013, v1194] level6ll level6lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6l_ok : everyKey (rowOK 5 level5) level6l = true := by
  change (_ && everyKey (rowOK 5 level5) level6ll && everyKey (rowOK 5 level5) level6lr) = true
  rw [level6ll_ok, level6lr_ok]
  decide +kernel
def level6rllll : BinaryTree (List W) := (.node [v359, v448, v474, v705, v958, v1013, v1348] (.node [v359, v438, v474, v705, v1013, v1194, v1348] (.node [v359, v437, v474, v705, v1013, v1194, v1348] (.node [v359, v437, v474, v525, v705, v1013, v1194] (.node [v359, v436, v474, v705, v1013, v1194, v1348] (.node [v359, v435, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v437, v474, v705, v792, v1013, v1194] (.node [v359, v437, v474, v705, v787, v1013, v1348] .nil .nil) .nil)) (.node [v359, v437, v474, v705, v1013, v1305, v1348] (.node [v359, v437, v474, v705, v1013, v1194, v1461] (.node [v359, v437, v474, v705, v1013, v1194, v1387] .nil .nil) .nil) (.node [v359, v437, v705, v1013, v1194, v1348, v1424] (.node [v359, v437, v705, v950, v1013, v1194, v1348] .nil .nil) .nil))) (.node [v359, v447, v474, v705, v1013, v1194, v1348] (.node [v359, v443, v474, v705, v1013, v1194, v1348] (.node [v359, v440, v474, v705, v1013, v1194, v1348] (.node [v359, v439, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v445, v474, v705, v1013, v1194, v1348] (.node [v359, v443, v705, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v359, v448, v474, v705, v755, v1013, v1348] (.node [v359, v448, v474, v666, v705, v1013, v1348] (.node [v359, v448, v474, v525, v705, v1013, v1194] .nil .nil) .nil) (.node [v359, v448, v474, v705, v892, v1013, v1348] (.node [v359, v448, v474, v705, v780, v1013, v1194] .nil .nil) .nil)))) (.node [v359, v454, v474, v705, v1013, v1194, v1348] (.node [v359, v448, v705, v1013, v1194, v1315, v1348] (.node [v359, v448, v474, v705, v1013, v1194, v1461] (.node [v359, v448, v474, v705, v1013, v1194, v1420] (.node [v359, v448, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v448, v474, v705, v1013, v1315, v1348] (.node [v359, v448, v474, v705, v1013, v1282, v1348] .nil .nil) .nil)) (.node [v359, v451, v474, v705, v1013, v1194, v1348] (.node [v359, v449, v474, v705, v1013, v1194, v1348] (.node [v359, v448, v705, v1013, v1315, v1348] .nil .nil) .nil) (.node [v359, v453, v474, v705, v1013, v1194, v1348] (.node [v359, v452, v474, v705, v1013, v1194, v1348] .nil .nil) .nil))) (.node [v359, v462, v474, v705, v759, v1013, v1348] (.node [v359, v457, v474, v705, v1013, v1194, v1348] (.node [v359, v456, v474, v705, v1013, v1194, v1348] (.node [v359, v455, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v462, v474, v525, v705, v1013, v1194] (.node [v359, v458, v474, v705, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v359, v462, v474, v705, v1013, v1194, v1424] (.node [v359, v462, v474, v705, v1013, v1194, v1348] (.node [v359, v462, v474, v705, v763, v1013, v1194] .nil .nil) .nil) (.node [v359, v462, v474, v705, v1013, v1194, v1461] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllll_ok : everyKey (rowOK 5 level5) level6rllll = true := by decide +kernel
def level6rlllr : BinaryTree (List W) := (.node [v359, v474, v491, v705, v1013, v1194, v1348] (.node [v359, v471, v474, v705, v1013, v1194, v1348] (.node [v359, v465, v474, v705, v1013, v1194, v1348] (.node [v359, v463, v474, v705, v1013, v1194, v1348] (.node [v359, v462, v705, v1013, v1194, v1424] (.node [v359, v462, v705, v1013, v1194, v1348, v1424] .nil .nil) .nil) (.node [v359, v464, v474, v705, v1013, v1194, v1461] (.node [v359, v464, v474, v705, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v359, v468, v474, v705, v1013, v1194, v1348] (.node [v359, v467, v474, v705, v1013, v1194, v1348] (.node [v359, v466, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v470, v474, v705, v1013, v1194, v1348] (.node [v359, v469, v474, v705, v1013, v1194, v1348] .nil .nil) .nil))) (.node [v359, v474, v479, v705, v1013, v1194, v1348] (.node [v359, v474, v474, v705, v1013, v1194, v1348] (.node [v359, v472, v705, v1013, v1194, v1348] (.node [v359, v472, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v478, v705, v1013, v1194, v1348] (.node [v359, v474, v477, v705, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v359, v474, v487, v705, v1013, v1194, v1348] (.node [v359, v474, v485, v705, v1013, v1194, v1348] (.node [v359, v474, v480, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v490, v705, v1013, v1194, v1348] (.node [v359, v474, v488, v705, v1013, v1194, v1348] .nil .nil) .nil)))) (.node [v359, v474, v509, v630, v705, v1194, v1348] (.node [v359, v474, v505, v705, v1013, v1194, v1348] (.node [v359, v474, v500, v705, v1013, v1194, v1348] (.node [v359, v474, v499, v705, v1013, v1194, v1348] (.node [v359, v474, v497, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v503, v705, v1013, v1194, v1348] (.node [v359, v474, v502, v705, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v359, v474, v508, v525, v705, v1013, v1194] (.node [v359, v474, v507, v705, v1013, v1194, v1348] (.node [v359, v474, v506, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v509, v525, v705, v1013, v1194] (.node [v359, v474, v508, v705, v1013, v1194, v1348] .nil .nil) .nil))) (.node [v359, v474, v509, v705, v1013, v1194, v1461] (.node [v359, v474, v509, v705, v865, v1194, v1348] (.node [v359, v474, v509, v705, v746, v1194, v1348] (.node [v359, v474, v509, v705, v736, v1013, v1348] .nil .nil) .nil) (.node [v359, v474, v509, v705, v1013, v1194, v1348] (.node [v359, v474, v509, v705, v958, v1194, v1348] .nil .nil) .nil)) (.node [v359, v474, v509, v705, v1138, v1194, v1348] (.node [v359, v474, v509, v705, v1114, v1194, v1348] (.node [v359, v474, v509, v705, v1013, v1245, v1348] .nil .nil) .nil) (.node [v359, v474, v509, v1013, v1159, v1194, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlllr_ok : everyKey (rowOK 5 level5) level6rlllr = true := by decide +kernel
def level6rlll : BinaryTree (List W) := .node [v359, v462, v474, v705, v1013, v1311, v1348] level6rllll level6rlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlll_ok : everyKey (rowOK 5 level5) level6rlll = true := by
  change (_ && everyKey (rowOK 5 level5) level6rllll && everyKey (rowOK 5 level5) level6rlllr) = true
  rw [level6rllll_ok, level6rlllr_ok]
  decide +kernel
def level6rllrl : BinaryTree (List W) := (.node [v359, v474, v525, v589, v705, v1013, v1194] (.node [v359, v474, v517, v705, v958, v1013, v1348] (.node [v359, v474, v516, v525, v705, v1013, v1194] (.node [v359, v474, v513, v705, v1013, v1194, v1348] (.node [v359, v474, v512, v705, v1013, v1194, v1348] (.node [v359, v474, v511, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v515, v705, v1013, v1194, v1348] (.node [v359, v474, v514, v705, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v359, v474, v517, v666, v705, v1013, v1348] (.node [v359, v474, v517, v525, v705, v1013, v1194] (.node [v359, v474, v516, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v517, v705, v892, v1013, v1348] (.node [v359, v474, v517, v705, v755, v1013, v1348] .nil .nil) .nil))) (.node [v359, v474, v518, v705, v1013, v1194, v1348] (.node [v359, v474, v517, v705, v1013, v1282, v1348] (.node [v359, v474, v517, v705, v1013, v1194, v1461] (.node [v359, v474, v517, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v517, v1013, v1194, v1327, v1348] (.node [v359, v474, v517, v705, v1013, v1315, v1348] .nil .nil) .nil)) (.node [v359, v474, v522, v705, v1013, v1194, v1348] (.node [v359, v474, v521, v705, v1013, v1194, v1348] (.node [v359, v474, v520, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v525, v565, v705, v1013, v1194] (.node [v359, v474, v525, v525, v705, v1013, v1194] .nil .nil) .nil)))) (.node [v359, v474, v525, v705, v746, v1013, v1194] (.node [v359, v474, v525, v666, v705, v1013, v1194] (.node [v359, v474, v525, v633, v705, v1013, v1194] (.node [v359, v474, v525, v630, v705, v1013, v1194] (.node [v359, v474, v525, v619, v705, v1013, v1194] .nil .nil) .nil) (.node [v359, v474, v525, v653, v705, v1013, v1194] (.node [v359, v474, v525, v642, v705, v1013, v1194] .nil .nil) .nil)) (.node [v359, v474, v525, v672, v705, v1013, v1348] (.node [v359, v474, v525, v672, v705, v1013, v1194] (.node [v359, v474, v525, v672, v705, v1013] .nil .nil) .nil) (.node [v359, v474, v525, v705, v705, v1013, v1194] (.node [v359, v474, v525, v691, v705, v1013, v1194] .nil .nil) .nil))) (.node [v359, v474, v525, v705, v902, v1013, v1194] (.node [v359, v474, v525, v705, v856, v1013, v1194] (.node [v359, v474, v525, v705, v763, v1013, v1194] (.node [v359, v474, v525, v705, v755, v1013, v1194] .nil .nil) .nil) (.node [v359, v474, v525, v705, v892, v1013, v1194] (.node [v359, v474, v525, v705, v865, v1013, v1194] .nil .nil) .nil)) (.node [v359, v474, v525, v705, v990, v1013, v1194] (.node [v359, v474, v525, v705, v958, v1013, v1194] (.node [v359, v474, v525, v705, v950, v1013, v1194] .nil .nil) .nil) (.node [v359, v474, v525, v705, v1013, v1063, v1194] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllrl_ok : everyKey (rowOK 5 level5) level6rllrl = true := by decide +kernel
def level6rllrr : BinaryTree (List W) := (.node [v359, v474, v535, v705, v1013, v1194, v1348] (.node [v359, v474, v525, v705, v1013, v1194, v1461] (.node [v359, v474, v525, v705, v1013, v1194, v1282] (.node [v359, v474, v525, v705, v1013, v1166, v1194] (.node [v359, v474, v525, v705, v1013, v1159, v1194] (.node [v359, v474, v525, v705, v1013, v1138, v1194] .nil .nil) .nil) (.node [v359, v474, v525, v705, v1013, v1194, v1249] (.node [v359, v474, v525, v705, v1013, v1194] .nil .nil) .nil)) (.node [v359, v474, v525, v705, v1013, v1194, v1337] (.node [v359, v474, v525, v705, v1013, v1194, v1327] (.node [v359, v474, v525, v705, v1013, v1194, v1315] .nil .nil) .nil) (.node [v359, v474, v525, v705, v1013, v1194, v1424] (.node [v359, v474, v525, v705, v1013, v1194, v1348] .nil .nil) .nil))) (.node [v359, v474, v525, v1013, v1194, v1348, v1461] (.node [v359, v474, v525, v705, v1013, v1194, v1483] (.node [v359, v474, v525, v705, v1013, v1194, v1474] (.node [v359, v474, v525, v705, v1013, v1194, v1469] .nil .nil) .nil) (.node [v359, v474, v525, v705, v1013, v1249, v1348] (.node [v359, v474, v525, v705, v1013, v1249] .nil .nil) .nil)) (.node [v359, v474, v531, v705, v1013, v1194, v1348] (.node [v359, v474, v529, v705, v1013, v1194, v1348] (.node [v359, v474, v525, v1013, v1194, v1461] .nil .nil) .nil) (.node [v359, v474, v534, v705, v1013, v1194, v1348] (.node [v359, v474, v533, v705, v1013, v1194, v1348] .nil .nil) .nil)))) (.node [v359, v474, v568, v705, v1013, v1194, v1348] (.node [v359, v474, v559, v705, v1013, v1194, v1348] (.node [v359, v474, v551, v705, v1013, v1194] (.node [v359, v474, v551, v666, v705, v1013, v1194] (.node [v359, v474, v538, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v553, v705, v1013, v1194, v1348] (.node [v359, v474, v551, v705, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v359, v474, v562, v705, v1013, v1194, v1348] (.node [v359, v474, v562, v705, v1013, v1194] (.node [v359, v474, v562, v653, v705, v1013, v1194] .nil .nil) .nil) (.node [v359, v474, v567, v705, v1013, v1194, v1348] (.node [v359, v474, v565, v705, v1013, v1194, v1348] .nil .nil) .nil))) (.node [v359, v474, v584, v642, v705, v1013, v1194] (.node [v359, v474, v576, v705, v1013, v1194, v1348] (.node [v359, v474, v574, v705, v1013, v1194, v1348] (.node [v359, v474, v572, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v582, v705, v1013, v1194, v1348] (.node [v359, v474, v577, v705, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v359, v474, v588, v705, v1013, v1194, v1348] (.node [v359, v474, v584, v705, v1013, v1194, v1348] (.node [v359, v474, v584, v705, v1013, v1194] .nil .nil) .nil) (.node [v359, v474, v589, v705, v1013, v1194, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllrr_ok : everyKey (rowOK 5 level5) level6rllrr = true := by decide +kernel
def level6rllr : BinaryTree (List W) := .node [v359, v474, v525, v705, v1013, v1114, v1194] level6rllrl level6rllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllr_ok : everyKey (rowOK 5 level5) level6rllr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rllrl && everyKey (rowOK 5 level5) level6rllrr) = true
  rw [level6rllrl_ok, level6rllrr_ok]
  decide +kernel
def level6rll : BinaryTree (List W) := .node [v359, v474, v510, v705, v1013, v1194, v1348] level6rlll level6rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rll_ok : everyKey (rowOK 5 level5) level6rll = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlll && everyKey (rowOK 5 level5) level6rllr) = true
  rw [level6rlll_ok, level6rllr_ok]
  decide +kernel
def level6rlrll : BinaryTree (List W) := (.node [v359, v474, v630, v705, v1013, v1194, v1461] (.node [v359, v474, v619, v705, v1013, v1194, v1348] (.node [v359, v474, v606, v705, v1013, v1194, v1348] (.node [v359, v474, v599, v705, v1013, v1194] (.node [v359, v474, v599, v630, v705, v1013, v1194] (.node [v359, v474, v597, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v603, v705, v1013, v1194, v1348] (.node [v359, v474, v599, v705, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v359, v474, v608, v705, v1013, v1194, v1348] (.node [v359, v474, v608, v705, v1013, v1194] (.node [v359, v474, v608, v619, v705, v1013, v1194] .nil .nil) .nil) (.node [v359, v474, v616, v705, v1013, v1194, v1348] (.node [v359, v474, v614, v705, v1013, v1194, v1348] .nil .nil) .nil))) (.node [v359, v474, v624, v705, v1013, v1194, v1348] (.node [v359, v474, v621, v705, v1013, v1194, v1348] (.node [v359, v474, v620, v705, v1013, v1194, v1348] (.node [v359, v474, v619, v705, v1013, v1194, v1461] .nil .nil) .nil) (.node [v359, v474, v623, v705, v1013, v1194, v1348] (.node [v359, v474, v622, v705, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v359, v474, v629, v705, v1013, v1194, v1348] (.node [v359, v474, v628, v705, v1013, v1194, v1348] (.node [v359, v474, v627, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v630, v705, v1013, v1194, v1438] (.node [v359, v474, v630, v705, v1013, v1194, v1348] .nil .nil) .nil)))) (.node [v359, v474, v642, v705, v1013, v1194, v1461] (.node [v359, v474, v634, v705, v1013, v1194, v1348] (.node [v359, v474, v630, v1159, v1194, v1348] (.node [v359, v474, v630, v1013, v1159, v1194, v1348] (.node [v359, v474, v630, v705, v1159, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v633, v705, v1013, v1194, v1348] (.node [v359, v474, v631, v705, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v359, v474, v641, v705, v1013, v1194, v1348] (.node [v359, v474, v639, v705, v1013, v1194, v1348] (.node [v359, v474, v635, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v642, v705, v1013, v1194, v1442] (.node [v359, v474, v642, v705, v1013, v1194, v1348] .nil .nil) .nil))) (.node [v359, v474, v649, v705, v1013, v1194, v1348] (.node [v359, v474, v644, v705, v1013, v1194, v1348] (.node [v359, v474, v643, v705, v1013, v1194, v1348] (.node [v359, v474, v642, v1013, v1159, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v647, v705, v1013, v1194, v1348] (.node [v359, v474, v646, v705, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v359, v474, v653, v705, v1013, v1194, v1348] (.node [v359, v474, v652, v705, v1013, v1194, v1348] (.node [v359, v474, v650, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v653, v705, v1013, v1194, v1394] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrll_ok : everyKey (rowOK 5 level5) level6rlrll = true := by decide +kernel
def level6rlrlr : BinaryTree (List W) := (.node [v359, v474, v680, v705, v1013, v1194, v1348] (.node [v359, v474, v666, v705, v1013, v1194, v1461] (.node [v359, v474, v658, v705, v1013, v1194, v1348] (.node [v359, v474, v654, v705, v1013, v1194, v1348] (.node [v359, v474, v653, v1013, v1194, v1461] (.node [v359, v474, v653, v1013, v1194, v1348, v1461] .nil .nil) .nil) (.node [v359, v474, v656, v1013, v1194, v1348] (.node [v359, v474, v656, v705, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v359, v474, v665, v705, v1013, v1194, v1348] (.node [v359, v474, v662, v705, v1013, v1194, v1348] (.node [v359, v474, v659, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v666, v705, v1013, v1194, v1449] (.node [v359, v474, v666, v705, v1013, v1194, v1348] .nil .nil) .nil))) (.node [v359, v474, v667, v705, v1013, v1194, v1348] (.node [v359, v474, v666, v705, v1013, v1348, v1483] (.node [v359, v474, v666, v705, v1013, v1337, v1348] (.node [v359, v474, v666, v705, v1013, v1327, v1348] .nil .nil) .nil) (.node [v359, v474, v666, v1013, v1327, v1348] (.node [v359, v474, v666, v1013, v1194, v1327, v1348] .nil .nil) .nil)) (.node [v359, v474, v673, v705, v1013, v1194, v1348] (.node [v359, v474, v672, v705, v1013, v1348] (.node [v359, v474, v672, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v677, v705, v1013, v1194, v1348] (.node [v359, v474, v676, v705, v1013, v1194, v1348] .nil .nil) .nil)))) (.node [v359, v474, v694, v705, v1013, v1194, v1348] (.node [v359, v474, v691, v705, v1013, v1194, v1348] (.node [v359, v474, v684, v705, v1013, v1194, v1348] (.node [v359, v474, v683, v705, v1013, v1194, v1348] (.node [v359, v474, v680, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v690, v705, v1013, v1194, v1348] (.node [v359, v474, v687, v705, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v359, v474, v691, v1013, v1194, v1461] (.node [v359, v474, v691, v1013, v1194, v1348, v1461] (.node [v359, v474, v691, v705, v1013, v1194, v1461] .nil .nil) .nil) (.node [v359, v474, v693, v705, v1013, v1194, v1348] (.node [v359, v474, v692, v705, v1013, v1194, v1348] .nil .nil) .nil))) (.node [v359, v474, v702, v705, v1013, v1194, v1348] (.node [v359, v474, v698, v705, v1013, v1194, v1348] (.node [v359, v474, v697, v705, v1013, v1194, v1348] (.node [v359, v474, v695, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v700, v705, v1013, v1194, v1348] (.node [v359, v474, v699, v705, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v359, v474, v705, v708, v1013, v1194] (.node [v359, v474, v705, v705, v1013, v1194, v1461] (.node [v359, v474, v705, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v708, v1013, v1194, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrlr_ok : everyKey (rowOK 5 level5) level6rlrlr = true := by decide +kernel
def level6rlrl : BinaryTree (List W) := .node [v359, v474, v653, v705, v1013, v1194, v1461] level6rlrll level6rlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrl_ok : everyKey (rowOK 5 level5) level6rlrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlrll && everyKey (rowOK 5 level5) level6rlrlr) = true
  rw [level6rlrll_ok, level6rlrlr_ok]
  decide +kernel
def level6rlrrl : BinaryTree (List W) := (.node [v359, v474, v705, v751, v1013, v1194, v1348] (.node [v359, v474, v705, v738, v1013, v1194, v1348] (.node [v359, v474, v705, v724, v1013, v1194, v1348] (.node [v359, v474, v705, v718, v1013, v1194, v1348] (.node [v359, v474, v705, v713, v1013, v1194, v1348] (.node [v359, v474, v705, v711, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v723, v1013, v1194, v1348] (.node [v359, v474, v705, v721, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v359, v474, v705, v732, v1013, v1194, v1348] (.node [v359, v474, v705, v731, v1013, v1194, v1348] (.node [v359, v474, v705, v725, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v736, v1013, v1348] (.node [v359, v474, v705, v736, v1013, v1194, v1348] .nil .nil) .nil))) (.node [v359, v474, v705, v746, v1013, v1194, v1348] (.node [v359, v474, v705, v742, v1013, v1194, v1348] (.node [v359, v474, v705, v741, v1013, v1194, v1348] (.node [v359, v474, v705, v739, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v745, v1013, v1194, v1348] (.node [v359, v474, v705, v743, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v359, v474, v705, v747, v1013, v1194, v1348] (.node [v359, v474, v705, v746, v1159, v1194, v1348] (.node [v359, v474, v705, v746, v1013, v1194, v1461] .nil .nil) .nil) (.node [v359, v474, v705, v750, v1013, v1194, v1348] (.node [v359, v474, v705, v748, v1013, v1194, v1348] .nil .nil) .nil)))) (.node [v359, v474, v705, v761, v1013, v1194, v1348] (.node [v359, v474, v705, v755, v1013, v1327, v1348] (.node [v359, v474, v705, v754, v1013, v1194, v1348] (.node [v359, v474, v705, v753, v1013, v1194, v1348] (.node [v359, v474, v705, v752, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v755, v1013, v1194, v1461] (.node [v359, v474, v705, v755, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v359, v474, v705, v759, v1013, v1194, v1348] (.node [v359, v474, v705, v755, v1013, v1348, v1483] (.node [v359, v474, v705, v755, v1013, v1337, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v760, v1013, v1194, v1348] (.node [v359, v474, v705, v759, v1013, v1348] .nil .nil) .nil))) (.node [v359, v474, v705, v766, v1013, v1194, v1348] (.node [v359, v474, v705, v763, v1013, v1194, v1474] (.node [v359, v474, v705, v763, v1013, v1194, v1461] (.node [v359, v474, v705, v763, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v765, v1013, v1194, v1348] (.node [v359, v474, v705, v763, v1013, v1194, v1483] .nil .nil) .nil)) (.node [v359, v474, v705, v770, v1013, v1194, v1348] (.node [v359, v474, v705, v769, v1013, v1194, v1348] (.node [v359, v474, v705, v767, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v772, v1013, v1194, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrrl_ok : everyKey (rowOK 5 level5) level6rlrrl = true := by decide +kernel
def level6rlrrr : BinaryTree (List W) := (.node [v359, v474, v705, v828, v1013, v1194, v1348] (.node [v359, v474, v705, v803, v1013, v1194, v1348] (.node [v359, v474, v705, v792, v1013, v1194] (.node [v359, v474, v705, v780, v1013, v1194, v1348] (.node [v359, v474, v705, v780, v1013, v1194] (.node [v359, v474, v705, v773, v1013, v1194, v1461] .nil .nil) .nil) (.node [v359, v474, v705, v787, v1013, v1348] (.node [v359, v474, v705, v787, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v359, v474, v705, v798, v1013, v1194, v1348] (.node [v359, v474, v705, v796, v1013, v1194, v1348] (.node [v359, v474, v705, v792, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v800, v1013, v1194, v1348] (.node [v359, v474, v705, v799, v1013, v1194, v1348] .nil .nil) .nil))) (.node [v359, v474, v705, v820, v1013, v1194, v1348] (.node [v359, v474, v705, v815, v1013, v1194, v1348] (.node [v359, v474, v705, v814, v1013, v1194, v1348] (.node [v359, v474, v705, v813, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v818, v1013, v1194, v1348] (.node [v359, v474, v705, v817, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v359, v474, v705, v827, v1013, v1348] (.node [v359, v474, v705, v827, v1013, v1194, v1348] (.node [v359, v474, v705, v821, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v828, v856, v1013, v1348] .nil .nil)))) (.node [v359, v474, v705, v856, v1013, v1194, v1348] (.node [v359, v474, v705, v842, v856, v1013, v1194] (.node [v359, v474, v705, v837, v1013, v1194] (.node [v359, v474, v705, v836, v1013, v1194, v1348] (.node [v359, v474, v705, v828, v1013, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v841, v1013, v1194, v1348] (.node [v359, v474, v705, v837, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v359, v474, v705, v847, v1013, v1194] (.node [v359, v474, v705, v842, v1013, v1194, v1348] (.node [v359, v474, v705, v842, v1013, v1194] .nil .nil) .nil) (.node [v359, v474, v705, v853, v1013, v1194, v1348] (.node [v359, v474, v705, v847, v1013, v1194, v1348] .nil .nil) .nil))) (.node [v359, v474, v705, v865, v1013, v1194, v1461] (.node [v359, v474, v705, v864, v1013, v1194, v1348] (.node [v359, v474, v705, v861, v1013, v1194, v1348] (.node [v359, v474, v705, v856, v1013, v1194, v1461] .nil .nil) .nil) (.node [v359, v474, v705, v865, v1013, v1194, v1399] (.node [v359, v474, v705, v865, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v359, v474, v705, v865, v1194, v1348, v1474] (.node [v359, v474, v705, v865, v1194, v1337, v1348] (.node [v359, v474, v705, v865, v1159, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v870, v1013, v1194, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrrr_ok : everyKey (rowOK 5 level5) level6rlrrr = true := by decide +kernel
def level6rlrr : BinaryTree (List W) := .node [v359, v474, v705, v773, v1013, v1194, v1348] level6rlrrl level6rlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrr_ok : everyKey (rowOK 5 level5) level6rlrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlrrl && everyKey (rowOK 5 level5) level6rlrrr) = true
  rw [level6rlrrl_ok, level6rlrrr_ok]
  decide +kernel
def level6rlr : BinaryTree (List W) := .node [v359, v474, v705, v710, v1013, v1194, v1348] level6rlrl level6rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlr_ok : everyKey (rowOK 5 level5) level6rlr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlrl && everyKey (rowOK 5 level5) level6rlrr) = true
  rw [level6rlrl_ok, level6rlrr_ok]
  decide +kernel
def level6rl : BinaryTree (List W) := .node [v359, v474, v596, v705, v1013, v1194, v1348] level6rll level6rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rl_ok : everyKey (rowOK 5 level5) level6rl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rll && everyKey (rowOK 5 level5) level6rlr) = true
  rw [level6rll_ok, level6rlr_ok]
  decide +kernel
def level6rrlll : BinaryTree (List W) := (.node [v359, v474, v705, v904, v1013, v1194, v1461] (.node [v359, v474, v705, v892, v1013, v1194, v1461] (.node [v359, v474, v705, v877, v1194, v1348] (.node [v359, v474, v705, v876, v1013, v1194, v1348] (.node [v359, v474, v705, v873, v1194, v1348] (.node [v359, v474, v705, v873, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v877, v1013, v1194, v1348] (.node [v359, v474, v705, v877, v950, v1194, v1348] .nil .nil) .nil)) (.node [v359, v474, v705, v891, v1013, v1194, v1348] (.node [v359, v474, v705, v881, v1194, v1348] (.node [v359, v474, v705, v881, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v892, v1013, v1194, v1400] (.node [v359, v474, v705, v892, v1013, v1194, v1348] .nil .nil) .nil))) (.node [v359, v474, v705, v900, v1013, v1194, v1348] (.node [v359, v474, v705, v892, v1013, v1348, v1483] (.node [v359, v474, v705, v892, v1013, v1337, v1348] (.node [v359, v474, v705, v892, v1013, v1327, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v896, v1013, v1348] (.node [v359, v474, v705, v896, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v359, v474, v705, v902, v1013, v1194, v1461] (.node [v359, v474, v705, v902, v1013, v1194, v1348] (.node [v359, v474, v705, v901, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v904, v1013, v1194, v1348] (.node [v359, v474, v705, v903, v1013, v1194, v1348] .nil .nil) .nil)))) (.node [v359, v474, v705, v925, v1013, v1194, v1348] (.node [v359, v474, v705, v911, v1013, v1194, v1348] (.node [v359, v474, v705, v908, v1013, v1194, v1348] (.node [v359, v474, v705, v906, v1013, v1194, v1348] (.node [v359, v474, v705, v905, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v910, v1013, v1194, v1348] (.node [v359, v474, v705, v909, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v359, v474, v705, v920, v1013, v1348] (.node [v359, v474, v705, v920, v1013, v1194, v1348] (.node [v359, v474, v705, v916, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v924, v1013, v1194, v1348] (.node [v359, v474, v705, v923, v1013, v1194, v1348] .nil .nil) .nil))) (.node [v359, v474, v705, v935, v1013, v1194, v1348] (.node [v359, v474, v705, v929, v1013, v1194, v1348] (.node [v359, v474, v705, v927, v1013, v1194, v1348] (.node [v359, v474, v705, v926, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v933, v1013, v1194, v1348] (.node [v359, v474, v705, v931, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v359, v474, v705, v940, v1013, v1194, v1348] (.node [v359, v474, v705, v939, v1013, v1194, v1348] (.node [v359, v474, v705, v937, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v941, v1013, v1194, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlll_ok : everyKey (rowOK 5 level5) level6rrlll = true := by decide +kernel
def level6rrllr : BinaryTree (List W) := (.node [v359, v474, v705, v964, v1013, v1348] (.node [v359, v474, v705, v956, v1013, v1194, v1348] (.node [v359, v474, v705, v948, v1013, v1194, v1348] (.node [v359, v474, v705, v945, v1013, v1194, v1348] (.node [v359, v474, v705, v942, v1013, v1348] (.node [v359, v474, v705, v942, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v947, v1013, v1194, v1348] (.node [v359, v474, v705, v946, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v359, v474, v705, v950, v1013, v1194, v1461] (.node [v359, v474, v705, v950, v1013, v1194, v1348] (.node [v359, v474, v705, v949, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v951, v1013, v1348] (.node [v359, v474, v705, v951, v1013, v1194, v1348] .nil .nil) .nil))) (.node [v359, v474, v705, v958, v1013, v1348, v1483] (.node [v359, v474, v705, v958, v1013, v1194, v1461] (.node [v359, v474, v705, v958, v1013, v1194, v1348] (.node [v359, v474, v705, v957, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v958, v1013, v1337, v1348] (.node [v359, v474, v705, v958, v1013, v1327, v1348] .nil .nil) .nil)) (.node [v359, v474, v705, v958, v1337, v1348] (.node [v359, v474, v705, v958, v1194, v1337, v1348] (.node [v359, v474, v705, v958, v1159, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v964, v1013, v1194, v1348] (.node [v359, v474, v705, v959, v1013, v1194, v1348] .nil .nil) .nil)))) (.node [v359, v474, v705, v984, v1194, v1348] (.node [v359, v474, v705, v976, v1194, v1348] (.node [v359, v474, v705, v972, v1013, v1194, v1348] (.node [v359, v474, v705, v970, v1194, v1348] (.node [v359, v474, v705, v970, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v976, v1013, v1194, v1348] (.node [v359, v474, v705, v973, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v359, v474, v705, v979, v1194, v1315, v1348] (.node [v359, v474, v705, v979, v1013, v1194, v1348] (.node [v359, v474, v705, v978, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v984, v1013, v1194, v1348] (.node [v359, v474, v705, v979, v1194, v1348] .nil .nil) .nil))) (.node [v359, v474, v705, v990, v1194, v1474] (.node [v359, v474, v705, v990, v1013, v1194, v1461] (.node [v359, v474, v705, v990, v1013, v1194, v1348] (.node [v359, v474, v705, v988, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v990, v1194, v1348, v1474] (.node [v359, v474, v705, v990, v1013, v1194, v1474] .nil .nil) .nil)) (.node [v359, v474, v705, v995, v1013, v1194, v1348] (.node [v359, v474, v705, v992, v1013, v1194, v1348] (.node [v359, v474, v705, v991, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v996, v1013, v1194, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrllr_ok : everyKey (rowOK 5 level5) level6rrllr = true := by decide +kernel
def level6rrll : BinaryTree (List W) := .node [v359, v474, v705, v942, v950, v1013, v1348] level6rrlll level6rrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrll_ok : everyKey (rowOK 5 level5) level6rrll = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrlll && everyKey (rowOK 5 level5) level6rrllr) = true
  rw [level6rrlll_ok, level6rrllr_ok]
  decide +kernel
def level6rrlrl : BinaryTree (List W) := (.node [v359, v474, v705, v1013, v1064, v1194, v1348] (.node [v359, v474, v705, v1013, v1032, v1194, v1348] (.node [v359, v474, v705, v1013, v1013, v1194, v1348] (.node [v359, v474, v705, v1002, v1013, v1194, v1348] (.node [v359, v474, v705, v1001, v1013, v1194, v1461] (.node [v359, v474, v705, v1001, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1005, v1013, v1194, v1348] (.node [v359, v474, v705, v1004, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v359, v474, v705, v1013, v1022, v1194, v1348] (.node [v359, v474, v705, v1013, v1021, v1194, v1348] (.node [v359, v474, v705, v1013, v1019, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1029, v1194, v1348] (.node [v359, v474, v705, v1013, v1023, v1194, v1348] .nil .nil) .nil))) (.node [v359, v474, v705, v1013, v1050, v1194, v1348] (.node [v359, v474, v705, v1013, v1036, v1194, v1348] (.node [v359, v474, v705, v1013, v1035, v1194, v1348] (.node [v359, v474, v705, v1013, v1034, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1046, v1194, v1348] (.node [v359, v474, v705, v1013, v1045, v1194, v1348] .nil .nil) .nil)) (.node [v359, v474, v705, v1013, v1060, v1194] (.node [v359, v474, v705, v1013, v1058, v1194, v1348] (.node [v359, v474, v705, v1013, v1050, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1063, v1194, v1348] (.node [v359, v474, v705, v1013, v1060, v1194, v1348] .nil .nil) .nil)))) (.node [v359, v474, v705, v1013, v1087, v1348] (.node [v359, v474, v705, v1013, v1080, v1194, v1348] (.node [v359, v474, v705, v1013, v1072, v1194, v1348] (.node [v359, v474, v705, v1013, v1070, v1194, v1348] (.node [v359, v474, v705, v1013, v1069, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1078, v1194, v1348] (.node [v359, v474, v705, v1013, v1077, v1194, v1348] .nil .nil) .nil)) (.node [v359, v474, v705, v1013, v1084, v1194, v1348] (.node [v359, v474, v705, v1013, v1084, v1114, v1348] (.node [v359, v474, v705, v1013, v1081, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1087, v1194, v1348] (.node [v359, v474, v705, v1013, v1084, v1348] .nil .nil) .nil))) (.node [v359, v474, v705, v1013, v1101, v1194] (.node [v359, v474, v705, v1013, v1094, v1194, v1348] (.node [v359, v474, v705, v1013, v1094, v1194] (.node [v359, v474, v705, v1013, v1093, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1101, v1114, v1194] (.node [v359, v474, v705, v1013, v1098, v1194, v1348] .nil .nil) .nil)) (.node [v359, v474, v705, v1013, v1110, v1194, v1348] (.node [v359, v474, v705, v1013, v1108, v1194, v1348] (.node [v359, v474, v705, v1013, v1101, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1114, v1194, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlrl_ok : everyKey (rowOK 5 level5) level6rrlrl = true := by decide +kernel
def level6rrlrr : BinaryTree (List W) := (.node [v359, v474, v705, v1013, v1154, v1194, v1348] (.node [v359, v474, v705, v1013, v1133, v1194, v1348] (.node [v359, v474, v705, v1013, v1126, v1194, v1348] (.node [v359, v474, v705, v1013, v1121, v1194, v1348] (.node [v359, v474, v705, v1013, v1120, v1194, v1348] (.node [v359, v474, v705, v1013, v1117, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1125, v1194, v1348] (.node [v359, v474, v705, v1013, v1123, v1194, v1348] .nil .nil) .nil)) (.node [v359, v474, v705, v1013, v1129, v1194, v1348] (.node [v359, v474, v705, v1013, v1129, v1138, v1348] (.node [v359, v474, v705, v1013, v1127, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1132, v1194, v1348] (.node [v359, v474, v705, v1013, v1129, v1348] .nil .nil) .nil))) (.node [v359, v474, v705, v1013, v1139, v1194, v1348] (.node [v359, v474, v705, v1013, v1136, v1194, v1348] (.node [v359, v474, v705, v1013, v1135, v1194, v1348] (.node [v359, v474, v705, v1013, v1134, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1138, v1194, v1461] (.node [v359, v474, v705, v1013, v1138, v1194, v1348] .nil .nil) .nil)) (.node [v359, v474, v705, v1013, v1146, v1194, v1348] (.node [v359, v474, v705, v1013, v1146, v1194] (.node [v359, v474, v705, v1013, v1139, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1153, v1194, v1348] (.node [v359, v474, v705, v1013, v1151, v1194, v1348] .nil .nil) .nil)))) (.node [v359, v474, v705, v1013, v1166, v1348, v1483] (.node [v359, v474, v705, v1013, v1160, v1194, v1348] (.node [v359, v474, v705, v1013, v1157, v1194, v1348] (.node [v359, v474, v705, v1013, v1156, v1194, v1348] (.node [v359, v474, v705, v1013, v1155, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1159, v1194, v1461] (.node [v359, v474, v705, v1013, v1159, v1194, v1348] .nil .nil) .nil)) (.node [v359, v474, v705, v1013, v1166, v1194, v1348] (.node [v359, v474, v705, v1013, v1165, v1194, v1348] (.node [v359, v474, v705, v1013, v1162, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1166, v1194, v1483] (.node [v359, v474, v705, v1013, v1166, v1194, v1461] .nil .nil) .nil))) (.node [v359, v474, v705, v1013, v1176, v1194, v1348] (.node [v359, v474, v705, v1013, v1168, v1194, v1348] (.node [v359, v474, v705, v1013, v1167, v1194, v1348] (.node [v359, v474, v705, v1013, v1166, v1483] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1172, v1194, v1348] (.node [v359, v474, v705, v1013, v1171, v1194, v1348] .nil .nil) .nil)) (.node [v359, v474, v705, v1013, v1181, v1194, v1348] (.node [v359, v474, v705, v1013, v1177, v1194, v1461] (.node [v359, v474, v705, v1013, v1177, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1184, v1194, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlrr_ok : everyKey (rowOK 5 level5) level6rrlrr = true := by decide +kernel
def level6rrlr : BinaryTree (List W) := .node [v359, v474, v705, v1013, v1114, v1194, v1461] level6rrlrl level6rrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlr_ok : everyKey (rowOK 5 level5) level6rrlr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrlrl && everyKey (rowOK 5 level5) level6rrlrr) = true
  rw [level6rrlrl_ok, level6rrlrr_ok]
  decide +kernel
def level6rrl : BinaryTree (List W) := .node [v359, v474, v705, v1000, v1013, v1194, v1348] level6rrll level6rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrl_ok : everyKey (rowOK 5 level5) level6rrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrll && everyKey (rowOK 5 level5) level6rrlr) = true
  rw [level6rrll_ok, level6rrlr_ok]
  decide +kernel
def level6rrrll : BinaryTree (List W) := (.node [v359, v474, v705, v1013, v1194, v1271] (.node [v359, v474, v705, v1013, v1194, v1243, v1348] (.node [v359, v474, v705, v1013, v1194, v1217, v1348] (.node [v359, v474, v705, v1013, v1194, v1207, v1348] (.node [v359, v474, v705, v1013, v1194, v1206, v1348] (.node [v359, v474, v705, v1013, v1194, v1202, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1194, v1210, v1348] (.node [v359, v474, v705, v1013, v1194, v1208, v1348] .nil .nil) .nil)) (.node [v359, v474, v705, v1013, v1194, v1226, v1348] (.node [v359, v474, v705, v1013, v1194, v1225, v1348] (.node [v359, v474, v705, v1013, v1194, v1223, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1194, v1236, v1348] (.node [v359, v474, v705, v1013, v1194, v1227, v1348] .nil .nil) .nil))) (.node [v359, v474, v705, v1013, v1194, v1258, v1348] (.node [v359, v474, v705, v1013, v1194, v1246, v1348] (.node [v359, v474, v705, v1013, v1194, v1246] (.node [v359, v474, v705, v1013, v1194, v1245, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1194, v1257, v1348] (.node [v359, v474, v705, v1013, v1194, v1249, v1348] .nil .nil) .nil)) (.node [v359, v474, v705, v1013, v1194, v1265, v1348] (.node [v359, v474, v705, v1013, v1194, v1263, v1348] (.node [v359, v474, v705, v1013, v1194, v1262, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1194, v1268, v1348] (.node [v359, v474, v705, v1013, v1194, v1267, v1348] .nil .nil) .nil)))) (.node [v359, v474, v705, v1013, v1194, v1304, v1348] (.node [v359, v474, v705, v1013, v1194, v1282, v1461] (.node [v359, v474, v705, v1013, v1194, v1276, v1348] (.node [v359, v474, v705, v1013, v1194, v1271, v1348] (.node [v359, v474, v705, v1013, v1194, v1271, v1282] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1194, v1282, v1348] (.node [v359, v474, v705, v1013, v1194, v1278, v1348] .nil .nil) .nil)) (.node [v359, v474, v705, v1013, v1194, v1300, v1348] (.node [v359, v474, v705, v1013, v1194, v1295, v1348] (.node [v359, v474, v705, v1013, v1194, v1294, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1194, v1302, v1348] (.node [v359, v474, v705, v1013, v1194, v1301, v1348] .nil .nil) .nil))) (.node [v359, v474, v705, v1013, v1194, v1315, v1461] (.node [v359, v474, v705, v1013, v1194, v1310, v1348] (.node [v359, v474, v705, v1013, v1194, v1309, v1348] (.node [v359, v474, v705, v1013, v1194, v1305, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1194, v1315, v1348] (.node [v359, v474, v705, v1013, v1194, v1311, v1348] .nil .nil) .nil)) (.node [v359, v474, v705, v1013, v1194, v1324, v1348] (.node [v359, v474, v705, v1013, v1194, v1323, v1348] (.node [v359, v474, v705, v1013, v1194, v1322, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1194, v1325, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrll_ok : everyKey (rowOK 5 level5) level6rrrll = true := by decide +kernel
def level6rrrlr : BinaryTree (List W) := (.node [v359, v474, v705, v1013, v1194, v1348, v1394] (.node [v359, v474, v705, v1013, v1194, v1348] (.node [v359, v474, v705, v1013, v1194, v1335, v1348] (.node [v359, v474, v705, v1013, v1194, v1332, v1348] (.node [v359, v474, v705, v1013, v1194, v1331, v1348] (.node [v359, v474, v705, v1013, v1194, v1327, v1461] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1194, v1334, v1348] (.node [v359, v474, v705, v1013, v1194, v1333, v1348] .nil .nil) .nil)) (.node [v359, v474, v705, v1013, v1194, v1340, v1348] (.node [v359, v474, v705, v1013, v1194, v1337, v1461] (.node [v359, v474, v705, v1013, v1194, v1337, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1194, v1342, v1348] (.node [v359, v474, v705, v1013, v1194, v1341, v1348] .nil .nil) .nil))) (.node [v359, v474, v705, v1013, v1194, v1348, v1366] (.node [v359, v474, v705, v1013, v1194, v1348, v1360] (.node [v359, v474, v705, v1013, v1194, v1348, v1353] (.node [v359, v474, v705, v1013, v1194, v1348, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1194, v1348, v1363] (.node [v359, v474, v705, v1013, v1194, v1348, v1362] .nil .nil) .nil)) (.node [v359, v474, v705, v1013, v1194, v1348, v1378] (.node [v359, v474, v705, v1013, v1194, v1348, v1376] (.node [v359, v474, v705, v1013, v1194, v1348, v1373] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1194, v1348, v1387] (.node [v359, v474, v705, v1013, v1194, v1348, v1381] .nil .nil) .nil)))) (.node [v359, v474, v705, v1013, v1194, v1348, v1431] (.node [v359, v474, v705, v1013, v1194, v1348, v1414] (.node [v359, v474, v705, v1013, v1194, v1348, v1409] (.node [v359, v474, v705, v1013, v1194, v1348, v1400] (.node [v359, v474, v705, v1013, v1194, v1348, v1399] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1194, v1348, v1413] (.node [v359, v474, v705, v1013, v1194, v1348, v1410] .nil .nil) .nil)) (.node [v359, v474, v705, v1013, v1194, v1348, v1420] (.node [v359, v474, v705, v1013, v1194, v1348, v1417] (.node [v359, v474, v705, v1013, v1194, v1348, v1416] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1194, v1348, v1430] (.node [v359, v474, v705, v1013, v1194, v1348, v1424] .nil .nil) .nil))) (.node [v359, v474, v705, v1013, v1194, v1348, v1461] (.node [v359, v474, v705, v1013, v1194, v1348, v1441] (.node [v359, v474, v705, v1013, v1194, v1348, v1438] (.node [v359, v474, v705, v1013, v1194, v1348, v1437] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1194, v1348, v1449] (.node [v359, v474, v705, v1013, v1194, v1348, v1442] .nil .nil) .nil)) (.node [v359, v474, v705, v1013, v1194, v1348, v1469] (.node [v359, v474, v705, v1013, v1194, v1348, v1468] (.node [v359, v474, v705, v1013, v1194, v1348, v1467] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1194, v1348, v1470] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrlr_ok : everyKey (rowOK 5 level5) level6rrrlr = true := by decide +kernel
def level6rrrl : BinaryTree (List W) := .node [v359, v474, v705, v1013, v1194, v1327, v1348] level6rrrll level6rrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrl_ok : everyKey (rowOK 5 level5) level6rrrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrrll && everyKey (rowOK 5 level5) level6rrrlr) = true
  rw [level6rrrll_ok, level6rrrlr_ok]
  decide +kernel
def level6rrrrl : BinaryTree (List W) := (.node [v359, v474, v705, v1013, v1194, v1420] (.node [v359, v474, v705, v1013, v1194, v1348, v1491] (.node [v359, v474, v705, v1013, v1194, v1348, v1483] (.node [v359, v474, v705, v1013, v1194, v1348, v1475] (.node [v359, v474, v705, v1013, v1194, v1348, v1474] (.node [v359, v474, v705, v1013, v1194, v1348, v1472] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1194, v1348, v1480] (.node [v359, v474, v705, v1013, v1194, v1348, v1476] .nil .nil) .nil)) (.node [v359, v474, v705, v1013, v1194, v1348, v1487] (.node [v359, v474, v705, v1013, v1194, v1348, v1485] (.node [v359, v474, v705, v1013, v1194, v1348, v1484] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1194, v1348, v1490] (.node [v359, v474, v705, v1013, v1194, v1348, v1488] .nil .nil) .nil))) (.node [v359, v474, v705, v1013, v1194, v1378] (.node [v359, v474, v705, v1013, v1194, v1348, v1494] (.node [v359, v474, v705, v1013, v1194, v1348, v1493] (.node [v359, v474, v705, v1013, v1194, v1348, v1492] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1194, v1373] (.node [v359, v474, v705, v1013, v1194, v1362] .nil .nil) .nil)) (.node [v359, v474, v705, v1013, v1194, v1399] (.node [v359, v474, v705, v1013, v1194, v1394] (.node [v359, v474, v705, v1013, v1194, v1387] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1194, v1414] (.node [v359, v474, v705, v1013, v1194, v1400] .nil .nil) .nil)))) (.node [v359, v474, v705, v1013, v1194, v1461, v1474] (.node [v359, v474, v705, v1013, v1194, v1442] (.node [v359, v474, v705, v1013, v1194, v1424, v1483] (.node [v359, v474, v705, v1013, v1194, v1424, v1474] (.node [v359, v474, v705, v1013, v1194, v1424, v1461] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1194, v1438] (.node [v359, v474, v705, v1013, v1194, v1431] .nil .nil) .nil)) (.node [v359, v474, v705, v1013, v1194, v1461, v1461] (.node [v359, v474, v705, v1013, v1194, v1461] (.node [v359, v474, v705, v1013, v1194, v1449] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1194, v1461, v1471] (.node [v359, v474, v705, v1013, v1194, v1461, v1469] .nil .nil) .nil))) (.node [v359, v474, v705, v1013, v1227, v1348] (.node [v359, v474, v705, v1013, v1194, v1461, v1487] (.node [v359, v474, v705, v1013, v1194, v1461, v1483] (.node [v359, v474, v705, v1013, v1194, v1461, v1480] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1225, v1348] (.node [v359, v474, v705, v1013, v1194, v1461, v1494] .nil .nil) .nil)) (.node [v359, v474, v705, v1013, v1258, v1348] (.node [v359, v474, v705, v1013, v1249, v1348] (.node [v359, v474, v705, v1013, v1245, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1263, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrrl_ok : everyKey (rowOK 5 level5) level6rrrrl = true := by decide +kernel
def level6rrrrr : BinaryTree (List W) := (.node [v359, v474, v847, v1013, v1194, v1348] (.node [v359, v474, v705, v1034, v1194, v1348] (.node [v359, v474, v705, v1013, v1301, v1348] (.node [v359, v474, v705, v1013, v1282, v1337, v1348] (.node [v359, v474, v705, v1013, v1282, v1327, v1348] (.node [v359, v474, v705, v1013, v1278, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1295, v1348] (.node [v359, v474, v705, v1013, v1282, v1348, v1483] .nil .nil) .nil)) (.node [v359, v474, v705, v1013, v1315, v1327, v1348] (.node [v359, v474, v705, v1013, v1311, v1348] (.node [v359, v474, v705, v1013, v1305, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1013, v1315, v1348, v1483] (.node [v359, v474, v705, v1013, v1315, v1337, v1348] .nil .nil) .nil))) (.node [v359, v474, v705, v1114, v1194, v1337, v1348] (.node [v359, v474, v705, v1098, v1194, v1348] (.node [v359, v474, v705, v1081, v1194, v1348] (.node [v359, v474, v705, v1070, v1194, v1348] .nil .nil) .nil) (.node [v359, v474, v705, v1114, v1159, v1194, v1348] (.node [v359, v474, v705, v1110, v1194, v1348] .nil .nil) .nil)) (.node [v359, v474, v705, v1138, v1159, v1194, v1348] (.node [v359, v474, v705, v1127, v1194, v1348] (.node [v359, v474, v705, v1114, v1194, v1348, v1474] .nil .nil) .nil) (.node [v359, v474, v847, v1013, v1194] .nil .nil)))) (.node [v359, v705, v763, v1013, v1194, v1348, v1424] (.node [v359, v614, v705, v1013, v1194, v1348] (.node [v359, v474, v941, v1013, v1194, v1348] (.node [v359, v474, v856, v1013, v1194, v1461] (.node [v359, v474, v856, v1013, v1194, v1348, v1461] .nil .nil) .nil) (.node [v359, v499, v705, v1013, v1194, v1348] (.node [v359, v474, v950, v1013, v1159, v1194, v1348] .nil .nil) .nil)) (.node [v359, v642, v705, v950, v1013, v1194, v1348] (.node [v359, v619, v705, v1013, v1194, v1348, v1424] (.node [v359, v619, v705, v950, v1013, v1194, v1348] .nil .nil) .nil) (.node [v359, v705, v755, v1013, v1194, v1315, v1348] (.node [v359, v705, v746, v1013, v1138, v1194, v1348] .nil .nil) .nil))) (.node [v474, v619, v705, v1013, v1114, v1194, v1348] (.node [v437, v474, v619, v705, v1013, v1194, v1348] (.node [v419, v474, v572, v705, v1013, v1194, v1348] (.node [v405, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v474, v619, v705, v856, v1013, v1194, v1348] (.node [v474, v572, v705, v1013, v1194, v1348] .nil .nil) .nil)) (.node [v474, v705, v892, v1013, v1194, v1282, v1348] (.node [v474, v705, v865, v1013, v1114, v1194, v1348] (.node [v474, v653, v705, v856, v1013, v1194, v1348] .nil .nil) .nil) (.node [v474, v705, v902, v1013, v1194, v1348, v1469] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrrr_ok : everyKey (rowOK 5 level5) level6rrrrr = true := by decide +kernel
def level6rrrr : BinaryTree (List W) := .node [v359, v474, v705, v1013, v1268, v1348] level6rrrrl level6rrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrr_ok : everyKey (rowOK 5 level5) level6rrrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrrrl && everyKey (rowOK 5 level5) level6rrrrr) = true
  rw [level6rrrrl_ok, level6rrrrr_ok]
  decide +kernel
def level6rrr : BinaryTree (List W) := .node [v359, v474, v705, v1013, v1194, v1348, v1471] level6rrrl level6rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrr_ok : everyKey (rowOK 5 level5) level6rrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrrl && everyKey (rowOK 5 level5) level6rrrr) = true
  rw [level6rrrl_ok, level6rrrr_ok]
  decide +kernel
def level6rr : BinaryTree (List W) := .node [v359, v474, v705, v1013, v1194, v1194, v1348] level6rrl level6rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rr_ok : everyKey (rowOK 5 level5) level6rr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrl && everyKey (rowOK 5 level5) level6rrr) = true
  rw [level6rrl_ok, level6rrr_ok]
  decide +kernel
def level6r : BinaryTree (List W) := .node [v359, v474, v705, v870, v1194, v1348] level6rl level6rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6r_ok : everyKey (rowOK 5 level5) level6r = true := by
  change (_ && everyKey (rowOK 5 level5) level6rl && everyKey (rowOK 5 level5) level6rr) = true
  rw [level6rl_ok, level6rr_ok]
  decide +kernel
def level6 : BinaryTree (List W) := .node [v359, v433, v474, v705, v1013, v1194, v1348] level6l level6r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6_ok : everyKey (rowOK 5 level5) level6 = true := by
  change (_ && everyKey (rowOK 5 level5) level6l && everyKey (rowOK 5 level5) level6r) = true
  rw [level6l_ok, level6r_ok]
  decide +kernel
theorem closed6 : Closed 6 level6 := closed_next 5 (by decide) level6 level5 closed5 level6_ok
def level7l : BinaryTree (List W) := (.node [v234, v359, v474, v705, v1013, v1194, v1348] (.node [v128, v359, v474, v705, v1013, v1194, v1348] (.node [v68, v359, v474, v705, v1013, v1194, v1348] (.node [v47, v359, v474, v705, v1013, v1194] (.node [v41, v359, v474, v705, v1013, v1194, v1348] (.node [v29, v359, v474, v705, v1013, v1194, v1348] .nil .nil) .nil) (.node [v47, v359, v474, v705, v1013, v1194, v1348] .nil .nil)) (.node [v106, v359, v474, v705, v1013, v1194, v1348] (.node [v74, v359, v474, v705, v1013, v1194, v1348] .nil .nil) (.node [v122, v359, v474, v705, v1013, v1194, v1348] .nil .nil))) (.node [v190, v359, v474, v705, v1013, v1194, v1348] (.node [v153, v359, v474, v705, v1013, v1194, v1348] (.node [v142, v359, v474, v705, v1013, v1194, v1348] .nil .nil) (.node [v175, v359, v474, v705, v1013, v1194, v1348] .nil .nil)) (.node [v215, v359, v474, v705, v1013, v1194, v1348] (.node [v202, v359, v474, v705, v1013, v1194, v1348] .nil .nil) (.node [v223, v359, v474, v705, v1013, v1194, v1348] .nil .nil)))) (.node [v325, v359, v474, v705, v1013, v1194, v1348] (.node [v292, v359, v474, v705, v1013, v1194, v1348] (.node [v252, v359, v474, v705, v1013, v1194, v1348] (.node [v245, v359, v474, v705, v1013, v1194, v1348] .nil .nil) (.node [v276, v359, v474, v705, v1013, v1194, v1348] .nil .nil)) (.node [v313, v359, v474, v705, v1013, v1194, v1348] (.node [v304, v359, v474, v705, v1013, v1194, v1348] .nil .nil) (.node [v325, v359, v474, v705, v1013, v1194] .nil .nil))) (.node [v359, v448, v474, v705, v1013, v1194, v1348] (.node [v359, v428, v474, v705, v1013, v1194, v1348] (.node [v359, v419, v474, v705, v1013, v1194, v1348] .nil .nil) (.node [v359, v437, v474, v705, v1013, v1194, v1348] .nil .nil)) (.node [v359, v474, v509, v705, v1013, v1194, v1348] (.node [v359, v462, v474, v705, v1013, v1194, v1348] .nil .nil) (.node [v359, v474, v517, v705, v1013, v1194, v1348] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7l_ok : everyKey (rowOK 6 level6) level7l = true := by decide +kernel
def level7r : BinaryTree (List W) := (.node [v359, v474, v705, v958, v1013, v1194, v1348] (.node [v359, v474, v705, v746, v1013, v1194, v1348] (.node [v359, v474, v642, v705, v1013, v1194, v1348] (.node [v359, v474, v619, v705, v1013, v1194, v1348] (.node [v359, v474, v525, v705, v1013, v1194, v1348] .nil .nil) (.node [v359, v474, v630, v705, v1013, v1194, v1348] .nil .nil)) (.node [v359, v474, v666, v705, v1013, v1194, v1348] (.node [v359, v474, v653, v705, v1013, v1194, v1348] .nil .nil) (.node [v359, v474, v691, v705, v1013, v1194, v1348] .nil .nil))) (.node [v359, v474, v705, v865, v1013, v1194, v1348] (.node [v359, v474, v705, v763, v1013, v1194, v1348] (.node [v359, v474, v705, v755, v1013, v1194, v1348] .nil .nil) (.node [v359, v474, v705, v856, v1013, v1194, v1348] .nil .nil)) (.node [v359, v474, v705, v902, v1013, v1194, v1348] (.node [v359, v474, v705, v892, v1013, v1194, v1348] .nil .nil) (.node [v359, v474, v705, v950, v1013, v1194, v1348] .nil .nil)))) (.node [v359, v474, v705, v1013, v1194, v1327, v1348] (.node [v359, v474, v705, v1013, v1159, v1194, v1348] (.node [v359, v474, v705, v1013, v1114, v1194, v1348] (.node [v359, v474, v705, v990, v1013, v1194, v1348] .nil .nil) (.node [v359, v474, v705, v1013, v1138, v1194, v1348] .nil .nil)) (.node [v359, v474, v705, v1013, v1194, v1282, v1348] (.node [v359, v474, v705, v1013, v1166, v1194, v1348] .nil .nil) (.node [v359, v474, v705, v1013, v1194, v1315, v1348] .nil .nil))) (.node [v359, v474, v705, v1013, v1194, v1348, v1469] (.node [v359, v474, v705, v1013, v1194, v1348, v1424] (.node [v359, v474, v705, v1013, v1194, v1337, v1348] .nil .nil) (.node [v359, v474, v705, v1013, v1194, v1348, v1461] .nil .nil)) (.node [v359, v474, v705, v1013, v1194, v1348, v1483] (.node [v359, v474, v705, v1013, v1194, v1348, v1474] .nil .nil) (.node [v359, v474, v705, v1013, v1194, v1461] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7r_ok : everyKey (rowOK 6 level6) level7r = true := by decide +kernel
def level7 : BinaryTree (List W) := .node [v359, v474, v525, v705, v1013, v1194] level7l level7r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7_ok : everyKey (rowOK 6 level6) level7 = true := by
  change (_ && everyKey (rowOK 6 level6) level7l && everyKey (rowOK 6 level6) level7r) = true
  rw [level7l_ok, level7r_ok]
  decide +kernel
theorem closed7 : Closed 7 level7 := closed_next 6 (by decide) level7 level6 closed6 level7_ok
def level8 : BinaryTree (List W) := (.node [v359, v474, v705, v1013, v1194, v1348] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8_ok : everyKey (rowOK 7 level7) level8 = true := by decide +kernel
theorem closed8 : Closed 8 level8 := closed_next 7 (by decide) level8 level7 closed7 level8_ok

theorem lower : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z 8 ins.toFinset :=
  @no_build 8 level8 ins (by decide +kernel) (by decide) closed8 (by decide +kernel)
def witness : List Gate := [⟨.and,[1,3]⟩, ⟨.and,[1,4]⟩, ⟨.or,[5,7]⟩, ⟨.and,[0,8]⟩, ⟨.and,[3,4]⟩, ⟨.or,[0,10]⟩, ⟨.or,[1,11]⟩, ⟨.and,[2,12]⟩, ⟨.or,[6,9]⟩, ⟨.or,[13,14]⟩]
theorem upper : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 10 ∧ ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xfeeaeeeafce8ece0 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact ⟨witness,15,by simp [witness],rfl,by decide +kernel⟩
end PEqualNP.Outside.L_meta_16013_aux

open PEqualNP.Outside.L_meta_16013_aux in
theorem PEqualNP.Outside.L_meta_16013 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4243123424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4243123424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  have code : 4276809450 * 2 ^ 32 + 4243123424 = 0xfeeaeeeafce8ece0 := by decide
  simp only [code] at h ⊢
  obtain ⟨C,legal,size,computes⟩ := h
  obtain ⟨gs,o,mono,bound,ev⟩ := replace 0xfeeaeeeafce8ece0 10 ins (by decide +kernel) sampled rfl lower upper C.gates C.output legal computes
  exact ⟨⟨gs,o⟩,mono,bound.trans size,ev⟩
