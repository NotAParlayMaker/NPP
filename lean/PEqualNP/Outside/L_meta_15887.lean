import PEqualNP.Defs

-- The live-wire search and circuit compiler are adapted from tacyon52 in L-meta-8639, pull request 12794 under Apache-2.0.
namespace PEqualNP.Outside.L_meta_15887_aux

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

def v0 : W := 0x2b1698bb00000070e0077
def v1 : W := 0x51f373990000000707788
def v2 : W := 0x63a1a3b000000678187f0
def v3 : W := 0x6bb7bbbb00000678f87f7
def v4 : W := 0x7a45f922000007801f800
def v5 : W := 0x7bf64200000007ffe0000
def v6 : W := 0x7bf7fbbb00000077e77ff
def v7 : W := 0x135800098ff0000000000077
def v8 : W := 0x24a00012500000e300007788
def v9 : W := 0x26b00013599000e300007788
def v10 : W := 0x34e0001a5f00030c000187f0
def v11 : W := 0x36f0001b5f9003ef0001f7f8
def v12 : W := 0x3700001b922003f00001f800
def v13 : W := 0x37b0001bdbb003f30001ff88
def v14 : W := 0x37e0001bdf2003fc0001fff0
def v15 : W := 0x37f80000444003ff80000000
def v16 : W := 0x37f800135dd003ff80007788
def v17 : W := 0x37f8001bdff000e3000077ff
def v18 : W := 0x37ffbf64644003fffffe0000
def v19 : W := 0x821011210990000000000000
def v20 : W := 0xa6b01133599000e300007788
def v21 : W := 0x4c05851a00dd00000070e0077
def v22 : W := 0x980b01b206990380300700788
def v23 : W := 0xd00e05a006d00c00c078007f0
def v24 : W := 0xd34e05a1a7f00c30c078187f0
def v25 : W := 0xdc0005ba02000fc0007fe0000
def v26 : W := 0xdc0f840804440fc0f80000000
def v27 : W := 0xdc0f85ba06dd03803077e07ff
def v28 : W := 0xdc0ffe4dfd660fc0ff801f800
def v29 : W := 0xdf7005bbbb220fff007fff800
def v30 : W := 0xdf7f840804440ffff80000000
def v31 : W := 0x10c31881e180f00000000e0007
def v32 : W := 0x2208010404000038e300707008
def v33 : W := 0x228a110525009038e300707008
def v34 : W := 0x228a111525099038e300707008
def v35 : W := 0x320b018445802300f018007800
def v36 : W := 0x320b07a45f922300f07801f800
def v37 : W := 0x328b11856580b338f318707808
def v38 : W := 0x32c80185e400033c00187e0000
def v39 : W := 0x32c807bfe420033c007ffe0000
def v40 : W := 0x32ca1185e500933ce3187e7008
def v41 : W := 0x32cb18008000433cf380000000
def v42 : W := 0x32cb1905a500d33cf380707008
def v43 : W := 0x32cb1985e580f038e3007e700f
def v44 : W := 0x32cb1e3a9a3b433cf3e78187f0
def v45 : W := 0x32fce185fe5f033f0c187f87f0
def v46 : W := 0x3f0be1de45ed23c0fc1f807ff0
def v47 : W := 0x3fc801dfe42003fc001ffe0000
def v48 : W := 0x3fcbf840804443fcff80000000
def v49 : W := 0x4410426008060cc30c67818070
def v50 : W := 0x44104270080f00000007000070
def v51 : W := 0x501102a048822f031078018800
def v52 : W := 0x501302a0498220000000000000
def v53 : W := 0x544002e0c0000fc4007f8e0000
def v54 : W := 0x5451484080044fc71c80000000
def v55 : W := 0x54514ae0c886600000070e0077
def v56 : W := 0x54514d5fb73ddfc71c80707788
def v57 : W := 0x5466b2e0d3599fc4e37f8e7788
def v58 : W := 0x5477f84080444fc7ff80000000
def v59 : W := 0x54c002f1e000000000070e0000
def v60 : W := 0x54d35840800440000000000000
def v61 : W := 0x54d35af1e98ff00000070e0077
def v62 : W := 0x54f7f84080444003ff80000000
def v63 : W := 0x54f7faf1fbdff000e3070e77ff
def v64 : W := 0x5991b2bb68ebbf3b1378718f88
def v65 : W := 0x5dd1f84080444fff1f80000000
def v66 : W := 0x5dd3f840804440fc0f80000000
def v67 : W := 0x669a53652d069cfbef67f1f078
def v68 : W := 0x76db5bf5ed8ff038e3077e707f
def v69 : W := 0x8924a40a127000000000000780
def v70 : W := 0x8924a40a12700cc30c60818780
def v71 : W := 0x8924a41a127900000000000780
def v72 : W := 0x8924a41a12790cc30c60818780
def v73 : W := 0x8924a63a1a7b000000678187f0
def v74 : W := 0x8924a63a1a7b0cc30c678187f0
def v75 : W := 0x8934e40a1a7f0cc30c608187f0
def v76 : W := 0x8934e41a1a7f00030c000187f0
def v77 : W := 0x89a6b41b337990000000000780
def v78 : W := 0x8d24e45a127d00c00c078007f0
def v79 : W := 0x8d24e45a127d0cc30c678187f0
def v80 : W := 0x99e7bc8bf3f0fcc30c608f8787
def v81 : W := 0xa22c050416100f03f07801f800
def v82 : W := 0xa22c07a45f922f03f07801f800
def v83 : W := 0xa22e050417100000e000007000
def v84 : W := 0xa22e07a45f922000e07801f800
def v85 : W := 0xa6ec5d55b61ddf03f07f0ff877
def v86 : W := 0xab08050e042000380000700000
def v87 : W := 0xab08050e04200ffc0078f00000
def v88 : W := 0xab0807bf64200ffc007ffe0000
def v89 : W := 0xab1b5d0e0daffffc0078f00077
def v90 : W := 0xab2ca00000400fffff80000000
def v91 : W := 0xab2ca2b169cbbfffff870e0077
def v92 : W := 0xab2ca50e16700038e300707788
def v93 : W := 0xab2ca51f37799038e300707788
def v94 : W := 0xab88051f242000380000700000
def v95 : W := 0xab88051f24200ffc0078f00000
def v96 : W := 0xab8807bf64200038007ffe0000
def v97 : W := 0xab8a151f252990380000700000
def v98 : W := 0xabacb51f36799038e300707788
def v99 : W := 0xabaeb00000400038e300000000
def v100 : W := 0xabaeb51f37799038e300707788
def v101 : W := 0xafc8055fa42000fc0007fe0000
def v102 : W := 0xafc8055fa4200ffc007ffe0000
def v103 : W := 0xafc8fd4e84644ffc0ff8f00000
def v104 : W := 0xafc8fd5fa46440fc0f80700000
def v105 : W := 0xafecf84080444fffff80000000
def v106 : W := 0xafeef840804440fcef80000000
def v107 : W := 0xbbc8058fe4200ffc0078fe0000
def v108 : W := 0xbbc8059fe420033c00187e0000
def v109 : W := 0xc03406201a120c030060018000
def v110 : W := 0xc934a62a1a720cc30c60818780
def v111 : W := 0xc934a63a1a7b0c030060018780
def v112 : W := 0xcd00067a00200cc00067800000
def v113 : W := 0xcd24a67a12700cc30c67818780
def v114 : W := 0xcd24a67a12790cc00067800780
def v115 : W := 0xcd34e04000440cc30c00000000
def v116 : W := 0xcd34e44a12740cc30c60818780
def v117 : W := 0xcd34e45a127d0cc30c00000780
def v118 : W := 0xcd34e66a1a760cc30c678187f0
def v119 : W := 0xcd34e67a1a7f000000070007f0
def v120 : W := 0xcd34e67a1a7f0cc30c678187f0
def v121 : W := 0xcd34e6fb7bffbcc30c678f87f7
def v122 : W := 0xcd37fe7a1bfffcc30c678187f7
def v123 : W := 0xcdb6f67b3b7f9cc30c678187f0
def v124 : W := 0xcdf4f84080444cff0f80000000
def v125 : W := 0xcdf4fe7bba7fdcc30c678f87f7
def v126 : W := 0xdd35e6fa5aff2fc31c7f818ff0
def v127 : W := 0xdd37e6fa5bff2cc30c678187f0
def v128 : W := 0xdd74e6fada7f0fc70c7f8f87f0
def v129 : W := 0xdd75e84080444fc71c80000000
def v130 : W := 0xdd75ee7a9a7f4fc71ce78187f0
def v131 : W := 0xdd75eefadaff6cc30c678f87f7
def v132 : W := 0xddf4e6fbfa7f0cc30c678f87f0
def v133 : W := 0xddf7f84080444cc30c00000000
def v134 : W := 0xddf7fe7a9a7f4cc30c678187f0
def v135 : W := 0xddf7fefbfbfff00000070e07f7
def v136 : W := 0xddf7fefbfbfffcc30c678f87f7
def v137 : W := 0xef08077e04200ffc007ff00000
def v138 : W := 0xef88077f24200cf80067f00000
def v139 : W := 0xefbef77f3f7f9cfbef67f1f7f8
def v140 : W := 0xf20807a444000f000078000000
def v141 : W := 0xf20807a45f922f00007801f800
def v142 : W := 0xf20807bf64200f00007ffe0000
def v143 : W := 0xf23d07a45e922f03f07801f800
def v144 : W := 0xf23f000000000f03f000000000
def v145 : W := 0xf23f07a45f922000e000007000
def v146 : W := 0xf23f07a45f922f03f07801f800
def v147 : W := 0xf23fffa45fd66f03fff801f800
def v148 : W := 0xf2bf17b57f9bbf03f07801f800
def v149 : W := 0xf67f4fe4df966fc7fcf801f800
def v150 : W := 0xf67fffe4dfd66fc7fff801f800
def v151 : W := 0xf6ff5fe4df966f03f07801f800
def v152 : W := 0xf6ff5ff5ff9fff03f07f0ff877
def v153 : W := 0xf6ffffe4dfd66f03fff801f800
def v154 : W := 0xfb0807ae44200ffc0078f00000
def v155 : W := 0xfb8807bf64200f380078700000
def v156 : W := 0xfbbfb7bf7ffbb038e300707788
def v157 : W := 0xfbbfb7bf7ffbbf3bf37871ff88
def v158 : W := 0xff0807fe44200fc0007f800000
def v159 : W := 0xff3ce7fe5e7f0fc30c7f8187f0
def v160 : W := 0xff3fe7e45fd62fc3fc7801f800
def v161 : W := 0xff3fe7fe5fff2fc3fc7f81fff0
def v162 : W := 0xff4807eec4200ffc007ffe0000
def v163 : W := 0xff7de84080444fffff80000000
def v164 : W := 0xff7defeedef66038e3077e77ff
def v165 : W := 0xff7fefe4dfd66fc7fcf801f800
def v166 : W := 0xffc8004080000ffc0000000000
def v167 : W := 0xffc8054e84200ffc0078f00000
def v168 : W := 0xffc8055fa4200ffc0000700000
def v169 : W := 0xffc807ffe420003800077e0000
def v170 : W := 0xffc807ffe4200ffc007ffe0000
def v171 : W := 0xffc807ffedabbffc007ffe0077
def v172 : W := 0xffc85fffe42ddffc007ffe0077
def v173 : W := 0xffc8f84080444ffc0f80000000
def v174 : W := 0xffc8ffffe4644ffc0ffffe0000
def v175 : W := 0xffca17ffe5299ffc007ffe0000
def v176 : W := 0xffcb1fffe5a0fffc007ffe0007
def v177 : W := 0xffd847ffec260fff0c7fff8070
def v178 : W := 0xffd847ffec2f0ffc007ffe0070
def v179 : W := 0xffd907ffeca22fff107fff8800
def v180 : W := 0xffd94fffe4244fff1cfffe0000
def v181 : W := 0xffd94fffeca66ffc007ffe0077
def v182 : W := 0xffdb07ffeda22ffc007ffe0000
def v183 : W := 0xffdb5fffe4244ffc007ffe0000
def v184 : W := 0xffdb5fffedaff03800077e0077
def v185 : W := 0xffdb5fffedaffffc007ffe0077
def v186 : W := 0xffeeb7fff7799ffce37ffe7788
def v187 : W := 0xfffc07fffe320fff007fff8000
def v188 : W := 0xfffce7ffe4640fff0c7ffe0000
def v189 : W := 0xfffce7fffe7f0fff0c7fff87f0
def v190 : W := 0xffff07ffffb22ffff07ffff800
def v191 : W := 0xfffff84080444038e300000000
def v192 : W := 0xfffff84080444fffff80000000
def v193 : W := 0xfffff8409bd66fffff8001f800
def v194 : W := 0xfffff851a14ddfffff80000000
def v195 : W := 0xfffff945a544dfffff80707008
def v196 : W := 0xfffff9c4c5c46fffff98007800
def v197 : W := 0xfffffae0c8c66ffffff8018800
def v198 : W := 0xfffffae0c9c66fffff80000000
def v199 : W := 0xfffffaf1e9cfffffff870e0077
def v200 : W := 0xfffffd4496544ffffff801f800
def v201 : W := 0xfffffd4497544fffff80007000
def v202 : W := 0xfffffd4e84644ffffff8f00000
def v203 : W := 0xfffffd5fa4644fffff80700000
def v204 : W := 0xfffffd5fb77dd038e300707788
def v205 : W := 0xfffffd5fb77ddfffff80707788
def v206 : W := 0xfffffe609a564fffffe0018000
def v207 : W := 0xfffffe7a9a7f4fffffe78187f0
def v208 : W := 0xffffffe4c4444ffffff8000000
def v209 : W := 0xffffffe4dfd66fc3fc7801f800
def v210 : W := 0xffffffe4dfd66ffffff801f800
def v211 : W := 0xffffffffe4644ffffffffe0000
def v212 : W := 0xfffffffffffff038e3077e77ff

def ins : List W := [v61, v100, v120, v146, v170, v192]
theorem sampled : ∀ j : Fin 104, Nat.testBit 0xeeeaeaeaeec8ea88 (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
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
def level3 : BinaryTree (List W) := (.node [v97, v135, v146, v192] (.node [v77, v146, v184, v192] .nil .nil) .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level3_ok : everyKey (rowOK 2 level2) level3 = true := by decide +kernel
theorem closed3 : Closed 3 level3 := closed_next 2 (by decide) level3 level2 closed2 level3_ok
def level4 : BinaryTree (List W) := (.node [v61, v100, v104, v120, v146] (.node [v57, v61, v120, v146, v192] (.node [v44, v61, v100, v146, v170] (.node [v29, v61, v100, v120, v192] (.node [v28, v61, v100, v120, v170] (.node [v18, v61, v100, v120, v146] .nil .nil) .nil) (.node [v33, v61, v100, v165, v170] .nil .nil)) (.node [v46, v61, v100, v170, v192] (.node [v45, v61, v100, v146, v192] .nil .nil) (.node [v56, v61, v120, v146, v170] .nil .nil))) (.node [v61, v77, v94, v146, v192] (.node [v61, v67, v146, v170, v192] (.node [v61, v64, v120, v170, v192] .nil .nil) (.node [v61, v71, v97, v146, v192] .nil .nil)) (.node [v61, v94, v100, v120, v150] (.node [v61, v87, v100, v120, v153] .nil .nil) (.node [v61, v100, v103, v120, v146] .nil .nil)))) (.node [v61, v100, v159, v170, v210] (.node [v61, v100, v120, v158, v210] (.node [v61, v100, v120, v150, v170] (.node [v61, v100, v120, v142, v210] .nil .nil) (.node [v61, v100, v120, v153, v170] .nil .nil)) (.node [v61, v100, v120, v170, v209] (.node [v61, v100, v120, v165, v170] .nil .nil) (.node [v61, v100, v136, v170, v209] .nil .nil))) (.node [v91, v100, v120, v146, v170] (.node [v85, v100, v120, v170, v192] (.node [v80, v100, v146, v170, v192] .nil .nil) (.node [v89, v100, v120, v146, v192] .nil .nil)) (.node [v100, v136, v146, v184, v192] (.node [v100, v135, v146, v185, v192] .nil .nil) (.node [v120, v146, v164, v170, v192] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4_ok : everyKey (rowOK 3 level3) level4 = true := by decide +kernel
theorem closed4 : Closed 4 level4 := closed_next 3 (by decide) level4 level3 closed3 level4_ok
def level5lll : BinaryTree (List W) := (.node [v9, v61, v70, v100, v146, v192] (.node [v5, v15, v61, v100, v120, v146] (.node [v3, v61, v100, v120, v146, v170] (.node [v1, v54, v61, v120, v146, v170] (.node [v0, v90, v100, v120, v146, v170] .nil .nil) (.node [v2, v41, v61, v100, v146, v170] .nil .nil)) (.node [v4, v26, v61, v100, v120, v170] (.node [v3, v61, v100, v136, v146, v170] .nil .nil) .nil)) (.node [v9, v26, v61, v100, v120, v146] (.node [v7, v87, v100, v120, v146, v192] (.node [v6, v61, v100, v120, v146, v170] .nil .nil) (.node [v8, v61, v100, v120, v146, v192] .nil .nil)) (.node [v9, v53, v61, v120, v146, v192] (.node [v9, v33, v61, v100, v146, v192] .nil .nil) .nil))) (.node [v11, v61, v100, v120, v146, v192] (.node [v9, v61, v100, v120, v146, v210] (.node [v9, v61, v94, v120, v146, v192] (.node [v9, v61, v71, v100, v146, v192] .nil .nil) (.node [v9, v61, v100, v120, v146, v192] .nil .nil)) (.node [v10, v38, v61, v100, v146, v192] (.node [v9, v61, v100, v136, v146, v192] .nil .nil) .nil)) (.node [v16, v61, v100, v120, v146, v192] (.node [v13, v61, v100, v120, v146, v192] (.node [v12, v25, v61, v100, v120, v192] .nil .nil) (.node [v14, v61, v100, v120, v146, v192] .nil .nil)) (.node [v19, v120, v146, v170, v192, v212] (.node [v17, v61, v100, v120, v146, v192] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lll_ok : everyKey (rowOK 4 level4) level5lll = true := by decide +kernel
def level5llr : BinaryTree (List W) := (.node [v26, v61, v100, v120, v146, v174] (.node [v26, v33, v61, v100, v146, v170] (.node [v23, v35, v61, v100, v170, v192] (.node [v22, v51, v61, v120, v170, v192] (.node [v21, v81, v100, v120, v170, v192] .nil .nil) (.node [v22, v61, v100, v120, v170, v210] .nil .nil)) (.node [v25, v61, v100, v120, v170, v210] (.node [v24, v61, v100, v146, v170, v192] .nil .nil) .nil)) (.node [v26, v61, v94, v100, v120, v146] (.node [v26, v61, v71, v100, v146, v170] (.node [v26, v61, v70, v100, v146, v170] .nil .nil) (.node [v26, v61, v87, v100, v120, v146] .nil .nil)) (.node [v26, v61, v100, v120, v146, v170] (.node [v26, v61, v100, v120, v142, v146] .nil .nil) .nil))) (.node [v32, v61, v100, v146, v170, v192] (.node [v27, v61, v100, v120, v170, v192] (.node [v26, v61, v100, v120, v170, v210] (.node [v26, v61, v100, v120, v146, v185] .nil .nil) (.node [v26, v61, v100, v136, v146, v170] .nil .nil)) (.node [v31, v70, v100, v146, v170, v192] (.node [v30, v61, v100, v120, v146, v170] .nil .nil) .nil)) (.node [v33, v61, v94, v100, v146, v192] (.node [v33, v61, v71, v146, v170, v192] (.node [v33, v49, v61, v146, v170, v192] .nil .nil) (.node [v33, v61, v87, v100, v146, v192] .nil .nil)) (.node [v33, v61, v100, v146, v170, v192] (.node [v33, v61, v100, v129, v146, v170] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llr_ok : everyKey (rowOK 4 level4) level5llr = true := by decide +kernel
def level5ll : BinaryTree (List W) := .node [v20, v61, v100, v120, v146, v192] level5lll level5llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5ll_ok : everyKey (rowOK 4 level4) level5ll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lll && everyKey (rowOK 4 level4) level5llr) = true
  rw [level5lll_ok, level5llr_ok]
  decide +kernel
def level5lrl : BinaryTree (List W) := (.node [v52, v100, v120, v152, v170, v192] (.node [v39, v61, v100, v120, v146, v192] (.node [v35, v61, v100, v120, v170, v210] (.node [v33, v61, v100, v146, v185, v192] (.node [v33, v61, v100, v146, v170, v210] .nil .nil) (.node [v34, v61, v100, v146, v170, v192] .nil .nil)) (.node [v37, v61, v100, v146, v170, v192] (.node [v36, v61, v100, v120, v170, v192] .nil .nil) .nil)) (.node [v47, v61, v100, v120, v146, v192] (.node [v42, v61, v100, v146, v170, v192] (.node [v40, v61, v100, v146, v170, v192] .nil .nil) (.node [v43, v61, v100, v146, v170, v192] .nil .nil)) (.node [v50, v100, v136, v146, v170, v192] (.node [v48, v61, v100, v120, v146, v170] .nil .nil) .nil))) (.node [v61, v62, v100, v120, v146, v170] (.node [v59, v100, v120, v146, v185, v192] (.node [v58, v61, v94, v100, v120, v146] (.node [v55, v92, v120, v146, v170, v192] .nil .nil) (.node [v58, v61, v100, v120, v146, v170] .nil .nil)) (.node [v61, v62, v87, v100, v120, v146] (.node [v60, v100, v120, v146, v170, v199] .nil .nil) .nil)) (.node [v61, v68, v100, v146, v170, v192] (.node [v61, v65, v100, v120, v146, v170] (.node [v61, v63, v100, v120, v146, v192] .nil .nil) (.node [v61, v66, v100, v120, v146, v170] .nil .nil)) (.node [v61, v70, v87, v100, v146, v192] (.node [v61, v69, v100, v146, v170, v192] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrl_ok : everyKey (rowOK 4 level4) level5lrl = true := by decide +kernel
def level5lrr : BinaryTree (List W) := (.node [v61, v76, v100, v146, v170, v192] (.node [v61, v71, v100, v146, v170, v210] (.node [v61, v71, v87, v100, v146, v192] (.node [v61, v70, v100, v146, v170, v210] (.node [v61, v70, v100, v146, v170, v192] .nil .nil) (.node [v61, v70, v100, v146, v185, v192] .nil .nil)) (.node [v61, v71, v100, v146, v170, v192] (.node [v61, v71, v94, v100, v146, v192] .nil .nil) .nil)) (.node [v61, v73, v100, v146, v170, v192] (.node [v61, v71, v139, v146, v170, v192] (.node [v61, v71, v100, v146, v185, v192] .nil .nil) (.node [v61, v72, v100, v146, v170, v192] .nil .nil)) (.node [v61, v75, v100, v146, v170, v192] (.node [v61, v74, v100, v146, v170, v192] .nil .nil) .nil))) (.node [v61, v83, v120, v157, v170, v192] (.node [v61, v81, v100, v120, v170, v210] (.node [v61, v78, v100, v146, v170, v192] (.node [v61, v77, v100, v146, v170, v192] .nil .nil) (.node [v61, v79, v100, v146, v170, v192] .nil .nil)) (.node [v61, v83, v100, v120, v170, v210] (.node [v61, v82, v100, v120, v170, v192] .nil .nil) .nil)) (.node [v61, v87, v100, v120, v146, v202] (.node [v61, v86, v100, v120, v146, v192] (.node [v61, v84, v100, v120, v170, v192] .nil .nil) (.node [v61, v87, v100, v120, v146, v192] .nil .nil)) (.node [v61, v87, v100, v136, v146, v192] (.node [v61, v87, v100, v120, v146, v210] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrr_ok : everyKey (rowOK 4 level4) level5lrr = true := by decide +kernel
def level5lr : BinaryTree (List W) := .node [v61, v70, v94, v100, v146, v192] level5lrl level5lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lr_ok : everyKey (rowOK 4 level4) level5lr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrl && everyKey (rowOK 4 level4) level5lrr) = true
  rw [level5lrl_ok, level5lrr_ok]
  decide +kernel
def level5l : BinaryTree (List W) := .node [v33, v61, v100, v146, v170, v195] level5ll level5lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5l_ok : everyKey (rowOK 4 level4) level5l = true := by
  change (_ && everyKey (rowOK 4 level4) level5ll && everyKey (rowOK 4 level4) level5lr) = true
  rw [level5ll_ok, level5lr_ok]
  decide +kernel
def level5rll : BinaryTree (List W) := (.node [v61, v100, v105, v120, v146, v170] (.node [v61, v95, v100, v120, v146, v192] (.node [v61, v94, v100, v120, v146, v210] (.node [v61, v94, v100, v120, v146, v192] (.node [v61, v93, v120, v146, v170, v192] .nil .nil) (.node [v61, v94, v100, v120, v146, v203] .nil .nil)) (.node [v61, v94, v120, v146, v186, v192] (.node [v61, v94, v100, v136, v146, v192] .nil .nil) .nil)) (.node [v61, v99, v120, v146, v170, v205] (.node [v61, v97, v100, v120, v146, v192] (.node [v61, v96, v100, v120, v146, v192] .nil .nil) (.node [v61, v98, v120, v146, v170, v192] .nil .nil)) (.node [v61, v100, v102, v120, v146, v192] (.node [v61, v100, v101, v120, v146, v192] .nil .nil) .nil))) (.node [v61, v100, v112, v146, v189, v192] (.node [v61, v100, v109, v161, v170, v192] (.node [v61, v100, v107, v120, v146, v192] (.node [v61, v100, v106, v120, v146, v170] .nil .nil) (.node [v61, v100, v108, v120, v146, v192] .nil .nil)) (.node [v61, v100, v111, v146, v170, v192] (.node [v61, v100, v110, v146, v170, v192] .nil .nil) .nil)) (.node [v61, v100, v116, v146, v170, v192] (.node [v61, v100, v114, v146, v170, v192] (.node [v61, v100, v113, v146, v170, v192] .nil .nil) (.node [v61, v100, v115, v146, v170, v207] .nil .nil)) (.node [v61, v100, v118, v146, v170, v192] (.node [v61, v100, v117, v146, v170, v192] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rll_ok : everyKey (rowOK 4 level4) level5rll = true := by decide +kernel
def level5rlr : BinaryTree (List W) := (.node [v61, v100, v120, v146, v155, v192] (.node [v61, v100, v120, v140, v190, v192] (.node [v61, v100, v120, v137, v146, v192] (.node [v61, v100, v120, v129, v146, v170] (.node [v61, v100, v120, v124, v146, v170] .nil .nil) (.node [v61, v100, v120, v133, v146, v170] .nil .nil)) (.node [v61, v100, v120, v140, v170, v210] (.node [v61, v100, v120, v138, v146, v192] .nil .nil) .nil)) (.node [v61, v100, v120, v144, v170, v210] (.node [v61, v100, v120, v142, v146, v192] (.node [v61, v100, v120, v141, v170, v192] .nil .nil) (.node [v61, v100, v120, v143, v170, v192] .nil .nil)) (.node [v61, v100, v120, v146, v154, v192] (.node [v61, v100, v120, v145, v170, v192] .nil .nil) .nil))) (.node [v61, v100, v120, v146, v169, v192] (.node [v61, v100, v120, v146, v166, v211] (.node [v61, v100, v120, v146, v162, v192] (.node [v61, v100, v120, v146, v158, v192] .nil .nil) (.node [v61, v100, v120, v146, v163, v170] .nil .nil)) (.node [v61, v100, v120, v146, v168, v192] (.node [v61, v100, v120, v146, v167, v192] .nil .nil) .nil)) (.node [v61, v100, v120, v146, v170, v193] (.node [v61, v100, v120, v146, v170, v191] (.node [v61, v100, v120, v146, v170, v173] .nil .nil) (.node [v61, v100, v120, v146, v170, v192] .nil .nil)) (.node [v61, v100, v120, v146, v170, v195] (.node [v61, v100, v120, v146, v170, v194] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlr_ok : everyKey (rowOK 4 level4) level5rlr = true := by decide +kernel
def level5rl : BinaryTree (List W) := .node [v61, v100, v119, v146, v170, v192] level5rll level5rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rl_ok : everyKey (rowOK 4 level4) level5rl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rll && everyKey (rowOK 4 level4) level5rlr) = true
  rw [level5rll_ok, level5rlr_ok]
  decide +kernel
def level5rrl : BinaryTree (List W) := (.node [v61, v100, v120, v146, v176, v192] (.node [v61, v100, v120, v146, v170, v206] (.node [v61, v100, v120, v146, v170, v201] (.node [v61, v100, v120, v146, v170, v198] (.node [v61, v100, v120, v146, v170, v197] .nil .nil) (.node [v61, v100, v120, v146, v170, v200] .nil .nil)) (.node [v61, v100, v120, v146, v170, v203] (.node [v61, v100, v120, v146, v170, v202] .nil .nil) .nil)) (.node [v61, v100, v120, v146, v172, v192] (.node [v61, v100, v120, v146, v170, v210] (.node [v61, v100, v120, v146, v170, v208] .nil .nil) (.node [v61, v100, v120, v146, v171, v192] .nil .nil)) (.node [v61, v100, v120, v146, v175, v192] (.node [v61, v100, v120, v146, v174, v192] .nil .nil) .nil))) (.node [v61, v100, v120, v146, v183, v192] (.node [v61, v100, v120, v146, v180, v192] (.node [v61, v100, v120, v146, v178, v192] (.node [v61, v100, v120, v146, v177, v192] .nil .nil) (.node [v61, v100, v120, v146, v179, v192] .nil .nil)) (.node [v61, v100, v120, v146, v182, v192] (.node [v61, v100, v120, v146, v181, v192] .nil .nil) .nil)) (.node [v61, v100, v120, v146, v187, v192] (.node [v61, v100, v120, v146, v185, v192] (.node [v61, v100, v120, v146, v184, v192] .nil .nil) (.node [v61, v100, v120, v146, v185, v210] .nil .nil)) (.node [v61, v100, v120, v147, v170, v192] (.node [v61, v100, v120, v146, v188, v192] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrl_ok : everyKey (rowOK 4 level4) level5rrl = true := by decide +kernel
def level5rrr : BinaryTree (List W) := (.node [v61, v100, v131, v146, v170, v192] (.node [v61, v100, v122, v146, v170, v192] (.node [v61, v100, v120, v160, v170, v192] (.node [v61, v100, v120, v151, v170, v192] (.node [v61, v100, v120, v149, v170, v192] .nil .nil) (.node [v61, v100, v120, v152, v170, v210] .nil .nil)) (.node [v61, v100, v121, v146, v170, v192] (.node [v61, v100, v120, v161, v170, v210] .nil .nil) .nil)) (.node [v61, v100, v127, v146, v170, v192] (.node [v61, v100, v125, v146, v170, v192] (.node [v61, v100, v123, v146, v170, v192] .nil .nil) (.node [v61, v100, v126, v146, v170, v192] .nil .nil)) (.node [v61, v100, v130, v146, v170, v192] (.node [v61, v100, v128, v146, v170, v192] .nil .nil) .nil))) (.node [v61, v100, v136, v146, v185, v192] (.node [v61, v100, v135, v146, v170, v192] (.node [v61, v100, v133, v136, v146, v170] (.node [v61, v100, v132, v146, v170, v192] .nil .nil) (.node [v61, v100, v134, v146, v170, v192] .nil .nil)) (.node [v61, v100, v136, v146, v170, v210] (.node [v61, v100, v136, v146, v170, v192] .nil .nil) .nil)) (.node [v61, v120, v146, v170, v192, v204] (.node [v61, v120, v146, v156, v170, v192] (.node [v61, v100, v146, v159, v170, v192] .nil .nil) .nil) (.node [v87, v100, v120, v146, v185, v192] (.node [v70, v100, v136, v146, v170, v192] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrr_ok : everyKey (rowOK 4 level4) level5rrr = true := by decide +kernel
def level5rr : BinaryTree (List W) := .node [v61, v100, v120, v148, v170, v192] level5rrl level5rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rr_ok : everyKey (rowOK 4 level4) level5rr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrl && everyKey (rowOK 4 level4) level5rrr) = true
  rw [level5rrl_ok, level5rrr_ok]
  decide +kernel
def level5r : BinaryTree (List W) := .node [v61, v100, v120, v146, v170, v196] level5rl level5rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5r_ok : everyKey (rowOK 4 level4) level5r = true := by
  change (_ && everyKey (rowOK 4 level4) level5rl && everyKey (rowOK 4 level4) level5rr) = true
  rw [level5rl_ok, level5rr_ok]
  decide +kernel
def level5 : BinaryTree (List W) := .node [v61, v88, v100, v120, v146, v192] level5l level5r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5_ok : everyKey (rowOK 4 level4) level5 = true := by
  change (_ && everyKey (rowOK 4 level4) level5l && everyKey (rowOK 4 level4) level5r) = true
  rw [level5l_ok, level5r_ok]
  decide +kernel
theorem closed5 : Closed 5 level5 := closed_next 4 (by decide) level5 level4 closed4 level5_ok
def level6l : BinaryTree (List W) := (.node [v26, v61, v100, v120, v146, v170, v192] (.node [v10, v61, v100, v120, v146, v170, v192] (.node [v5, v61, v100, v120, v146, v170, v192] (.node [v2, v61, v100, v120, v146, v170, v192] (.node [v1, v61, v100, v120, v146, v170, v192] (.node [v0, v61, v100, v120, v146, v170, v192] .nil .nil) .nil) (.node [v4, v61, v100, v120, v146, v170, v192] .nil .nil)) (.node [v9, v61, v100, v120, v146, v170, v192] (.node [v7, v61, v100, v120, v146, v170, v192] .nil .nil) (.node [v9, v61, v100, v120, v146, v192] .nil .nil))) (.node [v22, v61, v100, v120, v146, v170, v192] (.node [v19, v61, v100, v120, v146, v170, v192] (.node [v15, v61, v100, v120, v146, v170, v192] (.node [v12, v61, v100, v120, v146, v170, v192] .nil .nil) .nil) (.node [v21, v61, v100, v120, v146, v170, v192] .nil .nil)) (.node [v25, v61, v100, v120, v146, v170, v192] (.node [v23, v61, v100, v120, v146, v170, v192] .nil .nil) (.node [v26, v61, v100, v120, v146, v170] .nil .nil)))) (.node [v51, v61, v100, v120, v146, v170, v192] (.node [v38, v61, v100, v120, v146, v170, v192] (.node [v33, v61, v100, v146, v170, v192] (.node [v33, v61, v100, v120, v146, v170, v192] (.node [v31, v61, v100, v120, v146, v170, v192] .nil .nil) .nil) (.node [v35, v61, v100, v120, v146, v170, v192] .nil .nil)) (.node [v49, v61, v100, v120, v146, v170, v192] (.node [v41, v61, v100, v120, v146, v170, v192] .nil .nil) (.node [v50, v61, v100, v120, v146, v170, v192] .nil .nil))) (.node [v59, v61, v100, v120, v146, v170, v192] (.node [v54, v61, v100, v120, v146, v170, v192] (.node [v53, v61, v100, v120, v146, v170, v192] (.node [v52, v61, v100, v120, v146, v170, v192] .nil .nil) .nil) (.node [v55, v61, v100, v120, v146, v170, v192] .nil .nil)) (.node [v61, v70, v100, v120, v146, v170, v192] (.node [v60, v61, v100, v120, v146, v170, v192] .nil .nil) (.node [v61, v70, v100, v146, v170, v192] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6l_ok : everyKey (rowOK 5 level5) level6l = true := by decide +kernel
def level6r : BinaryTree (List W) := (.node [v61, v100, v120, v146, v152, v170, v192] (.node [v61, v94, v100, v120, v146, v192] (.node [v61, v87, v100, v120, v146, v192] (.node [v61, v83, v100, v120, v146, v170, v192] (.node [v61, v81, v100, v120, v146, v170, v192] (.node [v61, v71, v100, v146, v170, v192] .nil .nil) .nil) (.node [v61, v87, v100, v120, v146, v170, v192] .nil .nil)) (.node [v61, v92, v100, v120, v146, v170, v192] (.node [v61, v90, v100, v120, v146, v170, v192] .nil .nil) (.node [v61, v94, v100, v120, v146, v170, v192] .nil .nil))) (.node [v61, v100, v120, v136, v146, v170, v192] (.node [v61, v100, v112, v120, v146, v170, v192] (.node [v61, v100, v109, v120, v146, v170, v192] (.node [v61, v99, v100, v120, v146, v170, v192] .nil .nil) .nil) (.node [v61, v100, v115, v120, v146, v170, v192] .nil .nil)) (.node [v61, v100, v120, v140, v146, v170, v192] (.node [v61, v100, v120, v139, v146, v170, v192] .nil .nil) (.node [v61, v100, v120, v144, v146, v170, v192] .nil .nil)))) (.node [v61, v100, v120, v146, v170, v192, v205] (.node [v61, v100, v120, v146, v170, v186, v192] (.node [v61, v100, v120, v146, v166, v170, v192] (.node [v61, v100, v120, v146, v161, v170, v192] (.node [v61, v100, v120, v146, v157, v170, v192] .nil .nil) .nil) (.node [v61, v100, v120, v146, v170, v185, v192] .nil .nil)) (.node [v61, v100, v120, v146, v170, v190, v192] (.node [v61, v100, v120, v146, v170, v189, v192] .nil .nil) (.node [v61, v100, v120, v146, v170, v192, v199] .nil .nil))) (.node [v61, v100, v120, v146, v170, v192, v212] (.node [v61, v100, v120, v146, v170, v192, v210] (.node [v61, v100, v120, v146, v170, v192, v207] .nil .nil) (.node [v61, v100, v120, v146, v170, v192, v211] .nil .nil)) (.node [v61, v100, v120, v146, v185, v192] (.node [v61, v100, v120, v146, v170, v210] .nil .nil) (.node [v61, v100, v136, v146, v170, v192] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6r_ok : everyKey (rowOK 5 level5) level6r = true := by decide +kernel
def level6 : BinaryTree (List W) := .node [v61, v71, v100, v120, v146, v170, v192] level6l level6r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6_ok : everyKey (rowOK 5 level5) level6 = true := by
  change (_ && everyKey (rowOK 5 level5) level6l && everyKey (rowOK 5 level5) level6r) = true
  rw [level6l_ok, level6r_ok]
  decide +kernel
theorem closed6 : Closed 6 level6 := closed_next 5 (by decide) level6 level5 closed5 level6_ok
def level7 : BinaryTree (List W) := (.node [v61, v100, v120, v146, v170, v192] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7_ok : everyKey (rowOK 6 level6) level7 = true := by decide +kernel
theorem closed7 : Closed 7 level7 := closed_next 6 (by decide) level7 level6 closed6 level7_ok

theorem lower : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z 7 ins.toFinset :=
  @no_build 7 level7 ins (by decide +kernel) (by decide) closed7 (by decide +kernel)
def witness : List Gate := [⟨.or,[3,5]⟩, ⟨.and,[0,6]⟩, ⟨.or,[1,7]⟩, ⟨.or,[2,3]⟩, ⟨.and,[2,6]⟩, ⟨.and,[4,9]⟩, ⟨.or,[10,11]⟩, ⟨.or,[0,12]⟩, ⟨.and,[8,13]⟩]
theorem upper : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 9 ∧ ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xeeeaeaeaeec8ea88 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact ⟨witness,14,by simp [witness],rfl,by decide +kernel⟩
end PEqualNP.Outside.L_meta_15887_aux

open PEqualNP.Outside.L_meta_15887_aux in
theorem PEqualNP.Outside.L_meta_15887 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372970 * 2 ^ 32 + 4006144648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372970 * 2 ^ 32 + 4006144648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  have code : 4008372970 * 2 ^ 32 + 4006144648 = 0xeeeaeaeaeec8ea88 := by decide
  simp only [code] at h ⊢
  obtain ⟨C,legal,size,computes⟩ := h
  obtain ⟨gs,o,mono,bound,ev⟩ := replace 0xeeeaeaeaeec8ea88 9 ins (by decide +kernel) sampled rfl lower upper C.gates C.output legal computes
  exact ⟨⟨gs,o⟩,mono,bound.trans size,ev⟩
