import PEqualNP.Defs

-- The live-wire search and circuit compiler are adapted from the merged L-meta-8639 under Apache-2.0.
namespace PEqualNP.Outside.L_meta_13647_aux

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

def v0 : W := 0x24c05240000000f03c7
def v1 : W := 0x2a1916080000000f03c7
def v2 : W := 0x2a5d372c0000000f03c7
def v3 : W := 0x55c6e1e4000000703818
def v4 : W := 0x668b47c000001980c3e0
def v5 : W := 0x6edf77ec0000198fc3e7
def v6 : W := 0x7913f20800001e00fc00
def v7 : W := 0x7b5ff72c00001e0fffc7
def v8 : W := 0x7fdc840000001fff0000
def v9 : W := 0x7fddb72c00001fff03c7
def v10 : W := 0x7fdff7ec0000007f3bdf
def v11 : W := 0x13580013b3c0000000003c7
def v12 : W := 0x26b000261e40038c0003818
def v13 : W := 0x34e00034bc000c30000c3e0
def v14 : W := 0x36f00036be400fbc000fbf8
def v15 : W := 0x3700003720800fc0000fc00
def v16 : W := 0x37580037b3c00fc0000ffc7
def v17 : W := 0x37e00037bc800ff0000ffe0
def v18 : W := 0x37f8000081000ffe0000000
def v19 : W := 0x37f80037bfc0038c0003bdf
def v20 : W := 0x37fffdc8c1000ffffff0000
def v21 : W := 0x82100442124000000000000
def v22 : W := 0x8212a5d372c0000000f03c7
def v23 : W := 0x440480200810310320000000
def v24 : W := 0x4c0580200810000000000000
def v25 : W := 0x4c05826c0d340000000f03c7
def v26 : W := 0x980b04c401e40e00c0700018
def v27 : W := 0x980b06cc05e40e00c07f03df
def v28 : W := 0xd00e06880dc03003018003e0
def v29 : W := 0xd34e068b4fc030c30180c3e0
def v30 : W := 0xdc0006ec04003f0001ff0000
def v31 : W := 0xdc0586ec0d343f0001ff03c7
def v32 : W := 0xdc0f802008103f03e0000000
def v33 : W := 0xdc0f84e409f43f03e0700018
def v34 : W := 0xdc0f86ec0df40e00c07f03df
def v35 : W := 0xdc0ff933fa183f03fe00fc00
def v36 : W := 0xdf7006ef76083ffc01fffc00
def v37 : W := 0xdf7f802008103fffe0000000
def v38 : W := 0x10c318874303c0000000f0007
def v39 : W := 0x228a11144a0240e38c0703818
def v40 : W := 0x320b01910b008c03c06003c00
def v41 : W := 0x320b07913f208c03c1e00fc00
def v42 : W := 0x323f01913f208c0fc0600fc00
def v43 : W := 0x32c8019748000cf00067f0000
def v44 : W := 0x32c807ffc8400cf001fff0000
def v45 : W := 0x32ca11974a024cf38c67f3818
def v46 : W := 0x32cb180200010cf3ce0000000
def v47 : W := 0x32cb19974b03c0e38c07f381f
def v48 : W := 0x32cb1e6ab47d0cf3cf980c3e0
def v49 : W := 0x32fce1977cbc0cfc3067fc3e0
def v50 : W := 0x32fff80200810cfffe0000000
def v51 : W := 0x3f0be1f98bdc8f03f07803fe0
def v52 : W := 0x3fc801ffc8400ff0007ff0000
def v53 : W := 0x3fcbf80200810ff3fe0000000
def v54 : W := 0x4410422090e0330c31980c3e0
def v55 : W := 0x4410422090f000000000003c0
def v56 : W := 0x501102811120bc0c41e00c400
def v57 : W := 0x5013028113208000000000000
def v58 : W := 0x501302a5d372c0000000f03c7
def v59 : W := 0x544002a380403f1001f8f0000
def v60 : W := 0x5451480200810000000000000
def v61 : W := 0x5451480200813f1c720000000
def v62 : W := 0x54514a8311a1bf1c73e00c400
def v63 : W := 0x54514aa391e180000000f03c7
def v64 : W := 0x54514d5e6e9f7f1c720703818
def v65 : W := 0x5466b2a3a65e7f138df8f3818
def v66 : W := 0x5477f80200813f1ffe0000000
def v67 : W := 0x54c002a7c04000000000f0000
def v68 : W := 0x54d3580200810000000000000
def v69 : W := 0x54d3580200813f1c720000000
def v70 : W := 0x54d3580642934000000000000
def v71 : W := 0x54d35a8313a18000000000000
def v72 : W := 0x54d35aa7d3e3c0000000f03c7
def v73 : W := 0x54d35aa7d3f3c0000000f03c7
def v74 : W := 0x54f7f8020081000ffe0000000
def v75 : W := 0x5991b2cd513efcec4de70c418
def v76 : W := 0x5dd1f80200813ffc7e0000000
def v77 : W := 0x5dd3f802008103f03e0000000
def v78 : W := 0x669a5334dae273efbd9f0fbf8
def v79 : W := 0x721b03911b208c03c06003c00
def v80 : W := 0x721b03911b20bc0fc1e00fc00
def v81 : W := 0x76c803b7c8400cf00067f0000
def v82 : W := 0x76c803b7c8403ff001fff0000
def v83 : W := 0x76db580200810cf3ce0000000
def v84 : W := 0x76db580200813ffffe0000000
def v85 : W := 0x8924a448240c330c31980c020
def v86 : W := 0x8924a448241c0000000000000
def v87 : W := 0x8924a668b47c000001980c3e0
def v88 : W := 0x8924a668b47c330c31980c3e0
def v89 : W := 0x8d24e468a4dc03003018003e0
def v90 : W := 0x8d24e468a4dc330c31980c3e0
def v91 : W := 0x99e7bccf670ff30c3198fc027
def v92 : W := 0xa22c05102c003c0fc1e00fc00
def v93 : W := 0xa22c07913f20bc0fc1e00fc00
def v94 : W := 0xa22e05102e000003800003800
def v95 : W := 0xa22e07913f20800381e00fc00
def v96 : W := 0xa6ec5d36ecd37c0fc1e0fffc7
def v97 : W := 0xab08055808003ff001ff00000
def v98 : W := 0xab0807fdc8403ff001fff0000
def v99 : W := 0xab1b5d581bb3fff001ff003c7
def v100 : W := 0xab2ca00000003ffffe0000000
def v101 : W := 0xab2ca2a5d372fffffe00f03c7
def v102 : W := 0xab2ca5582c0c00e38c0703818
def v103 : W := 0xab2ca55c6e1e40e38c0703818
def v104 : W := 0xab88055c480000e0000700000
def v105 : W := 0xab8807fdc84000e001fff0000
def v106 : W := 0xabacb55c6c1e40e38c0703818
def v107 : W := 0xabaeb000000000e38c0000000
def v108 : W := 0xabaeb55c6e1e40e38c0703818
def v109 : W := 0xabaeb7fdff7ec0e38c07f3bdf
def v110 : W := 0xafc8057ec84003f0001ff0000
def v111 : W := 0xafc8057ec8403ff001fff0000
def v112 : W := 0xafecf80200813ffffe0000000
def v113 : W := 0xafeef802008103f3be0000000
def v114 : W := 0xafeefd5e6e9f40e38c0703818
def v115 : W := 0xafeefd5e6e9f43f3be0703818
def v116 : W := 0xc03406003420300c01800c000
def v117 : W := 0xcd00066880403300019800000
def v118 : W := 0xcd24a668a44c330c31980c020
def v119 : W := 0xcd24a668a45c3300019800000
def v120 : W := 0xcd34e0000080330c300000000
def v121 : W := 0xcd34e668b4ec330c31980c3e0
def v122 : W := 0xcd34e668b4fc00000000003c0
def v123 : W := 0xcd34e668b4fc330c31980c3e0
def v124 : W := 0xcd37fe68b7fff30c31980c3e7
def v125 : W := 0xcdb6f66cf6fe730c31980c3e0
def v126 : W := 0xcdf4f802008133fc3e0000000
def v127 : W := 0xdd35e6e9b5fcbf0c71f80c7e0
def v128 : W := 0xdd37e6e9b7fcb30c31980c3e0
def v129 : W := 0xdd75e80200813f1c720000000
def v130 : W := 0xdd75ee6ab4fd3f1c73980c3e0
def v131 : W := 0xddf7f8020081330c300000000
def v132 : W := 0xddf7fe6ab4fd330c31980c3e0
def v133 : W := 0xddf7feeff7ffc0000000f03c7
def v134 : W := 0xddf7feeff7fff30c3198fc3e7
def v135 : W := 0xef08077888403ff001ff00000
def v136 : W := 0xef88077cc84033e0019f00000
def v137 : W := 0xefbef77cfefe73efbd9f0fbf8
def v138 : W := 0xf208079108003c0001e000000
def v139 : W := 0xf20807913f20bc0001e00fc00
def v140 : W := 0xf20807fdc8403c0001fff0000
def v141 : W := 0xf21907911920bc0c41e00c400
def v142 : W := 0xf21b07911b20bc0001e000000
def v143 : W := 0xf23d07913d20bc0fc1e00fc00
def v144 : W := 0xf23f000000003c0fc00000000
def v145 : W := 0xf23f07913f208003800003800
def v146 : W := 0xf23f07913f20bc0fc1e00fc00
def v147 : W := 0xf23f07b5ff72fc0fc1e0fffc7
def v148 : W := 0xf23fb7913f3efc0fcde00fc18
def v149 : W := 0xf23fff913fa1bc0fffe00fc00
def v150 : W := 0xf2bf17957f32fc0fc1e00fc00
def v151 : W := 0xf64807b388403f1001f8f0000
def v152 : W := 0xf67f480200813f1ff20000000
def v153 : W := 0xf67f4f933fa1bc0fc1e00fc00
def v154 : W := 0xf67f4f933fa1bf1ff3e00fc00
def v155 : W := 0xf67fff933fa1bf1fffe00fc00
def v156 : W := 0xf6c807b7c8403c0001e0f0000
def v157 : W := 0xf6ff580200813c0fc00000000
def v158 : W := 0xf6ff5f933fa1bc0fc1e00fc00
def v159 : W := 0xf6ff5f933fa1bf1ff3e00fc00
def v160 : W := 0xf6ff5f977fb3fc0fc1e00fc00
def v161 : W := 0xf6ff5fb7fff3fc0fc1e0fffc7
def v162 : W := 0xf6ffff933fa1bc0fffe00fc00
def v163 : W := 0xfb3fa7d93f2cbf0ff1f80fc20
def v164 : W := 0xfb3fa7d93f3cbc0fc1e00fc00
def v165 : W := 0xfbbfb7dd7f3ec0e38c0703818
def v166 : W := 0xfbbfb7dd7f3efcefcde70fc18
def v167 : W := 0xff0807f988403f0001f800000
def v168 : W := 0xff3ce7f9bcfc3f0c31f80c3e0
def v169 : W := 0xff3f07f9bf60bf0fc1f80fc00
def v170 : W := 0xff3fe7913fa0bf0ff1e00fc00
def v171 : W := 0xff3fe7f9bffcbf0ff1f80ffe0
def v172 : W := 0xff4807fb88403ff001fff0000
def v173 : W := 0xff7de80200813ffffe0000000
def v174 : W := 0xff7deffbbded80e38c07f3bdf
def v175 : W := 0xff7fef933fa1bf1ff3e00fc00
def v176 : W := 0xffc8000200003ff0000000000
def v177 : W := 0xffc807ffc84000e00007f0000
def v178 : W := 0xffc807ffc8403ff001fff0000
def v179 : W := 0xffc8b7ffc85e7ff00dfff0018
def v180 : W := 0xffc8f80200813ff03e0000000
def v181 : W := 0xffc8ffffc8c13ff03ffff0000
def v182 : W := 0xffca17ffca527ff001fff0000
def v183 : W := 0xffcb1fffcb43fff001fff0007
def v184 : W := 0xffd907ffd960bffc41fffc400
def v185 : W := 0xffd9480200813ffc720000000
def v186 : W := 0xffd94fffc8c13ffc73fff0000
def v187 : W := 0xffdb07ffdb60bff001fff0000
def v188 : W := 0xffdb580200813ff0000000000
def v189 : W := 0xffdb5fffc8c13ff001fff0000
def v190 : W := 0xffdb5fffdbf3fff001fff03c7
def v191 : W := 0xffeca7ffec4c3ffc31fffc020
def v192 : W := 0xffeca7ffec5c3ff001fff0000
def v193 : W := 0xffeeb7ffee5e7ff38dfff3818
def v194 : W := 0xfffc07fffc603ffc01fffc000
def v195 : W := 0xfffce7ffc8c03ffc31fff0000
def v196 : W := 0xfffce7fffcfc3ffc31fffc3e0
def v197 : W := 0xffff07ffff60bfffc1ffffc00
def v198 : W := 0xfffff802008100e38c0000000
def v199 : W := 0xfffff80200813ffffe0000000
def v200 : W := 0xfffff802269f7ffffe0003818
def v201 : W := 0xfffff80237a1bffffe000fc00
def v202 : W := 0xfffff80642937ffffe0000000
def v203 : W := 0xfffff84e409f7ffffe0700018
def v204 : W := 0xfffff9164a837ffffe0703818
def v205 : W := 0xfffff9930b81bffffe6003c00
def v206 : W := 0xfffffa8311a1bfffffe00c400
def v207 : W := 0xfffffa8313a1bffffe0000000
def v208 : W := 0xfffffaa7d3f3fffffe00f03c7
def v209 : W := 0xfffffc4a248d3fffff980c020
def v210 : W := 0xfffffc4a249d3ffffe0000000
def v211 : W := 0xfffffd122c813fffffe00fc00
def v212 : W := 0xfffffd122e813ffffe0003800
def v213 : W := 0xfffffd5a08813fffffff00000
def v214 : W := 0xfffffd5a2c8d3ffffe0703818
def v215 : W := 0xfffffd5e48813ffffe0700000
def v216 : W := 0xfffffd5e6e9f40e38c0703818
def v217 : W := 0xfffffd5e6e9f7ffffe0703818
def v218 : W := 0xfffffe0234a13fffff800c000
def v219 : W := 0xfffffe6a80c13fffff9800000
def v220 : W := 0xfffffe6ab4fd3fffff980c3e0
def v221 : W := 0xffffff9308813fffffe000000
def v222 : W := 0xffffff933fa1bf0ff1e00fc00
def v223 : W := 0xffffff933fa1bfffffe00fc00
def v224 : W := 0xffffffdf7fbfc0e38c0703818
def v225 : W := 0xffffffdf7fbfffffffe70fc18
def v226 : W := 0xffffffffc8c13ffffffff0000
def v227 : W := 0xffffffffffffc0e38c07f3bdf

def ins : List W := [v73, v108, v123, v146, v178, v199]
theorem sampled : ∀ j : Fin 100, Nat.testBit 0xeeeaeaeaeee8eac8 (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
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
def level4llll : BinaryTree (List W) := (.node [v26, v62, v73, v123, v178] (.node [v20, v73, v108, v123, v146] .nil .nil) (.node [v27, v73, v108, v123, v178] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llll_ok : everyKey (rowOK 3 level3) level4llll = true := by decide +kernel
def level4lllr : BinaryTree (List W) := (.node [v48, v73, v108, v146, v178] (.node [v36, v73, v108, v123, v199] .nil .nil) (.node [v49, v73, v108, v146, v199] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lllr_ok : everyKey (rowOK 3 level3) level4lllr = true := by decide +kernel
def level4lll : BinaryTree (List W) := .node [v35, v73, v108, v123, v178] level4llll level4lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lll_ok : everyKey (rowOK 3 level3) level4lll = true := by
  change (_ && everyKey (rowOK 3 level3) level4llll && everyKey (rowOK 3 level3) level4lllr) = true
  rw [level4llll_ok, level4lllr_ok]
  decide +kernel
def level4llr : BinaryTree (List W) := (.node [v71, v108, v123, v161, v178] (.node [v65, v73, v123, v146, v199] (.node [v64, v73, v123, v146, v178] .nil .nil) (.node [v70, v123, v146, v178, v227] .nil .nil)) (.node [v73, v78, v146, v178, v199] (.node [v73, v75, v123, v178, v199] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llr_ok : everyKey (rowOK 3 level3) level4llr = true := by decide +kernel
def level4ll : BinaryTree (List W) := .node [v51, v73, v108, v178, v199] level4lll level4llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4ll_ok : everyKey (rowOK 3 level3) level4ll = true := by
  change (_ && everyKey (rowOK 3 level3) level4lll && everyKey (rowOK 3 level3) level4llr) = true
  rw [level4lll_ok, level4llr_ok]
  decide +kernel
def level4lrl : BinaryTree (List W) := (.node [v73, v98, v108, v123, v158] (.node [v73, v88, v146, v178, v216] (.node [v73, v88, v108, v158, v178] .nil .nil) (.node [v73, v93, v123, v178, v216] .nil .nil)) (.node [v73, v103, v123, v158, v178] (.node [v73, v98, v123, v146, v216] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrl_ok : everyKey (rowOK 3 level3) level4lrl = true := by decide +kernel
def level4lrr : BinaryTree (List W) := (.node [v73, v108, v123, v154, v178] (.node [v73, v108, v123, v151, v223] (.node [v73, v108, v123, v140, v223] .nil .nil) (.node [v73, v108, v123, v153, v178] .nil .nil)) (.node [v73, v108, v123, v155, v178] (.node [v73, v108, v123, v154, v186] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrr_ok : everyKey (rowOK 3 level3) level4lrr = true := by decide +kernel
def level4lr : BinaryTree (List W) := .node [v73, v105, v108, v123, v154] level4lrl level4lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lr_ok : everyKey (rowOK 3 level3) level4lr = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrl && everyKey (rowOK 3 level3) level4lrr) = true
  rw [level4lrl_ok, level4lrr_ok]
  decide +kernel
def level4l : BinaryTree (List W) := .node [v73, v87, v108, v154, v178] level4ll level4lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4l_ok : everyKey (rowOK 3 level3) level4l = true := by
  change (_ && everyKey (rowOK 3 level3) level4ll && everyKey (rowOK 3 level3) level4lr) = true
  rw [level4ll_ok, level4lr_ok]
  decide +kernel
def level4rll : BinaryTree (List W) := (.node [v73, v108, v123, v160, v178] (.node [v73, v108, v123, v158, v189] (.node [v73, v108, v123, v158, v178] .nil .nil) (.node [v73, v108, v123, v159, v178] .nil .nil)) (.node [v73, v108, v123, v167, v223] (.node [v73, v108, v123, v162, v178] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rll_ok : everyKey (rowOK 3 level3) level4rll = true := by decide +kernel
def level4rlr : BinaryTree (List W) := (.node [v73, v108, v132, v146, v189] (.node [v73, v108, v130, v146, v186] (.node [v73, v108, v123, v178, v222] .nil .nil) (.node [v73, v108, v130, v154, v178] .nil .nil)) (.node [v73, v108, v168, v178, v223] (.node [v73, v108, v132, v158, v178] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlr_ok : everyKey (rowOK 3 level3) level4rlr = true := by decide +kernel
def level4rl : BinaryTree (List W) := .node [v73, v108, v123, v175, v178] level4rll level4rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rl_ok : everyKey (rowOK 3 level3) level4rl = true := by
  change (_ && everyKey (rowOK 3 level3) level4rll && everyKey (rowOK 3 level3) level4rlr) = true
  rw [level4rll_ok, level4rlr_ok]
  decide +kernel
def level4rrl : BinaryTree (List W) := (.node [v73, v123, v146, v178, v216] (.node [v73, v108, v171, v194, v199] (.node [v73, v108, v169, v196, v199] .nil .nil) (.node [v73, v114, v123, v146, v178] .nil .nil)) (.node [v73, v123, v146, v189, v216] (.node [v73, v123, v146, v178, v224] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrl_ok : everyKey (rowOK 3 level3) level4rrl = true := by decide +kernel
def level4rrr : BinaryTree (List W) := (.node [v99, v108, v123, v146, v199] (.node [v91, v108, v146, v178, v199] (.node [v73, v132, v146, v178, v216] .nil .nil) (.node [v96, v108, v123, v178, v199] .nil .nil)) (.node [v123, v146, v174, v178, v199] (.node [v101, v108, v123, v146, v178] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrr_ok : everyKey (rowOK 3 level3) level4rrr = true := by decide +kernel
def level4rr : BinaryTree (List W) := .node [v73, v123, v158, v178, v216] level4rrl level4rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rr_ok : everyKey (rowOK 3 level3) level4rr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrl && everyKey (rowOK 3 level3) level4rrr) = true
  rw [level4rrl_ok, level4rrr_ok]
  decide +kernel
def level4r : BinaryTree (List W) := .node [v73, v108, v168, v197, v199] level4rl level4rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4r_ok : everyKey (rowOK 3 level3) level4r = true := by
  change (_ && everyKey (rowOK 3 level3) level4rl && everyKey (rowOK 3 level3) level4rr) = true
  rw [level4rl_ok, level4rr_ok]
  decide +kernel
def level4 : BinaryTree (List W) := .node [v73, v108, v123, v156, v223] level4l level4r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4_ok : everyKey (rowOK 3 level3) level4 = true := by
  change (_ && everyKey (rowOK 3 level3) level4l && everyKey (rowOK 3 level3) level4r) = true
  rw [level4l_ok, level4r_ok]
  decide +kernel
theorem closed4 : Closed 4 level4 := closed_next 3 (by decide) level4 level3 closed3 level4_ok
def level5lllll : BinaryTree (List W) := (.node [v2, v73, v108, v123, v146, v178] (.node [v1, v73, v108, v123, v146, v178] (.node [v0, v73, v108, v123, v146, v178] .nil .nil) (.node [v2, v68, v108, v123, v146, v178] .nil .nil)) (.node [v3, v61, v73, v123, v146, v178] (.node [v2, v100, v108, v123, v146, v178] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllll_ok : everyKey (rowOK 4 level4) level5lllll = true := by decide +kernel
def level5llllr : BinaryTree (List W) := (.node [v8, v18, v73, v108, v123, v146] (.node [v6, v32, v73, v108, v123, v178] (.node [v5, v73, v108, v123, v146, v178] .nil .nil) (.node [v7, v73, v108, v123, v146, v178] .nil .nil)) (.node [v10, v73, v108, v123, v146, v178] (.node [v9, v73, v108, v123, v146, v178] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llllr_ok : everyKey (rowOK 4 level4) level5llllr = true := by decide +kernel
def level5llll : BinaryTree (List W) := .node [v4, v46, v73, v108, v146, v178] level5lllll level5llllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llll_ok : everyKey (rowOK 4 level4) level5llll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lllll && everyKey (rowOK 4 level4) level5llllr) = true
  rw [level5lllll_ok, level5llllr_ok]
  decide +kernel
def level5lllrl : BinaryTree (List W) := (.node [v15, v30, v73, v108, v123, v199] (.node [v13, v43, v73, v108, v146, v199] (.node [v12, v59, v73, v123, v146, v199] .nil .nil) (.node [v14, v73, v108, v123, v146, v199] .nil .nil)) (.node [v17, v73, v108, v123, v146, v199] (.node [v16, v73, v108, v123, v146, v199] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrl_ok : everyKey (rowOK 4 level4) level5lllrl = true := by decide +kernel
def level5lllrr : BinaryTree (List W) := (.node [v23, v73, v108, v123, v146, v178] (.node [v22, v73, v108, v123, v146, v178] (.node [v21, v123, v146, v178, v199, v227] .nil .nil) .nil) (.node [v25, v92, v108, v123, v178, v199] (.node [v24, v73, v108, v123, v146, v178] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrr_ok : everyKey (rowOK 4 level4) level5lllrr = true := by decide +kernel
def level5lllr : BinaryTree (List W) := .node [v19, v73, v108, v123, v146, v199] level5lllrl level5lllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllr_ok : everyKey (rowOK 4 level4) level5lllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lllrl && everyKey (rowOK 4 level4) level5lllrr) = true
  rw [level5lllrl_ok, level5lllrr_ok]
  decide +kernel
def level5lll : BinaryTree (List W) := .node [v11, v97, v108, v123, v146, v199] level5llll level5lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lll_ok : everyKey (rowOK 4 level4) level5lll = true := by
  change (_ && everyKey (rowOK 4 level4) level5llll && everyKey (rowOK 4 level4) level5lllr) = true
  rw [level5llll_ok, level5lllr_ok]
  decide +kernel
def level5llrll : BinaryTree (List W) := (.node [v30, v73, v108, v123, v178, v223] (.node [v28, v40, v73, v108, v178, v199] (.node [v26, v73, v108, v123, v178, v223] .nil .nil) (.node [v29, v73, v108, v146, v178, v199] .nil .nil)) (.node [v32, v73, v108, v123, v140, v146] (.node [v31, v73, v108, v123, v178, v199] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrll_ok : everyKey (rowOK 4 level4) level5llrll = true := by decide +kernel
def level5llrlr : BinaryTree (List W) := (.node [v33, v73, v108, v123, v146, v178] (.node [v32, v73, v108, v123, v178, v223] (.node [v32, v73, v108, v123, v146, v181] .nil .nil) .nil) (.node [v37, v73, v108, v123, v146, v178] (.node [v34, v73, v108, v123, v178, v199] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrlr_ok : everyKey (rowOK 4 level4) level5llrlr = true := by decide +kernel
def level5llrl : BinaryTree (List W) := .node [v32, v73, v108, v123, v146, v178] level5llrll level5llrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrl_ok : everyKey (rowOK 4 level4) level5llrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrll && everyKey (rowOK 4 level4) level5llrlr) = true
  rw [level5llrll_ok, level5llrlr_ok]
  decide +kernel
def level5llrrl : BinaryTree (List W) := (.node [v42, v73, v108, v123, v178, v199] (.node [v40, v73, v108, v123, v178, v223] (.node [v39, v54, v73, v146, v178, v199] .nil .nil) (.node [v41, v73, v108, v123, v178, v199] .nil .nil)) (.node [v45, v73, v108, v146, v178, v199] (.node [v44, v73, v108, v123, v146, v199] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrl_ok : everyKey (rowOK 4 level4) level5llrrl = true := by decide +kernel
def level5llrrr : BinaryTree (List W) := (.node [v53, v73, v108, v123, v146, v178] (.node [v52, v73, v108, v123, v146, v199] (.node [v50, v73, v108, v123, v146, v178] .nil .nil) .nil) (.node [v57, v108, v123, v161, v178, v199] (.node [v55, v108, v134, v146, v178, v199] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrr_ok : everyKey (rowOK 4 level4) level5llrrr = true := by decide +kernel
def level5llrr : BinaryTree (List W) := .node [v47, v73, v108, v146, v178, v199] level5llrrl level5llrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrr_ok : everyKey (rowOK 4 level4) level5llrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrrl && everyKey (rowOK 4 level4) level5llrrr) = true
  rw [level5llrrl_ok, level5llrrr_ok]
  decide +kernel
def level5llr : BinaryTree (List W) := .node [v38, v85, v108, v146, v178, v199] level5llrl level5llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llr_ok : everyKey (rowOK 4 level4) level5llr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrl && everyKey (rowOK 4 level4) level5llrr) = true
  rw [level5llrl_ok, level5llrr_ok]
  decide +kernel
def level5ll : BinaryTree (List W) := .node [v26, v56, v73, v123, v178, v199] level5lll level5llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5ll_ok : everyKey (rowOK 4 level4) level5ll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lll && everyKey (rowOK 4 level4) level5llr) = true
  rw [level5lll_ok, level5llr_ok]
  decide +kernel
def level5lrlll : BinaryTree (List W) := (.node [v61, v73, v105, v108, v123, v146] (.node [v61, v73, v87, v108, v146, v178] (.node [v60, v73, v108, v123, v146, v178] .nil .nil) (.node [v61, v73, v95, v108, v123, v178] .nil .nil)) (.node [v61, v73, v108, v123, v146, v186] (.node [v61, v73, v108, v123, v146, v178] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlll_ok : everyKey (rowOK 4 level4) level5lrlll = true := by decide +kernel
def level5lrllr : BinaryTree (List W) := (.node [v62, v73, v108, v123, v146, v178] (.node [v61, v73, v123, v146, v178, v217] (.node [v61, v73, v108, v130, v146, v178] .nil .nil) .nil) (.node [v66, v73, v108, v123, v146, v178] (.node [v63, v102, v123, v146, v178, v199] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrllr_ok : everyKey (rowOK 4 level4) level5lrllr = true := by decide +kernel
def level5lrll : BinaryTree (List W) := .node [v61, v73, v108, v123, v154, v178] level5lrlll level5lrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrll_ok : everyKey (rowOK 4 level4) level5lrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrlll && everyKey (rowOK 4 level4) level5lrllr) = true
  rw [level5lrlll_ok, level5lrllr_ok]
  decide +kernel
def level5lrlrl : BinaryTree (List W) := (.node [v68, v73, v103, v123, v146, v178] (.node [v68, v73, v93, v108, v123, v178] (.node [v68, v73, v88, v108, v146, v178] .nil .nil) (.node [v68, v73, v98, v108, v123, v146] .nil .nil)) (.node [v68, v73, v108, v123, v146, v189] (.node [v68, v73, v108, v123, v146, v178] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrl_ok : everyKey (rowOK 4 level4) level5lrlrl = true := by decide +kernel
def level5lrlrr : BinaryTree (List W) := (.node [v68, v108, v123, v146, v178, v208] (.node [v68, v73, v123, v146, v178, v216] (.node [v68, v73, v108, v132, v146, v178] .nil .nil) .nil) (.node [v70, v73, v108, v123, v146, v178] (.node [v69, v73, v108, v123, v146, v178] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrr_ok : everyKey (rowOK 4 level4) level5lrlrr = true := by decide +kernel
def level5lrlr : BinaryTree (List W) := .node [v68, v73, v108, v123, v158, v178] level5lrlrl level5lrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlr_ok : everyKey (rowOK 4 level4) level5lrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrlrl && everyKey (rowOK 4 level4) level5lrlrr) = true
  rw [level5lrlrl_ok, level5lrlrr_ok]
  decide +kernel
def level5lrl : BinaryTree (List W) := .node [v67, v108, v123, v146, v190, v199] level5lrll level5lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrl_ok : everyKey (rowOK 4 level4) level5lrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrll && everyKey (rowOK 4 level4) level5lrlr) = true
  rw [level5lrll_ok, level5lrlr_ok]
  decide +kernel
def level5lrrll : BinaryTree (List W) := (.node [v73, v77, v108, v123, v146, v178] (.node [v73, v74, v108, v123, v146, v178] (.node [v72, v108, v123, v146, v178, v199] .nil .nil) (.node [v73, v76, v108, v123, v146, v178] .nil .nil)) (.node [v73, v80, v108, v123, v178, v199] (.node [v73, v79, v108, v123, v178, v199] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrll_ok : everyKey (rowOK 4 level4) level5lrrll = true := by decide +kernel
def level5lrrlr : BinaryTree (List W) := (.node [v73, v84, v108, v123, v146, v178] (.node [v73, v83, v108, v123, v146, v178] (.node [v73, v82, v108, v123, v146, v199] .nil .nil) .nil) (.node [v73, v87, v108, v146, v178, v199] (.node [v73, v86, v137, v146, v178, v199] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrlr_ok : everyKey (rowOK 4 level4) level5lrrlr = true := by decide +kernel
def level5lrrl : BinaryTree (List W) := .node [v73, v81, v108, v123, v146, v199] level5lrrll level5lrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrl_ok : everyKey (rowOK 4 level4) level5lrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrll && everyKey (rowOK 4 level4) level5lrrlr) = true
  rw [level5lrrll_ok, level5lrrlr_ok]
  decide +kernel
def level5lrrrl : BinaryTree (List W) := (.node [v73, v93, v108, v123, v178, v199] (.node [v73, v90, v108, v146, v178, v199] (.node [v73, v89, v108, v146, v178, v199] .nil .nil) (.node [v73, v92, v108, v123, v178, v223] .nil .nil)) (.node [v73, v94, v123, v166, v178, v199] (.node [v73, v94, v108, v123, v178, v223] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrl_ok : everyKey (rowOK 4 level4) level5lrrrl = true := by decide +kernel
def level5lrrrr : BinaryTree (List W) := (.node [v73, v103, v123, v146, v178, v199] (.node [v73, v102, v123, v146, v178, v217] (.node [v73, v98, v108, v123, v146, v199] .nil .nil) .nil) (.node [v73, v105, v108, v123, v146, v199] (.node [v73, v104, v123, v146, v193, v199] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrr_ok : everyKey (rowOK 4 level4) level5lrrrr = true := by decide +kernel
def level5lrrr : BinaryTree (List W) := .node [v73, v95, v108, v123, v178, v199] level5lrrrl level5lrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrr_ok : everyKey (rowOK 4 level4) level5lrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrrl && everyKey (rowOK 4 level4) level5lrrrr) = true
  rw [level5lrrrl_ok, level5lrrrr_ok]
  decide +kernel
def level5lrr : BinaryTree (List W) := .node [v73, v88, v108, v146, v178, v199] level5lrrl level5lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrr_ok : everyKey (rowOK 4 level4) level5lrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrl && everyKey (rowOK 4 level4) level5lrrr) = true
  rw [level5lrrl_ok, level5lrrr_ok]
  decide +kernel
def level5lr : BinaryTree (List W) := .node [v71, v73, v108, v123, v146, v178] level5lrl level5lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lr_ok : everyKey (rowOK 4 level4) level5lr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrl && everyKey (rowOK 4 level4) level5lrr) = true
  rw [level5lrl_ok, level5lrr_ok]
  decide +kernel
def level5l : BinaryTree (List W) := .node [v58, v73, v108, v123, v146, v178] level5ll level5lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5l_ok : everyKey (rowOK 4 level4) level5l = true := by
  change (_ && everyKey (rowOK 4 level4) level5ll && everyKey (rowOK 4 level4) level5lr) = true
  rw [level5ll_ok, level5lr_ok]
  decide +kernel
def level5rllll : BinaryTree (List W) := (.node [v73, v108, v111, v123, v146, v199] (.node [v73, v108, v109, v123, v146, v178] (.node [v73, v107, v123, v146, v178, v217] .nil .nil) (.node [v73, v108, v110, v123, v146, v199] .nil .nil)) (.node [v73, v108, v113, v123, v146, v178] (.node [v73, v108, v112, v123, v146, v178] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllll_ok : everyKey (rowOK 4 level4) level5rllll = true := by decide +kernel
def level5rlllr : BinaryTree (List W) := (.node [v73, v108, v119, v146, v178, v199] (.node [v73, v108, v117, v146, v196, v199] (.node [v73, v108, v116, v171, v178, v199] .nil .nil) (.node [v73, v108, v118, v146, v178, v199] .nil .nil)) (.node [v73, v108, v121, v146, v178, v199] (.node [v73, v108, v120, v146, v178, v220] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlllr_ok : everyKey (rowOK 4 level4) level5rlllr = true := by decide +kernel
def level5rlll : BinaryTree (List W) := .node [v73, v108, v115, v123, v146, v178] level5rllll level5rlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlll_ok : everyKey (rowOK 4 level4) level5rlll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rllll && everyKey (rowOK 4 level4) level5rlllr) = true
  rw [level5rllll_ok, level5rlllr_ok]
  decide +kernel
def level5rllrl : BinaryTree (List W) := (.node [v73, v108, v123, v135, v146, v199] (.node [v73, v108, v123, v129, v146, v178] (.node [v73, v108, v123, v126, v146, v178] .nil .nil) (.node [v73, v108, v123, v131, v146, v178] .nil .nil)) (.node [v73, v108, v123, v138, v178, v223] (.node [v73, v108, v123, v136, v146, v199] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrl_ok : everyKey (rowOK 4 level4) level5rllrl = true := by decide +kernel
def level5rllrr : BinaryTree (List W) := (.node [v73, v108, v123, v141, v178, v199] (.node [v73, v108, v123, v140, v146, v199] (.node [v73, v108, v123, v139, v178, v199] .nil .nil) .nil) (.node [v73, v108, v123, v143, v178, v199] (.node [v73, v108, v123, v142, v178, v199] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrr_ok : everyKey (rowOK 4 level4) level5rllrr = true := by decide +kernel
def level5rllr : BinaryTree (List W) := .node [v73, v108, v123, v138, v197, v199] level5rllrl level5rllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllr_ok : everyKey (rowOK 4 level4) level5rllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rllrl && everyKey (rowOK 4 level4) level5rllrr) = true
  rw [level5rllrl_ok, level5rllrr_ok]
  decide +kernel
def level5rll : BinaryTree (List W) := .node [v73, v108, v122, v146, v178, v199] level5rlll level5rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rll_ok : everyKey (rowOK 4 level4) level5rll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlll && everyKey (rowOK 4 level4) level5rllr) = true
  rw [level5rlll_ok, level5rllr_ok]
  decide +kernel
def level5rlrll : BinaryTree (List W) := (.node [v73, v108, v123, v146, v152, v178] (.node [v73, v108, v123, v146, v147, v178] (.node [v73, v108, v123, v145, v178, v199] .nil .nil) (.node [v73, v108, v123, v146, v151, v199] .nil .nil)) (.node [v73, v108, v123, v146, v156, v199] (.node [v73, v108, v123, v146, v154, v178] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrll_ok : everyKey (rowOK 4 level4) level5rlrll = true := by decide +kernel
def level5rlrlr : BinaryTree (List W) := (.node [v73, v108, v123, v146, v172, v199] (.node [v73, v108, v123, v146, v167, v199] (.node [v73, v108, v123, v146, v158, v178] .nil .nil) .nil) (.node [v73, v108, v123, v146, v176, v226] (.node [v73, v108, v123, v146, v173, v178] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrlr_ok : everyKey (rowOK 4 level4) level5rlrlr = true := by decide +kernel
def level5rlrl : BinaryTree (List W) := .node [v73, v108, v123, v146, v157, v178] level5rlrll level5rlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrl_ok : everyKey (rowOK 4 level4) level5rlrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrll && everyKey (rowOK 4 level4) level5rlrlr) = true
  rw [level5rlrll_ok, level5rlrlr_ok]
  decide +kernel
def level5rlrrl : BinaryTree (List W) := (.node [v73, v108, v123, v146, v178, v198] (.node [v73, v108, v123, v146, v178, v185] (.node [v73, v108, v123, v146, v178, v180] .nil .nil) (.node [v73, v108, v123, v146, v178, v188] .nil .nil)) (.node [v73, v108, v123, v146, v178, v200] (.node [v73, v108, v123, v146, v178, v199] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrl_ok : everyKey (rowOK 4 level4) level5rlrrl = true := by decide +kernel
def level5rlrrr : BinaryTree (List W) := (.node [v73, v108, v123, v146, v178, v204] (.node [v73, v108, v123, v146, v178, v203] (.node [v73, v108, v123, v146, v178, v202] .nil .nil) .nil) (.node [v73, v108, v123, v146, v178, v206] (.node [v73, v108, v123, v146, v178, v205] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrr_ok : everyKey (rowOK 4 level4) level5rlrrr = true := by decide +kernel
def level5rlrr : BinaryTree (List W) := .node [v73, v108, v123, v146, v178, v201] level5rlrrl level5rlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrr_ok : everyKey (rowOK 4 level4) level5rlrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrrl && everyKey (rowOK 4 level4) level5rlrrr) = true
  rw [level5rlrrl_ok, level5rlrrr_ok]
  decide +kernel
def level5rlr : BinaryTree (List W) := .node [v73, v108, v123, v146, v177, v199] level5rlrl level5rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlr_ok : everyKey (rowOK 4 level4) level5rlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrl && everyKey (rowOK 4 level4) level5rlrr) = true
  rw [level5rlrl_ok, level5rlrr_ok]
  decide +kernel
def level5rl : BinaryTree (List W) := .node [v73, v108, v123, v144, v178, v223] level5rll level5rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rl_ok : everyKey (rowOK 4 level4) level5rl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rll && everyKey (rowOK 4 level4) level5rlr) = true
  rw [level5rll_ok, level5rlr_ok]
  decide +kernel
def level5rrlll : BinaryTree (List W) := (.node [v73, v108, v123, v146, v178, v212] (.node [v73, v108, v123, v146, v178, v210] (.node [v73, v108, v123, v146, v178, v209] .nil .nil) (.node [v73, v108, v123, v146, v178, v211] .nil .nil)) (.node [v73, v108, v123, v146, v178, v214] (.node [v73, v108, v123, v146, v178, v213] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlll_ok : everyKey (rowOK 4 level4) level5rrlll = true := by decide +kernel
def level5rrllr : BinaryTree (List W) := (.node [v73, v108, v123, v146, v178, v218] (.node [v73, v108, v123, v146, v178, v217] (.node [v73, v108, v123, v146, v178, v216] .nil .nil) .nil) (.node [v73, v108, v123, v146, v178, v221] (.node [v73, v108, v123, v146, v178, v219] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrllr_ok : everyKey (rowOK 4 level4) level5rrllr = true := by decide +kernel
def level5rrll : BinaryTree (List W) := .node [v73, v108, v123, v146, v178, v215] level5rrlll level5rrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrll_ok : everyKey (rowOK 4 level4) level5rrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrlll && everyKey (rowOK 4 level4) level5rrllr) = true
  rw [level5rrlll_ok, level5rrllr_ok]
  decide +kernel
def level5rrlrl : BinaryTree (List W) := (.node [v73, v108, v123, v146, v182, v199] (.node [v73, v108, v123, v146, v179, v199] (.node [v73, v108, v123, v146, v178, v225] .nil .nil) (.node [v73, v108, v123, v146, v181, v199] .nil .nil)) (.node [v73, v108, v123, v146, v184, v199] (.node [v73, v108, v123, v146, v183, v199] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrl_ok : everyKey (rowOK 4 level4) level5rrlrl = true := by decide +kernel
def level5rrlrr : BinaryTree (List W) := (.node [v73, v108, v123, v146, v191, v199] (.node [v73, v108, v123, v146, v189, v199] (.node [v73, v108, v123, v146, v187, v199] .nil .nil) .nil) (.node [v73, v108, v123, v146, v194, v199] (.node [v73, v108, v123, v146, v192, v199] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrr_ok : everyKey (rowOK 4 level4) level5rrlrr = true := by decide +kernel
def level5rrlr : BinaryTree (List W) := .node [v73, v108, v123, v146, v186, v199] level5rrlrl level5rrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlr_ok : everyKey (rowOK 4 level4) level5rrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrlrl && everyKey (rowOK 4 level4) level5rrlrr) = true
  rw [level5rrlrl_ok, level5rrlrr_ok]
  decide +kernel
def level5rrl : BinaryTree (List W) := .node [v73, v108, v123, v146, v178, v223] level5rrll level5rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrl_ok : everyKey (rowOK 4 level4) level5rrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrll && everyKey (rowOK 4 level4) level5rrlr) = true
  rw [level5rrll_ok, level5rrlr_ok]
  decide +kernel
def level5rrrll : BinaryTree (List W) := (.node [v73, v108, v123, v154, v178] (.node [v73, v108, v123, v149, v178, v199] (.node [v73, v108, v123, v148, v178, v199] .nil .nil) (.node [v73, v108, v123, v150, v178, v199] .nil .nil)) (.node [v73, v108, v123, v158, v178] (.node [v73, v108, v123, v154, v178, v199] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrll_ok : everyKey (rowOK 4 level4) level5rrrll = true := by decide +kernel
def level5rrrlr : BinaryTree (List W) := (.node [v73, v108, v123, v164, v178, v199] (.node [v73, v108, v123, v163, v178, v199] (.node [v73, v108, v123, v161, v178, v223] .nil .nil) .nil) (.node [v73, v108, v123, v170, v178, v199] (.node [v73, v108, v123, v169, v178, v199] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrlr_ok : everyKey (rowOK 4 level4) level5rrrlr = true := by decide +kernel
def level5rrrl : BinaryTree (List W) := .node [v73, v108, v123, v158, v178, v199] level5rrrll level5rrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrl_ok : everyKey (rowOK 4 level4) level5rrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrll && everyKey (rowOK 4 level4) level5rrrlr) = true
  rw [level5rrrll_ok, level5rrrlr_ok]
  decide +kernel
def level5rrrrl : BinaryTree (List W) := (.node [v73, v108, v128, v146, v178, v199] (.node [v73, v108, v125, v146, v178, v199] (.node [v73, v108, v124, v146, v178, v199] .nil .nil) (.node [v73, v108, v127, v146, v178, v199] .nil .nil)) (.node [v73, v108, v132, v146, v178, v199] (.node [v73, v108, v130, v146, v178, v199] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrl_ok : everyKey (rowOK 4 level4) level5rrrrl = true := by decide +kernel
def level5rrrrr : BinaryTree (List W) := (.node [v73, v123, v146, v178, v216] (.node [v73, v123, v146, v178, v199, v216] (.node [v73, v123, v146, v165, v178, v199] .nil .nil) .nil) (.node [v108, v123, v133, v146, v178, v199] (.node [v73, v123, v146, v178, v217, v227] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrr_ok : everyKey (rowOK 4 level4) level5rrrrr = true := by decide +kernel
def level5rrrr : BinaryTree (List W) := .node [v73, v108, v146, v168, v178, v199] level5rrrrl level5rrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrr_ok : everyKey (rowOK 4 level4) level5rrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrrl && everyKey (rowOK 4 level4) level5rrrrr) = true
  rw [level5rrrrl_ok, level5rrrrr_ok]
  decide +kernel
def level5rrr : BinaryTree (List W) := .node [v73, v108, v123, v171, v178, v223] level5rrrl level5rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrr_ok : everyKey (rowOK 4 level4) level5rrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrl && everyKey (rowOK 4 level4) level5rrrr) = true
  rw [level5rrrl_ok, level5rrrr_ok]
  decide +kernel
def level5rr : BinaryTree (List W) := .node [v73, v108, v123, v146, v195, v199] level5rrl level5rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rr_ok : everyKey (rowOK 4 level4) level5rr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrl && everyKey (rowOK 4 level4) level5rrr) = true
  rw [level5rrl_ok, level5rrr_ok]
  decide +kernel
def level5r : BinaryTree (List W) := .node [v73, v108, v123, v146, v178, v207] level5rl level5rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5r_ok : everyKey (rowOK 4 level4) level5r = true := by
  change (_ && everyKey (rowOK 4 level4) level5rl && everyKey (rowOK 4 level4) level5rr) = true
  rw [level5rl_ok, level5rr_ok]
  decide +kernel
def level5 : BinaryTree (List W) := .node [v73, v106, v123, v146, v178, v199] level5l level5r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5_ok : everyKey (rowOK 4 level4) level5 = true := by
  change (_ && everyKey (rowOK 4 level4) level5l && everyKey (rowOK 4 level4) level5r) = true
  rw [level5l_ok, level5r_ok]
  decide +kernel
theorem closed5 : Closed 5 level5 := closed_next 4 (by decide) level5 level4 closed4 level5_ok
def level6llll : BinaryTree (List W) := (.node [v3, v73, v108, v123, v146, v178, v199] (.node [v2, v73, v108, v123, v146, v178, v199] (.node [v2, v73, v108, v123, v146, v178] .nil .nil) .nil) (.node [v4, v73, v108, v123, v146, v178, v199] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llll_ok : everyKey (rowOK 5 level5) level6llll = true := by decide +kernel
def level6lllr : BinaryTree (List W) := (.node [v11, v73, v108, v123, v146, v178, v199] (.node [v8, v73, v108, v123, v146, v178, v199] .nil .nil) (.node [v12, v73, v108, v123, v146, v178, v199] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllr_ok : everyKey (rowOK 5 level5) level6lllr = true := by decide +kernel
def level6lll : BinaryTree (List W) := .node [v6, v73, v108, v123, v146, v178, v199] level6llll level6lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lll_ok : everyKey (rowOK 5 level5) level6lll = true := by
  change (_ && everyKey (rowOK 5 level5) level6llll && everyKey (rowOK 5 level5) level6lllr) = true
  rw [level6llll_ok, level6lllr_ok]
  decide +kernel
def level6llrl : BinaryTree (List W) := (.node [v18, v73, v108, v123, v146, v178, v199] (.node [v15, v73, v108, v123, v146, v178, v199] .nil .nil) (.node [v21, v73, v108, v123, v146, v178, v199] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrl_ok : everyKey (rowOK 5 level5) level6llrl = true := by decide +kernel
def level6llrr : BinaryTree (List W) := (.node [v28, v73, v108, v123, v146, v178, v199] (.node [v26, v73, v108, v123, v146, v178, v199] .nil .nil) (.node [v30, v73, v108, v123, v146, v178, v199] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrr_ok : everyKey (rowOK 5 level5) level6llrr = true := by decide +kernel
def level6llr : BinaryTree (List W) := .node [v25, v73, v108, v123, v146, v178, v199] level6llrl level6llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llr_ok : everyKey (rowOK 5 level5) level6llr = true := by
  change (_ && everyKey (rowOK 5 level5) level6llrl && everyKey (rowOK 5 level5) level6llrr) = true
  rw [level6llrl_ok, level6llrr_ok]
  decide +kernel
def level6ll : BinaryTree (List W) := .node [v13, v73, v108, v123, v146, v178, v199] level6lll level6llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6ll_ok : everyKey (rowOK 5 level5) level6ll = true := by
  change (_ && everyKey (rowOK 5 level5) level6lll && everyKey (rowOK 5 level5) level6llr) = true
  rw [level6lll_ok, level6llr_ok]
  decide +kernel
def level6lrll : BinaryTree (List W) := (.node [v39, v73, v108, v123, v146, v178, v199] (.node [v38, v73, v108, v123, v146, v178, v199] (.node [v32, v73, v108, v123, v146, v178, v199] .nil .nil) .nil) (.node [v40, v73, v108, v123, v146, v178, v199] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrll_ok : everyKey (rowOK 5 level5) level6lrll = true := by decide +kernel
def level6lrlr : BinaryTree (List W) := (.node [v54, v73, v108, v123, v146, v178, v199] (.node [v46, v73, v108, v123, v146, v178, v199] .nil .nil) (.node [v55, v73, v108, v123, v146, v178, v199] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlr_ok : everyKey (rowOK 5 level5) level6lrlr = true := by decide +kernel
def level6lrl : BinaryTree (List W) := .node [v43, v73, v108, v123, v146, v178, v199] level6lrll level6lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrl_ok : everyKey (rowOK 5 level5) level6lrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrll && everyKey (rowOK 5 level5) level6lrlr) = true
  rw [level6lrll_ok, level6lrlr_ok]
  decide +kernel
def level6lrrl : BinaryTree (List W) := (.node [v59, v73, v108, v123, v146, v178, v199] (.node [v57, v73, v108, v123, v146, v178, v199] .nil .nil) (.node [v61, v73, v108, v123, v146, v178] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrl_ok : everyKey (rowOK 5 level5) level6lrrl = true := by decide +kernel
def level6lrrr : BinaryTree (List W) := (.node [v67, v73, v108, v123, v146, v178, v199] (.node [v63, v73, v108, v123, v146, v178, v199] .nil .nil) (.node [v68, v73, v108, v123, v146, v178] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrr_ok : everyKey (rowOK 5 level5) level6lrrr = true := by decide +kernel
def level6lrr : BinaryTree (List W) := .node [v61, v73, v108, v123, v146, v178, v199] level6lrrl level6lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrr_ok : everyKey (rowOK 5 level5) level6lrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrrl && everyKey (rowOK 5 level5) level6lrrr) = true
  rw [level6lrrl_ok, level6lrrr_ok]
  decide +kernel
def level6lr : BinaryTree (List W) := .node [v56, v73, v108, v123, v146, v178, v199] level6lrl level6lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lr_ok : everyKey (rowOK 5 level5) level6lr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrl && everyKey (rowOK 5 level5) level6lrr) = true
  rw [level6lrl_ok, level6lrr_ok]
  decide +kernel
def level6l : BinaryTree (List W) := .node [v32, v73, v108, v123, v146, v178] level6ll level6lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6l_ok : everyKey (rowOK 5 level5) level6l = true := by
  change (_ && everyKey (rowOK 5 level5) level6ll && everyKey (rowOK 5 level5) level6lr) = true
  rw [level6ll_ok, level6lr_ok]
  decide +kernel
def level6rlll : BinaryTree (List W) := (.node [v73, v92, v108, v123, v146, v178, v199] (.node [v73, v86, v108, v123, v146, v178, v199] (.node [v73, v85, v108, v123, v146, v178, v199] .nil .nil) .nil) (.node [v73, v94, v108, v123, v146, v178, v199] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlll_ok : everyKey (rowOK 5 level5) level6rlll = true := by decide +kernel
def level6rllr : BinaryTree (List W) := (.node [v73, v102, v108, v123, v146, v178, v199] (.node [v73, v100, v108, v123, v146, v178, v199] .nil .nil) (.node [v73, v104, v108, v123, v146, v178, v199] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllr_ok : everyKey (rowOK 5 level5) level6rllr = true := by decide +kernel
def level6rll : BinaryTree (List W) := .node [v73, v97, v108, v123, v146, v178, v199] level6rlll level6rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rll_ok : everyKey (rowOK 5 level5) level6rll = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlll && everyKey (rowOK 5 level5) level6rllr) = true
  rw [level6rlll_ok, level6rllr_ok]
  decide +kernel
def level6rlrl : BinaryTree (List W) := (.node [v73, v108, v117, v123, v146, v178, v199] (.node [v73, v108, v116, v123, v146, v178, v199] .nil .nil) (.node [v73, v108, v120, v123, v146, v178, v199] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrl_ok : everyKey (rowOK 5 level5) level6rlrl = true := by decide +kernel
def level6rlrr : BinaryTree (List W) := (.node [v73, v108, v123, v138, v146, v178, v199] (.node [v73, v108, v123, v137, v146, v178, v199] .nil .nil) (.node [v73, v108, v123, v144, v146, v178, v199] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrr_ok : everyKey (rowOK 5 level5) level6rlrr = true := by decide +kernel
def level6rlr : BinaryTree (List W) := .node [v73, v108, v123, v134, v146, v178, v199] level6rlrl level6rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlr_ok : everyKey (rowOK 5 level5) level6rlr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlrl && everyKey (rowOK 5 level5) level6rlrr) = true
  rw [level6rlrl_ok, level6rlrr_ok]
  decide +kernel
def level6rl : BinaryTree (List W) := .node [v73, v107, v108, v123, v146, v178, v199] level6rll level6rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rl_ok : everyKey (rowOK 5 level5) level6rl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rll && everyKey (rowOK 5 level5) level6rlr) = true
  rw [level6rll_ok, level6rlr_ok]
  decide +kernel
def level6rrll : BinaryTree (List W) := (.node [v73, v108, v123, v146, v171, v178, v199] (.node [v73, v108, v123, v146, v166, v178, v199] .nil .nil) (.node [v73, v108, v123, v146, v176, v178, v199] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrll_ok : everyKey (rowOK 5 level5) level6rrll = true := by decide +kernel
def level6rrlr : BinaryTree (List W) := (.node [v73, v108, v123, v146, v178, v196, v199] (.node [v73, v108, v123, v146, v178, v193, v199] .nil .nil) (.node [v73, v108, v123, v146, v178, v197, v199] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlr_ok : everyKey (rowOK 5 level5) level6rrlr = true := by decide +kernel
def level6rrl : BinaryTree (List W) := .node [v73, v108, v123, v146, v178, v190, v199] level6rrll level6rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrl_ok : everyKey (rowOK 5 level5) level6rrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrll && everyKey (rowOK 5 level5) level6rrlr) = true
  rw [level6rrll_ok, level6rrlr_ok]
  decide +kernel
def level6rrrl : BinaryTree (List W) := (.node [v73, v108, v123, v146, v178, v199, v220] (.node [v73, v108, v123, v146, v178, v199, v217] .nil .nil) (.node [v73, v108, v123, v146, v178, v199, v223] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrl_ok : everyKey (rowOK 5 level5) level6rrrl = true := by decide +kernel
def level6rrrr : BinaryTree (List W) := (.node [v73, v108, v123, v146, v178, v217] (.node [v73, v108, v123, v146, v178, v199, v227] .nil .nil) (.node [v73, v108, v123, v146, v178, v223] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrr_ok : everyKey (rowOK 5 level5) level6rrrr = true := by decide +kernel
def level6rrr : BinaryTree (List W) := .node [v73, v108, v123, v146, v178, v199, v226] level6rrrl level6rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrr_ok : everyKey (rowOK 5 level5) level6rrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrrl && everyKey (rowOK 5 level5) level6rrrr) = true
  rw [level6rrrl_ok, level6rrrr_ok]
  decide +kernel
def level6rr : BinaryTree (List W) := .node [v73, v108, v123, v146, v178, v199, v208] level6rrl level6rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rr_ok : everyKey (rowOK 5 level5) level6rr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrl && everyKey (rowOK 5 level5) level6rrr) = true
  rw [level6rrl_ok, level6rrr_ok]
  decide +kernel
def level6r : BinaryTree (List W) := .node [v73, v108, v123, v146, v161, v178, v199] level6rl level6rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6r_ok : everyKey (rowOK 5 level5) level6r = true := by
  change (_ && everyKey (rowOK 5 level5) level6rl && everyKey (rowOK 5 level5) level6rr) = true
  rw [level6rl_ok, level6rr_ok]
  decide +kernel
def level6 : BinaryTree (List W) := .node [v68, v73, v108, v123, v146, v178, v199] level6l level6r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6_ok : everyKey (rowOK 5 level5) level6 = true := by
  change (_ && everyKey (rowOK 5 level5) level6l && everyKey (rowOK 5 level5) level6r) = true
  rw [level6l_ok, level6r_ok]
  decide +kernel
theorem closed6 : Closed 6 level6 := closed_next 5 (by decide) level6 level5 closed5 level6_ok
def level7 : BinaryTree (List W) := (.node [v73, v108, v123, v146, v178, v199] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7_ok : everyKey (rowOK 6 level6) level7 = true := by decide +kernel
theorem closed7 : Closed 7 level7 := closed_next 6 (by decide) level7 level6 closed6 level7_ok

theorem lower : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z 7 ins.toFinset :=
  @no_build 7 level7 ins (by decide +kernel) (by decide) closed7 (by decide +kernel)
def witness : List Gate := [⟨.and,[3,4]⟩, ⟨.or,[0,6]⟩, ⟨.and,[2,4]⟩, ⟨.or,[3,5]⟩, ⟨.or,[8,9]⟩, ⟨.and,[0,10]⟩, ⟨.or,[1,11]⟩, ⟨.or,[2,7]⟩, ⟨.and,[12,13]⟩]
theorem upper : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 9 ∧ ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xeeeaeaeaeee8eac8 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact ⟨witness,14,by simp [witness],rfl,by decide +kernel⟩
end PEqualNP.Outside.L_meta_13647_aux

open PEqualNP.Outside.L_meta_13647_aux in
theorem PEqualNP.Outside.L_meta_13647 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372970 * 2 ^ 32 + 4008241864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372970 * 2 ^ 32 + 4008241864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  have code : 4008372970 * 2 ^ 32 + 4008241864 = 0xeeeaeaeaeee8eac8 := by decide
  simp only [code] at h ⊢
  obtain ⟨C,legal,size,computes⟩ := h
  obtain ⟨gs,o,mono,bound,ev⟩ := replace 0xeeeaeaeaeee8eac8 9 ins (by decide +kernel) sampled rfl lower upper C.gates C.output legal computes
  exact ⟨⟨gs,o⟩,mono,bound.trans size,ev⟩
