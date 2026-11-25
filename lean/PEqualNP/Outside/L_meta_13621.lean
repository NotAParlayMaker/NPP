import PEqualNP.Defs

-- The live-wire search and circuit compiler are adapted from the merged L-meta-8639 under Apache-2.0.
namespace PEqualNP.Outside.L_meta_13621_aux

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

def v0 : W := 0x134cc0000000000f7
def v1 : W := 0x268e00000000038f8
def v2 : W := 0x821c00000000000f0
def v3 : W := 0x4c05540000000000f7
def v4 : W := 0x9809600000000e00f8
def v5 : W := 0x10c31980000000000f7
def v6 : W := 0x228a1800000000e38f8
def v7 : W := 0x54d35dc0000000000f7
def v8 : W := 0xabae9e00000000e38f8
def v9 : W := 0xcd34c6400000330c300
def v10 : W := 0xddf7dfc00000330c3f7
def v11 : W := 0xefbede40000033efbf8
def v12 : W := 0xf23f088000003c0fc00
def v13 : W := 0xf6ff5dc000003c0fcf7
def v14 : W := 0xfbbf9e8000003cefcf8
def v15 : W := 0xffc8110000003ff0000
def v16 : W := 0xffdb5dc000003ff00f7
def v17 : W := 0xffee9f0000003ff38f8
def v18 : W := 0xffffdfc0000000e38ff
def v19 : W := 0xf300002000003fc000000
def v20 : W := 0x3150000200003cfc000000
def v21 : W := 0x1357000020000003c000000
def v22 : W := 0x135700136cc00003c0000f7
def v23 : W := 0x26b100002000038c0000000
def v24 : W := 0x26b10026ae00038c00038f8
def v25 : W := 0x34e20034c6400c30000c300
def v26 : W := 0x3704003708800fc0000fc00
def v27 : W := 0x375700376cc00fc3c00fcf7
def v28 : W := 0x37f7000020000fffc000000
def v29 : W := 0x37f70034e6400fffc00c300
def v30 : W := 0x37f7003728800fffc00fc00
def v31 : W := 0x37f70037eec0038fc0038ff
def v32 : W := 0x37f7ffc831000ffffff0000
def v33 : W := 0x82110000200000000000000
def v34 : W := 0x821100823c00000000000f0
def v35 : W := 0xc01900002000f00fc000000
def v36 : W := 0x4c05b000020000003c000000
def v37 : W := 0x4c05b04c075400003c0000f7
def v38 : W := 0x980b100002000e00c0000000
def v39 : W := 0x980b10980b600e00c00e00f8
def v40 : W := 0xd00e20d00c64300300300300
def v41 : W := 0xd34e20d34c6430c30030c300
def v42 : W := 0xdc0080dc01103f00003f0000
def v43 : W := 0xdc05b0dc07543f003c3f00f7
def v44 : W := 0xdc0fb00002003f03fc000000
def v45 : W := 0xdc0fb0d00e643f03fc300300
def v46 : W := 0xdc0fb0dc03103f03fc3f0000
def v47 : W := 0xdc0fb0dc0f740e00fc0e00ff
def v48 : W := 0xdc0fbf23f2883f03ffc0fc00
def v49 : W := 0xdf70c0df71983ffc003ffc00
def v50 : W := 0xdf7ff00002003ffffc000000
def v51 : W := 0x10c31d000020000003c000000
def v52 : W := 0x10c31d10c339800003c0000f7
def v53 : W := 0x228a1100002000e38c0000000
def v54 : W := 0x228a11228a3800e38c00e38f8
def v55 : W := 0x320b04320b088c03c00c03c00
def v56 : W := 0x320b04f23f088c03c03c0fc00
def v57 : W := 0x323f04323f088c0fc00c0fc00
def v58 : W := 0x32c80832c8110cf0000cf0000
def v59 : W := 0x32c808ffc8110cf0003ff0000
def v60 : W := 0x32cb1d0000200cf3cfc000000
def v61 : W := 0x32cb1d320b288cf3cfcc03c00
def v62 : W := 0x32cb1d32c8310cf3cfccf0000
def v63 : W := 0x32cb1d32cb3980e38fc0e38ff
def v64 : W := 0x32cb1dcd34e64cf3cff30c300
def v65 : W := 0x32fcea32fcd74cfc300cfc300
def v66 : W := 0x32ffff0000200cffffc000000
def v67 : W := 0x3f0be63f0bcecf03f00f03f00
def v68 : W := 0x3fc8083fc8110ff0000ff0000
def v69 : W := 0x3fcbff0000200ff3ffc000000
def v70 : W := 0x441042441040730c30330c300
def v71 : W := 0x4410424410444000000000000
def v72 : W := 0x44104254d35dc0000000000f7
def v73 : W := 0x501104501100bc0c403c0c400
def v74 : W := 0x5013045013088000000000000
def v75 : W := 0x50130454d35dc0000000000f7
def v76 : W := 0x5440085440013f10003f10000
def v77 : W := 0x54514e0000003f1c73c000000
def v78 : W := 0x54514e545141c00003c000007
def v79 : W := 0x54514e54d35dc00003c0000f7
def v80 : W := 0x54514eabae9e3f1c73c0e38f8
def v81 : W := 0x5466b95466af3f138c3f138f8
def v82 : W := 0x5477ff0000203f1fffc000000
def v83 : W := 0x54c00854c0110000000000000
def v84 : W := 0x54c00854d35dc0000000000f7
def v85 : W := 0x54d35f000020000003c000000
def v86 : W := 0x54d35f0000203f1c73c000000
def v87 : W := 0x54d35f441064400003c000000
def v88 : W := 0x54d35f501328800003c000000
def v89 : W := 0x54d35f545161c00003c000007
def v90 : W := 0x54d35f54c031000003c000000
def v91 : W := 0x54d35f54d379c00003c0000f7
def v92 : W := 0x54d35f54d37dc00003c0000f7
def v93 : W := 0x54f7ff000020000fffc000000
def v94 : W := 0x5991b55991b6bcec4c3cec4f8
def v95 : W := 0x5dd1ff0000203ffc7fc000000
def v96 : W := 0x5dd3ff00002003f03fc000000
def v97 : W := 0x669a53669a7873efbc33efbf8
def v98 : W := 0x721b04721b088c03c00c03c00
def v99 : W := 0x721b04721b08bc0fc03c0fc00
def v100 : W := 0x76c80876c8110cf0000cf0000
def v101 : W := 0x76c80876c8113ff0003ff0000
def v102 : W := 0x76db5f0000200cf3cfc000000
def v103 : W := 0x76db5f0000203fffffc000000
def v104 : W := 0x8924a0892482330c30330c300
def v105 : W := 0x8924a08924860000000000000
def v106 : W := 0x8924a0abae9e00000000e38f8
def v107 : W := 0x8934e28934c6400c30000c300
def v108 : W := 0x8934e28934c6730c30330c300
def v109 : W := 0x8d24e28d24c64300300300300
def v110 : W := 0x8d24e28d24c6730c30330c300
def v111 : W := 0x99e7bd99e7bbb30c33f30c3f7
def v112 : W := 0xa22c00a22c003c0fc03c0fc00
def v113 : W := 0xa22e00a22e080003800003800
def v114 : W := 0xa22e00abae9e00038000e38f8
def v115 : W := 0xa23f04a23f08800fc0000fc00
def v116 : W := 0xa23f04a23f08bc0fc03c0fc00
def v117 : W := 0xa6ec5ba6ec757c0fc3fc0fcf7
def v118 : W := 0xab0800ab08003ff0003ff0000
def v119 : W := 0xab1b57ab1b6cfff003fff00f7
def v120 : W := 0xab2ca00000003ffffc0000000
def v121 : W := 0xab2ca054d35dfffffc00000f7
def v122 : W := 0xab2ca0ab2c8200e38c00e3808
def v123 : W := 0xab2ca0abae9e00e38c00e38f8
def v124 : W := 0xab2eb1ab2ca200e38c00e3808
def v125 : W := 0xab2eb1ab2eae00e38c00e38f8
def v126 : W := 0xab3ff70000203fffffc000000
def v127 : W := 0xab8800ab881000e00000e0000
def v128 : W := 0xab8800abae9e00e00000e38f8
def v129 : W := 0xabacb1ab2ca200e38c00e3808
def v130 : W := 0xabacb1abacb600e38c00e38f8
def v131 : W := 0xabaeb100002000e38c0000000
def v132 : W := 0xabaeb10000203ffffc0000000
def v133 : W := 0xabaeb18924a600e38c0000000
def v134 : W := 0xabaeb1a22e2800e38c0003800
def v135 : W := 0xabaeb1ab2ca200e38c00e3808
def v136 : W := 0xabaeb1ab2ca600e38c00e3808
def v137 : W := 0xabaeb1ab2eaa00e38c00e3808
def v138 : W := 0xabaeb1ab2eae00e38c0003800
def v139 : W := 0xabaeb1ab883000e38c00e0000
def v140 : W := 0xabaeb1abacb200e38c00e3808
def v141 : W := 0xabaeb1abacb600e38c00e0000
def v142 : W := 0xabaeb1abaeba00e38c00e38f8
def v143 : W := 0xabaeb1abaebe00e38c00e38f8
def v144 : W := 0xabaeb1ffffffc0e38c00e38ff
def v145 : W := 0xabbff700002000efffc000000
def v146 : W := 0xafc808afc81103f00003f0000
def v147 : W := 0xafc808afc8113ff0003ff0000
def v148 : W := 0xafecfb0000203fffffc000000
def v149 : W := 0xafeefb00002003f3bfc000000
def v150 : W := 0xb22f04b22f088c03c00c03c00
def v151 : W := 0xb22f04b22f08bc0fc03c0fc00
def v152 : W := 0xbbc808bbc8110cf0000cf0000
def v153 : W := 0xbbc808bbc8113ff0003ff0000
def v154 : W := 0xbbefbd0000200cf3cfc000000
def v155 : W := 0xbbefbd0000203fffffc000000
def v156 : W := 0xc03400c03400300c00300c000
def v157 : W := 0xcd0000cd00003300003300000
def v158 : W := 0xcd34e2000000330c300000000
def v159 : W := 0xcd34e2cd34c64000000000000
def v160 : W := 0xcd34e2cd34c6730c30330c300
def v161 : W := 0xcd34e2ddf7dff30c30330c3f7
def v162 : W := 0xcd34e2efbede730c3033efbf8
def v163 : W := 0xcd37f7000020330fffc000000
def v164 : W := 0xcd37f7cd34e6730ffff30c300
def v165 : W := 0xcdb6f3cd34e6730c30330c300
def v166 : W := 0xcdf4fb00002033fc3fc000000
def v167 : W := 0xcdf4fbcd34e673fc3ff30c300
def v168 : W := 0xdd35e6dd35c6ff0c703f0c700
def v169 : W := 0xdd37e6dd37cef30c30330c300
def v170 : W := 0xdd74eadd74c77f1c303f1c300
def v171 : W := 0xddf4eaddf4d7730c30330c300
def v172 : W := 0xddf7ff000020330c33c000000
def v173 : W := 0xddf7ffcd34e6730c33f30c300
def v174 : W := 0xddf7ffddf7ffc00003c0000f7
def v175 : W := 0xddf7ffddf7fff30c33f30c3f7
def v176 : W := 0xefbef300002033efbc0000000
def v177 : W := 0xefbef3cd34e673efbc330c300
def v178 : W := 0xefbef3efbefe40e38c00e38f8
def v179 : W := 0xefbef3efbefe73efbc33efbf8
def v180 : W := 0xf20800f208003c00003c00000
def v181 : W := 0xf20b04f20b08bc03c03c03c00
def v182 : W := 0xf21b04f21b08bc00003c00000
def v183 : W := 0xf23f040000003c0fc00000000
def v184 : W := 0xf23f04320b08bc0fc00c03c00
def v185 : W := 0xf23f04f23f088003800003800
def v186 : W := 0xf23f04f23f08bc0fc03c0fc00
def v187 : W := 0xf23f04f6ff5dfc0fc03c0fcf7
def v188 : W := 0xf23f04fbbf9ebc0fc03cefcf8
def v189 : W := 0xf23f04ff3fcefc0fc03f0ff00
def v190 : W := 0xf23fb5f23f28bc0fcc3c0fc00
def v191 : W := 0xf23fe6f23fcefc0ff03c0ff00
def v192 : W := 0xf23ff70000203c0fffc000000
def v193 : W := 0xf23ff7f23f28bc0ffffc0fc00
def v194 : W := 0xf2bf15f23f28bc0fc03c0fc00
def v195 : W := 0xf2c808f2c8113cf0003cf0000
def v196 : W := 0xf2ff1d0000203cffcfc000000
def v197 : W := 0xf2ff1df23f28bcffcffc0fc00
def v198 : W := 0xf63f46f63f48ff0ff03f0ff00
def v199 : W := 0xf63f46f63f4cfc0fc03c0fc00
def v200 : W := 0xf67f0cf67f09bf1fc03f1fc00
def v201 : W := 0xf6c808f6c8113c00003c00000
def v202 : W := 0xf6ff0cf6ff19bc0fc03c0fc00
def v203 : W := 0xf6ff5f0000203c0fc3c000000
def v204 : W := 0xf6ff5ff23f28bc0fc3fc0fc00
def v205 : W := 0xf6ff5ff6ff7dfc0fc3fc0fcf7
def v206 : W := 0xfb3fa4fb3f8abf0ff03f0ff00
def v207 : W := 0xfb3fa4fb3f8ebc0fc03c0fc00
def v208 : W := 0xfbbfb50000203cefcc0000000
def v209 : W := 0xfbbfb5f23f28bcefcc3c0fc00
def v210 : W := 0xfbbfb5fbbfbe80e38c00e38f8
def v211 : W := 0xfbbfb5fbbfbebcefcc3cefcf8
def v212 : W := 0xff3ce2ff3cc67f0c303f0c300
def v213 : W := 0xff3f04ff3f08bf0fc03f0fc00
def v214 : W := 0xff3fe6f23f08bf0ff03c0fc00
def v215 : W := 0xff3fe6ff3fceff0c303f0c300
def v216 : W := 0xff3fe6ff3fceff0ff03f0ff00
def v217 : W := 0xff7deeff7dc3c0e38fc0e380f
def v218 : W := 0xffc8080000003ff0000000000
def v219 : W := 0xffc80832c8113ff0000cf0000
def v220 : W := 0xffc808ffc81100e00000e0000
def v221 : W := 0xffc808ffc8113ff0003ff0000
def v222 : W := 0xffc808ffdb5dfff0003ff00f7
def v223 : W := 0xffc808ffee9f3ff0003ff38f8
def v224 : W := 0xffc808fffcd77ff0003ffc300
def v225 : W := 0xffc8b9ffc8313ff00c3ff0000
def v226 : W := 0xffc8eaffc8d77ff0303ff0300
def v227 : W := 0xffc8fb0000203ff03fc000000
def v228 : W := 0xffc8fbffc8313ff03ffff0000
def v229 : W := 0xffca19ffc8313ff0003ff0000
def v230 : W := 0xffcb1d0000203ff3cfc000000
def v231 : W := 0xffcb1dffc8313ff3cffff0000
def v232 : W := 0xffd84affd8517ffc303ffc300
def v233 : W := 0xffd84affd8557ff0003ff0000
def v234 : W := 0xffd90cffd911bffc403ffc400
def v235 : W := 0xffdb0cffdb19bff0003ff0000
def v236 : W := 0xffdb5f0000203ff003c000000
def v237 : W := 0xffdb5fffc8313ff003fff0000
def v238 : W := 0xffdb5fffdb7dfff003fff00f7
def v239 : W := 0xffeca8ffec933ffc303ffc300
def v240 : W := 0xffeca8ffec973ff0003ff0000
def v241 : W := 0xffeeb90000203ff38c0000000
def v242 : W := 0xffeeb9ffc8313ff38c3ff0000
def v243 : W := 0xffeeb9ffeebf00e38c00e38f8
def v244 : W := 0xffeeb9ffeebf3ff38c3ff38f8
def v245 : W := 0xfffc08fffc113ffc003ffc000
def v246 : W := 0xfffceaffc8113ffc303ff0000
def v247 : W := 0xfffceafffcd77f0c303f0c300
def v248 : W := 0xfffceafffcd77ffc303ffc300
def v249 : W := 0xffff0cffff19bfffc03fffc00
def v250 : W := 0xffffff00002000e38fc000000
def v251 : W := 0xffffff0000203fffffc000000
def v252 : W := 0xffffff0034e67fffffc00c300
def v253 : W := 0xffffff003728bfffffc00fc00
def v254 : W := 0xffffff0d00e67fffffc300300
def v255 : W := 0xffffff0dc0313fffffc3f0000
def v256 : W := 0xffffff320b28bfffffcc03c00
def v257 : W := 0xffffff32c8313fffffccf0000
def v258 : W := 0xffffff4410607ffffff30c300
def v259 : W := 0xffffff4410647fffffc000000
def v260 : W := 0xffffff501120bffffffc0c400
def v261 : W := 0xffffff501328bfffffc000000
def v262 : W := 0xffffff5440213fffffff10000
def v263 : W := 0xffffff545161ffffffc000007
def v264 : W := 0xffffff54c0313fffffc000000
def v265 : W := 0xffffff54d37dffffffc0000f7
def v266 : W := 0xffffff8924a23ffffff30c300
def v267 : W := 0xffffff8924a63fffffc000000
def v268 : W := 0xffffffa22c203ffffffc0fc00
def v269 : W := 0xffffffa22e283fffffc003800
def v270 : W := 0xffffffab08203ffffffff0000
def v271 : W := 0xffffffab2ca23fffffc0e3808
def v272 : W := 0xffffffab88303fffffc0e0000
def v273 : W := 0xffffffabaebe3fffffc0e38f8
def v274 : W := 0xffffffc034203ffffff00c000
def v275 : W := 0xffffffcd00203ffffff300000
def v276 : W := 0xffffffcd34e67ffffff30c300
def v277 : W := 0xfffffff208203ffffffc00000
def v278 : W := 0xfffffff23f28bffffffc0fc00
def v279 : W := 0xffffffff3feeffffffff0ff00
def v280 : W := 0xffffffffc8313ffffffff0000
def v281 : W := 0xfffffffffcf77ffffffffc300
def v282 : W := 0xffffffffff39bfffffffffc00
def v283 : W := 0xffffffffffffc0e38fc0e38ff

def ins : List W := [v92, v143, v160, v186, v221, v251]
theorem sampled : ∀ j : Fin 100, Nat.testBit 0xeeeaeae8eeeaeae0 (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
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
def level3 : BinaryTree (List W) := (.node [v92, v138, v216, v248] (.node [v92, v135, v216, v248] .nil .nil) (.node [v92, v141, v216, v248] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level3_ok : everyKey (rowOK 2 level2) level3 = true := by decide +kernel
theorem closed3 : Closed 3 level3 := closed_next 2 (by decide) level3 level2 closed2 level3_ok
def level4llll : BinaryTree (List W) := (.node [v20, v92, v143, v216, v248] (.node [v8, v92, v143, v216, v248] (.node [v7, v92, v143, v216, v248] .nil .nil) .nil) (.node [v28, v92, v143, v216, v248] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llll_ok : everyKey (rowOK 3 level3) level4llll = true := by decide +kernel
def level4lllr : BinaryTree (List W) := (.node [v44, v92, v143, v216, v248] (.node [v35, v92, v143, v216, v248] .nil .nil) (.node [v48, v92, v143, v160, v221] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lllr_ok : everyKey (rowOK 3 level3) level4lllr = true := by decide +kernel
def level4lll : BinaryTree (List W) := .node [v32, v92, v143, v160, v186] level4llll level4lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lll_ok : everyKey (rowOK 3 level3) level4lll = true := by
  change (_ && everyKey (rowOK 3 level3) level4llll && everyKey (rowOK 3 level3) level4lllr) = true
  rw [level4llll_ok, level4lllr_ok]
  decide +kernel
def level4llrl : BinaryTree (List W) := (.node [v60, v92, v143, v216, v248] (.node [v58, v92, v135, v160, v186] (.node [v55, v92, v135, v160, v221] .nil .nil) .nil) (.node [v61, v92, v143, v216, v221] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llrl_ok : everyKey (rowOK 3 level3) level4llrl = true := by decide +kernel
def level4llrr : BinaryTree (List W) := (.node [v65, v92, v143, v186, v251] (.node [v64, v92, v143, v186, v221] .nil .nil) (.node [v67, v92, v143, v221, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llrr_ok : everyKey (rowOK 3 level3) level4llrr = true := by decide +kernel
def level4llr : BinaryTree (List W) := .node [v62, v92, v143, v186, v248] level4llrl level4llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llr_ok : everyKey (rowOK 3 level3) level4llr = true := by
  change (_ && everyKey (rowOK 3 level3) level4llrl && everyKey (rowOK 3 level3) level4llrr) = true
  rw [level4llrl_ok, level4llrr_ok]
  decide +kernel
def level4ll : BinaryTree (List W) := .node [v49, v92, v143, v160, v251] level4lll level4llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4ll_ok : everyKey (rowOK 3 level3) level4ll = true := by
  change (_ && everyKey (rowOK 3 level3) level4lll && everyKey (rowOK 3 level3) level4llr) = true
  rw [level4lll_ok, level4llr_ok]
  decide +kernel
def level4lrll : BinaryTree (List W) := (.node [v85, v92, v143, v216, v248] (.node [v81, v92, v160, v186, v251] (.node [v80, v92, v160, v186, v221] .nil .nil) .nil) (.node [v92, v94, v160, v221, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrll_ok : everyKey (rowOK 3 level3) level4lrll = true := by decide +kernel
def level4lrlr : BinaryTree (List W) := (.node [v92, v129, v160, v186, v221] (.node [v92, v124, v160, v186, v221] .nil .nil) (.node [v92, v131, v143, v216, v248] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrlr_ok : everyKey (rowOK 3 level3) level4lrlr = true := by decide +kernel
def level4lrl : BinaryTree (List W) := .node [v92, v97, v186, v221, v251] level4lrll level4lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrl_ok : everyKey (rowOK 3 level3) level4lrl = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrll && everyKey (rowOK 3 level3) level4lrlr) = true
  rw [level4lrll_ok, level4lrlr_ok]
  decide +kernel
def level4lrrl : BinaryTree (List W) := (.node [v92, v135, v160, v216, v221] (.node [v92, v135, v160, v186, v248] .nil .nil) (.node [v92, v136, v160, v186, v221] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrrl_ok : everyKey (rowOK 3 level3) level4lrrl = true := by decide +kernel
def level4lrrr : BinaryTree (List W) := (.node [v92, v138, v160, v216, v221] (.node [v92, v138, v160, v186, v221] .nil .nil) (.node [v92, v140, v160, v186, v221] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrrr_ok : everyKey (rowOK 3 level3) level4lrrr = true := by decide +kernel
def level4lrr : BinaryTree (List W) := .node [v92, v137, v160, v186, v221] level4lrrl level4lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrr_ok : everyKey (rowOK 3 level3) level4lrr = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrrl && everyKey (rowOK 3 level3) level4lrrr) = true
  rw [level4lrrl_ok, level4lrrr_ok]
  decide +kernel
def level4lr : BinaryTree (List W) := .node [v92, v135, v160, v186, v221] level4lrl level4lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lr_ok : everyKey (rowOK 3 level3) level4lr = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrl && everyKey (rowOK 3 level3) level4lrr) = true
  rw [level4lrl_ok, level4lrr_ok]
  decide +kernel
def level4l : BinaryTree (List W) := .node [v79, v122, v160, v186, v221] level4ll level4lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4l_ok : everyKey (rowOK 3 level3) level4l = true := by
  change (_ && everyKey (rowOK 3 level3) level4ll && everyKey (rowOK 3 level3) level4lr) = true
  rw [level4ll_ok, level4lr_ok]
  decide +kernel
def level4rlll : BinaryTree (List W) := (.node [v92, v143, v160, v186, v229] (.node [v92, v143, v160, v186, v225] (.node [v92, v141, v160, v186, v248] .nil .nil) .nil) (.node [v92, v143, v160, v190, v221] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlll_ok : everyKey (rowOK 3 level3) level4rlll = true := by decide +kernel
def level4rllr : BinaryTree (List W) := (.node [v92, v143, v161, v216, v221] (.node [v92, v143, v161, v186, v248] .nil .nil) (.node [v92, v143, v164, v186, v248] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rllr_ok : everyKey (rowOK 3 level3) level4rllr = true := by decide +kernel
def level4rll : BinaryTree (List W) := .node [v92, v143, v160, v194, v221] level4rlll level4rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rll_ok : everyKey (rowOK 3 level3) level4rll = true := by
  change (_ && everyKey (rowOK 3 level3) level4rlll && everyKey (rowOK 3 level3) level4rllr) = true
  rw [level4rlll_ok, level4rllr_ok]
  decide +kernel
def level4rlrl : BinaryTree (List W) := (.node [v92, v143, v173, v216, v221] (.node [v92, v143, v173, v186, v248] (.node [v92, v143, v167, v216, v221] .nil .nil) .nil) (.node [v92, v143, v186, v247, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlrl_ok : everyKey (rowOK 3 level3) level4rlrl = true := by decide +kernel
def level4rlrr : BinaryTree (List W) := (.node [v92, v143, v212, v249, v251] (.node [v92, v143, v207, v248, v251] .nil .nil) (.node [v92, v143, v213, v248, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlrr_ok : everyKey (rowOK 3 level3) level4rlrr = true := by decide +kernel
def level4rlr : BinaryTree (List W) := .node [v92, v143, v206, v248, v251] level4rlrl level4rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlr_ok : everyKey (rowOK 3 level3) level4rlr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rlrl && everyKey (rowOK 3 level3) level4rlrr) = true
  rw [level4rlrl_ok, level4rlrr_ok]
  decide +kernel
def level4rl : BinaryTree (List W) := .node [v92, v143, v165, v186, v221] level4rll level4rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rl_ok : everyKey (rowOK 3 level3) level4rl = true := by
  change (_ && everyKey (rowOK 3 level3) level4rll && everyKey (rowOK 3 level3) level4rlr) = true
  rw [level4rll_ok, level4rlr_ok]
  decide +kernel
def level4rrll : BinaryTree (List W) := (.node [v92, v143, v216, v245, v251] (.node [v92, v143, v216, v240, v251] (.node [v92, v143, v216, v239, v251] .nil .nil) .nil) (.node [v92, v143, v216, v248, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrll_ok : everyKey (rowOK 3 level3) level4rrll = true := by decide +kernel
def level4rrlr : BinaryTree (List W) := (.node [v92, v143, v216, v248, v279] (.node [v92, v143, v216, v248, v278] .nil .nil) (.node [v92, v143, v216, v248, v280] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrlr_ok : everyKey (rowOK 3 level3) level4rrlr = true := by decide +kernel
def level4rrl : BinaryTree (List W) := .node [v92, v143, v216, v248, v276] level4rrll level4rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrl_ok : everyKey (rowOK 3 level3) level4rrl = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrll && everyKey (rowOK 3 level3) level4rrlr) = true
  rw [level4rrll_ok, level4rrlr_ok]
  decide +kernel
def level4rrrl : BinaryTree (List W) := (.node [v117, v143, v160, v221, v251] (.node [v111, v143, v186, v221, v251] .nil .nil) (.node [v119, v143, v160, v186, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrrl_ok : everyKey (rowOK 3 level3) level4rrrl = true := by decide +kernel
def level4rrrr : BinaryTree (List W) := (.node [v143, v174, v216, v221, v251] (.node [v143, v174, v186, v248, v251] .nil .nil) (.node [v160, v186, v217, v221, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrrr_ok : everyKey (rowOK 3 level3) level4rrrr = true := by decide +kernel
def level4rrr : BinaryTree (List W) := .node [v121, v143, v160, v186, v221] level4rrrl level4rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrr_ok : everyKey (rowOK 3 level3) level4rrr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrrl && everyKey (rowOK 3 level3) level4rrrr) = true
  rw [level4rrrl_ok, level4rrrr_ok]
  decide +kernel
def level4rr : BinaryTree (List W) := .node [v92, v143, v216, v248, v281] level4rrl level4rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rr_ok : everyKey (rowOK 3 level3) level4rr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrl && everyKey (rowOK 3 level3) level4rrr) = true
  rw [level4rrl_ok, level4rrr_ok]
  decide +kernel
def level4r : BinaryTree (List W) := .node [v92, v143, v215, v221, v251] level4rl level4rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4r_ok : everyKey (rowOK 3 level3) level4r = true := by
  change (_ && everyKey (rowOK 3 level3) level4rl && everyKey (rowOK 3 level3) level4rr) = true
  rw [level4rl_ok, level4rr_ok]
  decide +kernel
def level4 : BinaryTree (List W) := .node [v92, v141, v160, v186, v221] level4l level4r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4_ok : everyKey (rowOK 3 level3) level4 = true := by
  change (_ && everyKey (rowOK 3 level3) level4l && everyKey (rowOK 3 level3) level4r) = true
  rw [level4l_ok, level4r_ok]
  decide +kernel
theorem closed4 : Closed 4 level4 := closed_next 3 (by decide) level4 level3 closed3 level4_ok
def level5llllll : BinaryTree (List W) := (.node [v2, v92, v143, v160, v186, v221] (.node [v1, v92, v143, v160, v186, v221] (.node [v0, v92, v143, v160, v186, v221] .nil .nil) .nil) (.node [v3, v92, v143, v160, v186, v221] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llllll_ok : everyKey (rowOK 4 level4) level5llllll = true := by decide +kernel
def level5lllllr : BinaryTree (List W) := (.node [v7, v55, v92, v143, v160, v221] (.node [v6, v92, v143, v160, v186, v221] (.node [v5, v92, v143, v160, v186, v221] .nil .nil) .nil) (.node [v7, v58, v92, v143, v160, v186] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllllr_ok : everyKey (rowOK 4 level4) level5lllllr = true := by decide +kernel
def level5lllll : BinaryTree (List W) := .node [v4, v92, v143, v160, v186, v221] level5llllll level5lllllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllll_ok : everyKey (rowOK 4 level4) level5lllll = true := by
  change (_ && everyKey (rowOK 4 level4) level5llllll && everyKey (rowOK 4 level4) level5lllllr) = true
  rw [level5llllll_ok, level5lllllr_ok]
  decide +kernel
def level5llllrl : BinaryTree (List W) := (.node [v7, v92, v143, v160, v186, v248] (.node [v7, v92, v143, v160, v186, v221] (.node [v7, v92, v135, v160, v186, v221] .nil .nil) .nil) (.node [v7, v92, v143, v160, v216, v221] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llllrl_ok : everyKey (rowOK 4 level4) level5llllrl = true := by decide +kernel
def level5llllrr : BinaryTree (List W) := (.node [v8, v58, v92, v143, v160, v186] (.node [v8, v55, v92, v143, v160, v221] (.node [v7, v120, v143, v160, v186, v221] .nil .nil) .nil) (.node [v8, v77, v92, v160, v186, v221] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llllrr_ok : everyKey (rowOK 4 level4) level5llllrr = true := by decide +kernel
def level5llllr : BinaryTree (List W) := .node [v7, v92, v144, v160, v186, v221] level5llllrl level5llllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llllr_ok : everyKey (rowOK 4 level4) level5llllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llllrl && everyKey (rowOK 4 level4) level5llllrr) = true
  rw [level5llllrl_ok, level5llllrr_ok]
  decide +kernel
def level5llll : BinaryTree (List W) := .node [v7, v85, v143, v160, v186, v221] level5lllll level5llllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llll_ok : everyKey (rowOK 4 level4) level5llll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lllll && everyKey (rowOK 4 level4) level5llllr) = true
  rw [level5lllll_ok, level5llllr_ok]
  decide +kernel
def level5lllrll : BinaryTree (List W) := (.node [v8, v92, v143, v160, v216, v221] (.node [v8, v92, v143, v160, v186, v248] (.node [v8, v92, v143, v160, v186, v221] .nil .nil) .nil) (.node [v9, v60, v92, v143, v186, v221] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrll_ok : everyKey (rowOK 4 level4) level5lllrll = true := by decide +kernel
def level5lllrlr : BinaryTree (List W) := (.node [v13, v92, v143, v160, v186, v221] (.node [v12, v44, v92, v143, v160, v221] (.node [v11, v92, v143, v160, v186, v221] .nil .nil) .nil) (.node [v14, v92, v143, v160, v186, v221] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrlr_ok : everyKey (rowOK 4 level4) level5lllrlr = true := by decide +kernel
def level5lllrl : BinaryTree (List W) := .node [v10, v92, v143, v160, v186, v221] level5lllrll level5lllrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrl_ok : everyKey (rowOK 4 level4) level5lllrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lllrll && everyKey (rowOK 4 level4) level5lllrlr) = true
  rw [level5lllrll_ok, level5lllrlr_ok]
  decide +kernel
def level5lllrrl : BinaryTree (List W) := (.node [v18, v92, v143, v160, v186, v221] (.node [v17, v92, v143, v160, v186, v221] (.node [v16, v92, v143, v160, v186, v221] .nil .nil) .nil) (.node [v19, v92, v143, v160, v186, v221] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrrl_ok : everyKey (rowOK 4 level4) level5lllrrl = true := by decide +kernel
def level5lllrrr : BinaryTree (List W) := (.node [v22, v118, v143, v160, v186, v251] (.node [v21, v92, v143, v160, v186, v221] (.node [v20, v92, v143, v160, v186, v248] .nil .nil) .nil) (.node [v23, v92, v143, v160, v186, v221] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrrr_ok : everyKey (rowOK 4 level4) level5lllrrr = true := by decide +kernel
def level5lllrr : BinaryTree (List W) := .node [v20, v92, v143, v160, v186, v221] level5lllrrl level5lllrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrr_ok : everyKey (rowOK 4 level4) level5lllrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lllrrl && everyKey (rowOK 4 level4) level5lllrrr) = true
  rw [level5lllrrl_ok, level5lllrrr_ok]
  decide +kernel
def level5lllr : BinaryTree (List W) := .node [v15, v28, v92, v143, v160, v186] level5lllrl level5lllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllr_ok : everyKey (rowOK 4 level4) level5lllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lllrl && everyKey (rowOK 4 level4) level5lllrr) = true
  rw [level5lllrl_ok, level5lllrr_ok]
  decide +kernel
def level5lll : BinaryTree (List W) := .node [v8, v92, v131, v160, v186, v221] level5llll level5lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lll_ok : everyKey (rowOK 4 level4) level5lll = true := by
  change (_ && everyKey (rowOK 4 level4) level5llll && everyKey (rowOK 4 level4) level5lllr) = true
  rw [level5llll_ok, level5lllr_ok]
  decide +kernel
def level5llrlll : BinaryTree (List W) := (.node [v26, v42, v92, v143, v160, v251] (.node [v25, v92, v143, v216, v221, v251] (.node [v25, v58, v92, v143, v186, v251] .nil .nil) .nil) (.node [v27, v92, v143, v160, v186, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrlll_ok : everyKey (rowOK 4 level4) level5llrlll = true := by decide +kernel
def level5llrllr : BinaryTree (List W) := (.node [v28, v92, v143, v160, v186, v248] (.node [v28, v92, v143, v160, v186, v221] (.node [v28, v58, v92, v143, v160, v186] .nil .nil) .nil) (.node [v28, v92, v143, v160, v186, v280] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrllr_ok : everyKey (rowOK 4 level4) level5llrllr = true := by decide +kernel
def level5llrll : BinaryTree (List W) := .node [v28, v55, v92, v143, v160, v221] level5llrlll level5llrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrll_ok : everyKey (rowOK 4 level4) level5llrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrlll && everyKey (rowOK 4 level4) level5llrllr) = true
  rw [level5llrlll_ok, level5llrllr_ok]
  decide +kernel
def level5llrlrl : BinaryTree (List W) := (.node [v31, v92, v143, v160, v186, v251] (.node [v30, v92, v143, v160, v186, v221] (.node [v29, v92, v143, v160, v186, v221] .nil .nil) .nil) (.node [v33, v92, v143, v160, v186, v221] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrlrl_ok : everyKey (rowOK 4 level4) level5llrlrl = true := by decide +kernel
def level5llrlrr : BinaryTree (List W) := (.node [v36, v92, v143, v160, v186, v221] (.node [v35, v92, v143, v160, v216, v221] (.node [v35, v92, v143, v160, v186, v221] .nil .nil) .nil) (.node [v37, v112, v143, v160, v221, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrlrr_ok : everyKey (rowOK 4 level4) level5llrlrr = true := by decide +kernel
def level5llrlr : BinaryTree (List W) := .node [v34, v160, v186, v221, v251, v283] level5llrlrl level5llrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrlr_ok : everyKey (rowOK 4 level4) level5llrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrlrl && everyKey (rowOK 4 level4) level5llrlrr) = true
  rw [level5llrlrl_ok, level5llrlrr_ok]
  decide +kernel
def level5llrl : BinaryTree (List W) := .node [v28, v92, v143, v160, v216, v221] level5llrll level5llrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrl_ok : everyKey (rowOK 4 level4) level5llrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrll && everyKey (rowOK 4 level4) level5llrlr) = true
  rw [level5llrll_ok, level5llrlr_ok]
  decide +kernel
def level5llrrll : BinaryTree (List W) := (.node [v40, v92, v143, v186, v248, v251] (.node [v40, v55, v92, v143, v221, v251] (.node [v39, v73, v92, v160, v221, v251] .nil .nil) .nil) (.node [v41, v92, v143, v186, v221, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrll_ok : everyKey (rowOK 4 level4) level5llrrll = true := by decide +kernel
def level5llrrlr : BinaryTree (List W) := (.node [v44, v92, v143, v160, v186, v221] (.node [v44, v58, v92, v143, v160, v186] (.node [v44, v55, v92, v143, v160, v221] .nil .nil) .nil) (.node [v44, v92, v143, v160, v186, v248] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrlr_ok : everyKey (rowOK 4 level4) level5llrrlr = true := by decide +kernel
def level5llrrl : BinaryTree (List W) := .node [v43, v92, v143, v160, v221, v251] level5llrrll level5llrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrl_ok : everyKey (rowOK 4 level4) level5llrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrrll && everyKey (rowOK 4 level4) level5llrrlr) = true
  rw [level5llrrll_ok, level5llrrlr_ok]
  decide +kernel
def level5llrrrl : BinaryTree (List W) := (.node [v46, v92, v143, v160, v186, v221] (.node [v45, v92, v143, v160, v186, v221] (.node [v44, v92, v143, v160, v221, v278] .nil .nil) .nil) (.node [v47, v92, v143, v160, v221, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrrl_ok : everyKey (rowOK 4 level4) level5llrrrl = true := by decide +kernel
def level5llrrrr : BinaryTree (List W) := (.node [v52, v104, v143, v186, v221, v251] (.node [v51, v92, v143, v160, v186, v221] .nil .nil) (.node [v53, v92, v143, v160, v186, v221] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrrr_ok : everyKey (rowOK 4 level4) level5llrrrr = true := by decide +kernel
def level5llrrr : BinaryTree (List W) := .node [v50, v92, v143, v160, v186, v221] level5llrrrl level5llrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrr_ok : everyKey (rowOK 4 level4) level5llrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrrrl && everyKey (rowOK 4 level4) level5llrrrr) = true
  rw [level5llrrrl_ok, level5llrrrr_ok]
  decide +kernel
def level5llrr : BinaryTree (List W) := .node [v44, v92, v143, v160, v216, v221] level5llrrl level5llrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrr_ok : everyKey (rowOK 4 level4) level5llrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrrl && everyKey (rowOK 4 level4) level5llrrr) = true
  rw [level5llrrl_ok, level5llrrr_ok]
  decide +kernel
def level5llr : BinaryTree (List W) := .node [v38, v92, v143, v160, v186, v221] level5llrl level5llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llr_ok : everyKey (rowOK 4 level4) level5llr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrl && everyKey (rowOK 4 level4) level5llrr) = true
  rw [level5llrl_ok, level5llrr_ok]
  decide +kernel
def level5ll : BinaryTree (List W) := .node [v24, v76, v92, v160, v186, v251] level5lll level5llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5ll_ok : everyKey (rowOK 4 level4) level5ll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lll && everyKey (rowOK 4 level4) level5llr) = true
  rw [level5lll_ok, level5llr_ok]
  decide +kernel
def level5lrllll : BinaryTree (List W) := (.node [v55, v58, v92, v143, v160, v251] (.node [v54, v92, v143, v216, v221, v251] (.node [v54, v92, v143, v186, v248, v251] .nil .nil) .nil) (.node [v55, v60, v92, v143, v160, v221] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrllll_ok : everyKey (rowOK 4 level4) level5lrllll = true := by decide +kernel
def level5lrlllr : BinaryTree (List W) := (.node [v55, v92, v143, v160, v221, v251] (.node [v55, v92, v143, v160, v166, v221] (.node [v55, v92, v131, v143, v160, v221] .nil .nil) .nil) (.node [v55, v92, v143, v160, v221, v256] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlllr_ok : everyKey (rowOK 4 level4) level5lrlllr = true := by decide +kernel
def level5lrlll : BinaryTree (List W) := .node [v55, v85, v92, v143, v160, v221] level5lrllll level5lrlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlll_ok : everyKey (rowOK 4 level4) level5lrlll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrllll && everyKey (rowOK 4 level4) level5lrlllr) = true
  rw [level5lrllll_ok, level5lrlllr_ok]
  decide +kernel
def level5lrllrl : BinaryTree (List W) := (.node [v55, v92, v143, v160, v248, v251] (.node [v55, v92, v143, v160, v221, v280] (.node [v55, v92, v143, v160, v221, v278] .nil .nil) .nil) (.node [v55, v92, v143, v216, v221, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrllrl_ok : everyKey (rowOK 4 level4) level5lrllrl = true := by decide +kernel
def level5lrllrr : BinaryTree (List W) := (.node [v58, v85, v92, v143, v160, v186] (.node [v58, v60, v92, v143, v160, v186] (.node [v57, v92, v143, v160, v221, v251] .nil .nil) .nil) (.node [v58, v92, v131, v143, v160, v186] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrllrr_ok : everyKey (rowOK 4 level4) level5lrllrr = true := by decide +kernel
def level5lrllr : BinaryTree (List W) := .node [v56, v92, v143, v160, v221, v251] level5lrllrl level5lrllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrllr_ok : everyKey (rowOK 4 level4) level5lrllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrllrl && everyKey (rowOK 4 level4) level5lrllrr) = true
  rw [level5lrllrl_ok, level5lrllrr_ok]
  decide +kernel
def level5lrll : BinaryTree (List W) := .node [v55, v92, v143, v160, v221, v276] level5lrlll level5lrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrll_ok : everyKey (rowOK 4 level4) level5lrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrlll && everyKey (rowOK 4 level4) level5lrllr) = true
  rw [level5lrlll_ok, level5lrllr_ok]
  decide +kernel
def level5lrlrll : BinaryTree (List W) := (.node [v58, v92, v143, v160, v186, v276] (.node [v58, v92, v143, v160, v186, v257] (.node [v58, v92, v143, v160, v186, v251] .nil .nil) .nil) (.node [v58, v92, v143, v160, v186, v278] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrll_ok : everyKey (rowOK 4 level4) level5lrlrll = true := by decide +kernel
def level5lrlrlr : BinaryTree (List W) := (.node [v59, v92, v143, v160, v186, v251] (.node [v58, v92, v143, v186, v248, v251] (.node [v58, v92, v143, v160, v216, v251] .nil .nil) .nil) (.node [v60, v92, v143, v160, v186, v221] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrlr_ok : everyKey (rowOK 4 level4) level5lrlrlr = true := by decide +kernel
def level5lrlrl : BinaryTree (List W) := .node [v58, v92, v143, v160, v186, v280] level5lrlrll level5lrlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrl_ok : everyKey (rowOK 4 level4) level5lrlrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrlrll && everyKey (rowOK 4 level4) level5lrlrlr) = true
  rw [level5lrlrll_ok, level5lrlrlr_ok]
  decide +kernel
def level5lrlrrl : BinaryTree (List W) := (.node [v61, v92, v143, v160, v186, v221] (.node [v60, v92, v143, v186, v221, v276] (.node [v60, v92, v143, v160, v216, v221] .nil .nil) .nil) (.node [v62, v92, v143, v160, v186, v221] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrrl_ok : everyKey (rowOK 4 level4) level5lrlrrl = true := by decide +kernel
def level5lrlrrr : BinaryTree (List W) := (.node [v68, v92, v143, v160, v186, v251] (.node [v66, v92, v143, v160, v186, v221] .nil .nil) (.node [v69, v92, v143, v160, v186, v221] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrrr_ok : everyKey (rowOK 4 level4) level5lrlrrr = true := by decide +kernel
def level5lrlrr : BinaryTree (List W) := .node [v63, v92, v143, v186, v221, v251] level5lrlrrl level5lrlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrr_ok : everyKey (rowOK 4 level4) level5lrlrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrlrrl && everyKey (rowOK 4 level4) level5lrlrrr) = true
  rw [level5lrlrrl_ok, level5lrlrrr_ok]
  decide +kernel
def level5lrlr : BinaryTree (List W) := .node [v60, v92, v143, v160, v186, v248] level5lrlrl level5lrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlr_ok : everyKey (rowOK 4 level4) level5lrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrlrl && everyKey (rowOK 4 level4) level5lrlrr) = true
  rw [level5lrlrl_ok, level5lrlrr_ok]
  decide +kernel
def level5lrl : BinaryTree (List W) := .node [v58, v92, v143, v160, v163, v186] level5lrll level5lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrl_ok : everyKey (rowOK 4 level4) level5lrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrll && everyKey (rowOK 4 level4) level5lrlr) = true
  rw [level5lrll_ok, level5lrlr_ok]
  decide +kernel
def level5lrrlll : BinaryTree (List W) := (.node [v75, v92, v143, v160, v186, v221] (.node [v74, v143, v160, v205, v221, v251] (.node [v72, v92, v143, v160, v186, v221] .nil .nil) .nil) (.node [v78, v122, v160, v186, v221, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrlll_ok : everyKey (rowOK 4 level4) level5lrrlll = true := by decide +kernel
def level5lrrllr : BinaryTree (List W) := (.node [v84, v92, v143, v160, v186, v221] (.node [v83, v143, v160, v186, v238, v251] (.node [v82, v92, v143, v160, v186, v221] .nil .nil) .nil) (.node [v85, v92, v143, v160, v186, v221] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrllr_ok : everyKey (rowOK 4 level4) level5lrrllr = true := by decide +kernel
def level5lrrll : BinaryTree (List W) := .node [v79, v92, v143, v160, v186, v221] level5lrrlll level5lrrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrll_ok : everyKey (rowOK 4 level4) level5lrrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrlll && everyKey (rowOK 4 level4) level5lrrllr) = true
  rw [level5lrrlll_ok, level5lrrllr_ok]
  decide +kernel
def level5lrrlrl : BinaryTree (List W) := (.node [v86, v92, v143, v160, v186, v221] (.node [v85, v143, v160, v186, v221, v265] (.node [v85, v92, v143, v160, v216, v221] .nil .nil) .nil) (.node [v87, v92, v143, v160, v186, v221] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrlrl_ok : everyKey (rowOK 4 level4) level5lrrlrl = true := by decide +kernel
def level5lrrlrr : BinaryTree (List W) := (.node [v91, v143, v160, v186, v221, v251] (.node [v90, v92, v143, v160, v186, v221] (.node [v89, v92, v143, v160, v186, v221] .nil .nil) .nil) (.node [v92, v93, v143, v160, v186, v221] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrlrr_ok : everyKey (rowOK 4 level4) level5lrrlrr = true := by decide +kernel
def level5lrrlr : BinaryTree (List W) := .node [v88, v92, v143, v160, v186, v221] level5lrrlrl level5lrrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrlr_ok : everyKey (rowOK 4 level4) level5lrrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrlrl && everyKey (rowOK 4 level4) level5lrrlrr) = true
  rw [level5lrrlrl_ok, level5lrrlrr_ok]
  decide +kernel
def level5lrrl : BinaryTree (List W) := .node [v85, v92, v143, v160, v186, v248] level5lrrll level5lrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrl_ok : everyKey (rowOK 4 level4) level5lrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrll && everyKey (rowOK 4 level4) level5lrrlr) = true
  rw [level5lrrll_ok, level5lrrlr_ok]
  decide +kernel
def level5lrrrll : BinaryTree (List W) := (.node [v92, v99, v143, v160, v221, v251] (.node [v92, v98, v143, v160, v221, v251] (.node [v92, v96, v143, v160, v186, v221] .nil .nil) .nil) (.node [v92, v100, v143, v160, v186, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrll_ok : everyKey (rowOK 4 level4) level5lrrrll = true := by decide +kernel
def level5lrrrlr : BinaryTree (List W) := (.node [v92, v104, v143, v186, v248, v251] (.node [v92, v103, v143, v160, v186, v221] (.node [v92, v102, v143, v160, v186, v221] .nil .nil) .nil) (.node [v92, v104, v143, v216, v221, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrlr_ok : everyKey (rowOK 4 level4) level5lrrrlr = true := by decide +kernel
def level5lrrrl : BinaryTree (List W) := .node [v92, v101, v143, v160, v186, v251] level5lrrrll level5lrrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrl_ok : everyKey (rowOK 4 level4) level5lrrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrrll && everyKey (rowOK 4 level4) level5lrrrlr) = true
  rw [level5lrrrll_ok, level5lrrrlr_ok]
  decide +kernel
def level5lrrrrl : BinaryTree (List W) := (.node [v92, v106, v143, v160, v186, v221] (.node [v92, v105, v179, v186, v221, v251] (.node [v92, v105, v143, v216, v221, v251] .nil .nil) .nil) (.node [v92, v107, v143, v186, v221, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrrl_ok : everyKey (rowOK 4 level4) level5lrrrrl = true := by decide +kernel
def level5lrrrrr : BinaryTree (List W) := (.node [v92, v110, v143, v186, v221, v251] (.node [v92, v109, v143, v186, v221, v251] .nil .nil) (.node [v92, v113, v160, v211, v221, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrrr_ok : everyKey (rowOK 4 level4) level5lrrrrr = true := by decide +kernel
def level5lrrrr : BinaryTree (List W) := .node [v92, v108, v143, v186, v221, v251] level5lrrrrl level5lrrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrr_ok : everyKey (rowOK 4 level4) level5lrrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrrrl && everyKey (rowOK 4 level4) level5lrrrrr) = true
  rw [level5lrrrrl_ok, level5lrrrrr_ok]
  decide +kernel
def level5lrrr : BinaryTree (List W) := .node [v92, v105, v143, v186, v248, v251] level5lrrrl level5lrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrr_ok : everyKey (rowOK 4 level4) level5lrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrrl && everyKey (rowOK 4 level4) level5lrrrr) = true
  rw [level5lrrrl_ok, level5lrrrr_ok]
  decide +kernel
def level5lrr : BinaryTree (List W) := .node [v92, v95, v143, v160, v186, v221] level5lrrl level5lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrr_ok : everyKey (rowOK 4 level4) level5lrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrl && everyKey (rowOK 4 level4) level5lrrr) = true
  rw [level5lrrl_ok, level5lrrr_ok]
  decide +kernel
def level5lr : BinaryTree (List W) := .node [v71, v143, v175, v186, v221, v251] level5lrl level5lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lr_ok : everyKey (rowOK 4 level4) level5lr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrl && everyKey (rowOK 4 level4) level5lrr) = true
  rw [level5lrl_ok, level5lrr_ok]
  decide +kernel
def level5l : BinaryTree (List W) := .node [v54, v70, v92, v186, v221, v251] level5ll level5lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5l_ok : everyKey (rowOK 4 level4) level5l = true := by
  change (_ && everyKey (rowOK 4 level4) level5ll && everyKey (rowOK 4 level4) level5lr) = true
  rw [level5ll_ok, level5lr_ok]
  decide +kernel
def level5rlllll : BinaryTree (List W) := (.node [v92, v122, v131, v160, v186, v221] (.node [v92, v116, v143, v160, v221, v251] (.node [v92, v115, v143, v160, v221, v251] .nil .nil) .nil) (.node [v92, v123, v143, v160, v186, v221] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlllll_ok : everyKey (rowOK 4 level4) level5rlllll = true := by decide +kernel
def level5rllllr : BinaryTree (List W) := (.node [v92, v128, v143, v160, v186, v221] (.node [v92, v127, v160, v186, v244, v251] (.node [v92, v126, v143, v160, v186, v221] .nil .nil) .nil) (.node [v92, v130, v160, v186, v221, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllllr_ok : everyKey (rowOK 4 level4) level5rllllr = true := by decide +kernel
def level5rllll : BinaryTree (List W) := .node [v92, v125, v160, v186, v221, v251] level5rlllll level5rllllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllll_ok : everyKey (rowOK 4 level4) level5rllll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlllll && everyKey (rowOK 4 level4) level5rllllr) = true
  rw [level5rlllll_ok, level5rllllr_ok]
  decide +kernel
def level5rlllrl : BinaryTree (List W) := (.node [v92, v131, v160, v186, v221, v273] (.node [v92, v131, v143, v160, v216, v221] (.node [v92, v131, v143, v160, v186, v248] .nil .nil) .nil) (.node [v92, v131, v160, v186, v221, v283] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlllrl_ok : everyKey (rowOK 4 level4) level5rlllrl = true := by decide +kernel
def level5rlllrr : BinaryTree (List W) := (.node [v92, v135, v143, v160, v186, v221] (.node [v92, v134, v143, v160, v186, v221] (.node [v92, v133, v143, v160, v186, v221] .nil .nil) .nil) (.node [v92, v135, v160, v186, v221] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlllrr_ok : everyKey (rowOK 4 level4) level5rlllrr = true := by decide +kernel
def level5rlllr : BinaryTree (List W) := .node [v92, v132, v143, v160, v186, v221] level5rlllrl level5rlllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlllr_ok : everyKey (rowOK 4 level4) level5rlllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlllrl && everyKey (rowOK 4 level4) level5rlllrr) = true
  rw [level5rlllrl_ok, level5rlllrr_ok]
  decide +kernel
def level5rlll : BinaryTree (List W) := .node [v92, v131, v143, v160, v186, v221] level5rllll level5rlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlll_ok : everyKey (rowOK 4 level4) level5rlll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rllll && everyKey (rowOK 4 level4) level5rlllr) = true
  rw [level5rllll_ok, level5rlllr_ok]
  decide +kernel
def level5rllrll : BinaryTree (List W) := (.node [v92, v143, v145, v160, v186, v221] (.node [v92, v142, v160, v186, v221, v251] (.node [v92, v139, v143, v160, v186, v221] .nil .nil) .nil) (.node [v92, v143, v146, v160, v186, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrll_ok : everyKey (rowOK 4 level4) level5rllrll = true := by decide +kernel
def level5rllrlr : BinaryTree (List W) := (.node [v92, v143, v150, v160, v221, v251] (.node [v92, v143, v149, v160, v186, v221] (.node [v92, v143, v148, v160, v186, v221] .nil .nil) .nil) (.node [v92, v143, v151, v160, v221, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrlr_ok : everyKey (rowOK 4 level4) level5rllrlr = true := by decide +kernel
def level5rllrl : BinaryTree (List W) := .node [v92, v143, v147, v160, v186, v251] level5rllrll level5rllrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrl_ok : everyKey (rowOK 4 level4) level5rllrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rllrll && everyKey (rowOK 4 level4) level5rllrlr) = true
  rw [level5rllrll_ok, level5rllrlr_ok]
  decide +kernel
def level5rllrrl : BinaryTree (List W) := (.node [v92, v143, v155, v160, v186, v221] (.node [v92, v143, v154, v160, v186, v221] (.node [v92, v143, v153, v160, v186, v251] .nil .nil) .nil) (.node [v92, v143, v156, v216, v221, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrrl_ok : everyKey (rowOK 4 level4) level5rllrrl = true := by decide +kernel
def level5rllrrr : BinaryTree (List W) := (.node [v92, v143, v159, v186, v221, v251] (.node [v92, v143, v158, v186, v221, v276] .nil .nil) (.node [v92, v143, v160, v161, v186, v221] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrrr_ok : everyKey (rowOK 4 level4) level5rllrrr = true := by decide +kernel
def level5rllrr : BinaryTree (List W) := .node [v92, v143, v157, v186, v248, v251] level5rllrrl level5rllrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrr_ok : everyKey (rowOK 4 level4) level5rllrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rllrrl && everyKey (rowOK 4 level4) level5rllrrr) = true
  rw [level5rllrrl_ok, level5rllrrr_ok]
  decide +kernel
def level5rllr : BinaryTree (List W) := .node [v92, v143, v152, v160, v186, v251] level5rllrl level5rllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllr_ok : everyKey (rowOK 4 level4) level5rllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rllrl && everyKey (rowOK 4 level4) level5rllrr) = true
  rw [level5rllrl_ok, level5rllrr_ok]
  decide +kernel
def level5rll : BinaryTree (List W) := .node [v92, v135, v160, v186, v221, v251] level5rlll level5rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rll_ok : everyKey (rowOK 4 level4) level5rll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlll && everyKey (rowOK 4 level4) level5rllr) = true
  rw [level5rlll_ok, level5rllr_ok]
  decide +kernel
def level5rlrlll : BinaryTree (List W) := (.node [v92, v143, v160, v166, v186, v221] (.node [v92, v143, v160, v164, v186, v221] (.node [v92, v143, v160, v163, v186, v221] .nil .nil) .nil) (.node [v92, v143, v160, v167, v186, v221] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrlll_ok : everyKey (rowOK 4 level4) level5rlrlll = true := by decide +kernel
def level5rlrllr : BinaryTree (List W) := (.node [v92, v143, v160, v177, v186, v221] (.node [v92, v143, v160, v176, v186, v221] (.node [v92, v143, v160, v173, v186, v221] .nil .nil) .nil) (.node [v92, v143, v160, v180, v249, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrllr_ok : everyKey (rowOK 4 level4) level5rlrllr = true := by decide +kernel
def level5rlrll : BinaryTree (List W) := .node [v92, v143, v160, v172, v186, v221] level5rlrlll level5rlrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrll_ok : everyKey (rowOK 4 level4) level5rlrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrlll && everyKey (rowOK 4 level4) level5rlrllr) = true
  rw [level5rlrlll_ok, level5rlrllr_ok]
  decide +kernel
def level5rlrlrl : BinaryTree (List W) := (.node [v92, v143, v160, v184, v221, v251] (.node [v92, v143, v160, v183, v221, v278] (.node [v92, v143, v160, v182, v221, v251] .nil .nil) .nil) (.node [v92, v143, v160, v185, v221, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrlrl_ok : everyKey (rowOK 4 level4) level5rlrlrl = true := by decide +kernel
def level5rlrlrr : BinaryTree (List W) := (.node [v92, v143, v160, v186, v193, v221] (.node [v92, v143, v160, v186, v192, v221] (.node [v92, v143, v160, v186, v188, v221] .nil .nil) .nil) (.node [v92, v143, v160, v186, v195, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrlrr_ok : everyKey (rowOK 4 level4) level5rlrlrr = true := by decide +kernel
def level5rlrlr : BinaryTree (List W) := .node [v92, v143, v160, v186, v187, v221] level5rlrlrl level5rlrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrlr_ok : everyKey (rowOK 4 level4) level5rlrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrlrl && everyKey (rowOK 4 level4) level5rlrlrr) = true
  rw [level5rlrlrl_ok, level5rlrlrr_ok]
  decide +kernel
def level5rlrl : BinaryTree (List W) := .node [v92, v143, v160, v181, v221, v251] level5rlrll level5rlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrl_ok : everyKey (rowOK 4 level4) level5rlrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrll && everyKey (rowOK 4 level4) level5rlrlr) = true
  rw [level5rlrll_ok, level5rlrlr_ok]
  decide +kernel
def level5rlrrll : BinaryTree (List W) := (.node [v92, v143, v160, v186, v203, v221] (.node [v92, v143, v160, v186, v201, v251] (.node [v92, v143, v160, v186, v197, v221] .nil .nil) .nil) (.node [v92, v143, v160, v186, v204, v221] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrll_ok : everyKey (rowOK 4 level4) level5rlrrll = true := by decide +kernel
def level5rlrrlr : BinaryTree (List W) := (.node [v92, v143, v160, v186, v219, v251] (.node [v92, v143, v160, v186, v218, v280] (.node [v92, v143, v160, v186, v209, v221] .nil .nil) .nil) (.node [v92, v143, v160, v186, v220, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrlr_ok : everyKey (rowOK 4 level4) level5rlrrlr = true := by decide +kernel
def level5rlrrl : BinaryTree (List W) := .node [v92, v143, v160, v186, v208, v221] level5rlrrll level5rlrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrl_ok : everyKey (rowOK 4 level4) level5rlrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrrll && everyKey (rowOK 4 level4) level5rlrrlr) = true
  rw [level5rlrrll_ok, level5rlrrlr_ok]
  decide +kernel
def level5rlrrrl : BinaryTree (List W) := (.node [v92, v143, v160, v186, v221, v228] (.node [v92, v143, v160, v186, v221, v227] (.node [v92, v143, v160, v186, v221, v223] .nil .nil) .nil) (.node [v92, v143, v160, v186, v221, v230] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrrl_ok : everyKey (rowOK 4 level4) level5rlrrrl = true := by decide +kernel
def level5rlrrrr : BinaryTree (List W) := (.node [v92, v143, v160, v186, v221, v237] (.node [v92, v143, v160, v186, v221, v236] .nil .nil) (.node [v92, v143, v160, v186, v221, v241] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrrr_ok : everyKey (rowOK 4 level4) level5rlrrrr = true := by decide +kernel
def level5rlrrr : BinaryTree (List W) := .node [v92, v143, v160, v186, v221, v231] level5rlrrrl level5rlrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrr_ok : everyKey (rowOK 4 level4) level5rlrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrrrl && everyKey (rowOK 4 level4) level5rlrrrr) = true
  rw [level5rlrrrl_ok, level5rlrrrr_ok]
  decide +kernel
def level5rlrr : BinaryTree (List W) := .node [v92, v143, v160, v186, v221, v222] level5rlrrl level5rlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrr_ok : everyKey (rowOK 4 level4) level5rlrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrrl && everyKey (rowOK 4 level4) level5rlrrr) = true
  rw [level5rlrrl_ok, level5rlrrr_ok]
  decide +kernel
def level5rlr : BinaryTree (List W) := .node [v92, v143, v160, v186, v196, v221] level5rlrl level5rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlr_ok : everyKey (rowOK 4 level4) level5rlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrl && everyKey (rowOK 4 level4) level5rlrr) = true
  rw [level5rlrl_ok, level5rlrr_ok]
  decide +kernel
def level5rl : BinaryTree (List W) := .node [v92, v143, v160, v162, v186, v221] level5rll level5rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rl_ok : everyKey (rowOK 4 level4) level5rl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rll && everyKey (rowOK 4 level4) level5rlr) = true
  rw [level5rll_ok, level5rlr_ok]
  decide +kernel
def level5rrllll : BinaryTree (List W) := (.node [v92, v143, v160, v186, v221, v252] (.node [v92, v143, v160, v186, v221, v251] (.node [v92, v143, v160, v186, v221, v250] .nil .nil) .nil) (.node [v92, v143, v160, v186, v221, v253] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrllll_ok : everyKey (rowOK 4 level4) level5rrllll = true := by decide +kernel
def level5rrlllr : BinaryTree (List W) := (.node [v92, v143, v160, v186, v221, v257] (.node [v92, v143, v160, v186, v221, v256] (.node [v92, v143, v160, v186, v221, v255] .nil .nil) .nil) (.node [v92, v143, v160, v186, v221, v258] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlllr_ok : everyKey (rowOK 4 level4) level5rrlllr = true := by decide +kernel
def level5rrlll : BinaryTree (List W) := .node [v92, v143, v160, v186, v221, v254] level5rrllll level5rrlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlll_ok : everyKey (rowOK 4 level4) level5rrlll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrllll && everyKey (rowOK 4 level4) level5rrlllr) = true
  rw [level5rrllll_ok, level5rrlllr_ok]
  decide +kernel
def level5rrllrl : BinaryTree (List W) := (.node [v92, v143, v160, v186, v221, v262] (.node [v92, v143, v160, v186, v221, v261] (.node [v92, v143, v160, v186, v221, v260] .nil .nil) .nil) (.node [v92, v143, v160, v186, v221, v263] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrllrl_ok : everyKey (rowOK 4 level4) level5rrllrl = true := by decide +kernel
def level5rrllrr : BinaryTree (List W) := (.node [v92, v143, v160, v186, v221, v268] (.node [v92, v143, v160, v186, v221, v267] (.node [v92, v143, v160, v186, v221, v266] .nil .nil) .nil) (.node [v92, v143, v160, v186, v221, v269] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrllrr_ok : everyKey (rowOK 4 level4) level5rrllrr = true := by decide +kernel
def level5rrllr : BinaryTree (List W) := .node [v92, v143, v160, v186, v221, v264] level5rrllrl level5rrllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrllr_ok : everyKey (rowOK 4 level4) level5rrllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrllrl && everyKey (rowOK 4 level4) level5rrllrr) = true
  rw [level5rrllrl_ok, level5rrllrr_ok]
  decide +kernel
def level5rrll : BinaryTree (List W) := .node [v92, v143, v160, v186, v221, v259] level5rrlll level5rrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrll_ok : everyKey (rowOK 4 level4) level5rrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrlll && everyKey (rowOK 4 level4) level5rrllr) = true
  rw [level5rrlll_ok, level5rrllr_ok]
  decide +kernel
def level5rrlrll : BinaryTree (List W) := (.node [v92, v143, v160, v186, v221, v274] (.node [v92, v143, v160, v186, v221, v272] (.node [v92, v143, v160, v186, v221, v271] .nil .nil) .nil) (.node [v92, v143, v160, v186, v221, v275] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrll_ok : everyKey (rowOK 4 level4) level5rrlrll = true := by decide +kernel
def level5rrlrlr : BinaryTree (List W) := (.node [v92, v143, v160, v186, v221, v279] (.node [v92, v143, v160, v186, v221, v278] (.node [v92, v143, v160, v186, v221, v277] .nil .nil) .nil) (.node [v92, v143, v160, v186, v221, v280] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrlr_ok : everyKey (rowOK 4 level4) level5rrlrlr = true := by decide +kernel
def level5rrlrl : BinaryTree (List W) := .node [v92, v143, v160, v186, v221, v276] level5rrlrll level5rrlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrl_ok : everyKey (rowOK 4 level4) level5rrlrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrlrll && everyKey (rowOK 4 level4) level5rrlrlr) = true
  rw [level5rrlrll_ok, level5rrlrlr_ok]
  decide +kernel
def level5rrlrrl : BinaryTree (List W) := (.node [v92, v143, v160, v186, v226, v251] (.node [v92, v143, v160, v186, v224, v251] (.node [v92, v143, v160, v186, v221, v282] .nil .nil) .nil) (.node [v92, v143, v160, v186, v232, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrrl_ok : everyKey (rowOK 4 level4) level5rrlrrl = true := by decide +kernel
def level5rrlrrr : BinaryTree (List W) := (.node [v92, v143, v160, v186, v235, v251] (.node [v92, v143, v160, v186, v234, v251] .nil .nil) (.node [v92, v143, v160, v186, v239, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrrr_ok : everyKey (rowOK 4 level4) level5rrlrrr = true := by decide +kernel
def level5rrlrr : BinaryTree (List W) := .node [v92, v143, v160, v186, v233, v251] level5rrlrrl level5rrlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrr_ok : everyKey (rowOK 4 level4) level5rrlrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrlrrl && everyKey (rowOK 4 level4) level5rrlrrr) = true
  rw [level5rrlrrl_ok, level5rrlrrr_ok]
  decide +kernel
def level5rrlr : BinaryTree (List W) := .node [v92, v143, v160, v186, v221, v281] level5rrlrl level5rrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlr_ok : everyKey (rowOK 4 level4) level5rrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrlrl && everyKey (rowOK 4 level4) level5rrlrr) = true
  rw [level5rrlrl_ok, level5rrlrr_ok]
  decide +kernel
def level5rrl : BinaryTree (List W) := .node [v92, v143, v160, v186, v221, v270] level5rrll level5rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrl_ok : everyKey (rowOK 4 level4) level5rrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrll && everyKey (rowOK 4 level4) level5rrlr) = true
  rw [level5rrll_ok, level5rrlr_ok]
  decide +kernel
def level5rrrlll : BinaryTree (List W) := (.node [v92, v143, v160, v186, v248, v251] (.node [v92, v143, v160, v186, v246, v251] (.node [v92, v143, v160, v186, v245, v251] .nil .nil) .nil) (.node [v92, v143, v160, v186, v248, v276] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrlll_ok : everyKey (rowOK 4 level4) level5rrrlll = true := by decide +kernel
def level5rrrllr : BinaryTree (List W) := (.node [v92, v143, v160, v189, v221, v251] (.node [v92, v143, v160, v186, v248, v281] (.node [v92, v143, v160, v186, v248, v280] .nil .nil) .nil) (.node [v92, v143, v160, v191, v221, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrllr_ok : everyKey (rowOK 4 level4) level5rrrllr = true := by decide +kernel
def level5rrrll : BinaryTree (List W) := .node [v92, v143, v160, v186, v248, v278] level5rrrlll level5rrrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrll_ok : everyKey (rowOK 4 level4) level5rrrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrlll && everyKey (rowOK 4 level4) level5rrrllr) = true
  rw [level5rrrlll_ok, level5rrrllr_ok]
  decide +kernel
def level5rrrlrl : BinaryTree (List W) := (.node [v92, v143, v160, v202, v221, v251] (.node [v92, v143, v160, v200, v221, v251] (.node [v92, v143, v160, v199, v221, v251] .nil .nil) .nil) (.node [v92, v143, v160, v206, v221, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrlrl_ok : everyKey (rowOK 4 level4) level5rrrlrl = true := by decide +kernel
def level5rrrlrr : BinaryTree (List W) := (.node [v92, v143, v160, v216, v221, v251] (.node [v92, v143, v160, v214, v221, v251] (.node [v92, v143, v160, v213, v221, v251] .nil .nil) .nil) (.node [v92, v143, v160, v216, v221, v276] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrlrr_ok : everyKey (rowOK 4 level4) level5rrrlrr = true := by decide +kernel
def level5rrrlr : BinaryTree (List W) := .node [v92, v143, v160, v207, v221, v251] level5rrrlrl level5rrrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrlr_ok : everyKey (rowOK 4 level4) level5rrrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrlrl && everyKey (rowOK 4 level4) level5rrrlrr) = true
  rw [level5rrrlrl_ok, level5rrrlrr_ok]
  decide +kernel
def level5rrrl : BinaryTree (List W) := .node [v92, v143, v160, v198, v221, v251] level5rrrll level5rrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrl_ok : everyKey (rowOK 4 level4) level5rrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrll && everyKey (rowOK 4 level4) level5rrrlr) = true
  rw [level5rrrll_ok, level5rrrlr_ok]
  decide +kernel
def level5rrrrll : BinaryTree (List W) := (.node [v92, v143, v160, v216, v248, v251] (.node [v92, v143, v160, v216, v221, v280] (.node [v92, v143, v160, v216, v221, v279] .nil .nil) .nil) (.node [v92, v143, v168, v186, v221, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrll_ok : everyKey (rowOK 4 level4) level5rrrrll = true := by decide +kernel
def level5rrrrlr : BinaryTree (List W) := (.node [v92, v143, v175, v186, v248, v251] (.node [v92, v143, v171, v186, v221, v251] (.node [v92, v143, v170, v186, v221, v251] .nil .nil) .nil) (.node [v92, v143, v175, v216, v221, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrlr_ok : everyKey (rowOK 4 level4) level5rrrrlr = true := by decide +kernel
def level5rrrrl : BinaryTree (List W) := .node [v92, v143, v169, v186, v221, v251] level5rrrrll level5rrrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrl_ok : everyKey (rowOK 4 level4) level5rrrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrrll && everyKey (rowOK 4 level4) level5rrrrlr) = true
  rw [level5rrrrll_ok, level5rrrrlr_ok]
  decide +kernel
def level5rrrrrl : BinaryTree (List W) := (.node [v92, v143, v216, v248, v251] (.node [v92, v143, v216, v221, v248, v251] (.node [v92, v143, v186, v216, v248, v251] .nil .nil) .nil) (.node [v92, v144, v160, v186, v221, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrrl_ok : everyKey (rowOK 4 level4) level5rrrrrl = true := by decide +kernel
def level5rrrrrr : BinaryTree (List W) := (.node [v92, v160, v186, v221, v243, v251] (.node [v92, v160, v186, v210, v221, v251] .nil .nil) (.node [v143, v160, v174, v186, v221, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrrr_ok : everyKey (rowOK 4 level4) level5rrrrrr = true := by decide +kernel
def level5rrrrr : BinaryTree (List W) := .node [v92, v160, v178, v186, v221, v251] level5rrrrrl level5rrrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrr_ok : everyKey (rowOK 4 level4) level5rrrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrrrl && everyKey (rowOK 4 level4) level5rrrrrr) = true
  rw [level5rrrrrl_ok, level5rrrrrr_ok]
  decide +kernel
def level5rrrr : BinaryTree (List W) := .node [v92, v143, v186, v212, v221, v251] level5rrrrl level5rrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrr_ok : everyKey (rowOK 4 level4) level5rrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrrl && everyKey (rowOK 4 level4) level5rrrrr) = true
  rw [level5rrrrl_ok, level5rrrrr_ok]
  decide +kernel
def level5rrr : BinaryTree (List W) := .node [v92, v143, v160, v216, v221, v278] level5rrrl level5rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrr_ok : everyKey (rowOK 4 level4) level5rrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrl && everyKey (rowOK 4 level4) level5rrrr) = true
  rw [level5rrrl_ok, level5rrrr_ok]
  decide +kernel
def level5rr : BinaryTree (List W) := .node [v92, v143, v160, v186, v240, v251] level5rrl level5rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rr_ok : everyKey (rowOK 4 level4) level5rr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrl && everyKey (rowOK 4 level4) level5rrr) = true
  rw [level5rrl_ok, level5rrr_ok]
  decide +kernel
def level5r : BinaryTree (List W) := .node [v92, v143, v160, v186, v221, v242] level5rl level5rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5r_ok : everyKey (rowOK 4 level4) level5r = true := by
  change (_ && everyKey (rowOK 4 level4) level5rl && everyKey (rowOK 4 level4) level5rr) = true
  rw [level5rl_ok, level5rr_ok]
  decide +kernel
def level5 : BinaryTree (List W) := .node [v92, v114, v143, v160, v186, v221] level5l level5r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5_ok : everyKey (rowOK 4 level4) level5 = true := by
  change (_ && everyKey (rowOK 4 level4) level5l && everyKey (rowOK 4 level4) level5r) = true
  rw [level5l_ok, level5r_ok]
  decide +kernel
theorem closed5 : Closed 5 level5 := closed_next 4 (by decide) level5 level4 closed4 level5_ok
def level6llll : BinaryTree (List W) := (.node [v8, v92, v143, v160, v186, v221] (.node [v7, v92, v143, v160, v186, v221, v251] (.node [v7, v92, v143, v160, v186, v221] .nil .nil) .nil) (.node [v8, v92, v143, v160, v186, v221, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llll_ok : everyKey (rowOK 5 level5) level6llll = true := by decide +kernel
def level6lllr : BinaryTree (List W) := (.node [v22, v92, v143, v160, v186, v221, v251] (.node [v15, v92, v143, v160, v186, v221, v251] (.node [v12, v92, v143, v160, v186, v221, v251] .nil .nil) .nil) (.node [v24, v92, v143, v160, v186, v221, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllr_ok : everyKey (rowOK 5 level5) level6lllr = true := by decide +kernel
def level6lll : BinaryTree (List W) := .node [v9, v92, v143, v160, v186, v221, v251] level6llll level6lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lll_ok : everyKey (rowOK 5 level5) level6lll = true := by
  change (_ && everyKey (rowOK 5 level5) level6llll && everyKey (rowOK 5 level5) level6lllr) = true
  rw [level6llll_ok, level6lllr_ok]
  decide +kernel
def level6llrl : BinaryTree (List W) := (.node [v28, v92, v143, v160, v186, v221, v251] (.node [v28, v92, v143, v160, v186, v221] (.node [v26, v92, v143, v160, v186, v221, v251] .nil .nil) .nil) (.node [v34, v92, v143, v160, v186, v221, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrl_ok : everyKey (rowOK 5 level5) level6llrl = true := by decide +kernel
def level6llrr : BinaryTree (List W) := (.node [v40, v92, v143, v160, v186, v221, v251] (.node [v39, v92, v143, v160, v186, v221, v251] .nil .nil) (.node [v42, v92, v143, v160, v186, v221, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrr_ok : everyKey (rowOK 5 level5) level6llrr = true := by decide +kernel
def level6llr : BinaryTree (List W) := .node [v37, v92, v143, v160, v186, v221, v251] level6llrl level6llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llr_ok : everyKey (rowOK 5 level5) level6llr = true := by
  change (_ && everyKey (rowOK 5 level5) level6llrl && everyKey (rowOK 5 level5) level6llrr) = true
  rw [level6llrl_ok, level6llrr_ok]
  decide +kernel
def level6ll : BinaryTree (List W) := .node [v25, v92, v143, v160, v186, v221, v251] level6lll level6llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6ll_ok : everyKey (rowOK 5 level5) level6ll = true := by
  change (_ && everyKey (rowOK 5 level5) level6lll && everyKey (rowOK 5 level5) level6llr) = true
  rw [level6lll_ok, level6llr_ok]
  decide +kernel
def level6lrll : BinaryTree (List W) := (.node [v54, v92, v143, v160, v186, v221, v251] (.node [v52, v92, v143, v160, v186, v221, v251] (.node [v44, v92, v143, v160, v186, v221, v251] .nil .nil) .nil) (.node [v55, v92, v143, v160, v186, v221, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrll_ok : everyKey (rowOK 5 level5) level6lrll = true := by decide +kernel
def level6lrlr : BinaryTree (List W) := (.node [v60, v92, v143, v160, v186, v221] (.node [v58, v92, v143, v160, v186, v251] (.node [v58, v92, v143, v160, v186, v221, v251] .nil .nil) .nil) (.node [v60, v92, v143, v160, v186, v221, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlr_ok : everyKey (rowOK 5 level5) level6lrlr = true := by decide +kernel
def level6lrl : BinaryTree (List W) := .node [v55, v92, v143, v160, v221, v251] level6lrll level6lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrl_ok : everyKey (rowOK 5 level5) level6lrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrll && everyKey (rowOK 5 level5) level6lrlr) = true
  rw [level6lrll_ok, level6lrlr_ok]
  decide +kernel
def level6lrrl : BinaryTree (List W) := (.node [v74, v92, v143, v160, v186, v221, v251] (.node [v73, v92, v143, v160, v186, v221, v251] (.node [v71, v92, v143, v160, v186, v221, v251] .nil .nil) .nil) (.node [v76, v92, v143, v160, v186, v221, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrl_ok : everyKey (rowOK 5 level5) level6lrrl = true := by decide +kernel
def level6lrrr : BinaryTree (List W) := (.node [v83, v92, v143, v160, v186, v221, v251] (.node [v78, v92, v143, v160, v186, v221, v251] .nil .nil) (.node [v85, v92, v143, v160, v186, v221] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrr_ok : everyKey (rowOK 5 level5) level6lrrr = true := by decide +kernel
def level6lrr : BinaryTree (List W) := .node [v77, v92, v143, v160, v186, v221, v251] level6lrrl level6lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrr_ok : everyKey (rowOK 5 level5) level6lrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrrl && everyKey (rowOK 5 level5) level6lrrr) = true
  rw [level6lrrl_ok, level6lrrr_ok]
  decide +kernel
def level6lr : BinaryTree (List W) := .node [v70, v92, v143, v160, v186, v221, v251] level6lrl level6lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lr_ok : everyKey (rowOK 5 level5) level6lr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrl && everyKey (rowOK 5 level5) level6lrr) = true
  rw [level6lrl_ok, level6lrr_ok]
  decide +kernel
def level6l : BinaryTree (List W) := .node [v44, v92, v143, v160, v186, v221] level6ll level6lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6l_ok : everyKey (rowOK 5 level5) level6l = true := by
  change (_ && everyKey (rowOK 5 level5) level6ll && everyKey (rowOK 5 level5) level6lr) = true
  rw [level6ll_ok, level6lr_ok]
  decide +kernel
def level6rlll : BinaryTree (List W) := (.node [v92, v112, v143, v160, v186, v221, v251] (.node [v92, v105, v143, v160, v186, v221, v251] (.node [v92, v104, v143, v160, v186, v221, v251] .nil .nil) .nil) (.node [v92, v113, v143, v160, v186, v221, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlll_ok : everyKey (rowOK 5 level5) level6rlll = true := by decide +kernel
def level6rllr : BinaryTree (List W) := (.node [v92, v127, v143, v160, v186, v221, v251] (.node [v92, v122, v143, v160, v186, v221, v251] (.node [v92, v120, v143, v160, v186, v221, v251] .nil .nil) .nil) (.node [v92, v131, v143, v160, v186, v221] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllr_ok : everyKey (rowOK 5 level5) level6rllr = true := by decide +kernel
def level6rll : BinaryTree (List W) := .node [v92, v118, v143, v160, v186, v221, v251] level6rlll level6rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rll_ok : everyKey (rowOK 5 level5) level6rll = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlll && everyKey (rowOK 5 level5) level6rllr) = true
  rw [level6rlll_ok, level6rllr_ok]
  decide +kernel
def level6rlrl : BinaryTree (List W) := (.node [v92, v143, v158, v160, v186, v221, v251] (.node [v92, v143, v157, v160, v186, v221, v251] (.node [v92, v143, v156, v160, v186, v221, v251] .nil .nil) .nil) (.node [v92, v143, v160, v175, v186, v221, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrl_ok : everyKey (rowOK 5 level5) level6rlrl = true := by decide +kernel
def level6rlrr : BinaryTree (List W) := (.node [v92, v143, v160, v183, v186, v221, v251] (.node [v92, v143, v160, v180, v186, v221, v251] .nil .nil) (.node [v92, v143, v160, v186, v205, v221, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrr_ok : everyKey (rowOK 5 level5) level6rlrr = true := by decide +kernel
def level6rlr : BinaryTree (List W) := .node [v92, v143, v160, v179, v186, v221, v251] level6rlrl level6rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlr_ok : everyKey (rowOK 5 level5) level6rlr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlrl && everyKey (rowOK 5 level5) level6rlrr) = true
  rw [level6rlrl_ok, level6rlrr_ok]
  decide +kernel
def level6rl : BinaryTree (List W) := .node [v92, v131, v143, v160, v186, v221, v251] level6rll level6rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rl_ok : everyKey (rowOK 5 level5) level6rl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rll && everyKey (rowOK 5 level5) level6rlr) = true
  rw [level6rll_ok, level6rlr_ok]
  decide +kernel
def level6rrll : BinaryTree (List W) := (.node [v92, v143, v160, v186, v221, v238, v251] (.node [v92, v143, v160, v186, v218, v221, v251] (.node [v92, v143, v160, v186, v216, v221, v251] .nil .nil) .nil) (.node [v92, v143, v160, v186, v221, v244, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrll_ok : everyKey (rowOK 5 level5) level6rrll = true := by decide +kernel
def level6rrlr : BinaryTree (List W) := (.node [v92, v143, v160, v186, v221, v251, v265] (.node [v92, v143, v160, v186, v221, v249, v251] .nil .nil) (.node [v92, v143, v160, v186, v221, v251, v273] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlr_ok : everyKey (rowOK 5 level5) level6rrlr = true := by decide +kernel
def level6rrl : BinaryTree (List W) := .node [v92, v143, v160, v186, v221, v248, v251] level6rrll level6rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrl_ok : everyKey (rowOK 5 level5) level6rrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrll && everyKey (rowOK 5 level5) level6rrlr) = true
  rw [level6rrll_ok, level6rrlr_ok]
  decide +kernel
def level6rrrl : BinaryTree (List W) := (.node [v92, v143, v160, v186, v221, v251, v283] (.node [v92, v143, v160, v186, v221, v251, v280] (.node [v92, v143, v160, v186, v221, v251, v278] .nil .nil) .nil) (.node [v92, v143, v160, v186, v221, v276] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrl_ok : everyKey (rowOK 5 level5) level6rrrl = true := by decide +kernel
def level6rrrr : BinaryTree (List W) := (.node [v92, v143, v160, v186, v248, v251] (.node [v92, v143, v160, v186, v221, v280] .nil .nil) (.node [v92, v143, v160, v216, v221, v251] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrr_ok : everyKey (rowOK 5 level5) level6rrrr = true := by decide +kernel
def level6rrr : BinaryTree (List W) := .node [v92, v143, v160, v186, v221, v278] level6rrrl level6rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrr_ok : everyKey (rowOK 5 level5) level6rrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrrl && everyKey (rowOK 5 level5) level6rrrr) = true
  rw [level6rrrl_ok, level6rrrr_ok]
  decide +kernel
def level6rr : BinaryTree (List W) := .node [v92, v143, v160, v186, v221, v251, v276] level6rrl level6rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rr_ok : everyKey (rowOK 5 level5) level6rr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrl && everyKey (rowOK 5 level5) level6rrr) = true
  rw [level6rrl_ok, level6rrr_ok]
  decide +kernel
def level6r : BinaryTree (List W) := .node [v92, v143, v160, v186, v211, v221, v251] level6rl level6rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6r_ok : everyKey (rowOK 5 level5) level6r = true := by
  change (_ && everyKey (rowOK 5 level5) level6rl && everyKey (rowOK 5 level5) level6rr) = true
  rw [level6rl_ok, level6rr_ok]
  decide +kernel
def level6 : BinaryTree (List W) := .node [v85, v92, v143, v160, v186, v221, v251] level6l level6r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6_ok : everyKey (rowOK 5 level5) level6 = true := by
  change (_ && everyKey (rowOK 5 level5) level6l && everyKey (rowOK 5 level5) level6r) = true
  rw [level6l_ok, level6r_ok]
  decide +kernel
theorem closed6 : Closed 6 level6 := closed_next 5 (by decide) level6 level5 closed5 level6_ok
def level7 : BinaryTree (List W) := (.node [v92, v143, v160, v186, v221, v251] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7_ok : everyKey (rowOK 6 level6) level7 = true := by decide +kernel
theorem closed7 : Closed 7 level7 := closed_next 6 (by decide) level7 level6 closed6 level7_ok

theorem lower : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z 7 ins.toFinset :=
  @no_build 7 level7 ins (by decide +kernel) (by decide) closed7 (by decide +kernel)
def witness : List Gate := [⟨.and,[1,5]⟩, ⟨.or,[3,6]⟩, ⟨.and,[0,7]⟩, ⟨.or,[2,8]⟩, ⟨.or,[3,9]⟩, ⟨.and,[1,10]⟩, ⟨.or,[0,11]⟩, ⟨.or,[4,9]⟩, ⟨.and,[12,13]⟩]
theorem upper : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 9 ∧ ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xeeeaeae8eeeaeae0 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact ⟨witness,14,by simp [witness],rfl,by decide +kernel⟩
end PEqualNP.Outside.L_meta_13621_aux

open PEqualNP.Outside.L_meta_13621_aux in
theorem PEqualNP.Outside.L_meta_13621 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 4008372960) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372968 * 2 ^ 32 + 4008372960) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  have code : 4008372968 * 2 ^ 32 + 4008372960 = 0xeeeaeae8eeeaeae0 := by decide
  simp only [code] at h ⊢
  obtain ⟨C,legal,size,computes⟩ := h
  obtain ⟨gs,o,mono,bound,ev⟩ := replace 0xeeeaeae8eeeaeae0 9 ins (by decide +kernel) sampled rfl lower upper C.gates C.output legal computes
  exact ⟨⟨gs,o⟩,mono,bound.trans size,ev⟩
