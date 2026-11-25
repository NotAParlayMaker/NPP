import PEqualNP.Defs

-- The live-wire search and circuit compiler are adapted from the merged L-meta-8639 under Apache-2.0.
namespace PEqualNP.Outside.L_meta_13403_aux

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

def v0 : W := 0x2f359e600000003778ee
def v1 : W := 0x59b8f77000000187830f
def v2 : W := 0x7399e330000006383c30
def v3 : W := 0x7bb9f770000007bfbf3f
def v4 : W := 0x7e25fc40000007c03fc0
def v5 : W := 0x7f35fe60000007f77fee
def v6 : W := 0x7fbd0800000007ffc000
def v7 : W := 0x7fbd9e60000007fff8ee
def v8 : W := 0x7fbdff70000001b7fbef
def v9 : W := 0x7fbdff700000063f7cfe
def v10 : W := 0x7fbdff70000007c7bfcf
def v11 : W := 0x45000020000000f880038e0
def v12 : W := 0x4500002000000ce00003cc0
def v13 : W := 0x57000029440000e000038c0
def v14 : W := 0x579800296e0000f880038ee
def v15 : W := 0xb2f8000f7f000303000030f
def v16 : W := 0xe5e0002e33000c1c0003c30
def v17 : W := 0xf700002f44000fe00003fc0
def v18 : W := 0xf798002f6e000ff88003fee
def v19 : W := 0xf7e0002f77000ffc0003ff0
def v20 : W := 0xf7f8002008000fff8000000
def v21 : W := 0xf7f800296e000fff80038ee
def v22 : W := 0xf7f8002f4c000fff8003fc0
def v23 : W := 0xf7f8002f7f0003fb8003bef
def v24 : W := 0xf7f8002f7f000cfc8003cfe
def v25 : W := 0xf7f8002f7f000fe30003fcf
def v26 : W := 0xf7fffbf088000ffffffc000
def v27 : W := 0x25009815002a063018837402e
def v28 : W := 0x25579815296e0630f883778ee
def v29 : W := 0x3800e019803307001c0380030
def v30 : W := 0x3d00001d800007f00003fc000
def v31 : W := 0x3d00981d802a07f01883fc02e
def v32 : W := 0x3d00f804000807f01f8000000
def v33 : W := 0x3d00f815002a07f01f837402e
def v34 : W := 0x3d00f81d803b00c003007800f
def v35 : W := 0x3d00f81d803b06f01b837c02f
def v36 : W := 0x3d00f81d803b07301c83f403e
def v37 : W := 0x3d00ffe65fcc07f01ffc03fc0
def v38 : W := 0x3df7001daf4407ffe003fffc0
def v39 : W := 0x3df7f804200807ffff8000000
def v40 : W := 0x105121886014c30c303187830f
def v41 : W := 0x125129897096e000000007000e
def v42 : W := 0x125579897296e0000f880738ee
def v43 : W := 0x1821a00c241c43803e01c003c0
def v44 : W := 0x1870800c6408038f0001c7c000
def v45 : W := 0x1870807ffd08038f0007ffc000
def v46 : W := 0x1871a1804000838f3e38000000
def v47 : W := 0x1871a1886014c38f3e3987830f
def v48 : W := 0x1871a18c641cc0030e080740ce
def v49 : W := 0x1871a18c641cc30f3e3987c3cf
def v50 : W := 0x1871a18c641cc38c3e31c783cf
def v51 : W := 0x1871a1f3d9e3b38f3e3e383c30
def v52 : W := 0x187ede0c66eb338fc1c1c7fc30
def v53 : W := 0x187fff804200838ffff8000000
def v54 : W := 0x1ba1ae0dbc1f73f03fc1f803f0
def v55 : W := 0x4404502203000c70c1c6383c30
def v56 : W := 0x46045823138220600180303820
def v57 : W := 0x4c208026050800630000304000
def v58 : W := 0x4c20802605080c800006400000
def v59 : W := 0x4c20802605080cf30006784000
def v60 : W := 0x4c20807fbd080cf30007ffc000
def v61 : W := 0x4c24d00002000cf3cfc8000000
def v62 : W := 0x4c24d026070800630f883078e0
def v63 : W := 0x4c24d02607080c73cfce387cf0
def v64 : W := 0x4c24d02607080c80ce06403cc0
def v65 : W := 0x4c24d059baf77cf3cfc987830f
def v66 : W := 0x4c24d07e27fc4c80ce07c03fc0
def v67 : W := 0x4c2bafa605fffcf3303678430f
def v68 : W := 0x4ff08027dd080cff00067fc000
def v69 : W := 0x4ff4df8042008cffcff8000000
def v70 : W := 0x4ff4dfa7df0bbc8cce3647bccf
def v71 : W := 0x545571aa6314cf7cf1f7bfbf3f
def v72 : W := 0x5c20802e250800000000000000
def v73 : W := 0x5c25f02e271c4f80fe07c03fc0
def v74 : W := 0x5c25f02e279c40000e000038c0
def v75 : W := 0x5c25f02e279c43803e01c03bc0
def v76 : W := 0x5c25f02e279c4c80ce06403cc0
def v77 : W := 0x5c25f07e27fc40000e07c03fc0
def v78 : W := 0x5c2ff02e27fc4000fe00003fc0
def v79 : W := 0x5c70802e65080fff0007ffc000
def v80 : W := 0x5c75f18042008ffffff8000000
def v81 : W := 0x5c75f1ae671cc0630f883778ee
def v82 : W := 0x5c75f1ae679cc0030e080778ce
def v83 : W := 0x5e70802f750800630000374000
def v84 : W := 0x5e70802f750803ef0001f7c000
def v85 : W := 0x5e70802f75080cf300067f4000
def v86 : W := 0x5e70807ffd0800630007ffc000
def v87 : W := 0x5e7089af750aa063018837402e
def v88 : W := 0x5e71a9af759ee063000037400e
def v89 : W := 0x5e75f980420080630f88000000
def v90 : W := 0x5e75f980420083ef3fb8000000
def v91 : W := 0x5e75f98042008cf3cfc8000000
def v92 : W := 0x5e75f9ae679cc0000e000038c0
def v93 : W := 0x5e75f9ae679cc0630f880038c0
def v94 : W := 0x5e75f9af779ee0000e000738ce
def v95 : W := 0x5e75f9af779ee0630f883778ee
def v96 : W := 0x5e7fff8042008063fff8000000
def v97 : W := 0x5ff0802ffd08007f00003fc000
def v98 : W := 0x5ff5ff804200807f0ff8000000
def v99 : W := 0x5ff5ffafff9ff0730fc83f78fe
def v100 : W := 0xa00a005000600f80f007c00700
def v101 : W := 0xa00f705002f44f80fe07c03fc0
def v102 : W := 0xa180005088000f9c0007c88000
def v103 : W := 0xa18579d08a96ef9c0f8fc8b8ee
def v104 : W := 0xa18a060000000f9cf070000000
def v105 : W := 0xa18a062f359e6f9cf0703778ee
def v106 : W := 0xa18a065000600f9cf077c00700
def v107 : W := 0xa18a06508861130c3031808301
def v108 : W := 0xa18a065088611c10c046080410
def v109 : W := 0xa18a065088611f8cf037c08701
def v110 : W := 0xa25a09d15062afe3f18ff7472e
def v111 : W := 0xa38a0e5198e330000000000000
def v112 : W := 0xa38e5e519ae33000c1c0003c30
def v113 : W := 0xb00b205820f443003001800300
def v114 : W := 0xb00f705822f44300fe01803fc0
def v115 : W := 0xb3d00059f800030c0001878000
def v116 : W := 0xb3db2f804000830c3030000000
def v117 : W := 0xb3db2fd9f8f7f000000007000e
def v118 : W := 0xb3db2fd9f8f7f30c303187830f
def v119 : W := 0xb3df7f804200830cfff8000000
def v120 : W := 0xb3df7fd9faf7f30c3fb987bbef
def v121 : W := 0xb3df7fd9faf7f30cfe3187bfcf
def v122 : W := 0xb9fba7dcec7ddc13ce4e0f44de
def v123 : W := 0xe40e507203e00c00c006003c00
def v124 : W := 0xe780007399000c700006380000
def v125 : W := 0xe78e5e0002000c70c1c0000000
def v126 : W := 0xe78e5e519ae33c70c1c0000000
def v127 : W := 0xe78e5e739be330600180303820
def v128 : W := 0xe78e5e739be33c00c006003c00
def v129 : W := 0xe78e5e739be33c70c1c6383c30
def v130 : W := 0xe7de5f8042008c7fc1f8000000
def v131 : W := 0xeda080768d080fff0007f8c000
def v132 : W := 0xedaed6768f69136f3fb9b0fbe1
def v133 : W := 0xefa080779d080cf30006784000
def v134 : W := 0xefaede779feb3cf3c1c6787c30
def v135 : W := 0xf7df7f8042008f7cf1f0000000
def v136 : W := 0xf7df7ffbfbf7ff7cf1f7bfbf3f
def v137 : W := 0xfc20807e25080f800007c00000
def v138 : W := 0xfc20807e25080ff30007f84000
def v139 : W := 0xfc20807fbd080f800007ffc000
def v140 : W := 0xfc25f07e279c4f800e07c038c0
def v141 : W := 0xfc2a807e25680f80f007c00700
def v142 : W := 0xfc2ba07e25fc4f803007c00300
def v143 : W := 0xfc2ff00002000f80fe00000000
def v144 : W := 0xfc2ff02e279c4f80fe000038c0
def v145 : W := 0xfc2ff07e27fc43003e01803bc0
def v146 : W := 0xfc2ff07e27fc4c00ce06003cc0
def v147 : W := 0xfc2ff07e27fc4f80fe07c03fc0
def v148 : W := 0xfc70807e65080f8f0007c7c000
def v149 : W := 0xfc7ff18042008f8ffe38000000
def v150 : W := 0xfda0807ead080f9c0007c88000
def v151 : W := 0xfdaff07eaffc4f9cfe07c8bfc0
def v152 : W := 0xfdaff67e27fc4f9cfe77c03fc0
def v153 : W := 0xfdaff67eaffd5f8cfe37c0bfc1
def v154 : W := 0xfdaff67eaffd5f90fe47c83fd0
def v155 : W := 0xfe70807f75080fe30007f74000
def v156 : W := 0xfe7ff98042008fe3ff88000000
def v157 : W := 0xfe7ff9ff77feefe3ff8ff77fee
def v158 : W := 0xffa0807fbd080ff00007f80000
def v159 : W := 0xffaffe7fbfff7f80fe07c03fc0
def v160 : W := 0xffaffe7fbfff7ff0ffc7f83ff0
def v161 : W := 0xfff0800040000fff0000000000
def v162 : W := 0xfff0802645080fff0006784000
def v163 : W := 0xfff0802f75080fff0000374000
def v164 : W := 0xfff0807e65080fff0007c00000
def v165 : W := 0xfff0807ffd08036f0001b7c000
def v166 : W := 0xfff0807ffd080c7300063f4000
def v167 : W := 0xfff0807ffd080f8c0007c78000
def v168 : W := 0xfff0807ffd080fff0007ffc000
def v169 : W := 0xfff0807ffdff7fff0007ffc30f
def v170 : W := 0xfff089fffd0aafff018fffc02e
def v171 : W := 0xfff08e7ffd0b3fff01c7ffc030
def v172 : W := 0xfff08ffffd088fff01ffffc000
def v173 : W := 0xfff08ffffd0bbfff0037ffc00f
def v174 : W := 0xfff1a1fffd1ccfff3037ffc30f
def v175 : W := 0xfff1a9fffd9eefff0007ffc00e
def v176 : W := 0xfff5f98042008fff0f88000000
def v177 : W := 0xfff5f9ffff9eefff0f8ffff8ee
def v178 : W := 0xfffa807ffd680ffff007ffc700
def v179 : W := 0xfffa867ffd080ffff077ffc000
def v180 : W := 0xfffa867ffd691fff3037ffc301
def v181 : W := 0xfffa867ffd691fffc047ffc410
def v182 : W := 0xfffa8e7ffdeb3fff0007ffc000
def v183 : W := 0xfffba07ffdfc4fff3007ffc300
def v184 : W := 0xfffbaffffd088fff3037ffc000
def v185 : W := 0xfffbaffffdfff30c303187830f
def v186 : W := 0xfffbaffffdfff36f3031b7c30f
def v187 : W := 0xfffbaffffdffff8c3037c7830f
def v188 : W := 0xfffbaffffdffffff3037ffc30f
def v189 : W := 0xfffede7fff080fffc1c7ffc000
def v190 : W := 0xfffede7fffeb3fffc1c7fffc30
def v191 : W := 0xfffff07ffffc4ffffe07ffffc0
def v192 : W := 0xffffff804200836f3fb8000000
def v193 : W := 0xffffff8042008c73cfc8000000
def v194 : W := 0xffffff8042008f8cfe30000000
def v195 : W := 0xffffff8042008ffffff8000000
def v196 : W := 0xffffff81da03bffffff8380030
def v197 : W := 0xffffff8c661ccffffff9c003c0
def v198 : W := 0xffffffa647088ffffffe784000
def v199 : W := 0xffffffaf779eeffffff83778ee
def v200 : W := 0xffffffd042608fffffffc00700
def v201 : W := 0xffffffd0ca008fffffffc88000
def v202 : W := 0xffffffd0ca619ffffff9808301
def v203 : W := 0xffffffd0ca619ffffffe080410
def v204 : W := 0xffffffd1dae3bffffff8000000
def v205 : W := 0xffffffd862f4cffffff9800300
def v206 : W := 0xffffffd9faf7fffffff987830f
def v207 : W := 0xfffffff3db008ffffffe380000
def v208 : W := 0xfffffff3dbe3bffffffe383c30
def v209 : W := 0xfffffffe67088fffffffc00000
def v210 : W := 0xfffffffe67fccf8cfe37c03fc0
def v211 : W := 0xfffffffe67fccfffffffc03fc0
def v212 : W := 0xffffffffff088fffffffffc000
def v213 : W := 0xfffffffffffff0630f883778ee
def v214 : W := 0xfffffffffffff36f3fb9b7fbef
def v215 : W := 0xfffffffffffffc73cfce3f7cfe
def v216 : W := 0xffffffffffffff8cfe37c7bfcf

def ins : List W := [v95, v118, v129, v147, v168, v195]
theorem sampled : ∀ j : Fin 104, Nat.testBit 0xeac8e8c8eac0c8c0 (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
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
def level3 : BinaryTree (List W) := (.node [v74, v89, v129, v185] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level3_ok : everyKey (rowOK 2 level2) level3 = true := by decide +kernel
theorem closed3 : Closed 3 level3 := closed_next 2 (by decide) level3 level2 closed2 level3_ok
def level4lll : BinaryTree (List W) := (.node [v17, v74, v89, v118, v129] (.node [v14, v74, v89, v118, v129] (.node [v13, v74, v89, v118, v129] .nil .nil) .nil) (.node [v26, v95, v118, v129, v147] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lll_ok : everyKey (rowOK 3 level3) level4lll = true := by decide +kernel
def level4llr : BinaryTree (List W) := (.node [v42, v74, v118, v129, v195] (.node [v38, v95, v118, v129, v195] (.node [v37, v95, v118, v129, v168] .nil .nil) .nil) (.node [v51, v95, v118, v147, v168] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llr_ok : everyKey (rowOK 3 level3) level4llr = true := by decide +kernel
def level4ll : BinaryTree (List W) := .node [v28, v74, v118, v129, v195] level4lll level4llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4ll_ok : everyKey (rowOK 3 level3) level4ll = true := by
  change (_ && everyKey (rowOK 3 level3) level4lll && everyKey (rowOK 3 level3) level4llr) = true
  rw [level4lll_ok, level4llr_ok]
  decide +kernel
def level4lrl : BinaryTree (List W) := (.node [v65, v95, v129, v147, v168] (.node [v59, v74, v89, v118, v129] (.node [v54, v95, v118, v168, v195] .nil .nil) .nil) (.node [v67, v95, v129, v147, v195] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrl_ok : everyKey (rowOK 3 level3) level4lrl = true := by decide +kernel
def level4lrr : BinaryTree (List W) := (.node [v74, v83, v89, v118, v129] (.node [v72, v74, v89, v118, v129] (.node [v71, v95, v147, v168, v195] .nil .nil) .nil) (.node [v74, v87, v118, v129, v195] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrr_ok : everyKey (rowOK 3 level3) level4lrr = true := by decide +kernel
def level4lr : BinaryTree (List W) := .node [v70, v95, v129, v168, v195] level4lrl level4lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lr_ok : everyKey (rowOK 3 level3) level4lr = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrl && everyKey (rowOK 3 level3) level4lrr) = true
  rw [level4lrl_ok, level4lrr_ok]
  decide +kernel
def level4l : BinaryTree (List W) := .node [v52, v95, v118, v147, v195] level4ll level4lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4l_ok : everyKey (rowOK 3 level3) level4l = true := by
  change (_ && everyKey (rowOK 3 level3) level4ll && everyKey (rowOK 3 level3) level4lr) = true
  rw [level4ll_ok, level4lr_ok]
  decide +kernel
def level4rll : BinaryTree (List W) := (.node [v74, v89, v118, v129, v188] (.node [v74, v89, v118, v129, v168] (.node [v74, v89, v118, v129, v137] .nil .nil) .nil) (.node [v74, v91, v118, v129, v168] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rll_ok : everyKey (rowOK 3 level3) level4rll = true := by decide +kernel
def level4rlr : BinaryTree (List W) := (.node [v74, v118, v129, v168, v193] (.node [v74, v118, v129, v156, v168] (.node [v74, v117, v129, v168, v195] .nil .nil) .nil) (.node [v88, v89, v118, v129, v147] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlr_ok : everyKey (rowOK 3 level3) level4rlr = true := by decide +kernel
def level4rl : BinaryTree (List W) := .node [v74, v95, v129, v185, v195] level4rll level4rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rl_ok : everyKey (rowOK 3 level3) level4rl = true := by
  change (_ && everyKey (rowOK 3 level3) level4rll && everyKey (rowOK 3 level3) level4rlr) = true
  rw [level4rll_ok, level4rlr_ok]
  decide +kernel
def level4rrl : BinaryTree (List W) := (.node [v95, v118, v134, v147, v198] (.node [v93, v118, v129, v143, v168] (.node [v92, v118, v129, v168, v195] .nil .nil) .nil) (.node [v95, v129, v147, v185, v195] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrl_ok : everyKey (rowOK 3 level3) level4rrl = true := by decide +kernel
def level4rrr : BinaryTree (List W) := (.node [v118, v122, v147, v168, v195] (.node [v110, v118, v129, v168, v195] (.node [v105, v118, v129, v147, v168] .nil .nil) .nil) (.node [v129, v132, v147, v168, v195] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrr_ok : everyKey (rowOK 3 level3) level4rrr = true := by decide +kernel
def level4rr : BinaryTree (List W) := .node [v103, v118, v129, v147, v195] level4rrl level4rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rr_ok : everyKey (rowOK 3 level3) level4rr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrl && everyKey (rowOK 3 level3) level4rrr) = true
  rw [level4rrl_ok, level4rrr_ok]
  decide +kernel
def level4r : BinaryTree (List W) := .node [v89, v118, v129, v144, v168] level4rl level4rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4r_ok : everyKey (rowOK 3 level3) level4r = true := by
  change (_ && everyKey (rowOK 3 level3) level4rl && everyKey (rowOK 3 level3) level4rr) = true
  rw [level4rl_ok, level4rr_ok]
  decide +kernel
def level4 : BinaryTree (List W) := .node [v74, v88, v118, v129, v195] level4l level4r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4_ok : everyKey (rowOK 3 level3) level4 = true := by
  change (_ && everyKey (rowOK 3 level3) level4l && everyKey (rowOK 3 level3) level4r) = true
  rw [level4l_ok, level4r_ok]
  decide +kernel
theorem closed4 : Closed 4 level4 := closed_next 3 (by decide) level4 level3 closed3 level4_ok
def level5llllll : BinaryTree (List W) := (.node [v0, v17, v95, v118, v129, v147] (.node [v0, v14, v95, v118, v129, v147] .nil .nil) (.node [v0, v27, v95, v118, v129, v168] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llllll_ok : everyKey (rowOK 4 level4) level5llllll = true := by decide +kernel
def level5lllllr : BinaryTree (List W) := (.node [v0, v83, v95, v118, v129, v147] (.node [v0, v74, v95, v118, v129, v168] .nil .nil) (.node [v0, v89, v118, v129, v147, v168] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllllr_ok : everyKey (rowOK 4 level4) level5lllllr = true := by decide +kernel
def level5lllll : BinaryTree (List W) := .node [v0, v59, v95, v118, v129, v147] level5llllll level5lllllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllll_ok : everyKey (rowOK 4 level4) level5lllll = true := by
  change (_ && everyKey (rowOK 4 level4) level5llllll && everyKey (rowOK 4 level4) level5lllllr) = true
  rw [level5llllll_ok, level5lllllr_ok]
  decide +kernel
def level5llllr : BinaryTree (List W) := (.node [v1, v61, v95, v129, v147, v168] (.node [v0, v95, v118, v129, v147, v188] (.node [v0, v95, v118, v129, v147, v168] .nil .nil) (.node [v0, v104, v118, v129, v147, v168] .nil .nil)) (.node [v3, v95, v118, v129, v147, v168] (.node [v2, v46, v95, v118, v147, v168] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llllr_ok : everyKey (rowOK 4 level4) level5llllr = true := by decide +kernel
def level5llll : BinaryTree (List W) := .node [v0, v95, v118, v129, v137, v147] level5lllll level5llllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llll_ok : everyKey (rowOK 4 level4) level5llll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lllll && everyKey (rowOK 4 level4) level5llllr) = true
  rw [level5lllll_ok, level5llllr_ok]
  decide +kernel
def level5lllrl : BinaryTree (List W) := (.node [v8, v95, v118, v129, v147, v168] (.node [v6, v20, v95, v118, v129, v147] (.node [v5, v95, v118, v129, v147, v168] .nil .nil) (.node [v7, v95, v118, v129, v147, v168] .nil .nil)) (.node [v10, v95, v118, v129, v147, v168] (.node [v9, v95, v118, v129, v147, v168] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrl_ok : everyKey (rowOK 4 level4) level5lllrl = true := by decide +kernel
def level5lllrr : BinaryTree (List W) := (.node [v14, v27, v95, v118, v129, v195] (.node [v13, v74, v95, v118, v129, v195] (.node [v12, v95, v118, v129, v147, v195] .nil .nil) (.node [v13, v95, v118, v129, v147, v195] .nil .nil)) (.node [v14, v83, v118, v129, v147, v195] (.node [v14, v74, v95, v118, v129, v195] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrr_ok : everyKey (rowOK 4 level4) level5lllrr = true := by decide +kernel
def level5lllr : BinaryTree (List W) := .node [v11, v95, v118, v129, v147, v195] level5lllrl level5lllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllr_ok : everyKey (rowOK 4 level4) level5lllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lllrl && everyKey (rowOK 4 level4) level5lllrr) = true
  rw [level5lllrl_ok, level5lllrr_ok]
  decide +kernel
def level5lll : BinaryTree (List W) := .node [v4, v32, v95, v118, v129, v168] level5llll level5lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lll_ok : everyKey (rowOK 4 level4) level5lll = true := by
  change (_ && everyKey (rowOK 4 level4) level5llll && everyKey (rowOK 4 level4) level5lllr) = true
  rw [level5llll_ok, level5lllr_ok]
  decide +kernel
def level5llrll : BinaryTree (List W) := (.node [v16, v44, v95, v118, v147, v195] (.node [v14, v102, v118, v129, v147, v195] (.node [v14, v95, v118, v129, v147, v195] .nil .nil) (.node [v15, v59, v95, v129, v147, v195] .nil .nil)) (.node [v17, v30, v95, v118, v129, v195] (.node [v17, v27, v95, v118, v129, v195] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrll_ok : everyKey (rowOK 4 level4) level5llrll = true := by decide +kernel
def level5llrlr : BinaryTree (List W) := (.node [v18, v95, v118, v129, v147, v195] (.node [v17, v95, v118, v129, v137, v195] (.node [v17, v89, v95, v118, v129, v147] .nil .nil) (.node [v17, v95, v118, v129, v147, v195] .nil .nil)) (.node [v21, v95, v118, v129, v147, v195] (.node [v19, v95, v118, v129, v147, v195] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrlr_ok : everyKey (rowOK 4 level4) level5llrlr = true := by decide +kernel
def level5llrl : BinaryTree (List W) := .node [v17, v74, v95, v118, v129, v195] level5llrll level5llrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrl_ok : everyKey (rowOK 4 level4) level5llrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrll && everyKey (rowOK 4 level4) level5llrlr) = true
  rw [level5llrll_ok, level5llrlr_ok]
  decide +kernel
def level5llrrl : BinaryTree (List W) := (.node [v27, v59, v95, v118, v129, v195] (.node [v24, v95, v118, v129, v147, v195] (.node [v23, v95, v118, v129, v147, v195] .nil .nil) (.node [v25, v95, v118, v129, v147, v195] .nil .nil)) (.node [v27, v83, v95, v118, v129, v195] (.node [v27, v74, v118, v129, v168, v195] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrl_ok : everyKey (rowOK 4 level4) level5llrrl = true := by decide +kernel
def level5llrrr : BinaryTree (List W) := (.node [v27, v95, v118, v129, v170, v195] (.node [v27, v95, v118, v129, v150, v195] (.node [v27, v95, v118, v129, v137, v195] .nil .nil) (.node [v27, v95, v118, v129, v168, v195] .nil .nil)) (.node [v27, v100, v118, v129, v168, v195] (.node [v27, v95, v118, v129, v188, v195] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrr_ok : everyKey (rowOK 4 level4) level5llrrr = true := by decide +kernel
def level5llrr : BinaryTree (List W) := .node [v27, v89, v95, v118, v129, v168] level5llrrl level5llrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrr_ok : everyKey (rowOK 4 level4) level5llrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrrl && everyKey (rowOK 4 level4) level5llrrr) = true
  rw [level5llrrl_ok, level5llrrr_ok]
  decide +kernel
def level5llr : BinaryTree (List W) := .node [v22, v95, v118, v129, v147, v195] level5llrl level5llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llr_ok : everyKey (rowOK 4 level4) level5llr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrl && everyKey (rowOK 4 level4) level5llrr) = true
  rw [level5llrl_ok, level5llrr_ok]
  decide +kernel
def level5ll : BinaryTree (List W) := .node [v14, v89, v95, v118, v129, v147] level5lll level5llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5ll_ok : everyKey (rowOK 4 level4) level5ll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lll && everyKey (rowOK 4 level4) level5llr) = true
  rw [level5lll_ok, level5llr_ok]
  decide +kernel
def level5lrllll : BinaryTree (List W) := (.node [v31, v95, v118, v129, v168, v195] (.node [v29, v43, v95, v118, v168, v195] .nil .nil) (.node [v33, v95, v118, v129, v168, v195] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrllll_ok : everyKey (rowOK 4 level4) level5lrllll = true := by decide +kernel
def level5lrlllr : BinaryTree (List W) := (.node [v36, v95, v118, v129, v168, v195] (.node [v35, v95, v118, v129, v168, v195] .nil .nil) (.node [v39, v95, v118, v129, v137, v147] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlllr_ok : everyKey (rowOK 4 level4) level5lrlllr = true := by decide +kernel
def level5lrlll : BinaryTree (List W) := .node [v34, v64, v95, v129, v168, v195] level5lrllll level5lrlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlll_ok : everyKey (rowOK 4 level4) level5lrlll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrllll && everyKey (rowOK 4 level4) level5lrlllr) = true
  rw [level5lrllll_ok, level5lrlllr_ok]
  decide +kernel
def level5lrllr : BinaryTree (List W) := (.node [v42, v95, v118, v129, v147, v195] (.node [v41, v74, v118, v129, v168, v195] (.node [v40, v55, v95, v147, v168, v195] .nil .nil) (.node [v41, v129, v147, v168, v195, v214] .nil .nil)) (.node [v47, v95, v118, v147, v168, v195] (.node [v45, v95, v118, v129, v147, v195] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrllr_ok : everyKey (rowOK 4 level4) level5lrllr = true := by decide +kernel
def level5lrll : BinaryTree (List W) := .node [v39, v95, v118, v129, v147, v168] level5lrlll level5lrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrll_ok : everyKey (rowOK 4 level4) level5lrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrlll && everyKey (rowOK 4 level4) level5lrllr) = true
  rw [level5lrlll_ok, level5lrllr_ok]
  decide +kernel
def level5lrlrl : BinaryTree (List W) := (.node [v53, v95, v118, v129, v147, v168] (.node [v49, v95, v118, v147, v168, v195] (.node [v48, v108, v118, v147, v168, v195] .nil .nil) (.node [v50, v95, v118, v147, v168, v195] .nil .nil)) (.node [v57, v95, v118, v129, v147, v195] (.node [v56, v118, v147, v168, v195, v215] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrl_ok : everyKey (rowOK 4 level4) level5lrlrl = true := by decide +kernel
def level5lrlrr : BinaryTree (List W) := (.node [v59, v95, v118, v119, v129, v147] (.node [v59, v89, v95, v118, v129, v147] (.node [v59, v74, v95, v118, v129, v195] .nil .nil) (.node [v59, v95, v112, v118, v147, v195] .nil .nil)) (.node [v59, v95, v118, v129, v147, v198] (.node [v59, v95, v118, v129, v147, v195] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrr_ok : everyKey (rowOK 4 level4) level5lrlrr = true := by decide +kernel
def level5lrlr : BinaryTree (List W) := .node [v58, v95, v118, v129, v147, v195] level5lrlrl level5lrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlr_ok : everyKey (rowOK 4 level4) level5lrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrlrl && everyKey (rowOK 4 level4) level5lrlrr) = true
  rw [level5lrlrl_ok, level5lrlrr_ok]
  decide +kernel
def level5lrl : BinaryTree (List W) := .node [v48, v74, v118, v129, v168, v195] level5lrll level5lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrl_ok : everyKey (rowOK 4 level4) level5lrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrll && everyKey (rowOK 4 level4) level5lrlr) = true
  rw [level5lrll_ok, level5lrlr_ok]
  decide +kernel
def level5lrrll : BinaryTree (List W) := (.node [v63, v95, v129, v147, v168, v195] (.node [v60, v95, v118, v129, v147, v195] (.node [v59, v95, v129, v147, v188, v195] .nil .nil) (.node [v62, v107, v129, v147, v168, v195] .nil .nil)) (.node [v68, v95, v118, v129, v147, v195] (.node [v66, v95, v118, v129, v168, v195] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrll_ok : everyKey (rowOK 4 level4) level5lrrll = true := by decide +kernel
def level5lrrlr : BinaryTree (List W) := (.node [v74, v83, v95, v118, v129, v195] (.node [v72, v95, v118, v129, v147, v195] (.node [v72, v74, v95, v118, v129, v195] .nil .nil) (.node [v73, v95, v118, v129, v168, v195] .nil .nil)) (.node [v74, v89, v118, v129, v147, v168] (.node [v74, v89, v95, v118, v129, v168] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrlr_ok : everyKey (rowOK 4 level4) level5lrrlr = true := by decide +kernel
def level5lrrl : BinaryTree (List W) := .node [v69, v95, v118, v129, v147, v168] level5lrrll level5lrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrl_ok : everyKey (rowOK 4 level4) level5lrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrll && everyKey (rowOK 4 level4) level5lrrlr) = true
  rw [level5lrrll_ok, level5lrrlr_ok]
  decide +kernel
def level5lrrrl : BinaryTree (List W) := (.node [v74, v95, v118, v129, v188, v195] (.node [v74, v95, v118, v129, v137, v195] (.node [v74, v89, v118, v129, v168, v195] .nil .nil) (.node [v74, v95, v118, v129, v168, v195] .nil .nil)) (.node [v74, v107, v118, v129, v168, v195] (.node [v74, v104, v118, v129, v168, v195] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrl_ok : everyKey (rowOK 4 level4) level5lrrrl = true := by decide +kernel
def level5lrrrr : BinaryTree (List W) := (.node [v77, v95, v118, v129, v168, v195] (.node [v75, v95, v118, v129, v168, v195] (.node [v74, v118, v129, v168, v195, v215] .nil .nil) (.node [v76, v95, v118, v129, v168, v195] .nil .nil)) (.node [v79, v95, v118, v129, v147, v195] (.node [v78, v95, v118, v129, v168, v195] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrr_ok : everyKey (rowOK 4 level4) level5lrrrr = true := by decide +kernel
def level5lrrr : BinaryTree (List W) := .node [v74, v118, v129, v157, v168, v195] level5lrrrl level5lrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrr_ok : everyKey (rowOK 4 level4) level5lrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrrl && everyKey (rowOK 4 level4) level5lrrrr) = true
  rw [level5lrrrl_ok, level5lrrrr_ok]
  decide +kernel
def level5lrr : BinaryTree (List W) := .node [v74, v89, v118, v129, v168] level5lrrl level5lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrr_ok : everyKey (rowOK 4 level4) level5lrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrl && everyKey (rowOK 4 level4) level5lrrr) = true
  rw [level5lrrl_ok, level5lrrr_ok]
  decide +kernel
def level5lr : BinaryTree (List W) := .node [v59, v95, v118, v134, v147, v195] level5lrl level5lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lr_ok : everyKey (rowOK 4 level4) level5lr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrl && everyKey (rowOK 4 level4) level5lrr) = true
  rw [level5lrl_ok, level5lrr_ok]
  decide +kernel
def level5l : BinaryTree (List W) := .node [v28, v95, v118, v129, v147, v195] level5ll level5lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5l_ok : everyKey (rowOK 4 level4) level5l = true := by
  change (_ && everyKey (rowOK 4 level4) level5ll && everyKey (rowOK 4 level4) level5lr) = true
  rw [level5ll_ok, level5lr_ok]
  decide +kernel
def level5rlllll : BinaryTree (List W) := (.node [v82, v118, v129, v147, v168, v195] (.node [v81, v118, v129, v147, v168, v195] .nil .nil) (.node [v83, v89, v95, v118, v129, v147] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlllll_ok : everyKey (rowOK 4 level4) level5rlllll = true := by decide +kernel
def level5rllllr : BinaryTree (List W) := (.node [v84, v95, v118, v129, v147, v195] (.node [v83, v118, v129, v147, v177, v195] .nil .nil) (.node [v85, v95, v118, v129, v147, v195] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllllr_ok : everyKey (rowOK 4 level4) level5rllllr = true := by decide +kernel
def level5rllll : BinaryTree (List W) := .node [v83, v95, v118, v129, v147, v195] level5rlllll level5rllllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllll_ok : everyKey (rowOK 4 level4) level5rllll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlllll && everyKey (rowOK 4 level4) level5rllllr) = true
  rw [level5rlllll_ok, level5rllllr_ok]
  decide +kernel
def level5rlllr : BinaryTree (List W) := (.node [v89, v95, v118, v129, v147, v168] (.node [v88, v95, v118, v129, v147, v195] (.node [v87, v95, v118, v129, v147, v195] .nil .nil) (.node [v89, v95, v118, v129, v137, v147] .nil .nil)) (.node [v89, v100, v118, v129, v147, v168] (.node [v89, v95, v118, v129, v147, v188] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlllr_ok : everyKey (rowOK 4 level4) level5rlllr = true := by decide +kernel
def level5rlll : BinaryTree (List W) := .node [v86, v95, v118, v129, v147, v195] level5rllll level5rlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlll_ok : everyKey (rowOK 4 level4) level5rlll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rllll && everyKey (rowOK 4 level4) level5rlllr) = true
  rw [level5rllll_ok, level5rlllr_ok]
  decide +kernel
def level5rllrl : BinaryTree (List W) := (.node [v94, v118, v129, v147, v168, v195] (.node [v91, v95, v118, v129, v147, v168] (.node [v90, v95, v118, v129, v147, v168] .nil .nil) (.node [v93, v118, v129, v147, v168, v195] .nil .nil)) (.node [v95, v97, v118, v129, v147, v195] (.node [v95, v96, v118, v129, v147, v168] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrl_ok : everyKey (rowOK 4 level4) level5rllrl = true := by decide +kernel
def level5rllrr : BinaryTree (List W) := (.node [v95, v113, v129, v168, v195, v216] (.node [v95, v111, v136, v147, v168, v195] (.node [v95, v101, v118, v129, v147, v195] .nil .nil) (.node [v95, v112, v118, v147, v168, v195] .nil .nil)) (.node [v95, v115, v129, v147, v188, v195] (.node [v95, v114, v118, v129, v147, v195] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrr_ok : everyKey (rowOK 4 level4) level5rllrr = true := by decide +kernel
def level5rllr : BinaryTree (List W) := .node [v95, v98, v118, v129, v147, v168] level5rllrl level5rllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllr_ok : everyKey (rowOK 4 level4) level5rllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rllrl && everyKey (rowOK 4 level4) level5rllrr) = true
  rw [level5rllrl_ok, level5rllrr_ok]
  decide +kernel
def level5rll : BinaryTree (List W) := .node [v89, v118, v129, v147, v168, v199] level5rlll level5rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rll_ok : everyKey (rowOK 4 level4) level5rll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlll && everyKey (rowOK 4 level4) level5rllr) = true
  rw [level5rlll_ok, level5rllr_ok]
  decide +kernel
def level5rlrll : BinaryTree (List W) := (.node [v95, v118, v121, v129, v147, v195] (.node [v95, v118, v119, v129, v147, v168] (.node [v95, v117, v129, v147, v168, v195] .nil .nil) (.node [v95, v118, v120, v129, v147, v195] .nil .nil)) (.node [v95, v118, v124, v147, v190, v195] (.node [v95, v118, v123, v160, v168, v195] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrll_ok : everyKey (rowOK 4 level4) level5rlrll = true := by decide +kernel
def level5rlrlr : BinaryTree (List W) := (.node [v95, v118, v129, v130, v147, v168] (.node [v95, v118, v127, v147, v168, v195] (.node [v95, v118, v126, v147, v168, v195] .nil .nil) (.node [v95, v118, v128, v147, v168, v195] .nil .nil)) (.node [v95, v118, v129, v133, v147, v195] (.node [v95, v118, v129, v131, v147, v195] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrlr_ok : everyKey (rowOK 4 level4) level5rlrlr = true := by decide +kernel
def level5rlrl : BinaryTree (List W) := .node [v95, v118, v125, v147, v168, v208] level5rlrll level5rlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrl_ok : everyKey (rowOK 4 level4) level5rlrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrll && everyKey (rowOK 4 level4) level5rlrlr) = true
  rw [level5rlrll_ok, level5rlrlr_ok]
  decide +kernel
def level5rlrrl : BinaryTree (List W) := (.node [v95, v118, v129, v138, v147, v195] (.node [v95, v118, v129, v137, v147, v209] (.node [v95, v118, v129, v137, v147, v195] .nil .nil) (.node [v95, v118, v129, v137, v191, v195] .nil .nil)) (.node [v95, v118, v129, v140, v168, v195] (.node [v95, v118, v129, v139, v147, v195] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrl_ok : everyKey (rowOK 4 level4) level5rlrrl = true := by decide +kernel
def level5rlrrr : BinaryTree (List W) := (.node [v95, v118, v129, v145, v168, v195] (.node [v95, v118, v129, v143, v168, v211] (.node [v95, v118, v129, v142, v147, v195] .nil .nil) (.node [v95, v118, v129, v144, v168, v195] .nil .nil)) (.node [v95, v118, v129, v147, v148, v195] (.node [v95, v118, v129, v146, v168, v195] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrr_ok : everyKey (rowOK 4 level4) level5rlrrr = true := by decide +kernel
def level5rlrr : BinaryTree (List W) := .node [v95, v118, v129, v141, v147, v195] level5rlrrl level5rlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrr_ok : everyKey (rowOK 4 level4) level5rlrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrrl && everyKey (rowOK 4 level4) level5rlrrr) = true
  rw [level5rlrrl_ok, level5rlrrr_ok]
  decide +kernel
def level5rlr : BinaryTree (List W) := .node [v95, v118, v129, v135, v147, v168] level5rlrl level5rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlr_ok : everyKey (rowOK 4 level4) level5rlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrl && everyKey (rowOK 4 level4) level5rlrr) = true
  rw [level5rlrl_ok, level5rlrr_ok]
  decide +kernel
def level5rl : BinaryTree (List W) := .node [v95, v116, v129, v147, v168, v206] level5rll level5rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rl_ok : everyKey (rowOK 4 level4) level5rl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rll && everyKey (rowOK 4 level4) level5rlr) = true
  rw [level5rll_ok, level5rlr_ok]
  decide +kernel
def level5rrllll : BinaryTree (List W) := (.node [v95, v118, v129, v147, v155, v195] (.node [v95, v118, v129, v147, v150, v195] .nil .nil) (.node [v95, v118, v129, v147, v156, v168] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrllll_ok : everyKey (rowOK 4 level4) level5rrllll = true := by decide +kernel
def level5rrlllr : BinaryTree (List W) := (.node [v95, v118, v129, v147, v162, v195] (.node [v95, v118, v129, v147, v161, v212] .nil .nil) (.node [v95, v118, v129, v147, v163, v195] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlllr_ok : everyKey (rowOK 4 level4) level5rrlllr = true := by decide +kernel
def level5rrlll : BinaryTree (List W) := .node [v95, v118, v129, v147, v158, v195] level5rrllll level5rrlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlll_ok : everyKey (rowOK 4 level4) level5rrlll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrllll && everyKey (rowOK 4 level4) level5rrlllr) = true
  rw [level5rrllll_ok, level5rrlllr_ok]
  decide +kernel
def level5rrllr : BinaryTree (List W) := (.node [v95, v118, v129, v147, v168, v176] (.node [v95, v118, v129, v147, v166, v195] (.node [v95, v118, v129, v147, v165, v195] .nil .nil) (.node [v95, v118, v129, v147, v167, v195] .nil .nil)) (.node [v95, v118, v129, v147, v168, v193] (.node [v95, v118, v129, v147, v168, v192] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrllr_ok : everyKey (rowOK 4 level4) level5rrllr = true := by decide +kernel
def level5rrll : BinaryTree (List W) := .node [v95, v118, v129, v147, v164, v195] level5rrlll level5rrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrll_ok : everyKey (rowOK 4 level4) level5rrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrlll && everyKey (rowOK 4 level4) level5rrllr) = true
  rw [level5rrlll_ok, level5rrllr_ok]
  decide +kernel
def level5rrlrl : BinaryTree (List W) := (.node [v95, v118, v129, v147, v168, v198] (.node [v95, v118, v129, v147, v168, v196] (.node [v95, v118, v129, v147, v168, v195] .nil .nil) (.node [v95, v118, v129, v147, v168, v197] .nil .nil)) (.node [v95, v118, v129, v147, v168, v201] (.node [v95, v118, v129, v147, v168, v200] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrl_ok : everyKey (rowOK 4 level4) level5rrlrl = true := by decide +kernel
def level5rrlrr : BinaryTree (List W) := (.node [v95, v118, v129, v147, v168, v207] (.node [v95, v118, v129, v147, v168, v204] (.node [v95, v118, v129, v147, v168, v203] .nil .nil) (.node [v95, v118, v129, v147, v168, v205] .nil .nil)) (.node [v95, v118, v129, v147, v169, v195] (.node [v95, v118, v129, v147, v168, v209] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrr_ok : everyKey (rowOK 4 level4) level5rrlrr = true := by decide +kernel
def level5rrlr : BinaryTree (List W) := .node [v95, v118, v129, v147, v168, v202] level5rrlrl level5rrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlr_ok : everyKey (rowOK 4 level4) level5rrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrlrl && everyKey (rowOK 4 level4) level5rrlrr) = true
  rw [level5rrlrl_ok, level5rrlrr_ok]
  decide +kernel
def level5rrl : BinaryTree (List W) := .node [v95, v118, v129, v147, v168, v194] level5rrll level5rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrl_ok : everyKey (rowOK 4 level4) level5rrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrll && everyKey (rowOK 4 level4) level5rrlr) = true
  rw [level5rrll_ok, level5rrlr_ok]
  decide +kernel
def level5rrrll : BinaryTree (List W) := (.node [v95, v118, v129, v147, v174, v195] (.node [v95, v118, v129, v147, v172, v195] (.node [v95, v118, v129, v147, v171, v195] .nil .nil) (.node [v95, v118, v129, v147, v173, v195] .nil .nil)) (.node [v95, v118, v129, v147, v178, v195] (.node [v95, v118, v129, v147, v175, v195] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrll_ok : everyKey (rowOK 4 level4) level5rrrll = true := by decide +kernel
def level5rrrlr : BinaryTree (List W) := (.node [v95, v118, v129, v147, v183, v195] (.node [v95, v118, v129, v147, v181, v195] (.node [v95, v118, v129, v147, v180, v195] .nil .nil) (.node [v95, v118, v129, v147, v182, v195] .nil .nil)) (.node [v95, v118, v129, v147, v186, v195] (.node [v95, v118, v129, v147, v184, v195] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrlr_ok : everyKey (rowOK 4 level4) level5rrrlr = true := by decide +kernel
def level5rrrl : BinaryTree (List W) := .node [v95, v118, v129, v147, v179, v195] level5rrrll level5rrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrl_ok : everyKey (rowOK 4 level4) level5rrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrll && everyKey (rowOK 4 level4) level5rrrlr) = true
  rw [level5rrrll_ok, level5rrrlr_ok]
  decide +kernel
def level5rrrrl : BinaryTree (List W) := (.node [v95, v118, v129, v152, v168, v195] (.node [v95, v118, v129, v147, v189, v195] (.node [v95, v118, v129, v147, v188, v195] .nil .nil) (.node [v95, v118, v129, v151, v168, v195] .nil .nil)) (.node [v95, v118, v129, v154, v168, v195] (.node [v95, v118, v129, v153, v168, v195] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrl_ok : everyKey (rowOK 4 level4) level5rrrrl = true := by decide +kernel
def level5rrrrr : BinaryTree (List W) := (.node [v106, v118, v129, v147, v168, v195] (.node [v95, v118, v134, v147, v168, v195] (.node [v95, v118, v129, v168, v195, v210] .nil .nil) (.node [v99, v118, v129, v147, v168, v195] .nil .nil)) (.node [v118, v129, v147, v168, v195, v213] (.node [v109, v118, v129, v147, v168, v195] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrr_ok : everyKey (rowOK 4 level4) level5rrrrr = true := by decide +kernel
def level5rrrr : BinaryTree (List W) := .node [v95, v118, v129, v159, v168, v195] level5rrrrl level5rrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrr_ok : everyKey (rowOK 4 level4) level5rrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrrl && everyKey (rowOK 4 level4) level5rrrrr) = true
  rw [level5rrrrl_ok, level5rrrrr_ok]
  decide +kernel
def level5rrr : BinaryTree (List W) := .node [v95, v118, v129, v147, v187, v195] level5rrrl level5rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrr_ok : everyKey (rowOK 4 level4) level5rrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrl && everyKey (rowOK 4 level4) level5rrrr) = true
  rw [level5rrrl_ok, level5rrrr_ok]
  decide +kernel
def level5rr : BinaryTree (List W) := .node [v95, v118, v129, v147, v170, v195] level5rrl level5rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rr_ok : everyKey (rowOK 4 level4) level5rr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrl && everyKey (rowOK 4 level4) level5rrr) = true
  rw [level5rrl_ok, level5rrr_ok]
  decide +kernel
def level5r : BinaryTree (List W) := .node [v95, v118, v129, v147, v149, v168] level5rl level5rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5r_ok : everyKey (rowOK 4 level4) level5r = true := by
  change (_ && everyKey (rowOK 4 level4) level5rl && everyKey (rowOK 4 level4) level5rr) = true
  rw [level5rl_ok, level5rr_ok]
  decide +kernel
def level5 : BinaryTree (List W) := .node [v80, v95, v118, v129, v147, v168] level5l level5r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5_ok : everyKey (rowOK 4 level4) level5 = true := by
  change (_ && everyKey (rowOK 4 level4) level5l && everyKey (rowOK 4 level4) level5r) = true
  rw [level5l_ok, level5r_ok]
  decide +kernel
theorem closed5 : Closed 5 level5 := closed_next 4 (by decide) level5 level4 closed4 level5_ok
def level6llll : BinaryTree (List W) := (.node [v1, v95, v118, v129, v147, v168, v195] (.node [v0, v95, v118, v129, v147, v168, v195] (.node [v0, v95, v118, v129, v147, v168] .nil .nil) .nil) (.node [v2, v95, v118, v129, v147, v168, v195] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llll_ok : everyKey (rowOK 5 level5) level6llll = true := by decide +kernel
def level6lllr : BinaryTree (List W) := (.node [v14, v95, v118, v129, v147, v168, v195] (.node [v6, v95, v118, v129, v147, v168, v195] .nil .nil) (.node [v14, v95, v118, v129, v147, v195] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllr_ok : everyKey (rowOK 5 level5) level6lllr = true := by decide +kernel
def level6lll : BinaryTree (List W) := .node [v4, v95, v118, v129, v147, v168, v195] level6llll level6lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lll_ok : everyKey (rowOK 5 level5) level6lll = true := by
  change (_ && everyKey (rowOK 5 level5) level6llll && everyKey (rowOK 5 level5) level6lllr) = true
  rw [level6llll_ok, level6lllr_ok]
  decide +kernel
def level6llrl : BinaryTree (List W) := (.node [v17, v95, v118, v129, v147, v195] (.node [v17, v95, v118, v129, v147, v168, v195] (.node [v16, v95, v118, v129, v147, v168, v195] .nil .nil) .nil) (.node [v20, v95, v118, v129, v147, v168, v195] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrl_ok : everyKey (rowOK 5 level5) level6llrl = true := by decide +kernel
def level6llrr : BinaryTree (List W) := (.node [v29, v95, v118, v129, v147, v168, v195] (.node [v27, v95, v118, v129, v168, v195] .nil .nil) (.node [v30, v95, v118, v129, v147, v168, v195] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrr_ok : everyKey (rowOK 5 level5) level6llrr = true := by decide +kernel
def level6llr : BinaryTree (List W) := .node [v27, v95, v118, v129, v147, v168, v195] level6llrl level6llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llr_ok : everyKey (rowOK 5 level5) level6llr = true := by
  change (_ && everyKey (rowOK 5 level5) level6llrl && everyKey (rowOK 5 level5) level6llrr) = true
  rw [level6llrl_ok, level6llrr_ok]
  decide +kernel
def level6ll : BinaryTree (List W) := .node [v15, v95, v118, v129, v147, v168, v195] level6lll level6llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6ll_ok : everyKey (rowOK 5 level5) level6ll = true := by
  change (_ && everyKey (rowOK 5 level5) level6lll && everyKey (rowOK 5 level5) level6llr) = true
  rw [level6lll_ok, level6llr_ok]
  decide +kernel
def level6lrll : BinaryTree (List W) := (.node [v41, v95, v118, v129, v147, v168, v195] (.node [v40, v95, v118, v129, v147, v168, v195] (.node [v34, v95, v118, v129, v147, v168, v195] .nil .nil) .nil) (.node [v43, v95, v118, v129, v147, v168, v195] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrll_ok : everyKey (rowOK 5 level5) level6lrll = true := by decide +kernel
def level6lrlr : BinaryTree (List W) := (.node [v48, v95, v118, v129, v147, v168, v195] (.node [v46, v95, v118, v129, v147, v168, v195] .nil .nil) (.node [v55, v95, v118, v129, v147, v168, v195] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlr_ok : everyKey (rowOK 5 level5) level6lrlr = true := by decide +kernel
def level6lrl : BinaryTree (List W) := .node [v44, v95, v118, v129, v147, v168, v195] level6lrll level6lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrl_ok : everyKey (rowOK 5 level5) level6lrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrll && everyKey (rowOK 5 level5) level6lrlr) = true
  rw [level6lrll_ok, level6lrlr_ok]
  decide +kernel
def level6lrrl : BinaryTree (List W) := (.node [v61, v95, v118, v129, v147, v168, v195] (.node [v59, v95, v118, v129, v147, v195] (.node [v59, v95, v118, v129, v147, v168, v195] .nil .nil) .nil) (.node [v62, v95, v118, v129, v147, v168, v195] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrl_ok : everyKey (rowOK 5 level5) level6lrrl = true := by decide +kernel
def level6lrrr : BinaryTree (List W) := (.node [v74, v95, v118, v129, v168, v195] (.node [v74, v95, v118, v129, v147, v168, v195] .nil .nil) (.node [v83, v95, v118, v129, v147, v168, v195] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrr_ok : everyKey (rowOK 5 level5) level6lrrr = true := by decide +kernel
def level6lrr : BinaryTree (List W) := .node [v64, v95, v118, v129, v147, v168, v195] level6lrrl level6lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrr_ok : everyKey (rowOK 5 level5) level6lrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrrl && everyKey (rowOK 5 level5) level6lrrr) = true
  rw [level6lrrl_ok, level6lrrr_ok]
  decide +kernel
def level6lr : BinaryTree (List W) := .node [v56, v95, v118, v129, v147, v168, v195] level6lrl level6lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lr_ok : everyKey (rowOK 5 level5) level6lr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrl && everyKey (rowOK 5 level5) level6lrr) = true
  rw [level6lrl_ok, level6lrr_ok]
  decide +kernel
def level6l : BinaryTree (List W) := .node [v32, v95, v118, v129, v147, v168, v195] level6ll level6lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6l_ok : everyKey (rowOK 5 level5) level6l = true := by
  change (_ && everyKey (rowOK 5 level5) level6ll && everyKey (rowOK 5 level5) level6lr) = true
  rw [level6ll_ok, level6lr_ok]
  decide +kernel
def level6rlll : BinaryTree (List W) := (.node [v95, v100, v118, v129, v147, v168, v195] (.node [v89, v95, v118, v129, v147, v168, v195] (.node [v89, v95, v118, v129, v147, v168] .nil .nil) .nil) (.node [v95, v102, v118, v129, v147, v168, v195] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlll_ok : everyKey (rowOK 5 level5) level6rlll = true := by decide +kernel
def level6rllr : BinaryTree (List W) := (.node [v95, v108, v118, v129, v147, v168, v195] (.node [v95, v107, v118, v129, v147, v168, v195] .nil .nil) (.node [v95, v111, v118, v129, v147, v168, v195] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllr_ok : everyKey (rowOK 5 level5) level6rllr = true := by decide +kernel
def level6rll : BinaryTree (List W) := .node [v95, v104, v118, v129, v147, v168, v195] level6rlll level6rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rll_ok : everyKey (rowOK 5 level5) level6rll = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlll && everyKey (rowOK 5 level5) level6rllr) = true
  rw [level6rlll_ok, level6rllr_ok]
  decide +kernel
def level6rlrl : BinaryTree (List W) := (.node [v95, v118, v123, v129, v147, v168, v195] (.node [v95, v116, v118, v129, v147, v168, v195] (.node [v95, v115, v118, v129, v147, v168, v195] .nil .nil) .nil) (.node [v95, v118, v124, v129, v147, v168, v195] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrl_ok : everyKey (rowOK 5 level5) level6rlrl = true := by decide +kernel
def level6rlrr : BinaryTree (List W) := (.node [v95, v118, v129, v137, v147, v168, v195] (.node [v95, v118, v129, v136, v147, v168, v195] .nil .nil) (.node [v95, v118, v129, v137, v147, v195] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrr_ok : everyKey (rowOK 5 level5) level6rlrr = true := by decide +kernel
def level6rlr : BinaryTree (List W) := .node [v95, v118, v125, v129, v147, v168, v195] level6rlrl level6rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlr_ok : everyKey (rowOK 5 level5) level6rlr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlrl && everyKey (rowOK 5 level5) level6rlrr) = true
  rw [level6rlrl_ok, level6rlrr_ok]
  decide +kernel
def level6rl : BinaryTree (List W) := .node [v95, v113, v118, v129, v147, v168, v195] level6rll level6rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rl_ok : everyKey (rowOK 5 level5) level6rl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rll && everyKey (rowOK 5 level5) level6rlr) = true
  rw [level6rll_ok, level6rlr_ok]
  decide +kernel
def level6rrll : BinaryTree (List W) := (.node [v95, v118, v129, v147, v161, v168, v195] (.node [v95, v118, v129, v147, v160, v168, v195] (.node [v95, v118, v129, v147, v157, v168, v195] .nil .nil) .nil) (.node [v95, v118, v129, v147, v168, v177, v195] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrll_ok : everyKey (rowOK 5 level5) level6rrll = true := by decide +kernel
def level6rrlr : BinaryTree (List W) := (.node [v95, v118, v129, v147, v168, v191, v195] (.node [v95, v118, v129, v147, v168, v190, v195] .nil .nil) (.node [v95, v118, v129, v147, v168, v195, v199] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlr_ok : everyKey (rowOK 5 level5) level6rrlr = true := by decide +kernel
def level6rrl : BinaryTree (List W) := .node [v95, v118, v129, v147, v168, v188, v195] level6rrll level6rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrl_ok : everyKey (rowOK 5 level5) level6rrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrll && everyKey (rowOK 5 level5) level6rrlr) = true
  rw [level6rrll_ok, level6rrlr_ok]
  decide +kernel
def level6rrrl : BinaryTree (List W) := (.node [v95, v118, v129, v147, v168, v195, v211] (.node [v95, v118, v129, v147, v168, v195, v208] .nil .nil) (.node [v95, v118, v129, v147, v168, v195, v212] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrl_ok : everyKey (rowOK 5 level5) level6rrrl = true := by decide +kernel
def level6rrrr : BinaryTree (List W) := (.node [v95, v118, v129, v147, v168, v195, v216] (.node [v95, v118, v129, v147, v168, v195, v215] .nil .nil) (.node [v95, v118, v129, v147, v188, v195] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrr_ok : everyKey (rowOK 5 level5) level6rrrr = true := by decide +kernel
def level6rrr : BinaryTree (List W) := .node [v95, v118, v129, v147, v168, v195, v214] level6rrrl level6rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrr_ok : everyKey (rowOK 5 level5) level6rrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrrl && everyKey (rowOK 5 level5) level6rrrr) = true
  rw [level6rrrl_ok, level6rrrr_ok]
  decide +kernel
def level6rr : BinaryTree (List W) := .node [v95, v118, v129, v147, v168, v195, v206] level6rrl level6rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rr_ok : everyKey (rowOK 5 level5) level6rr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrl && everyKey (rowOK 5 level5) level6rrr) = true
  rw [level6rrl_ok, level6rrr_ok]
  decide +kernel
def level6r : BinaryTree (List W) := .node [v95, v118, v129, v143, v147, v168, v195] level6rl level6rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6r_ok : everyKey (rowOK 5 level5) level6r = true := by
  change (_ && everyKey (rowOK 5 level5) level6rl && everyKey (rowOK 5 level5) level6rr) = true
  rw [level6rl_ok, level6rr_ok]
  decide +kernel
def level6 : BinaryTree (List W) := .node [v83, v95, v118, v129, v147, v195] level6l level6r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6_ok : everyKey (rowOK 5 level5) level6 = true := by
  change (_ && everyKey (rowOK 5 level5) level6l && everyKey (rowOK 5 level5) level6r) = true
  rw [level6l_ok, level6r_ok]
  decide +kernel
theorem closed6 : Closed 6 level6 := closed_next 5 (by decide) level6 level5 closed5 level6_ok
def level7 : BinaryTree (List W) := (.node [v95, v118, v129, v147, v168, v195] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7_ok : everyKey (rowOK 6 level6) level7 = true := by decide +kernel
theorem closed7 : Closed 7 level7 := closed_next 6 (by decide) level7 level6 closed6 level7_ok

theorem lower : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z 7 ins.toFinset :=
  @no_build 7 level7 ins (by decide +kernel) (by decide) closed7 (by decide +kernel)
def witness : List Gate := [⟨.and,[1,5]⟩, ⟨.and,[2,5]⟩, ⟨.or,[3,6]⟩, ⟨.and,[0,8]⟩, ⟨.and,[1,2]⟩, ⟨.or,[1,4]⟩, ⟨.or,[7,11]⟩, ⟨.and,[9,12]⟩, ⟨.or,[10,13]⟩]
theorem upper : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 9 ∧ ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xeac8e8c8eac0c8c0 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact ⟨witness,14,by simp [witness],rfl,by decide +kernel⟩
end PEqualNP.Outside.L_meta_13403_aux

open PEqualNP.Outside.L_meta_13403_aux in
theorem PEqualNP.Outside.L_meta_13403 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3939035336 * 2 ^ 32 + 3938502848) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3939035336 * 2 ^ 32 + 3938502848) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  have code : 3939035336 * 2 ^ 32 + 3938502848 = 0xeac8e8c8eac0c8c0 := by decide
  simp only [code] at h ⊢
  obtain ⟨C,legal,size,computes⟩ := h
  obtain ⟨gs,o,mono,bound,ev⟩ := replace 0xeac8e8c8eac0c8c0 9 ins (by decide +kernel) sampled rfl lower upper C.gates C.output legal computes
  exact ⟨⟨gs,o⟩,mono,bound.trans size,ev⟩
