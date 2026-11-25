import PEqualNP.Defs

-- The live-wire search and circuit compiler are adapted from tacyon52 in L-meta-8639, pull request 12794 under Apache-2.0.
namespace PEqualNP.Outside.L_meta_15139_aux

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

def v0 : W := 0xd24000d20
def v1 : W := 0xe20000e20
def v2 : W := 0xf00000f00
def v3 : W := 0x2902900000001f01f
def v4 : W := 0x29029000000067027
def v5 : W := 0x2821420000001870c7
def v6 : W := 0x282142000000607107
def v7 : W := 0x2ab56b000000007007
def v8 : W := 0xbbb7fb00000019f0df
def v9 : W := 0x16ebd6b000000667007
def v10 : W := 0x16ebd6b000000667d27
def v11 : W := 0x1d79eb9000001878e38
def v12 : W := 0x1fd2fd2000001f80fc0
def v13 : W := 0x1ffb800000001fff000
def v14 : W := 0x1ffbd6b000001fffd27
def v15 : W := 0x1ffbffb0000007ffdff
def v16 : W := 0x1ffbffb0000019ffeff
def v17 : W := 0x1ffbffb000001e7ff3f
def v18 : W := 0x1ffbffb000001f9ffdf
def v19 : W := 0x1ffbffb000001fe7fe7
def v20 : W := 0x1ffbffb000001fff0df
def v21 : W := 0x428000429000c20000c20
def v22 : W := 0x540000542000d00000d00
def v23 : W := 0x56e00056f000d24000d27
def v24 : W := 0x690000690000e00000e00
def v25 : W := 0x6b80006b9000e38000e38
def v26 : W := 0x6b8bbb7fb000e3819feff
def v27 : W := 0x6be0006bd000e3e000e38
def v28 : W := 0x7d00007d2000fc0000fc0
def v29 : W := 0x7d0bbb7fb000fc019ffdf
def v30 : W := 0x7d60007d6000fc6000fc0
def v31 : W := 0x7f80007fb000ff8000ff8
def v32 : W := 0x7fe000004000ffe000000
def v33 : W := 0x7fe00056f000ffe000d27
def v34 : W := 0x7fe0006bd000ffe000e38
def v35 : W := 0x7fe0007d6000ffe000fc0
def v36 : W := 0x7fe0007ff0000da0000df
def v37 : W := 0x7fe0007ff000dfe000dff
def v38 : W := 0x7fe0007ff000efa000eff
def v39 : W := 0x7fe0007ff000f3c000f3f
def v40 : W := 0x7fe0007ff000fda000fdf
def v41 : W := 0x7fe0007ff000fe4000fe7
def v42 : W := 0x7ffffb804000ffffff000
def v43 : W := 0x3006004004003006000000
def v44 : W := 0x1402802902903c038078038
def v45 : W := 0x1402802902903c03807f03f
def v46 : W := 0x146b80296b903ce38078e38
def v47 : W := 0x1700002d00003f00007f000
def v48 : W := 0x1702e00400400d01a000000
def v49 : W := 0x1702e004004032024000000
def v50 : W := 0x1702e00400403f03e000000
def v51 : W := 0x1702e00400403ff3e000000
def v52 : W := 0x1702e02d02d00d01a01f01f
def v53 : W := 0x1702e02d02d032024067027
def v54 : W := 0x1702e02d02d03d03a07f03f
def v55 : W := 0x1702e02d02d03e03c07f03f
def v56 : W := 0x1702e02d02d03f01a07f01f
def v57 : W := 0x1702e02d02d03f03e078038
def v58 : W := 0x1702e02d02d03f03e07f03f
def v59 : W := 0x1702ffd6fd603f03ff80fc0
def v60 : W := 0x1756e02d56f032d24067d27
def v61 : W := 0x176be0046bd03fe3e000e38
def v62 : W := 0x177d002d7d203ffc007ffc0
def v63 : W := 0x177fe00400403fffe000000
def v64 : W := 0x177fe0047d603fffe000fc0
def v65 : W := 0x177fe02d6bd03fffe078e38
def v66 : W := 0x1401402821423c01c07801c0
def v67 : W := 0x1401402821423c01c07871c7
def v68 : W := 0x1407d02827d23c0fc0780fc0
def v69 : W := 0x1430002860003c3000787000
def v70 : W := 0x1431460040040c10c2000000
def v71 : W := 0x143146004004302104000000
def v72 : W := 0x1431460040043c31c6000000
def v73 : W := 0x1431460040043c3fe6000000
def v74 : W := 0x1431462861460c10c21870c7
def v75 : W := 0x143146286146302104607107
def v76 : W := 0x1431462861463c11c27871c7
def v77 : W := 0x1431462861463c21c47871c7
def v78 : W := 0x1431462861463c30c27870c7
def v79 : W := 0x1431462861463c31c67801c0
def v80 : W := 0x1431462861463c31c67871c7
def v81 : W := 0x143147d7debd3c31c7878e38
def v82 : W := 0x14356e28656f302d24607d27
def v83 : W := 0x1436b82866b93c3e38787e38
def v84 : W := 0x1437d60047d63c3fc6000fc0
def v85 : W := 0x1437fe0040043c3ffe000000
def v86 : W := 0x1437fe0046bd3c3ffe000e38
def v87 : W := 0x1437fe2867d63c3ffe780fc0
def v88 : W := 0x1541682ab16b3fc1f87f81f8
def v89 : W := 0x15716e0040043ff1fe000000
def v90 : W := 0x15716e2af16f3ff1fe7f81f8
def v91 : W := 0x15756e004004000000000000
def v92 : W := 0x15756e2af56f000000007007
def v93 : W := 0x15756e2af56f000d24007d27
def v94 : W := 0x488000910000ccd001998000
def v95 : W := 0x488290000000ccd2da000000
def v96 : W := 0x4882909102900cd0da1980d8
def v97 : W := 0x488290910290c0c219818218
def v98 : W := 0x488290910290cc02c19802c0
def v99 : W := 0x488290910290ccd0db9980d8
def v100 : W := 0x488290910290ccd2db9982d8
def v101 : W := 0x488290bbb7fb0cd0da19f0df
def v102 : W := 0x4882916ebd6bccd2da667d27
def v103 : W := 0x48856e91056fccdd25998d27
def v104 : W := 0x4886b89106b9c0ce39818e38
def v105 : W := 0x4887d09107d2cc0fc1980fc0
def v106 : W := 0x49c6b89396b900c018018018
def v107 : W := 0x49c6b89396b900ce38018e38
def v108 : W := 0x49c6b8bbb7fb00c01819f0df
def v109 : W := 0x49f2be004004cff2fe000000
def v110 : W := 0x49f2be93d2bdcf22e59e72e7
def v111 : W := 0x5c87d0b927d20c00c01800c0
def v112 : W := 0x5c87d0b927d20c0fc0180fc0
def v113 : W := 0x5c87d0bbb7fb0c00c019f0df
def v114 : W := 0x5cb3d6004004fcf3de000000
def v115 : W := 0x5cb3d6b963d6f0e31de1f31f
def v116 : W := 0x5df000bbf0000cd00019f000
def v117 : W := 0x5df7fe0040040cd0da000000
def v118 : W := 0x5df7fe0040040cdffe000000
def v119 : W := 0x5df7fe0040040ff0fe000000
def v120 : W := 0x5df7fe0040043cf1de000000
def v121 : W := 0x5df7fe004004ccd2da000000
def v122 : W := 0x5df7fe0046bd0cdefa000e38
def v123 : W := 0x5df7fe0047d60cdfda000fc0
def v124 : W := 0x5df7fe9142940cd0da1980d8
def v125 : W := 0x5df7fe93d6bd0cd0da018018
def v126 : W := 0x5df7fe93d6bd0cdffe018e38
def v127 : W := 0x5df7feb967d60cd0da1800c0
def v128 : W := 0x5df7feb967d60cdffe180fc0
def v129 : W := 0x5df7febbf7ff00c01801f01f
def v130 : W := 0x5df7febbf7ff0c00c01870c7
def v131 : W := 0x5df7febbf7ff0cd0da1980d8
def v132 : W := 0x5df7febbf7ff0cd0da19f0df
def v133 : W := 0x5df7febbf7ff0cddfe19fdff
def v134 : W := 0x5df7febbf7ff0cdefa19feff
def v135 : W := 0x5df7febbf7ff0cdfda19ffdf
def v136 : W := 0xa20800000000f32f24000000
def v137 : W := 0xa20800bbb7fbf32f2419f0df
def v138 : W := 0xa20801440800332000660000
def v139 : W := 0xa20801440800332d24660d20
def v140 : W := 0xa20801440800c30001860000
def v141 : W := 0xa20801440800c30e21860e20
def v142 : W := 0xa20801440800f00001e00000
def v143 : W := 0xa20801440800f00f01e00f00
def v144 : W := 0xa20801440800f32001e60000
def v145 : W := 0xa20801440800f32f25e60f20
def v146 : W := 0xa208016ebd6b332d24667d27
def v147 : W := 0xa20801ffb800f32001fff000
def v148 : W := 0xa20801ffbffbf32001fff0df
def v149 : W := 0xa20fff440ffff320dbe600df
def v150 : W := 0xa34801469800030000060000
def v151 : W := 0xa34c29469c29030c20060c20
def v152 : W := 0xa34c296ebd6b030c20667d27
def v153 : W := 0xa3780146d800f3f001e7f000
def v154 : W := 0xa3782e004004f3ff3e000000
def v155 : W := 0xa3782f444804f3f03fe60000
def v156 : W := 0xa3782f46d82df0df1be1ff1f
def v157 : W := 0xb608016c2800300000600000
def v158 : W := 0xb60d416c2d42300d00600d00
def v159 : W := 0xb60d416ebd6b300d00667d27
def v160 : W := 0xb638016c6800ff3001fe7000
def v161 : W := 0xb63946004004ff3fe6000000
def v162 : W := 0xb63947444804ff31c7e60000
def v163 : W := 0xb639476c6946cf1ee39e7ee7
def v164 : W := 0xb778016ef800332000667000
def v165 : W := 0xb778016ef80033f00067f000
def v166 : W := 0xb778016ef8003f30007e7000
def v167 : W := 0xb778016ef800f32001e67000
def v168 : W := 0xb77801fff800332001fff000
def v169 : W := 0xb7782f6ef82d332024667027
def v170 : W := 0xb779476ef946332104667107
def v171 : W := 0xb7796f6ef96f332124667127
def v172 : W := 0xb77d6e004004332000000000
def v173 : W := 0xb77d6e004004332d24000000
def v174 : W := 0xb77d6e00400433fd3e000000
def v175 : W := 0xb77d6e0040043f3de6000000
def v176 : W := 0xb77d6e004004f32f24000000
def v177 : W := 0xb77d6f444804332d24660d20
def v178 : W := 0xb77d6f46dc2d332d24060c20
def v179 : W := 0xb77d6f6c6d46332d24600d00
def v180 : W := 0xb77d6f6efd6f030000067007
def v181 : W := 0xb77d6f6efd6f030c20067c27
def v182 : W := 0xb77d6f6efd6f300000607007
def v183 : W := 0xb77d6f6efd6f300d00607d07
def v184 : W := 0xb77d6f6efd6f332000667007
def v185 : W := 0xb77d6f6efd6f332024667027
def v186 : W := 0xb77d6f6efd6f332104667107
def v187 : W := 0xb77d6f6efd6f332d24660d20
def v188 : W := 0xb77d6f6efd6f332d24667d27
def v189 : W := 0xb77ffe004004332ffe000000
def v190 : W := 0xea8801d50800c00001800000
def v191 : W := 0xea8801d50800fff001ff8000
def v192 : W := 0xea8a91d50a903ffdfe7f8df8
def v193 : W := 0xea8e91d50e90c00e01800e00
def v194 : W := 0xea8e91d79eb9c00e01878e38
def v195 : W := 0xea8e91fd2fd2c00e01f80fc0
def v196 : W := 0xebc801d79800c3c001878000
def v197 : W := 0xebc801d79800cfd0019f8000
def v198 : W := 0xebc801d79800f3e001e78000
def v199 : W := 0xebc801ffb800c3c001fff000
def v200 : W := 0xebc801ffbffbc3c0019ff0df
def v201 : W := 0xebc829d79829c3c039878038
def v202 : W := 0xebca91d79a90c3c219878218
def v203 : W := 0xebcab9d79ab9c3c239878238
def v204 : W := 0xebceb8000000c3ce38000000
def v205 : W := 0xebceb9d79eb903c018078018
def v206 : W := 0xebceb9d79eb903cc38078c38
def v207 : W := 0xebceb9d79eb9c0c019818018
def v208 : W := 0xebceb9d79eb9c0ce19818e18
def v209 : W := 0xebceb9d79eb9c30e21860e20
def v210 : W := 0xebceb9d79eb9c3c019878018
def v211 : W := 0xebceb9d79eb9c3c039878038
def v212 : W := 0xebceb9d79eb9c3c219878218
def v213 : W := 0xebceb9d79eb9c3ce39878e38
def v214 : W := 0xebceb9ffbffbc3c019fff0df
def v215 : W := 0xebceb9ffbffbc3ce399ffeff
def v216 : W := 0xebceb9ffbffbc3ce39e7ff3f
def v217 : W := 0xebf801d7d800c3f001878000
def v218 : W := 0xebf801d7d800c3f00187f000
def v219 : W := 0xebf82fd7d804c3f03f878000
def v220 : W := 0xebfebe004004c3fe3e000000
def v221 : W := 0xebfebfd7debdc3de3b878e38
def v222 : W := 0xebfebfd7debdc3ee3d878e38
def v223 : W := 0xebfebfd7debdc3f01b878018
def v224 : W := 0xebfebfd7debdc3f03f878018
def v225 : W := 0xebfebfd7debdc3fe3f878e38
def v226 : W := 0xebfebfd7debdc3ff3f878e38
def v227 : W := 0xfe8801fd2800fc0001f80000
def v228 : W := 0xfe8801fd2800fcd001f98000
def v229 : W := 0xfe8801fd2800ff2001fe0000
def v230 : W := 0xfe8801ffb800fc0001fff000
def v231 : W := 0xfe8801ffbffbfc0001f9f0df
def v232 : W := 0xfe8941fd2942fc01c1f801c0
def v233 : W := 0xfe8a91fd2a90fc02c1f802c0
def v234 : W := 0xfe8bd1fd2bd2fc03c1f803c0
def v235 : W := 0xfe8fd0000000fc0fc0000000
def v236 : W := 0xfe8fd1fd2fd23c00c07800c0
def v237 : W := 0xfe8fd1fd2fd23c0dc0780dc0
def v238 : W := 0xfe8fd1fd2fd2cc00c19800c0
def v239 : W := 0xfe8fd1fd2fd2cc0ec1980ec0
def v240 : W := 0xfe8fd1fd2fd2f00f01e00f00
def v241 : W := 0xfe8fd1fd2fd2fc00c1f800c0
def v242 : W := 0xfe8fd1fd2fd2fc01c1f801c0
def v243 : W := 0xfe8fd1fd2fd2fc02c1f802c0
def v244 : W := 0xfe8fd1fd2fd2fc0fc1f80fc0
def v245 : W := 0xfe8fd1ffbffbfc00c1fff0df
def v246 : W := 0xfe8fd1ffbffbfc0fc1f9ffdf
def v247 : W := 0xfe8fd1ffbffbfc0fc1fe7fe7
def v248 : W := 0xfeb801fd6800fc3001f80000
def v249 : W := 0xfeb801fd6800fc3001f87000
def v250 : W := 0xfeb947fd6804fc31c7f80000
def v251 : W := 0xfebfd6004004fc3fc6000000
def v252 : W := 0xfebfd7fd6fd6fc1fc3f80fc0
def v253 : W := 0xfebfd7fd6fd6fc2fc5f80fc0
def v254 : W := 0xfebfd7fd6fd6fc30c3f800c0
def v255 : W := 0xfebfd7fd6fd6fc31c7f800c0
def v256 : W := 0xfebfd7fd6fd6fc3fc7f80fc0
def v257 : W := 0xfebfd7fd6fd6fc3fe7f80fc0
def v258 : W := 0xffc801ffb800ffc001ff8000
def v259 : W := 0xffcff9ffbffbffcff9ff8ff8
def v260 : W := 0xfff800004000fff000000000
def v261 : W := 0xfff801444800fff001e60000
def v262 : W := 0xfff8016ef800fff000667000
def v263 : W := 0xfff801d7d800fff001878000
def v264 : W := 0xfff801fd6800fff001f80000
def v265 : W := 0xfff801fff8003ff0007ff000
def v266 : W := 0xfff801fff800cfd0019ff000
def v267 : W := 0xfff801fff800f3e001e7f000
def v268 : W := 0xfff801fff800fcd001f9f000
def v269 : W := 0xfff801fff800ff2001fe7000
def v270 : W := 0xfff801fff800fff001fff000
def v271 : W := 0xfff801fffffbfff001fff0df
def v272 : W := 0xfff829fff829fff039fff038
def v273 : W := 0xfff82e004004fff03e000000
def v274 : W := 0xfff82fd7d82dfff03f878038
def v275 : W := 0xfff82ffd6804fff03ff80000
def v276 : W := 0xfff82ffff804fff03ffff000
def v277 : W := 0xfff82ffff82dfff01bfff01f
def v278 : W := 0xfff82ffff82dfff025fff027
def v279 : W := 0xfff941fff942fff1c1fff1c0
def v280 : W := 0xfff946004004fff1c6000000
def v281 : W := 0xfff947d7d804fff1c7878000
def v282 : W := 0xfff947fd6946fff1c7f801c0
def v283 : W := 0xfff947fff804fff1c7fff000
def v284 : W := 0xfff947fff946fff0c3fff0c7
def v285 : W := 0xfff947fff946fff105fff107
def v286 : W := 0xfffa91fff800fff2dbfff000
def v287 : W := 0xfffa91fffa90fff0dbfff0d8
def v288 : W := 0xfffa91fffa90fff219fff218
def v289 : W := 0xfffa91fffa90fff2c1fff2c0
def v290 : W := 0xfffd6e004004fffd24000000
def v291 : W := 0xfffd6ffffd6ffff001fff007
def v292 : W := 0xfffd6ffffd6ffffd25fffd27
def v293 : W := 0xfffeb9fffeb9fff019fff018
def v294 : W := 0xfffeb9fffeb9fffe39fffe38
def v295 : W := 0xffffd1ffffd2fff0c1fff0c0
def v296 : W := 0xffffd1ffffd2ffffc1ffffc0
def v297 : W := 0xfffffe0040043ffdfe000000
def v298 : W := 0xfffffe004004cfdefa000000
def v299 : W := 0xfffffe004004f3ef3c000000
def v300 : W := 0xfffffe004004fcdfda000000
def v301 : W := 0xfffffe004004ff2fe4000000
def v302 : W := 0xfffffe004004fff0da000000
def v303 : W := 0xfffffe004004fffffe000000
def v304 : W := 0xfffffe0046bdfffffe000e38
def v305 : W := 0xfffffe0047d6fffffe000fc0
def v306 : W := 0xfffffe02d02dfffffe078038
def v307 : W := 0xfffffe286146fffffe7801c0
def v308 : W := 0xfffffe914004ffffff998000
def v309 : W := 0xfffffe914294fffffe1980d8
def v310 : W := 0xfffffe914294ffffff818218
def v311 : W := 0xfffffe914294ffffff9802c0
def v312 : W := 0xfffffe93d6bdfffffe018018
def v313 : W := 0xfffffeb967d6fffffe1800c0
def v314 : W := 0xfffffebbf7fffffffe19f0df
def v315 : W := 0xffffff444804fff0dbe60000
def v316 : W := 0xffffff444804fffffe660d20
def v317 : W := 0xffffff444804ffffff860e20
def v318 : W := 0xffffff444804ffffffe00f00
def v319 : W := 0xffffff444804ffffffe60000
def v320 : W := 0xffffff46dc2dfffffe060c20
def v321 : W := 0xffffff6c6d46fffffe600d00
def v322 : W := 0xffffff6efd6ffffffe667d27
def v323 : W := 0xffffffd54e94ffffff800e00
def v324 : W := 0xffffffd7d804cfd0db878000
def v325 : W := 0xffffffd7d804ffffff878000
def v326 : W := 0xffffffd7debdc3ce39878e38
def v327 : W := 0xffffffd7debdcfdefb878e38
def v328 : W := 0xffffffd7debdf3ef3d878e38
def v329 : W := 0xffffffd7debdfff0db878018
def v330 : W := 0xffffffd7debdffffff878018
def v331 : W := 0xffffffd7debdffffff878e38
def v332 : W := 0xfffffffd6804fcd0dbf80000
def v333 : W := 0xfffffffd6804fffffff80000
def v334 : W := 0xfffffffd6fd6fc0fc1f80fc0
def v335 : W := 0xfffffffd6fd6fcdfdbf80fc0
def v336 : W := 0xfffffffd6fd6ff2fe5f80fc0
def v337 : W := 0xfffffffd6fd6fff0dbf800c0
def v338 : W := 0xfffffffd6fd6fffffff800c0
def v339 : W := 0xfffffffd6fd6fffffff80fc0
def v340 : W := 0xfffffffff804fff0dbfff000
def v341 : W := 0xfffffffff804fffffffff000
def v342 : W := 0xffffffffffff3ff0da7ff0df
def v343 : W := 0xffffffffffff3ffdfe7ffdff
def v344 : W := 0xffffffffffffcfd0db9ff0df
def v345 : W := 0xffffffffffffcfdefb9ffeff
def v346 : W := 0xfffffffffffff3ef3de7ff3f
def v347 : W := 0xfffffffffffffcd0dbf9f0df
def v348 : W := 0xfffffffffffffcdfdbf9ffdf
def v349 : W := 0xffffffffffffff2fe5fe7fe7
def v350 : W := 0xfffffffffffffff0dbfff0df
def v351 : W := 0xffffffffffffffffffff8ff8

def ins : List W := [v132, v188, v213, v244, v270, v303]
theorem sampled : ∀ j : Fin 96, Nat.testBit 0xe888a888e880a880 (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
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
def level3 : BinaryTree (List W) := (.node [v132, v187, v193, v270] (.node [v111, v182, v213, v303] (.node [v92, v213, v236, v303] (.node [v92, v205, v244, v303] (.node [v90, v132, v188, v270] .nil .nil) .nil) (.node [v106, v180, v244, v303] .nil .nil)) (.node [v132, v184, v213, v256] (.node [v131, v188, v193, v270] .nil .nil) (.node [v132, v184, v225, v244] .nil .nil))) (.node [v132, v188, v223, v244] (.node [v132, v188, v213, v254] (.node [v132, v188, v210, v257] (.node [v132, v188, v210, v256] .nil .nil) .nil) (.node [v132, v188, v213, v255] .nil .nil)) (.node [v132, v188, v225, v241] (.node [v132, v188, v224, v244] .nil .nil) (.node [v132, v188, v226, v241] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level3_ok : everyKey (rowOK 2 level2) level3 = true := by decide +kernel
theorem closed3 : Closed 3 level3 := closed_next 2 (by decide) level3 level2 closed2 level3_ok
def level4ll : BinaryTree (List W) := (.node [v42, v132, v188, v213, v244] (.node [v23, v132, v188, v213, v256] (.node [v10, v132, v188, v210, v244] (.node [v8, v132, v188, v213, v241] (.node [v8, v132, v188, v210, v244] (.node [v8, v132, v184, v213, v244] .nil .nil) .nil) (.node [v10, v132, v184, v213, v244] (.node [v9, v132, v184, v213, v244] .nil .nil) .nil)) (.node [v20, v132, v188, v210, v244] (.node [v20, v132, v184, v213, v244] (.node [v10, v132, v188, v213, v241] .nil .nil) .nil) (.node [v20, v132, v188, v213, v241] .nil .nil))) (.node [v27, v132, v188, v225, v244] (.node [v25, v132, v188, v225, v244] (.node [v25, v132, v188, v213, v256] (.node [v23, v132, v188, v225, v244] .nil .nil) .nil) (.node [v26, v132, v188, v213, v244] .nil .nil)) (.node [v29, v132, v188, v213, v244] (.node [v28, v132, v188, v225, v244] (.node [v28, v132, v188, v213, v256] .nil .nil) .nil) (.node [v30, v132, v188, v213, v256] .nil .nil)))) (.node [v59, v132, v188, v213, v270] (.node [v50, v132, v188, v213, v241] (.node [v50, v132, v184, v213, v244] (.node [v45, v132, v188, v213, v270] (.node [v44, v79, v132, v188, v270] .nil .nil) .nil) (.node [v50, v132, v188, v210, v244] .nil .nil)) (.node [v56, v132, v188, v210, v303] (.node [v56, v132, v184, v213, v303] (.node [v51, v132, v188, v213, v241] .nil .nil) .nil) (.node [v57, v66, v132, v188, v270] .nil .nil))) (.node [v67, v132, v188, v244, v270] (.node [v64, v132, v188, v213, v244] (.node [v62, v132, v188, v213, v303] (.node [v61, v132, v188, v213, v244] .nil .nil) .nil) (.node [v65, v132, v188, v213, v244] .nil .nil)) (.node [v72, v132, v188, v213, v241] (.node [v72, v132, v188, v210, v244] (.node [v72, v132, v184, v213, v244] .nil .nil) .nil) (.node [v73, v132, v188, v210, v244] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4ll_ok : everyKey (rowOK 3 level3) level4ll = true := by decide +kernel
def level4lr : BinaryTree (List W) := (.node [v117, v132, v184, v213, v244] (.node [v99, v132, v210, v244, v303] (.node [v87, v132, v188, v213, v244] (.node [v83, v132, v188, v244, v303] (.node [v81, v132, v188, v244, v270] (.node [v78, v132, v188, v241, v303] .nil .nil) .nil) (.node [v86, v132, v188, v213, v244] (.node [v84, v132, v188, v213, v244] .nil .nil) .nil)) (.node [v92, v213, v237, v270, v303] (.node [v92, v206, v244, v270, v303] (.node [v88, v132, v188, v270, v303] .nil .nil) .nil) (.node [v92, v213, v244, v303, v342] .nil .nil))) (.node [v106, v188, v244, v303, v344] (.node [v103, v132, v213, v244, v303] (.node [v102, v132, v213, v244, v270] (.node [v99, v132, v213, v241, v303] .nil .nil) .nil) (.node [v106, v181, v244, v270, v303] .nil .nil)) (.node [v111, v188, v213, v303, v347] (.node [v111, v183, v213, v270, v303] (.node [v110, v132, v213, v270, v303] .nil .nil) .nil) (.node [v115, v132, v244, v270, v303] .nil .nil)))) (.node [v132, v144, v188, v213, v256] (.node [v126, v132, v188, v213, v244] (.node [v122, v132, v188, v213, v244] (.node [v117, v132, v188, v213, v241] (.node [v117, v132, v188, v210, v244] .nil .nil) .nil) (.node [v123, v132, v188, v213, v244] .nil .nil)) (.node [v130, v158, v213, v270, v303] (.node [v129, v151, v244, v270, v303] (.node [v128, v132, v188, v213, v244] .nil .nil) .nil) (.node [v131, v188, v213, v244, v270] .nil .nil))) (.node [v132, v164, v188, v213, v256] (.node [v132, v155, v188, v213, v244] (.node [v132, v148, v188, v213, v244] (.node [v132, v144, v188, v225, v244] .nil .nil) .nil) (.node [v132, v162, v188, v213, v244] .nil .nil)) (.node [v132, v172, v184, v213, v244] (.node [v132, v171, v213, v244, v303] (.node [v132, v164, v188, v225, v244] .nil .nil) .nil) (.node [v132, v173, v184, v213, v244] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lr_ok : everyKey (rowOK 3 level3) level4lr = true := by decide +kernel
def level4l : BinaryTree (List W) := .node [v78, v132, v184, v244, v303] level4ll level4lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4l_ok : everyKey (rowOK 3 level3) level4l = true := by
  change (_ && everyKey (rowOK 3 level3) level4ll && everyKey (rowOK 3 level3) level4lr) = true
  rw [level4ll_ok, level4lr_ok]
  decide +kernel
def level4rl : BinaryTree (List W) := (.node [v132, v188, v202, v244, v331] (.node [v132, v186, v213, v244, v303] (.node [v132, v184, v213, v244, v302] (.node [v132, v182, v213, v244, v303] (.node [v132, v180, v213, v244, v303] (.node [v132, v173, v188, v213, v241] .nil .nil) .nil) (.node [v132, v184, v213, v241, v303] (.node [v132, v184, v210, v244, v303] .nil .nil) .nil)) (.node [v132, v184, v213, v244, v339] (.node [v132, v184, v213, v244, v331] (.node [v132, v184, v213, v244, v303] .nil .nil) .nil) (.node [v132, v185, v213, v244, v303] .nil .nil))) (.node [v132, v188, v196, v213, v256] (.node [v132, v188, v194, v270, v339] (.node [v132, v188, v193, v270, v351] (.node [v132, v187, v213, v244, v270] .nil .nil) .nil) (.node [v132, v188, v195, v270, v331] .nil .nil)) (.node [v132, v188, v199, v213, v256] (.node [v132, v188, v196, v244, v328] (.node [v132, v188, v196, v225, v244] .nil .nil) .nil) (.node [v132, v188, v200, v213, v244] .nil .nil)))) (.node [v132, v188, v211, v244, v303] (.node [v132, v188, v210, v244, v302] (.node [v132, v188, v207, v244, v303] (.node [v132, v188, v205, v244, v303] (.node [v132, v188, v203, v244, v303] .nil .nil) .nil) (.node [v132, v188, v210, v241, v303] .nil .nil)) (.node [v132, v188, v210, v244, v331] (.node [v132, v188, v210, v244, v330] (.node [v132, v188, v210, v244, v303] .nil .nil) .nil) (.node [v132, v188, v210, v244, v339] .nil .nil))) (.node [v132, v188, v213, v227, v336] (.node [v132, v188, v213, v219, v244] (.node [v132, v188, v213, v214, v244] (.node [v132, v188, v212, v244, v303] .nil .nil) .nil) (.node [v132, v188, v213, v227, v256] .nil .nil)) (.node [v132, v188, v213, v234, v303] (.node [v132, v188, v213, v233, v339] (.node [v132, v188, v213, v231, v244] .nil .nil) .nil) (.node [v132, v188, v213, v236, v303] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rl_ok : everyKey (rowOK 3 level3) level4rl = true := by decide +kernel
def level4rr : BinaryTree (List W) := (.node [v132, v188, v213, v252, v270] (.node [v132, v188, v213, v244, v274] (.node [v132, v188, v213, v241, v339] (.node [v132, v188, v213, v241, v331] (.node [v132, v188, v213, v241, v303] (.node [v132, v188, v213, v241, v302] .nil .nil) .nil) (.node [v132, v188, v213, v241, v338] .nil .nil)) (.node [v132, v188, v213, v244, v245] (.node [v132, v188, v213, v243, v303] (.node [v132, v188, v213, v242, v303] .nil .nil) .nil) (.node [v132, v188, v213, v244, v250] .nil .nil))) (.node [v132, v188, v213, v244, v324] (.node [v132, v188, v213, v244, v282] (.node [v132, v188, v213, v244, v281] (.node [v132, v188, v213, v244, v275] .nil .nil) .nil) (.node [v132, v188, v213, v244, v315] .nil .nil)) (.node [v132, v188, v213, v244, v337] (.node [v132, v188, v213, v244, v332] (.node [v132, v188, v213, v244, v329] .nil .nil) .nil) (.node [v132, v188, v213, v248, v256] .nil .nil)))) (.node [v132, v188, v225, v230, v244] (.node [v132, v188, v213, v270, v334] (.node [v132, v188, v213, v256, v283] (.node [v132, v188, v213, v256, v270] (.node [v132, v188, v213, v253, v270] .nil .nil) .nil) (.node [v132, v188, v213, v256, v350] .nil .nil)) (.node [v132, v188, v222, v244, v270] (.node [v132, v188, v221, v244, v270] (.node [v132, v188, v217, v225, v244] .nil .nil) .nil) (.node [v132, v188, v225, v227, v244] .nil .nil))) (.node [v137, v188, v213, v244, v270] (.node [v132, v188, v225, v244, v350] (.node [v132, v188, v225, v244, v276] (.node [v132, v188, v225, v244, v270] .nil .nil) .nil) (.node [v132, v188, v244, v270, v326] .nil .nil)) (.node [v163, v188, v244, v270, v303] (.node [v156, v188, v213, v270, v303] (.node [v149, v188, v213, v244, v303] .nil .nil) .nil) (.node [v192, v213, v244, v270, v303] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rr_ok : everyKey (rowOK 3 level3) level4rr = true := by decide +kernel
def level4r : BinaryTree (List W) := .node [v132, v188, v213, v238, v303] level4rl level4rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4r_ok : everyKey (rowOK 3 level3) level4r = true := by
  change (_ && everyKey (rowOK 3 level3) level4rl && everyKey (rowOK 3 level3) level4rr) = true
  rw [level4rl_ok, level4rr_ok]
  decide +kernel
def level4 : BinaryTree (List W) := .node [v132, v173, v188, v210, v244] level4l level4r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4_ok : everyKey (rowOK 3 level3) level4 = true := by
  change (_ && everyKey (rowOK 3 level3) level4l && everyKey (rowOK 3 level3) level4r) = true
  rw [level4l_ok, level4r_ok]
  decide +kernel
theorem closed4 : Closed 4 level4 := closed_next 3 (by decide) level4 level3 closed3 level4_ok
def level5lll : BinaryTree (List W) := (.node [v10, v28, v132, v188, v213, v244] (.node [v8, v117, v188, v213, v244, v270] (.node [v5, v132, v188, v213, v244, v270] (.node [v2, v132, v188, v213, v244, v303] (.node [v1, v132, v188, v213, v244, v303] (.node [v0, v132, v188, v213, v244, v303] .nil .nil) .nil) (.node [v4, v132, v188, v213, v244, v270] (.node [v3, v132, v188, v213, v244, v270] .nil .nil) .nil)) (.node [v8, v23, v132, v188, v213, v244] (.node [v7, v132, v188, v213, v244, v270] (.node [v6, v132, v188, v213, v244, v270] .nil .nil) .nil) (.node [v8, v28, v132, v188, v213, v244] (.node [v8, v25, v132, v188, v213, v244] .nil .nil) .nil))) (.node [v8, v132, v188, v213, v244, v270] (.node [v8, v132, v188, v196, v213, v244] (.node [v8, v132, v164, v188, v213, v244] (.node [v8, v132, v144, v188, v213, v244] .nil .nil) .nil) (.node [v8, v132, v188, v213, v244, v261] (.node [v8, v132, v188, v213, v227, v244] .nil .nil) .nil)) (.node [v8, v136, v188, v213, v244, v270] (.node [v8, v132, v188, v213, v244, v350] (.node [v8, v132, v188, v213, v244, v271] .nil .nil) .nil) (.node [v10, v25, v132, v188, v213, v244] (.node [v10, v23, v132, v188, v213, v244] .nil .nil) .nil)))) (.node [v14, v132, v188, v213, v244, v270] (.node [v10, v132, v188, v213, v227, v244] (.node [v10, v132, v164, v188, v213, v244] (.node [v10, v132, v144, v188, v213, v244] (.node [v10, v95, v132, v213, v244, v270] .nil .nil) .nil) (.node [v10, v132, v188, v196, v213, v244] (.node [v10, v132, v173, v213, v244, v270] .nil .nil) .nil)) (.node [v11, v72, v132, v188, v244, v270] (.node [v10, v132, v188, v213, v244, v350] (.node [v10, v132, v188, v213, v244, v270] .nil .nil) .nil) (.node [v13, v32, v132, v188, v213, v244] (.node [v12, v50, v132, v188, v213, v270] .nil .nil) .nil))) (.node [v20, v132, v188, v213, v244, v270] (.node [v17, v132, v188, v213, v244, v270] (.node [v16, v132, v188, v213, v244, v270] (.node [v15, v132, v188, v213, v244, v270] .nil .nil) .nil) (.node [v19, v132, v188, v213, v244, v270] (.node [v18, v132, v188, v213, v244, v270] .nil .nil) .nil)) (.node [v22, v132, v188, v213, v244, v303] (.node [v21, v132, v188, v213, v244, v303] (.node [v20, v132, v188, v213, v244, v350] .nil .nil) .nil) (.node [v23, v50, v132, v188, v213, v244] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lll_ok : everyKey (rowOK 4 level4) level5lll = true := by decide +kernel
def level5llr : BinaryTree (List W) := (.node [v28, v132, v173, v188, v213, v244] (.node [v25, v117, v132, v188, v213, v244] (.node [v23, v132, v188, v213, v244, v331] (.node [v23, v132, v164, v213, v244, v303] (.node [v23, v117, v132, v188, v213, v244] (.node [v23, v94, v132, v213, v244, v303] .nil .nil) .nil) (.node [v23, v132, v188, v213, v244, v303] (.node [v23, v132, v173, v188, v213, v244] .nil .nil) .nil)) (.node [v25, v50, v132, v188, v213, v244] (.node [v24, v132, v188, v213, v244, v303] (.node [v23, v132, v188, v213, v244, v339] .nil .nil) .nil) (.node [v25, v72, v132, v188, v213, v244] (.node [v25, v69, v132, v188, v244, v303] .nil .nil) .nil))) (.node [v25, v132, v188, v213, v244, v331] (.node [v25, v132, v188, v213, v244, v280] (.node [v25, v132, v188, v196, v244, v303] (.node [v25, v132, v173, v188, v213, v244] .nil .nil) .nil) (.node [v25, v132, v188, v213, v244, v304] (.node [v25, v132, v188, v213, v244, v303] .nil .nil) .nil)) (.node [v28, v50, v132, v188, v213, v244] (.node [v28, v47, v132, v188, v213, v303] (.node [v25, v132, v188, v213, v244, v339] .nil .nil) .nil) (.node [v28, v117, v132, v188, v213, v244] (.node [v28, v72, v132, v188, v213, v244] .nil .nil) .nil)))) (.node [v35, v132, v188, v213, v244, v339] (.node [v28, v132, v188, v213, v244, v339] (.node [v28, v132, v188, v213, v244, v303] (.node [v28, v132, v188, v213, v244, v273] (.node [v28, v132, v188, v213, v227, v303] .nil .nil) .nil) (.node [v28, v132, v188, v213, v244, v331] (.node [v28, v132, v188, v213, v244, v305] .nil .nil) .nil)) (.node [v34, v132, v188, v213, v244, v303] (.node [v33, v132, v188, v213, v244, v303] (.node [v31, v132, v188, v213, v244, v303] .nil .nil) .nil) (.node [v35, v132, v188, v213, v244, v303] (.node [v34, v132, v188, v213, v244, v331] .nil .nil) .nil))) (.node [v41, v132, v188, v213, v244, v303] (.node [v38, v132, v188, v213, v244, v303] (.node [v37, v132, v188, v213, v244, v303] (.node [v36, v144, v188, v213, v244, v303] .nil .nil) .nil) (.node [v40, v132, v188, v213, v244, v303] (.node [v39, v132, v188, v213, v244, v303] .nil .nil) .nil)) (.node [v44, v132, v188, v213, v270, v339] (.node [v44, v66, v132, v188, v270, v303] (.node [v43, v132, v188, v213, v244, v270] .nil .nil) .nil) (.node [v46, v132, v188, v213, v244, v303] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llr_ok : everyKey (rowOK 4 level4) level5llr = true := by decide +kernel
def level5ll : BinaryTree (List W) := .node [v23, v72, v132, v188, v213, v244] level5lll level5llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5ll_ok : everyKey (rowOK 4 level4) level5ll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lll && everyKey (rowOK 4 level4) level5llr) = true
  rw [level5lll_ok, level5llr_ok]
  decide +kernel
def level5lrl : BinaryTree (List W) := (.node [v63, v132, v188, v213, v244, v270] (.node [v50, v132, v188, v225, v244, v270] (.node [v50, v132, v188, v213, v227, v244] (.node [v50, v132, v164, v188, v213, v244] (.node [v50, v132, v144, v188, v213, v244] (.node [v49, v132, v188, v213, v244, v270] .nil .nil) .nil) (.node [v50, v132, v188, v196, v213, v244] (.node [v50, v132, v188, v194, v244, v270] .nil .nil) .nil)) (.node [v50, v132, v188, v213, v244, v276] (.node [v50, v132, v188, v213, v244, v270] (.node [v50, v132, v188, v213, v230, v244] .nil .nil) .nil) (.node [v50, v132, v188, v213, v270, v339] (.node [v50, v132, v188, v213, v244, v350] .nil .nil) .nil))) (.node [v56, v132, v188, v213, v270, v303] (.node [v53, v98, v132, v213, v270, v303] (.node [v52, v143, v188, v213, v270, v303] (.node [v52, v132, v188, v213, v227, v303] .nil .nil) .nil) (.node [v55, v132, v188, v213, v270, v303] (.node [v54, v132, v188, v213, v270, v303] .nil .nil) .nil)) (.node [v58, v132, v188, v213, v270, v303] (.node [v57, v132, v188, v213, v244, v270] (.node [v56, v132, v188, v213, v303, v350] .nil .nil) .nil) (.node [v63, v132, v188, v213, v227, v244] (.node [v60, v132, v188, v213, v244, v303] .nil .nil) .nil)))) (.node [v72, v132, v188, v213, v244, v283] (.node [v72, v132, v164, v188, v213, v244] (.node [v70, v132, v188, v213, v244, v270] (.node [v68, v132, v188, v213, v244, v303] (.node [v66, v132, v188, v244, v270, v331] .nil .nil) .nil) (.node [v72, v132, v144, v188, v213, v244] (.node [v71, v132, v188, v213, v244, v270] .nil .nil) .nil)) (.node [v72, v132, v188, v199, v213, v244] (.node [v72, v132, v188, v196, v213, v244] (.node [v72, v132, v188, v195, v213, v270] .nil .nil) .nil) (.node [v72, v132, v188, v213, v244, v270] (.node [v72, v132, v188, v213, v227, v244] .nil .nil) .nil))) (.node [v75, v97, v132, v244, v270, v303] (.node [v72, v132, v188, v244, v270, v331] (.node [v72, v132, v188, v213, v256, v270] (.node [v72, v132, v188, v213, v244, v350] .nil .nil) .nil) (.node [v74, v141, v188, v244, v270, v303] (.node [v74, v132, v188, v196, v244, v303] .nil .nil) .nil)) (.node [v78, v132, v188, v244, v270, v303] (.node [v77, v132, v188, v244, v270, v303] (.node [v76, v132, v188, v244, v270, v303] .nil .nil) .nil) (.node [v78, v132, v188, v244, v303, v350] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrl_ok : everyKey (rowOK 4 level4) level5lrl = true := by decide +kernel
def level5lrr : BinaryTree (List W) := (.node [v111, v132, v188, v213, v227, v303] (.node [v99, v132, v213, v244, v270, v303] (.node [v91, v132, v188, v213, v244, v270] (.node [v85, v132, v188, v196, v213, v244] (.node [v82, v132, v188, v213, v244, v303] (.node [v80, v132, v188, v244, v270, v303] .nil .nil) .nil) (.node [v89, v132, v188, v213, v244, v270] (.node [v85, v132, v188, v213, v244, v270] .nil .nil) .nil)) (.node [v93, v132, v188, v213, v244, v303] (.node [v92, v213, v244, v270, v303, v343] (.node [v92, v132, v164, v213, v244, v303] .nil .nil) .nil) (.node [v96, v139, v213, v244, v270, v303] (.node [v96, v132, v164, v213, v244, v303] .nil .nil) .nil))) (.node [v106, v132, v188, v196, v244, v303] (.node [v101, v132, v188, v213, v244, v270] (.node [v100, v132, v213, v244, v270, v303] (.node [v99, v132, v213, v244, v303, v350] .nil .nil) .nil) (.node [v105, v132, v188, v213, v244, v303] (.node [v104, v132, v188, v213, v244, v303] .nil .nil) .nil)) (.node [v108, v132, v188, v213, v244, v270] (.node [v107, v132, v188, v213, v244, v303] (.node [v106, v188, v244, v270, v303, v345] .nil .nil) .nil) (.node [v109, v132, v188, v213, v244, v270] .nil .nil)))) (.node [v117, v132, v188, v213, v244, v340] (.node [v117, v132, v144, v188, v213, v244] (.node [v113, v132, v188, v213, v244, v270] (.node [v112, v132, v188, v213, v244, v303] (.node [v111, v188, v213, v270, v303, v348] .nil .nil) .nil) (.node [v116, v188, v213, v244, v303, v350] (.node [v114, v132, v188, v213, v244, v270] .nil .nil) .nil)) (.node [v117, v132, v188, v196, v213, v244] (.node [v117, v132, v164, v188, v213, v244] (.node [v117, v132, v147, v188, v213, v244] .nil .nil) .nil) (.node [v117, v132, v188, v213, v244, v270] (.node [v117, v132, v188, v213, v227, v244] .nil .nil) .nil))) (.node [v120, v132, v188, v213, v244, v270] (.node [v118, v132, v144, v188, v213, v244] (.node [v117, v188, v213, v244, v270, v314] (.node [v117, v132, v188, v213, v244, v350] .nil .nil) .nil) (.node [v119, v132, v188, v213, v244, v270] (.node [v118, v132, v188, v213, v244, v270] .nil .nil) .nil)) (.node [v125, v132, v188, v213, v244, v270] (.node [v124, v132, v188, v213, v244, v270] (.node [v121, v132, v188, v213, v244, v270] .nil .nil) .nil) (.node [v127, v132, v188, v213, v244, v270] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrr_ok : everyKey (rowOK 4 level4) level5lrr = true := by decide +kernel
def level5lr : BinaryTree (List W) := .node [v79, v132, v188, v213, v244, v270] level5lrl level5lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lr_ok : everyKey (rowOK 4 level4) level5lr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrl && everyKey (rowOK 4 level4) level5lrr) = true
  rw [level5lrl_ok, level5lrr_ok]
  decide +kernel
def level5l : BinaryTree (List W) := .node [v48, v132, v188, v213, v244, v270] level5ll level5lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5l_ok : everyKey (rowOK 4 level4) level5l = true := by
  change (_ && everyKey (rowOK 4 level4) level5ll && everyKey (rowOK 4 level4) level5lr) = true
  rw [level5ll_ok, level5lr_ok]
  decide +kernel
def level5rll : BinaryTree (List W) := (.node [v132, v161, v188, v213, v244, v270] (.node [v132, v144, v188, v213, v244, v339] (.node [v132, v140, v188, v213, v244, v303] (.node [v132, v134, v188, v213, v244, v303] (.node [v132, v133, v188, v213, v244, v303] (.node [v130, v188, v213, v244, v270, v303] .nil .nil) .nil) (.node [v132, v138, v188, v213, v244, v303] (.node [v132, v135, v188, v213, v244, v303] .nil .nil) .nil)) (.node [v132, v144, v188, v213, v244, v303] (.node [v132, v144, v173, v188, v213, v244] (.node [v132, v142, v188, v213, v244, v303] .nil .nil) .nil) (.node [v132, v144, v188, v213, v244, v331] (.node [v132, v144, v188, v213, v244, v319] .nil .nil) .nil))) (.node [v132, v153, v188, v213, v244, v303] (.node [v132, v150, v188, v213, v244, v303] (.node [v132, v147, v188, v213, v244, v303] (.node [v132, v146, v188, v213, v244, v270] .nil .nil) .nil) (.node [v132, v152, v188, v213, v244, v270] (.node [v132, v151, v244, v270, v303, v346] .nil .nil) .nil)) (.node [v132, v158, v213, v270, v303, v349] (.node [v132, v157, v188, v213, v244, v303] (.node [v132, v154, v188, v213, v244, v270] .nil .nil) .nil) (.node [v132, v160, v188, v213, v244, v303] (.node [v132, v159, v188, v213, v244, v270] .nil .nil) .nil)))) (.node [v132, v173, v188, v196, v213, v244] (.node [v132, v165, v188, v213, v244, v303] (.node [v132, v164, v188, v213, v244, v331] (.node [v132, v164, v188, v213, v244, v303] (.node [v132, v164, v173, v188, v213, v244] .nil .nil) .nil) (.node [v132, v164, v213, v244, v292, v303] (.node [v132, v164, v188, v213, v244, v339] .nil .nil) .nil)) (.node [v132, v168, v188, v213, v244, v303] (.node [v132, v167, v188, v213, v244, v303] (.node [v132, v166, v188, v213, v244, v303] .nil .nil) .nil) (.node [v132, v170, v188, v213, v244, v303] (.node [v132, v169, v188, v213, v244, v303] .nil .nil) .nil))) (.node [v132, v175, v188, v213, v244, v270] (.node [v132, v173, v188, v213, v244, v350] (.node [v132, v173, v188, v213, v244, v270] (.node [v132, v173, v188, v213, v227, v244] .nil .nil) .nil) (.node [v132, v174, v188, v213, v244, v270] (.node [v132, v173, v213, v244, v270, v322] .nil .nil) .nil)) (.node [v132, v178, v188, v213, v244, v270] (.node [v132, v177, v188, v213, v244, v270] (.node [v132, v176, v188, v213, v244, v270] .nil .nil) .nil) (.node [v132, v179, v188, v213, v244, v270] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rll_ok : everyKey (rowOK 4 level4) level5rll = true := by decide +kernel
def level5rlr : BinaryTree (List W) := (.node [v132, v188, v202, v213, v244, v303] (.node [v132, v188, v194, v244, v270, v303] (.node [v132, v188, v189, v213, v244, v270] (.node [v132, v184, v213, v244, v270, v303] (.node [v132, v184, v188, v213, v244, v303] (.node [v132, v183, v213, v244, v270, v303] .nil .nil) .nil) (.node [v132, v184, v213, v244, v303, v350] (.node [v132, v184, v213, v244, v303] .nil .nil) .nil)) (.node [v132, v188, v193, v213, v270, v339] (.node [v132, v188, v191, v213, v244, v303] (.node [v132, v188, v190, v213, v244, v303] .nil .nil) .nil) (.node [v132, v188, v193, v259, v270, v303] (.node [v132, v188, v193, v244, v270, v331] .nil .nil) .nil))) (.node [v132, v188, v196, v244, v294, v303] (.node [v132, v188, v196, v213, v244, v325] (.node [v132, v188, v196, v213, v244, v303] (.node [v132, v188, v195, v213, v270, v303] .nil .nil) .nil) (.node [v132, v188, v196, v213, v244, v339] (.node [v132, v188, v196, v213, v244, v331] .nil .nil) .nil)) (.node [v132, v188, v199, v213, v244, v303] (.node [v132, v188, v198, v213, v244, v303] (.node [v132, v188, v197, v213, v244, v303] .nil .nil) .nil) (.node [v132, v188, v201, v213, v244, v303] .nil .nil)))) (.node [v132, v188, v213, v220, v244, v270] (.node [v132, v188, v210, v244, v270, v303] (.node [v132, v188, v208, v244, v270, v303] (.node [v132, v188, v206, v244, v270, v303] (.node [v132, v188, v204, v244, v270, v331] .nil .nil) .nil) (.node [v132, v188, v210, v213, v244, v303] (.node [v132, v188, v209, v244, v270, v303] .nil .nil) .nil)) (.node [v132, v188, v213, v215, v244, v270] (.node [v132, v188, v210, v244, v303, v350] (.node [v132, v188, v210, v244, v303] .nil .nil) .nil) (.node [v132, v188, v213, v218, v244, v303] (.node [v132, v188, v213, v216, v244, v270] .nil .nil) .nil))) (.node [v132, v188, v213, v227, v296, v303] (.node [v132, v188, v213, v227, v244, v331] (.node [v132, v188, v213, v227, v244, v303] (.node [v132, v188, v213, v225, v244, v270] .nil .nil) .nil) (.node [v132, v188, v213, v227, v244, v339] (.node [v132, v188, v213, v227, v244, v333] .nil .nil) .nil)) (.node [v132, v188, v213, v230, v244, v303] (.node [v132, v188, v213, v229, v244, v303] (.node [v132, v188, v213, v228, v244, v303] .nil .nil) .nil) (.node [v132, v188, v213, v232, v244, v303] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlr_ok : everyKey (rowOK 4 level4) level5rlr = true := by decide +kernel
def level5rl : BinaryTree (List W) := .node [v132, v181, v213, v244, v270, v303] level5rll level5rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rl_ok : everyKey (rowOK 4 level4) level5rl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rll && everyKey (rowOK 4 level4) level5rlr) = true
  rw [level5rll_ok, level5rlr_ok]
  decide +kernel
def level5rrl : BinaryTree (List W) := (.node [v132, v188, v213, v244, v267, v303] (.node [v132, v188, v213, v244, v251, v270] (.node [v132, v188, v213, v241, v270, v303] (.node [v132, v188, v213, v239, v270, v303] (.node [v132, v188, v213, v237, v270, v303] (.node [v132, v188, v213, v235, v270, v339] .nil .nil) .nil) (.node [v132, v188, v213, v241, v244, v303] (.node [v132, v188, v213, v240, v270, v303] .nil .nil) .nil)) (.node [v132, v188, v213, v244, v246, v270] (.node [v132, v188, v213, v241, v303, v350] (.node [v132, v188, v213, v241, v303] .nil .nil) .nil) (.node [v132, v188, v213, v244, v249, v303] (.node [v132, v188, v213, v244, v247, v270] .nil .nil) .nil))) (.node [v132, v188, v213, v244, v263, v303] (.node [v132, v188, v213, v244, v260, v341] (.node [v132, v188, v213, v244, v258, v303] (.node [v132, v188, v213, v244, v256, v270] .nil .nil) .nil) (.node [v132, v188, v213, v244, v262, v303] (.node [v132, v188, v213, v244, v261, v303] .nil .nil) .nil)) (.node [v132, v188, v213, v244, v264, v339] (.node [v132, v188, v213, v244, v264, v303] (.node [v132, v188, v213, v244, v263, v331] .nil .nil) .nil) (.node [v132, v188, v213, v244, v266, v303] (.node [v132, v188, v213, v244, v265, v303] .nil .nil) .nil)))) (.node [v132, v188, v213, v244, v270, v303] (.node [v132, v188, v213, v244, v270, v297] (.node [v132, v188, v213, v244, v270, v273] (.node [v132, v188, v213, v244, v269, v303] (.node [v132, v188, v213, v244, v268, v303] .nil .nil) .nil) (.node [v132, v188, v213, v244, v270, v290] (.node [v132, v188, v213, v244, v270, v280] .nil .nil) .nil)) (.node [v132, v188, v213, v244, v270, v300] (.node [v132, v188, v213, v244, v270, v299] (.node [v132, v188, v213, v244, v270, v298] .nil .nil) .nil) (.node [v132, v188, v213, v244, v270, v302] (.node [v132, v188, v213, v244, v270, v301] .nil .nil) .nil))) (.node [v132, v188, v213, v244, v270, v309] (.node [v132, v188, v213, v244, v270, v306] (.node [v132, v188, v213, v244, v270, v305] (.node [v132, v188, v213, v244, v270, v304] .nil .nil) .nil) (.node [v132, v188, v213, v244, v270, v308] (.node [v132, v188, v213, v244, v270, v307] .nil .nil) .nil)) (.node [v132, v188, v213, v244, v270, v312] (.node [v132, v188, v213, v244, v270, v311] (.node [v132, v188, v213, v244, v270, v310] .nil .nil) .nil) (.node [v132, v188, v213, v244, v270, v313] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrl_ok : everyKey (rowOK 4 level4) level5rrl = true := by decide +kernel
def level5rrr : BinaryTree (List W) := (.node [v132, v188, v213, v244, v284, v303] (.node [v132, v188, v213, v244, v270, v335] (.node [v132, v188, v213, v244, v270, v323] (.node [v132, v188, v213, v244, v270, v319] (.node [v132, v188, v213, v244, v270, v318] (.node [v132, v188, v213, v244, v270, v317] .nil .nil) .nil) (.node [v132, v188, v213, v244, v270, v321] (.node [v132, v188, v213, v244, v270, v320] .nil .nil) .nil)) (.node [v132, v188, v213, v244, v270, v328] (.node [v132, v188, v213, v244, v270, v327] (.node [v132, v188, v213, v244, v270, v325] .nil .nil) .nil) (.node [v132, v188, v213, v244, v270, v333] (.node [v132, v188, v213, v244, v270, v331] .nil .nil) .nil))) (.node [v132, v188, v213, v244, v276, v303] (.node [v132, v188, v213, v244, v270, v351] (.node [v132, v188, v213, v244, v270, v339] (.node [v132, v188, v213, v244, v270, v336] .nil .nil) .nil) (.node [v132, v188, v213, v244, v272, v303] (.node [v132, v188, v213, v244, v271, v303] .nil .nil) .nil)) (.node [v132, v188, v213, v244, v279, v303] (.node [v132, v188, v213, v244, v278, v303] (.node [v132, v188, v213, v244, v277, v303] .nil .nil) .nil) (.node [v132, v188, v213, v244, v283, v303] .nil .nil)))) (.node [v132, v188, v213, v244, v303, v344] (.node [v132, v188, v213, v244, v291, v303] (.node [v132, v188, v213, v244, v287, v303] (.node [v132, v188, v213, v244, v286, v303] (.node [v132, v188, v213, v244, v285, v303] .nil .nil) .nil) (.node [v132, v188, v213, v244, v289, v303] (.node [v132, v188, v213, v244, v288, v303] .nil .nil) .nil)) (.node [v132, v188, v213, v244, v302, v350] (.node [v132, v188, v213, v244, v295, v303] (.node [v132, v188, v213, v244, v293, v303] .nil .nil) .nil) (.node [v132, v188, v213, v244, v303, v342] (.node [v132, v188, v213, v244, v303, v340] .nil .nil) .nil))) (.node [v132, v188, v213, v256, v270, v303] (.node [v132, v188, v213, v244, v331, v350] (.node [v132, v188, v213, v244, v303, v350] (.node [v132, v188, v213, v244, v303, v347] .nil .nil) .nil) (.node [v132, v188, v213, v256, v270] (.node [v132, v188, v213, v244, v339, v350] .nil .nil) .nil)) (.node [v144, v188, v213, v244, v303, v350] (.node [v132, v188, v225, v244, v270, v303] (.node [v132, v188, v225, v244, v270] .nil .nil) .nil) (.node [v145, v188, v213, v244, v270, v303] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrr_ok : everyKey (rowOK 4 level4) level5rrr = true := by decide +kernel
def level5rr : BinaryTree (List W) := .node [v132, v188, v213, v244, v270, v316] level5rrl level5rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rr_ok : everyKey (rowOK 4 level4) level5rr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrl && everyKey (rowOK 4 level4) level5rrr) = true
  rw [level5rrl_ok, level5rrr_ok]
  decide +kernel
def level5r : BinaryTree (List W) := .node [v132, v188, v213, v233, v244, v303] level5rl level5rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5r_ok : everyKey (rowOK 4 level4) level5r = true := by
  change (_ && everyKey (rowOK 4 level4) level5rl && everyKey (rowOK 4 level4) level5rr) = true
  rw [level5rl_ok, level5rr_ok]
  decide +kernel
def level5 : BinaryTree (List W) := .node [v129, v188, v213, v244, v270, v303] level5l level5r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5_ok : everyKey (rowOK 4 level4) level5 = true := by
  change (_ && everyKey (rowOK 4 level4) level5l && everyKey (rowOK 4 level4) level5r) = true
  rw [level5l_ok, level5r_ok]
  decide +kernel
theorem closed5 : Closed 5 level5 := closed_next 4 (by decide) level5 level4 closed4 level5_ok
def level6l : BinaryTree (List W) := (.node [v52, v132, v188, v213, v244, v270, v303] (.node [v25, v132, v188, v213, v244, v270, v303] (.node [v11, v132, v188, v213, v244, v270, v303] (.node [v10, v132, v188, v213, v244, v270] (.node [v8, v132, v188, v213, v244, v270, v303] (.node [v8, v132, v188, v213, v244, v270] .nil .nil) .nil) (.node [v10, v132, v188, v213, v244, v270, v303] .nil .nil)) (.node [v23, v132, v188, v213, v244, v270, v303] (.node [v13, v132, v188, v213, v244, v270, v303] (.node [v12, v132, v188, v213, v244, v270, v303] .nil .nil) .nil) (.node [v23, v132, v188, v213, v244, v303] .nil .nil))) (.node [v36, v132, v188, v213, v244, v270, v303] (.node [v28, v132, v188, v213, v244, v303] (.node [v28, v132, v188, v213, v244, v270, v303] (.node [v25, v132, v188, v213, v244, v303] .nil .nil) .nil) (.node [v32, v132, v188, v213, v244, v270, v303] .nil .nil)) (.node [v50, v132, v188, v213, v244, v270] (.node [v47, v132, v188, v213, v244, v270, v303] (.node [v44, v132, v188, v213, v244, v270, v303] .nil .nil) .nil) (.node [v50, v132, v188, v213, v244, v270, v303] .nil .nil)))) (.node [v95, v132, v188, v213, v244, v270, v303] (.node [v72, v132, v188, v213, v244, v270, v303] (.node [v69, v132, v188, v213, v244, v270, v303] (.node [v66, v132, v188, v213, v244, v270, v303] (.node [v53, v132, v188, v213, v244, v270, v303] .nil .nil) .nil) (.node [v72, v132, v188, v213, v244, v270] .nil .nil)) (.node [v92, v132, v188, v213, v244, v270, v303] (.node [v75, v132, v188, v213, v244, v270, v303] (.node [v74, v132, v188, v213, v244, v270, v303] .nil .nil) .nil) (.node [v94, v132, v188, v213, v244, v270, v303] .nil .nil))) (.node [v111, v132, v188, v213, v244, v270, v303] (.node [v98, v132, v188, v213, v244, v270, v303] (.node [v97, v132, v188, v213, v244, v270, v303] (.node [v96, v132, v188, v213, v244, v270, v303] .nil .nil) .nil) (.node [v106, v132, v188, v213, v244, v270, v303] .nil .nil)) (.node [v117, v132, v188, v213, v244, v270] (.node [v116, v132, v188, v213, v244, v270, v303] .nil .nil) (.node [v117, v132, v188, v213, v244, v270, v303] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6l_ok : everyKey (rowOK 5 level5) level6l = true := by decide +kernel
def level6r : BinaryTree (List W) := (.node [v132, v188, v213, v244, v259, v270, v303] (.node [v132, v173, v188, v213, v244, v270] (.node [v132, v144, v188, v213, v244, v303] (.node [v132, v143, v188, v213, v244, v270, v303] (.node [v132, v141, v188, v213, v244, v270, v303] (.node [v132, v139, v188, v213, v244, v270, v303] .nil .nil) .nil) (.node [v132, v144, v188, v213, v244, v270, v303] .nil .nil)) (.node [v132, v164, v188, v213, v244, v270, v303] (.node [v132, v158, v188, v213, v244, v270, v303] (.node [v132, v151, v188, v213, v244, v270, v303] .nil .nil) .nil) (.node [v132, v164, v188, v213, v244, v303] .nil .nil))) (.node [v132, v188, v204, v213, v244, v270, v303] (.node [v132, v188, v196, v213, v244, v270, v303] (.node [v132, v188, v193, v213, v244, v270, v303] (.node [v132, v173, v188, v213, v244, v270, v303] .nil .nil) .nil) (.node [v132, v188, v196, v213, v244, v303] .nil .nil)) (.node [v132, v188, v213, v227, v244, v303] (.node [v132, v188, v213, v227, v244, v270, v303] .nil .nil) (.node [v132, v188, v213, v235, v244, v270, v303] .nil .nil)))) (.node [v132, v188, v213, v244, v270, v303, v343] (.node [v132, v188, v213, v244, v270, v303, v314] (.node [v132, v188, v213, v244, v270, v294, v303] (.node [v132, v188, v213, v244, v270, v292, v303] (.node [v132, v188, v213, v244, v260, v270, v303] .nil .nil) .nil) (.node [v132, v188, v213, v244, v270, v296, v303] .nil .nil)) (.node [v132, v188, v213, v244, v270, v303, v339] (.node [v132, v188, v213, v244, v270, v303, v331] (.node [v132, v188, v213, v244, v270, v303, v322] .nil .nil) .nil) (.node [v132, v188, v213, v244, v270, v303, v341] .nil .nil))) (.node [v132, v188, v213, v244, v270, v303, v350] (.node [v132, v188, v213, v244, v270, v303, v348] (.node [v132, v188, v213, v244, v270, v303, v346] (.node [v132, v188, v213, v244, v270, v303, v345] .nil .nil) .nil) (.node [v132, v188, v213, v244, v270, v303, v349] .nil .nil)) (.node [v132, v188, v213, v244, v270, v339] (.node [v132, v188, v213, v244, v270, v331] .nil .nil) (.node [v132, v188, v213, v244, v303, v350] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6r_ok : everyKey (rowOK 5 level5) level6r = true := by decide +kernel
def level6 : BinaryTree (List W) := .node [v132, v136, v188, v213, v244, v270, v303] level6l level6r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6_ok : everyKey (rowOK 5 level5) level6 = true := by
  change (_ && everyKey (rowOK 5 level5) level6l && everyKey (rowOK 5 level5) level6r) = true
  rw [level6l_ok, level6r_ok]
  decide +kernel
theorem closed6 : Closed 6 level6 := closed_next 5 (by decide) level6 level5 closed5 level6_ok
def level7 : BinaryTree (List W) := (.node [v132, v188, v213, v244, v270, v303] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7_ok : everyKey (rowOK 6 level6) level7 = true := by decide +kernel
theorem closed7 : Closed 7 level7 := closed_next 6 (by decide) level7 level6 closed6 level7_ok

theorem lower : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z 7 ins.toFinset :=
  @no_build 7 level7 ins (by decide +kernel) (by decide) closed7 (by decide +kernel)
def witness : List Gate := [⟨.and,[1,4]⟩, ⟨.or,[0,6]⟩, ⟨.and,[3,7]⟩, ⟨.or,[2,8]⟩, ⟨.or,[5,9]⟩, ⟨.and,[1,10]⟩, ⟨.and,[0,11]⟩, ⟨.and,[2,8]⟩, ⟨.or,[12,13]⟩]
theorem upper : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 9 ∧ ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xe888a888e880a880 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact ⟨witness,14,by simp [witness],rfl,by decide +kernel⟩
end PEqualNP.Outside.L_meta_15139_aux

open PEqualNP.Outside.L_meta_15139_aux in
theorem PEqualNP.Outside.L_meta_15139 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3901270152 * 2 ^ 32 + 3900745856) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3901270152 * 2 ^ 32 + 3900745856) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  have code : 3901270152 * 2 ^ 32 + 3900745856 = 0xe888a888e880a880 := by decide
  simp only [code] at h ⊢
  obtain ⟨C,legal,size,computes⟩ := h
  obtain ⟨gs,o,mono,bound,ev⟩ := replace 0xe888a888e880a880 9 ins (by decide +kernel) sampled rfl lower upper C.gates C.output legal computes
  exact ⟨⟨gs,o⟩,mono,bound.trans size,ev⟩
