import PEqualNP.Defs

-- The live-wire search and its circuit compiler follow the merged L-meta-8639.
namespace PEqualNP.Outside.L_meta_12693_aux

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

def v0 : W := 0x0
def v1 : W := 0x9002400000000ff03f0
def v2 : W := 0x9090000000000fffc00
def v3 : W := 0x90926400000001c1c77
def v4 : W := 0x9092640000000e0e388
def v5 : W := 0x24cb0b2ec00000001c1c77
def v6 : W := 0x4b9919664000000ee0e388
def v7 : W := 0x9d1b406c00000070ff03f0
def v8 : W := 0xf21b5b0000000380fffc00
def v9 : W := 0xffd25248800003ff000000
def v10 : W := 0x93000d0d37400000001c1c77
def v11 : W := 0x12e002929a640003800e0e388
def v12 : W := 0x274002d80b40001c000ff03f0
def v13 : W := 0x3c8002dad00000e0000fffc00
def v14 : W := 0x3ff0024a491000ffc00000000
def v15 : W := 0x3fffff6f6d9800fffff000000
def v16 : W := 0x8020089092640000000000000
def v17 : W := 0x4010040f003c000000001c0070
def v18 : W := 0x4c1304c0003fc0000000000077
def v19 : W := 0x9024090000c007f1fc7f000000
def v20 : W := 0x9024093900e400000000e00380
def v21 : W := 0x9826098000e640e0380e000388
def v22 : W := 0xd0340d0000fc0701c0700003f0
def v23 : W := 0xd8360d8000fe47e1f87e0003f8
def v24 : W := 0xdc000dc0004887f0007f000000
def v25 : W := 0xdc00ffd2524887f003ff000000
def v26 : W := 0xdc370000009107f1fc00000000
def v27 : W := 0xdc370dc000d987f1fc7f000000
def v28 : W := 0xdc370dc000fd87f1fc7f0003f0
def v29 : W := 0xdc370dc000ffc7f1fc7f000077
def v30 : W := 0xdc370dc000ffc7f1fc7f000388
def v31 : W := 0xdc370dc909d987f1fc7ffffc00
def v32 : W := 0xdc37f21b5b9107f1ff80fffc00
def v33 : W := 0xdfc80dedad4887fe007ffffc00
def v34 : W := 0xdfff0024a49107fffc00000000
def v35 : W := 0x20080200f0f00000000001c1c00
def v36 : W := 0x20c8320c00f03c0000000001c07
def v37 : W := 0x2449124460619800000001c1c77
def v38 : W := 0x24c0024c2020880000000000000
def v39 : W := 0x24c00ffd25248800003ff000000
def v40 : W := 0x24c930004041100000000000000
def v41 : W := 0x24c9324c6061980000000000000
def v42 : W := 0x24c9324cf0f3fc0000000000000
def v43 : W := 0x24c9324cf0f3fc00000001c1c77
def v44 : W := 0x24fff0024a491000ffc00000000
def v45 : W := 0x2dcb72dc606d987f1fc7f000000
def v46 : W := 0x2dcb72dcf0fffc7f1fc7f1c1c77
def v47 : W := 0x421084200300038fe3f8f000000
def v48 : W := 0x421084239390000000000e0e000
def v49 : W := 0x4290a4280390240e0380e00e008
def v50 : W := 0x4b12c4b3030c000e0380ee0e388
def v51 : W := 0x4b12c4b3939e640e0380ee0e388
def v52 : W := 0x4b12c4bb939e640e0380ee0e388
def v53 : W := 0x4b12e4b3939e640e0380ee0e388
def v54 : W := 0x4b8004b90104000e0000e000000
def v55 : W := 0x4b800ffd2524880e003ff000000
def v56 : W := 0x4b92e0020208000e03800000000
def v57 : W := 0x4b92e4bb030c000e0380e000000
def v58 : W := 0x4b92e4bb939e640e0380e000000
def v59 : W := 0x4b92e4bb939e640e0380ee0e388
def v60 : W := 0x4bbff0024a49100effc00000000
def v61 : W := 0x6218862003f00380e038000fc00
def v62 : W := 0x6298a62803f0278ee3b8e00fc08
def v63 : W := 0x62c0062c01200b8f0038f000000
def v64 : W := 0x62c00ffd25248b8f003ff000000
def v65 : W := 0x62d8b0000240138fe3c00000000
def v66 : W := 0x62d8b62c03601b8fe3f8f000000
def v67 : W := 0x62d8b62c03f01b8fe3f8f00fc00
def v68 : W := 0x62d8b62c03f03f8fe3f8f001c07
def v69 : W := 0x62d8b62c03f03f8fe3f8f00e008
def v70 : W := 0x62d8b62c93625b8fe3f8fff03f0
def v71 : W := 0x62d8b9d1b646d38fe3c70ff03f0
def v72 : W := 0x62e7462ed92b4b8f1c38fff03f0
def v73 : W := 0x62fff0024a49138fffc00000000
def v74 : W := 0x66d9b66c63619b8fe3f8f000000
def v75 : W := 0x66d9b66cf3f3ff8fe3f8f1c1c77
def v76 : W := 0x6f1bc6f003ffc3f0fc3f000fff0
def v77 : W := 0x6f5bd6f7636d980e0380efcffff
def v78 : W := 0x6fd2e6ffb3beec0e0380ee0e388
def v79 : W := 0x6fdbf4bbd3df740e0380ee0e388
def v80 : W := 0x6fdbf6fff3fffc0e0380ee0e388
def v81 : W := 0x6fdbf6fff3fffc0e0380efcffff
def v82 : W := 0x90240903fc00000000000ff0000
def v83 : W := 0x942509406c0180701c0701f0070
def v84 : W := 0x992649930c0c00701c070000000
def v85 : W := 0x992649930c0c00701c070e30380
def v86 : W := 0x992649939c0e40701c070e30380
def v87 : W := 0x992649939c0e40701c070ff03f0
def v88 : W := 0x99264993fc0c00701c070ff0380
def v89 : W := 0x99264993fc0e400000000ff0380
def v90 : W := 0x992649d3bc0ec0701c070ff03f0
def v91 : W := 0x99274993dc0f40701c070ff03f0
def v92 : W := 0x9d0009d12404807000070000000
def v93 : W := 0x9d000ffd25248870003ff000000
def v94 : W := 0x9d2649d32c0c80701c070e30380
def v95 : W := 0x9d274002480900701c000000000
def v96 : W := 0x9d2749934c0d00701c070e30380
def v97 : W := 0x9d2749d06c0fc0701c0701f03f0
def v98 : W := 0x9d2749d30c0fc0701c070e303f0
def v99 : W := 0x9d2749d36c0d80701c070000000
def v100 : W := 0x9d2749d36c0d80701c0701f0070
def v101 : W := 0x9d2749d36c0d80701c070e30380
def v102 : W := 0x9d2749d36c0d80701c070ff03f0
def v103 : W := 0x9d2749d36c0fc0701c0700003f0
def v104 : W := 0x9d2749d3fc0d80701c070ff0000
def v105 : W := 0x9d2749d3fc0fc0701c0701c0070
def v106 : W := 0x9d2749d3fc0fc0701c070e00380
def v107 : W := 0x9d2749d3fc0fc0701c070ff03f0
def v108 : W := 0x9d2749d3fc9fc0701c070fffff0
def v109 : W := 0x9d2749d3fc9fe4701c070ff1ff7
def v110 : W := 0x9d2749d3fc9fe4701c070ffe3f8
def v111 : W := 0x9d274bdffcbfec701c070ff1ff7
def v112 : W := 0x9d2f79d3fcdff4701c070ff1ff7
def v113 : W := 0x9d3ff0024a491070ffc00000000
def v114 : W := 0x9da769dbfc9fe4701c070ff03f0
def v115 : W := 0x9de779dffc0ffc701c070ff03f7
def v116 : W := 0xb02c0b006c600380e03801f1c00
def v117 : W := 0xb4400b4424208bf1003f1000000
def v118 : W := 0xb4400ffd25248bf1003ff000000
def v119 : W := 0xb452eb46b6baeff103bf1e0e388
def v120 : W := 0xb46d1000484113f1fc400000000
def v121 : W := 0xb46d14b9d9d777f1fc40ee0e388
def v122 : W := 0xb46d1b446c619bf1fc7f1000000
def v123 : W := 0xb46d1b446c619bf1fc7f11c1c77
def v124 : W := 0xb46d1b44fcf3fff1fc7f1e0e388
def v125 : W := 0xb47ff0024a4913f1ffc00000000
def v126 : W := 0xb9ae6b986c6e678ee3b8e1f1f88
def v127 : W := 0xb9ee7b9f0cfc3c701c070e31f87
def v128 : W := 0xbd2f4bd3fcffc0701c070ff1ff0
def v129 : W := 0xbd6f5bd7fc6fd8701c070ff1ff7
def v130 : W := 0xbde74bdffc2fc8701c070ff03f0
def v131 : W := 0xbdef79d3fc4fd0701c070ff03f0
def v132 : W := 0xbdef7bdf6c6d98701c070000000
def v133 : W := 0xbdef7bdffc6fd8701c070ff03f0
def v134 : W := 0xbdef7bdffcfffc701c0701c1c77
def v135 : W := 0xbdef7bdffcfffc701c070ff1ff7
def v136 : W := 0xd2348d230f000380e0380000000
def v137 : W := 0xd2348d230f000380e0380e3e000
def v138 : W := 0xd2348d239f900380e0380e3e000
def v139 : W := 0xd2348d239f900380e0380fffc00
def v140 : W := 0xd2348d23ff000380e0380ffe000
def v141 : W := 0xd2348d23ff90000000000ffe000
def v142 : W := 0xd2348f23bfb00380e0380fffc00
def v143 : W := 0xd23c8d23dfd00380e0380fffc00
def v144 : W := 0xd6b5ad686f91a47e1f87e1fe078
def v145 : W := 0xd6f5bd6f0f03ff80e0380e3e077
def v146 : W := 0xdb000db1050403ff003ff000000
def v147 : W := 0xdb000ffd25248bff003ff000000
def v148 : W := 0xdb093db1d5d777ff003ff1c1c77
def v149 : W := 0xdb36c0020a0803ffffc00000000
def v150 : W := 0xdb36c24ebabaefffffc001c1c77
def v151 : W := 0xdb36cdb30f0c03fffffff000000
def v152 : W := 0xdb36cdb30f0c03fffffffe0e388
def v153 : W := 0xdb36cdb39f9e67fffffff1c1c77
def v154 : W := 0xdb3ff0024a4913ffffc00000000
def v155 : W := 0xdf37cdf3ff9fc0701c070ffe3f0
def v156 : W := 0xdfb7edfbff9fe47e1f87effe3f8
def v157 : W := 0xf2000f212520038000380000000
def v158 : W := 0xf2000ffd25248b80003ff000000
def v159 : W := 0xf2348f232f200380e0380e3e000
def v160 : W := 0xf23c80024a400380e0000000000
def v161 : W := 0xf23c8d234f400380e0380e3e000
def v162 : W := 0xf23c8f206ff00380e03801ffc00
def v163 : W := 0xf23c8f230ff00380e0380e3fc00
def v164 : W := 0xf23c8f236f600380e0380000000
def v165 : W := 0xf23c8f236f600380e03801f1c00
def v166 : W := 0xf23c8f236f600380e0380e3e000
def v167 : W := 0xf23c8f236f600380e0380fffc00
def v168 : W := 0xf23c8f236ff00380e038000fc00
def v169 : W := 0xf23c8f23ff600380e0380ff0000
def v170 : W := 0xf23c8f23fff00380e03801c1c00
def v171 : W := 0xf23c8f23fff00380e0380e0e000
def v172 : W := 0xf23c8f23fff00380e0380fffc00
def v173 : W := 0xf23c8f23fff24380e0380fffff0
def v174 : W := 0xf23c8f23fff26780e0380fffc77
def v175 : W := 0xf23c8f23fff26780e0380ffff88
def v176 : W := 0xf23c8f6ffff2ef80e0380fffc77
def v177 : W := 0xf23dbf23fff37780e0380fffc77
def v178 : W := 0xf23ff0024a491380ffc00000000
def v179 : W := 0xf2bcaf2bfff26780e0380fffc00
def v180 : W := 0xf2fcbf2ffff03f80e0380fffc07
def v181 : W := 0xf63d8f63fff3c380e0380fffc70
def v182 : W := 0xf67d9f67fff19b80e0380fffc77
def v183 : W := 0xf6fc8f6ffff08b80e0380fffc00
def v184 : W := 0xf6fdbf23fff11380e0380fffc00
def v185 : W := 0xf6fdbf6f6f619b80e0380000000
def v186 : W := 0xf6fdbf6ffff19b80e0380fffc00
def v187 : W := 0xf6fdbf6ffff3ff80e03801c1c77
def v188 : W := 0xf6fdbf6ffff3ff80e0380fffc77
def v189 : W := 0xfb3ecfb3fffe4380e0380ffff80
def v190 : W := 0xfbbeefbbfffe678ee3b8effff88
def v191 : W := 0xff3fcff3ffffc3f0fc3f0fffff0
def v192 : W := 0xff400ff525248bff003ff000000
def v193 : W := 0xff7fd0024a4913ffffc00000000
def v194 : W := 0xff7fdff76f6d9bfffffff000000
def v195 : W := 0xffc00000000003ff00000000000
def v196 : W := 0xffc00ffd25248bff003ff000000
def v197 : W := 0xffc02ffdb5b6efff003ff000000
def v198 : W := 0xffc37ffd252d9bff1ffff000000
def v199 : W := 0xffc93ffd65659bff003ff000000
def v200 : W := 0xffc93ffdf5f7ffff003ff1c1c77
def v201 : W := 0xffd2efff272c8bff03bff000000
def v202 : W := 0xffd2efffb7beefff03bffe0e388
def v203 : W := 0xffd8bffd27649bffe3fff000000
def v204 : W := 0xffe74fff6d2d8bff1c3ff000000
def v205 : W := 0xffe74ffffd2fcbff1c3ffff03f0
def v206 : W := 0xffed1ffd6d659bfffc7ff000000
def v207 : W := 0xfff6cfff2f2c8bfffffff000000
def v208 : W := 0xfffc8fff6f648bffe03ff000000
def v209 : W := 0xfffc8ffffff48bffe03fffffc00
def v210 : W := 0xffffdfff6f6d9bfffffff000000
def v211 : W := 0xfffff0024a4913ffffc00000000
def v212 : W := 0xfffff00adadb77ffffc00000000
def v213 : W := 0xfffff0de4a4d9bffffc7f000000
def v214 : W := 0xfffff24e6a699bffffc00000000
def v215 : W := 0xfffff24efafbffffffc001c1c77
def v216 : W := 0xfffff4bb4b4d13ffffc0e000000
def v217 : W := 0xfffff4bbdbdf77ffffc0ee0e388
def v218 : W := 0xfffff62e4b691bfffff8f000000
def v219 : W := 0xfffff9d36e4d93ffffc70000000
def v220 : W := 0xfffff9d3fe4fd3ffffc70ff03f0
def v221 : W := 0xfffffb466e699bffffff1000000
def v222 : W := 0xfffffdb34f4d13fffffff000000
def v223 : W := 0xffffff236f6913fffff80000000
def v224 : W := 0xffffff23fff913fffff80fffc00
def v225 : W := 0xfffffff76f6d9bfffffff000000
def v226 : W := 0xffffffff6f6d9bfffffff000000
def v227 : W := 0xffffffffff6fdbfffffffff03f0
def v228 : W := 0xfffffffffffd9bffffffffffc00
def v229 : W := 0xfffffffffffffffffffff000000
def v230 : W := 0xfffffffffffffffffffff1c1c77
def v231 : W := 0xfffffffffffffffffffffe0e388

def ins : List W := [v43, v59, v107, v172, v196, v211]
theorem sampled : ∀ j : Fin 108, Nat.testBit 0xfeeafeeafeea8888 (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
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
def level2 : BinaryTree (List W) := (.node [v59, v134, v185] (.node [v59, v132, v187] .nil .nil) .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level2_ok : everyKey (rowOK 1 level1) level2 = true := by decide +kernel
theorem closed2 : Closed 2 level2 := closed_next 1 (by decide) level2 level1 closed1 level2_ok
def level3ll : BinaryTree (List W) := (.node [v43, v59, v70, v172] (.node [v31, v43, v59, v107] .nil .nil) (.node [v43, v59, v76, v226] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level3ll_ok : everyKey (rowOK 2 level2) level3ll = true := by decide +kernel
def level3lr : BinaryTree (List W) := (.node [v43, v107, v124, v172] (.node [v43, v59, v132, v164] .nil .nil) (.node [v43, v107, v126, v226] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level3lr_ok : everyKey (rowOK 2 level2) level3lr = true := by decide +kernel
def level3l : BinaryTree (List W) := .node [v43, v59, v99, v185] level3ll level3lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level3l_ok : everyKey (rowOK 2 level2) level3l = true := by
  change (_ && everyKey (rowOK 2 level2) level3ll && everyKey (rowOK 2 level2) level3lr) = true
  rw [level3ll_ok, level3lr_ok]
  decide +kernel
def level3r : BinaryTree (List W) := (.node [v59, v134, v188, v226] (.node [v59, v107, v153, v172] (.node [v59, v107, v145, v226] .nil .nil) (.node [v59, v127, v172, v226] .nil .nil)) (.node [v77, v107, v172, v226] (.node [v59, v135, v187, v226] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level3r_ok : everyKey (rowOK 2 level2) level3r = true := by decide +kernel
def level3 : BinaryTree (List W) := .node [v43, v144, v172, v226] level3l level3r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level3_ok : everyKey (rowOK 2 level2) level3 = true := by
  change (_ && everyKey (rowOK 2 level2) level3l && everyKey (rowOK 2 level2) level3r) = true
  rw [level3l_ok, level3r_ok]
  decide +kernel
theorem closed3 : Closed 3 level3 := closed_next 2 (by decide) level3 level2 closed2 level3_ok
def level4lllll : BinaryTree (List W) := (.node [v3, v59, v107, v151, v172] (.node [v2, v27, v43, v59, v107] (.node [v1, v43, v59, v66, v172] .nil .nil) .nil) (.node [v4, v43, v107, v122, v172] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lllll_ok : everyKey (rowOK 3 level3) level4lllll = true := by decide +kernel
def level4llllr : BinaryTree (List W) := (.node [v18, v59, v107, v137, v226] (.node [v17, v59, v135, v172, v226] (.node [v16, v81, v107, v172, v226] .nil .nil) .nil) (.node [v19, v43, v59, v107, v226] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llllr_ok : everyKey (rowOK 3 level3) level4llllr = true := by decide +kernel
def level4llll : BinaryTree (List W) := .node [v15, v43, v59, v107, v172] level4lllll level4llllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llll_ok : everyKey (rowOK 3 level3) level4llll = true := by
  change (_ && everyKey (rowOK 3 level3) level4lllll && everyKey (rowOK 3 level3) level4llllr) = true
  rw [level4lllll_ok, level4llllr_ok]
  decide +kernel
def level4lllrl : BinaryTree (List W) := (.node [v23, v43, v59, v107, v226] (.node [v22, v43, v59, v61, v226] (.node [v21, v43, v107, v116, v226] .nil .nil) .nil) (.node [v27, v43, v59, v66, v226] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lllrl_ok : everyKey (rowOK 3 level3) level4lllrl = true := by decide +kernel
def level4lllrr : BinaryTree (List W) := (.node [v27, v43, v59, v107, v226] (.node [v27, v43, v59, v107, v164] (.node [v27, v43, v59, v99, v226] .nil .nil) .nil) (.node [v27, v43, v59, v135, v226] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lllrr_ok : everyKey (rowOK 3 level3) level4lllrr = true := by decide +kernel
def level4lllr : BinaryTree (List W) := .node [v27, v43, v59, v85, v226] level4lllrl level4lllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lllr_ok : everyKey (rowOK 3 level3) level4lllr = true := by
  change (_ && everyKey (rowOK 3 level3) level4lllrl && everyKey (rowOK 3 level3) level4lllrr) = true
  rw [level4lllrl_ok, level4lllrr_ok]
  decide +kernel
def level4lll : BinaryTree (List W) := .node [v20, v43, v156, v172, v226] level4llll level4lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lll_ok : everyKey (rowOK 3 level3) level4lll = true := by
  change (_ && everyKey (rowOK 3 level3) level4llll && everyKey (rowOK 3 level3) level4lllr) = true
  rw [level4llll_ok, level4lllr_ok]
  decide +kernel
def level4llrll : BinaryTree (List W) := (.node [v32, v43, v59, v107, v196] (.node [v30, v43, v59, v107, v226] (.node [v29, v43, v59, v107, v226] .nil .nil) .nil) (.node [v33, v43, v59, v107, v211] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llrll_ok : everyKey (rowOK 3 level3) level4llrll = true := by decide +kernel
def level4llrlr : BinaryTree (List W) := (.node [v41, v59, v107, v172, v230] (.node [v37, v50, v107, v172, v226] (.node [v36, v59, v85, v172, v226] .nil .nil) .nil) (.node [v42, v59, v107, v172, v226] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llrlr_ok : everyKey (rowOK 3 level3) level4llrlr = true := by decide +kernel
def level4llrl : BinaryTree (List W) := .node [v35, v59, v107, v188, v226] level4llrll level4llrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llrl_ok : everyKey (rowOK 3 level3) level4llrl = true := by
  change (_ && everyKey (rowOK 3 level3) level4llrll && everyKey (rowOK 3 level3) level4llrlr) = true
  rw [level4llrll_ok, level4llrlr_ok]
  decide +kernel
def level4llrrl : BinaryTree (List W) := (.node [v43, v48, v107, v190, v226] (.node [v43, v47, v59, v172, v226] (.node [v43, v46, v59, v107, v226] .nil .nil) .nil) (.node [v43, v49, v83, v172, v226] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llrrl_ok : everyKey (rowOK 3 level3) level4llrrl = true := by decide +kernel
def level4llrrr : BinaryTree (List W) := (.node [v43, v57, v107, v172, v231] (.node [v43, v53, v107, v172, v226] (.node [v43, v52, v107, v172, v226] .nil .nil) .nil) (.node [v43, v58, v107, v172, v226] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llrrr_ok : everyKey (rowOK 3 level3) level4llrrr = true := by decide +kernel
def level4llrr : BinaryTree (List W) := .node [v43, v51, v107, v172, v226] level4llrrl level4llrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llrr_ok : everyKey (rowOK 3 level3) level4llrr = true := by
  change (_ && everyKey (rowOK 3 level3) level4llrrl && everyKey (rowOK 3 level3) level4llrrr) = true
  rw [level4llrrl_ok, level4llrrr_ok]
  decide +kernel
def level4llr : BinaryTree (List W) := .node [v43, v45, v59, v107, v226] level4llrl level4llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llr_ok : everyKey (rowOK 3 level3) level4llr = true := by
  change (_ && everyKey (rowOK 3 level3) level4llrl && everyKey (rowOK 3 level3) level4llrr) = true
  rw [level4llrl_ok, level4llrr_ok]
  decide +kernel
def level4ll : BinaryTree (List W) := .node [v28, v43, v59, v107, v226] level4lll level4llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4ll_ok : everyKey (rowOK 3 level3) level4ll = true := by
  change (_ && everyKey (rowOK 3 level3) level4lll && everyKey (rowOK 3 level3) level4llr) = true
  rw [level4lll_ok, level4llr_ok]
  decide +kernel
def level4lrlll : BinaryTree (List W) := (.node [v43, v59, v66, v164, v226] (.node [v43, v59, v66, v137, v226] (.node [v43, v59, v66, v99, v172] .nil .nil) .nil) (.node [v43, v59, v66, v172, v226] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrlll_ok : everyKey (rowOK 3 level3) level4lrlll = true := by decide +kernel
def level4lrllr : BinaryTree (List W) := (.node [v43, v59, v69, v172, v226] (.node [v43, v59, v68, v172, v226] (.node [v43, v59, v67, v172, v226] .nil .nil) .nil) (.node [v43, v59, v71, v172, v196] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrllr_ok : everyKey (rowOK 3 level3) level4lrllr = true := by decide +kernel
def level4lrll : BinaryTree (List W) := .node [v43, v59, v66, v188, v226] level4lrlll level4lrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrll_ok : everyKey (rowOK 3 level3) level4lrll = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrlll && everyKey (rowOK 3 level3) level4lrllr) = true
  rw [level4lrlll_ok, level4lrllr_ok]
  decide +kernel
def level4lrlrl : BinaryTree (List W) := (.node [v43, v59, v76, v196, v211] (.node [v43, v59, v75, v172, v226] (.node [v43, v59, v74, v172, v226] .nil .nil) .nil) (.node [v43, v59, v82, v191, v226] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrlrl_ok : everyKey (rowOK 3 level3) level4lrlrl = true := by decide +kernel
def level4lrlrr : BinaryTree (List W) := (.node [v43, v59, v85, v172, v226] (.node [v43, v59, v85, v164, v226] (.node [v43, v59, v85, v137, v226] .nil .nil) .nil) (.node [v43, v59, v85, v188, v226] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrlrr_ok : everyKey (rowOK 3 level3) level4lrlrr = true := by decide +kernel
def level4lrlr : BinaryTree (List W) := .node [v43, v59, v84, v172, v226] level4lrlrl level4lrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrlr_ok : everyKey (rowOK 3 level3) level4lrlr = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrlrl && everyKey (rowOK 3 level3) level4lrlrr) = true
  rw [level4lrlrl_ok, level4lrlrr_ok]
  decide +kernel
def level4lrl : BinaryTree (List W) := .node [v43, v59, v72, v172, v211] level4lrll level4lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrl_ok : everyKey (rowOK 3 level3) level4lrl = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrll && everyKey (rowOK 3 level3) level4lrlr) = true
  rw [level4lrll_ok, level4lrlr_ok]
  decide +kernel
def level4lrrll : BinaryTree (List W) := (.node [v43, v59, v89, v172, v226] (.node [v43, v59, v88, v172, v226] (.node [v43, v59, v87, v172, v226] .nil .nil) .nil) (.node [v43, v59, v90, v172, v226] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrrll_ok : everyKey (rowOK 3 level3) level4lrrll = true := by decide +kernel
def level4lrrlr : BinaryTree (List W) := (.node [v43, v59, v97, v172, v226] (.node [v43, v59, v96, v172, v226] (.node [v43, v59, v94, v172, v226] .nil .nil) .nil) (.node [v43, v59, v98, v172, v226] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrrlr_ok : everyKey (rowOK 3 level3) level4lrrlr = true := by decide +kernel
def level4lrrl : BinaryTree (List W) := .node [v43, v59, v91, v172, v226] level4lrrll level4lrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrrl_ok : everyKey (rowOK 3 level3) level4lrrl = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrrll && everyKey (rowOK 3 level3) level4lrrlr) = true
  rw [level4lrrll_ok, level4lrrlr_ok]
  decide +kernel
def level4lrrrl : BinaryTree (List W) := (.node [v43, v59, v99, v172, v227] (.node [v43, v59, v99, v172, v226] (.node [v43, v59, v99, v164, v226] .nil .nil) .nil) (.node [v43, v59, v99, v188, v226] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrrrl_ok : everyKey (rowOK 3 level3) level4lrrrl = true := by decide +kernel
def level4lrrrr : BinaryTree (List W) := (.node [v43, v59, v103, v172, v226] (.node [v43, v59, v102, v172, v226] (.node [v43, v59, v101, v172, v226] .nil .nil) .nil) (.node [v43, v59, v104, v172, v226] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrrrr_ok : everyKey (rowOK 3 level3) level4lrrrr = true := by decide +kernel
def level4lrrr : BinaryTree (List W) := .node [v43, v59, v100, v172, v226] level4lrrrl level4lrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrrr_ok : everyKey (rowOK 3 level3) level4lrrr = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrrrl && everyKey (rowOK 3 level3) level4lrrrr) = true
  rw [level4lrrrl_ok, level4lrrrr_ok]
  decide +kernel
def level4lrr : BinaryTree (List W) := .node [v43, v59, v99, v137, v226] level4lrrl level4lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrr_ok : everyKey (rowOK 3 level3) level4lrr = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrrl && everyKey (rowOK 3 level3) level4lrrr) = true
  rw [level4lrrl_ok, level4lrrr_ok]
  decide +kernel
def level4lr : BinaryTree (List W) := .node [v43, v59, v86, v172, v226] level4lrl level4lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lr_ok : everyKey (rowOK 3 level3) level4lr = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrl && everyKey (rowOK 3 level3) level4lrr) = true
  rw [level4lrl_ok, level4lrr_ok]
  decide +kernel
def level4l : BinaryTree (List W) := .node [v43, v59, v62, v172, v226] level4ll level4lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4l_ok : everyKey (rowOK 3 level3) level4l = true := by
  change (_ && everyKey (rowOK 3 level3) level4ll && everyKey (rowOK 3 level3) level4lr) = true
  rw [level4ll_ok, level4lr_ok]
  decide +kernel
def level4rllll : BinaryTree (List W) := (.node [v43, v59, v107, v137, v226] (.node [v43, v59, v107, v136, v226] (.node [v43, v59, v106, v172, v226] .nil .nil) .nil) (.node [v43, v59, v107, v138, v226] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rllll_ok : everyKey (rowOK 3 level3) level4rllll = true := by decide +kernel
def level4rlllr : BinaryTree (List W) := (.node [v43, v59, v107, v142, v226] (.node [v43, v59, v107, v141, v226] (.node [v43, v59, v107, v140, v226] .nil .nil) .nil) (.node [v43, v59, v107, v143, v226] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlllr_ok : everyKey (rowOK 3 level3) level4rlllr = true := by decide +kernel
def level4rlll : BinaryTree (List W) := .node [v43, v59, v107, v139, v226] level4rllll level4rlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlll_ok : everyKey (rowOK 3 level3) level4rlll = true := by
  change (_ && everyKey (rowOK 3 level3) level4rllll && everyKey (rowOK 3 level3) level4rlllr) = true
  rw [level4rllll_ok, level4rlllr_ok]
  decide +kernel
def level4rllrl : BinaryTree (List W) := (.node [v43, v59, v107, v163, v226] (.node [v43, v59, v107, v162, v226] (.node [v43, v59, v107, v161, v226] .nil .nil) .nil) (.node [v43, v59, v107, v164, v226] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rllrl_ok : everyKey (rowOK 3 level3) level4rllrl = true := by decide +kernel
def level4rllrr : BinaryTree (List W) := (.node [v43, v59, v107, v167, v226] (.node [v43, v59, v107, v166, v226] (.node [v43, v59, v107, v165, v226] .nil .nil) .nil) (.node [v43, v59, v107, v168, v226] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rllrr_ok : everyKey (rowOK 3 level3) level4rllrr = true := by decide +kernel
def level4rllr : BinaryTree (List W) := .node [v43, v59, v107, v164, v228] level4rllrl level4rllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rllr_ok : everyKey (rowOK 3 level3) level4rllr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rllrl && everyKey (rowOK 3 level3) level4rllrr) = true
  rw [level4rllrl_ok, level4rllrr_ok]
  decide +kernel
def level4rll : BinaryTree (List W) := .node [v43, v59, v107, v159, v226] level4rlll level4rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rll_ok : everyKey (rowOK 3 level3) level4rll = true := by
  change (_ && everyKey (rowOK 3 level3) level4rlll && everyKey (rowOK 3 level3) level4rllr) = true
  rw [level4rlll_ok, level4rllr_ok]
  decide +kernel
def level4rlrll : BinaryTree (List W) := (.node [v43, v59, v107, v172, v194] (.node [v43, v59, v107, v171, v226] (.node [v43, v59, v107, v170, v226] .nil .nil) .nil) (.node [v43, v59, v107, v172, v210] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlrll_ok : everyKey (rowOK 3 level3) level4rlrll = true := by decide +kernel
def level4rlrlr : BinaryTree (List W) := (.node [v43, v59, v107, v173, v226] (.node [v43, v59, v107, v172, v229] (.node [v43, v59, v107, v172, v226] .nil .nil) .nil) (.node [v43, v59, v107, v174, v226] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlrlr_ok : everyKey (rowOK 3 level3) level4rlrlr = true := by decide +kernel
def level4rlrl : BinaryTree (List W) := .node [v43, v59, v107, v172, v225] level4rlrll level4rlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlrl_ok : everyKey (rowOK 3 level3) level4rlrl = true := by
  change (_ && everyKey (rowOK 3 level3) level4rlrll && everyKey (rowOK 3 level3) level4rlrlr) = true
  rw [level4rlrll_ok, level4rlrlr_ok]
  decide +kernel
def level4rlrrl : BinaryTree (List W) := (.node [v43, v59, v107, v179, v226] (.node [v43, v59, v107, v177, v226] (.node [v43, v59, v107, v176, v226] .nil .nil) .nil) (.node [v43, v59, v107, v180, v226] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlrrl_ok : everyKey (rowOK 3 level3) level4rlrrl = true := by decide +kernel
def level4rlrrr : BinaryTree (List W) := (.node [v43, v59, v107, v184, v226] (.node [v43, v59, v107, v183, v226] (.node [v43, v59, v107, v182, v226] .nil .nil) .nil) (.node [v43, v59, v107, v185, v226] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlrrr_ok : everyKey (rowOK 3 level3) level4rlrrr = true := by decide +kernel
def level4rlrr : BinaryTree (List W) := .node [v43, v59, v107, v181, v226] level4rlrrl level4rlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlrr_ok : everyKey (rowOK 3 level3) level4rlrr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rlrrl && everyKey (rowOK 3 level3) level4rlrrr) = true
  rw [level4rlrrl_ok, level4rlrrr_ok]
  decide +kernel
def level4rlr : BinaryTree (List W) := .node [v43, v59, v107, v175, v226] level4rlrl level4rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlr_ok : everyKey (rowOK 3 level3) level4rlr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rlrl && everyKey (rowOK 3 level3) level4rlrr) = true
  rw [level4rlrl_ok, level4rlrr_ok]
  decide +kernel
def level4rl : BinaryTree (List W) := .node [v43, v59, v107, v169, v226] level4rll level4rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rl_ok : everyKey (rowOK 3 level3) level4rl = true := by
  change (_ && everyKey (rowOK 3 level3) level4rll && everyKey (rowOK 3 level3) level4rlr) = true
  rw [level4rll_ok, level4rlr_ok]
  decide +kernel
def level4rrlll : BinaryTree (List W) := (.node [v43, v59, v107, v189, v226] (.node [v43, v59, v107, v188, v226] (.node [v43, v59, v107, v187, v226] .nil .nil) .nil) (.node [v43, v59, v108, v172, v226] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrlll_ok : everyKey (rowOK 3 level3) level4rrlll = true := by decide +kernel
def level4rrllr : BinaryTree (List W) := (.node [v43, v59, v112, v172, v226] (.node [v43, v59, v111, v172, v226] (.node [v43, v59, v110, v172, v226] .nil .nil) .nil) (.node [v43, v59, v114, v172, v226] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrllr_ok : everyKey (rowOK 3 level3) level4rrllr = true := by decide +kernel
def level4rrll : BinaryTree (List W) := .node [v43, v59, v109, v172, v226] level4rrlll level4rrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrll_ok : everyKey (rowOK 3 level3) level4rrll = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrlll && everyKey (rowOK 3 level3) level4rrllr) = true
  rw [level4rrlll_ok, level4rrllr_ok]
  decide +kernel
def level4rrlrl : BinaryTree (List W) := (.node [v43, v59, v130, v172, v226] (.node [v43, v59, v129, v172, v226] (.node [v43, v59, v128, v172, v226] .nil .nil) .nil) (.node [v43, v59, v131, v172, v226] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrlrl_ok : everyKey (rowOK 3 level3) level4rrlrl = true := by decide +kernel
def level4rrlrr : BinaryTree (List W) := (.node [v43, v59, v135, v137, v226] (.node [v43, v59, v134, v172, v226] (.node [v43, v59, v133, v172, v226] .nil .nil) .nil) (.node [v43, v59, v135, v164, v226] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrlrr_ok : everyKey (rowOK 3 level3) level4rrlrr = true := by decide +kernel
def level4rrlr : BinaryTree (List W) := .node [v43, v59, v132, v172, v226] level4rrlrl level4rrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrlr_ok : everyKey (rowOK 3 level3) level4rrlr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrlrl && everyKey (rowOK 3 level3) level4rrlrr) = true
  rw [level4rrlrl_ok, level4rrlrr_ok]
  decide +kernel
def level4rrl : BinaryTree (List W) := .node [v43, v59, v115, v172, v226] level4rrll level4rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrl_ok : everyKey (rowOK 3 level3) level4rrl = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrll && everyKey (rowOK 3 level3) level4rrlr) = true
  rw [level4rrll_ok, level4rrlr_ok]
  decide +kernel
def level4rrrll : BinaryTree (List W) := (.node [v43, v78, v107, v172, v226] (.node [v43, v59, v155, v172, v226] (.node [v43, v59, v135, v188, v226] .nil .nil) .nil) (.node [v43, v79, v107, v172, v226] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrrll_ok : everyKey (rowOK 3 level3) level4rrrll = true := by decide +kernel
def level4rrrlr : BinaryTree (List W) := (.node [v43, v107, v123, v172, v226] (.node [v43, v107, v121, v172, v196] (.node [v43, v107, v119, v172, v211] .nil .nil) .nil) (.node [v43, v107, v126, v196, v211] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrrlr_ok : everyKey (rowOK 3 level3) level4rrrlr = true := by decide +kernel
def level4rrrl : BinaryTree (List W) := .node [v43, v80, v107, v172, v226] level4rrrll level4rrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrrl_ok : everyKey (rowOK 3 level3) level4rrrl = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrrll && everyKey (rowOK 3 level3) level4rrrlr) = true
  rw [level4rrrll_ok, level4rrrlr_ok]
  decide +kernel
def level4rrrrl : BinaryTree (List W) := (.node [v59, v107, v145, v196, v211] (.node [v59, v107, v137, v188, v226] (.node [v59, v85, v135, v172, v226] .nil .nil) .nil) (.node [v59, v107, v148, v172, v211] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrrrl_ok : everyKey (rowOK 3 level3) level4rrrrl = true := by decide +kernel
def level4rrrrr : BinaryTree (List W) := (.node [v59, v127, v172, v196, v211] (.node [v59, v107, v152, v172, v226] .nil .nil) (.node [v77, v107, v172, v196, v211] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrrrr_ok : everyKey (rowOK 3 level3) level4rrrrr = true := by decide +kernel
def level4rrrr : BinaryTree (List W) := .node [v59, v107, v150, v172, v196] level4rrrrl level4rrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrrr_ok : everyKey (rowOK 3 level3) level4rrrr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrrrl && everyKey (rowOK 3 level3) level4rrrrr) = true
  rw [level4rrrrl_ok, level4rrrrr_ok]
  decide +kernel
def level4rrr : BinaryTree (List W) := .node [v43, v144, v172, v196, v211] level4rrrl level4rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrr_ok : everyKey (rowOK 3 level3) level4rrr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrrl && everyKey (rowOK 3 level3) level4rrrr) = true
  rw [level4rrrl_ok, level4rrrr_ok]
  decide +kernel
def level4rr : BinaryTree (List W) := .node [v43, v59, v135, v172, v226] level4rrl level4rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rr_ok : everyKey (rowOK 3 level3) level4rr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrl && everyKey (rowOK 3 level3) level4rrr) = true
  rw [level4rrl_ok, level4rrr_ok]
  decide +kernel
def level4r : BinaryTree (List W) := .node [v43, v59, v107, v186, v226] level4rl level4rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4r_ok : everyKey (rowOK 3 level3) level4r = true := by
  change (_ && everyKey (rowOK 3 level3) level4rl && everyKey (rowOK 3 level3) level4rr) = true
  rw [level4rl_ok, level4rr_ok]
  decide +kernel
def level4 : BinaryTree (List W) := .node [v43, v59, v105, v172, v226] level4l level4r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4_ok : everyKey (rowOK 3 level3) level4 = true := by
  change (_ && everyKey (rowOK 3 level3) level4l && everyKey (rowOK 3 level3) level4r) = true
  rw [level4l_ok, level4r_ok]
  decide +kernel
theorem closed4 : Closed 4 level4 := closed_next 3 (by decide) level4 level3 closed3 level4_ok
def level5llllll : BinaryTree (List W) := (.node [v1, v43, v59, v107, v172, v226] (.node [v0, v43, v59, v107, v172, v226] .nil .nil) (.node [v2, v43, v59, v107, v172, v226] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llllll_ok : everyKey (rowOK 4 level4) level5llllll = true := by decide +kernel
def level5lllllr : BinaryTree (List W) := (.node [v5, v43, v59, v107, v172, v226] (.node [v4, v43, v59, v107, v172, v226] .nil .nil) (.node [v5, v59, v107, v149, v172, v196] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllllr_ok : everyKey (rowOK 4 level4) level5lllllr = true := by decide +kernel
def level5lllll : BinaryTree (List W) := .node [v3, v43, v59, v107, v172, v226] level5llllll level5lllllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllll_ok : everyKey (rowOK 4 level4) level5lllll = true := by
  change (_ && everyKey (rowOK 4 level4) level5llllll && everyKey (rowOK 4 level4) level5lllllr) = true
  rw [level5llllll_ok, level5lllllr_ok]
  decide +kernel
def level5llllr : BinaryTree (List W) := (.node [v8, v26, v43, v59, v107, v196] (.node [v7, v43, v59, v65, v172, v196] (.node [v6, v43, v107, v120, v172, v196] .nil .nil) (.node [v7, v43, v59, v107, v172, v226] .nil .nil)) (.node [v9, v14, v43, v59, v107, v172] (.node [v8, v43, v59, v107, v172, v226] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llllr_ok : everyKey (rowOK 4 level4) level5llllr = true := by decide +kernel
def level5llll : BinaryTree (List W) := .node [v6, v43, v59, v107, v172, v226] level5lllll level5llllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llll_ok : everyKey (rowOK 4 level4) level5llll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lllll && everyKey (rowOK 4 level4) level5llllr) = true
  rw [level5lllll_ok, level5llllr_ok]
  decide +kernel
def level5lllrll : BinaryTree (List W) := (.node [v9, v43, v59, v107, v172, v211] (.node [v9, v43, v59, v107, v137, v211] .nil .nil) (.node [v9, v43, v59, v107, v172, v226] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrll_ok : everyKey (rowOK 4 level4) level5lllrll = true := by decide +kernel
def level5lllrlr : BinaryTree (List W) := (.node [v10, v43, v59, v107, v172, v226] (.node [v9, v43, v59, v135, v172, v211] .nil .nil) (.node [v10, v59, v107, v146, v172, v211] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrlr_ok : everyKey (rowOK 4 level4) level5lllrlr = true := by decide +kernel
def level5lllrl : BinaryTree (List W) := .node [v9, v43, v59, v107, v188, v211] level5lllrll level5lllrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrl_ok : everyKey (rowOK 4 level4) level5lllrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lllrll && everyKey (rowOK 4 level4) level5lllrlr) = true
  rw [level5lllrll_ok, level5lllrlr_ok]
  decide +kernel
def level5lllrr : BinaryTree (List W) := (.node [v13, v24, v43, v59, v107, v211] (.node [v12, v43, v59, v63, v172, v211] (.node [v11, v43, v107, v117, v172, v211] .nil .nil) (.node [v12, v43, v59, v107, v172, v226] .nil .nil)) (.node [v14, v43, v59, v85, v172, v196] (.node [v13, v43, v59, v107, v172, v226] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrr_ok : everyKey (rowOK 4 level4) level5lllrr = true := by decide +kernel
def level5lllr : BinaryTree (List W) := .node [v11, v43, v59, v107, v172, v226] level5lllrl level5lllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllr_ok : everyKey (rowOK 4 level4) level5lllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lllrl && everyKey (rowOK 4 level4) level5lllrr) = true
  rw [level5lllrl_ok, level5lllrr_ok]
  decide +kernel
def level5lll : BinaryTree (List W) := .node [v9, v43, v59, v85, v172, v211] level5llll level5lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lll_ok : everyKey (rowOK 4 level4) level5lll = true := by
  change (_ && everyKey (rowOK 4 level4) level5llll && everyKey (rowOK 4 level4) level5lllr) = true
  rw [level5llll_ok, level5lllr_ok]
  decide +kernel
def level5llrlll : BinaryTree (List W) := (.node [v14, v43, v59, v107, v172, v226] (.node [v14, v43, v59, v107, v172, v196] .nil .nil) (.node [v14, v43, v59, v107, v188, v196] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrlll_ok : everyKey (rowOK 4 level4) level5llrlll = true := by decide +kernel
def level5llrllr : BinaryTree (List W) := (.node [v16, v81, v107, v172, v196, v211] (.node [v16, v43, v59, v107, v172, v226] .nil .nil) (.node [v17, v43, v59, v107, v172, v226] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrllr_ok : everyKey (rowOK 4 level4) level5llrllr = true := by decide +kernel
def level5llrll : BinaryTree (List W) := .node [v14, v43, v59, v135, v172, v196] level5llrlll level5llrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrll_ok : everyKey (rowOK 4 level4) level5llrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrlll && everyKey (rowOK 4 level4) level5llrllr) = true
  rw [level5llrlll_ok, level5llrllr_ok]
  decide +kernel
def level5llrlr : BinaryTree (List W) := (.node [v20, v43, v156, v172, v196, v211] (.node [v18, v59, v107, v137, v196, v211] (.node [v18, v43, v59, v107, v172, v226] .nil .nil) (.node [v20, v43, v59, v107, v172, v226] .nil .nil)) (.node [v21, v43, v107, v116, v196, v211] (.node [v21, v43, v59, v107, v172, v226] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrlr_ok : everyKey (rowOK 4 level4) level5llrlr = true := by decide +kernel
def level5llrl : BinaryTree (List W) := .node [v17, v59, v135, v172, v196, v211] level5llrll level5llrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrl_ok : everyKey (rowOK 4 level4) level5llrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrll && everyKey (rowOK 4 level4) level5llrlr) = true
  rw [level5llrll_ok, level5llrlr_ok]
  decide +kernel
def level5llrrll : BinaryTree (List W) := (.node [v23, v43, v59, v107, v196, v211] (.node [v22, v43, v59, v107, v172, v226] .nil .nil) (.node [v24, v43, v59, v107, v172, v226] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrll_ok : everyKey (rowOK 4 level4) level5llrrll = true := by decide +kernel
def level5llrrlr : BinaryTree (List W) := (.node [v27, v43, v59, v107, v172, v226] (.node [v26, v43, v59, v107, v172, v226] .nil .nil) (.node [v27, v43, v59, v107, v196, v211] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrlr_ok : everyKey (rowOK 4 level4) level5llrrlr = true := by decide +kernel
def level5llrrl : BinaryTree (List W) := .node [v25, v43, v59, v107, v172, v211] level5llrrll level5llrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrl_ok : everyKey (rowOK 4 level4) level5llrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrrll && everyKey (rowOK 4 level4) level5llrrlr) = true
  rw [level5llrrll_ok, level5llrrlr_ok]
  decide +kernel
def level5llrrr : BinaryTree (List W) := (.node [v35, v43, v59, v107, v172, v226] (.node [v27, v43, v59, v107, v226] (.node [v27, v43, v59, v107, v211, v226] .nil .nil) (.node [v34, v43, v59, v107, v172, v196] .nil .nil)) (.node [v36, v43, v59, v107, v172, v226] (.node [v35, v59, v107, v188, v196, v211] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrr_ok : everyKey (rowOK 4 level4) level5llrrr = true := by decide +kernel
def level5llrr : BinaryTree (List W) := .node [v27, v43, v59, v107, v196, v226] level5llrrl level5llrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrr_ok : everyKey (rowOK 4 level4) level5llrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrrl && everyKey (rowOK 4 level4) level5llrrr) = true
  rw [level5llrrl_ok, level5llrrr_ok]
  decide +kernel
def level5llr : BinaryTree (List W) := .node [v22, v43, v59, v61, v196, v211] level5llrl level5llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llr_ok : everyKey (rowOK 4 level4) level5llr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrl && everyKey (rowOK 4 level4) level5llrr) = true
  rw [level5llrl_ok, level5llrr_ok]
  decide +kernel
def level5ll : BinaryTree (List W) := .node [v14, v43, v59, v107, v137, v196] level5lll level5llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5ll_ok : everyKey (rowOK 4 level4) level5ll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lll && everyKey (rowOK 4 level4) level5llr) = true
  rw [level5lll_ok, level5llr_ok]
  decide +kernel
def level5lrllll : BinaryTree (List W) := (.node [v37, v50, v107, v172, v196, v211] (.node [v37, v43, v59, v107, v172, v226] .nil .nil) (.node [v38, v43, v59, v107, v172, v226] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrllll_ok : everyKey (rowOK 4 level4) level5lrllll = true := by decide +kernel
def level5lrlllr : BinaryTree (List W) := (.node [v40, v43, v59, v107, v172, v226] (.node [v39, v43, v59, v107, v172, v211] .nil .nil) (.node [v40, v59, v107, v172, v196, v215] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlllr_ok : everyKey (rowOK 4 level4) level5lrlllr = true := by decide +kernel
def level5lrlll : BinaryTree (List W) := .node [v38, v59, v107, v172, v200, v211] level5lrllll level5lrlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlll_ok : everyKey (rowOK 4 level4) level5lrlll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrllll && everyKey (rowOK 4 level4) level5lrlllr) = true
  rw [level5lrllll_ok, level5lrlllr_ok]
  decide +kernel
def level5lrllr : BinaryTree (List W) := (.node [v43, v49, v59, v107, v172, v226] (.node [v43, v48, v59, v107, v172, v226] (.node [v43, v44, v59, v107, v172, v196] .nil .nil) (.node [v43, v48, v107, v190, v196, v211] .nil .nil)) (.node [v43, v50, v59, v107, v172, v226] (.node [v43, v49, v83, v172, v196, v211] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrllr_ok : everyKey (rowOK 4 level4) level5lrllr = true := by decide +kernel
def level5lrll : BinaryTree (List W) := .node [v41, v43, v59, v107, v172, v226] level5lrlll level5lrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrll_ok : everyKey (rowOK 4 level4) level5lrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrlll && everyKey (rowOK 4 level4) level5lrllr) = true
  rw [level5lrlll_ok, level5lrllr_ok]
  decide +kernel
def level5lrlrll : BinaryTree (List W) := (.node [v43, v54, v59, v107, v172, v226] (.node [v43, v53, v107, v172, v196, v211] .nil .nil) (.node [v43, v54, v107, v172, v202, v211] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrll_ok : everyKey (rowOK 4 level4) level5lrlrll = true := by decide +kernel
def level5lrlrlr : BinaryTree (List W) := (.node [v43, v56, v107, v172, v196, v217] (.node [v43, v56, v59, v107, v172, v226] .nil .nil) (.node [v43, v57, v59, v107, v172, v226] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrlr_ok : everyKey (rowOK 4 level4) level5lrlrlr = true := by decide +kernel
def level5lrlrl : BinaryTree (List W) := .node [v43, v55, v59, v107, v172, v211] level5lrlrll level5lrlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrl_ok : everyKey (rowOK 4 level4) level5lrlrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrlrll && everyKey (rowOK 4 level4) level5lrlrlr) = true
  rw [level5lrlrll_ok, level5lrlrlr_ok]
  decide +kernel
def level5lrlrr : BinaryTree (List W) := (.node [v43, v59, v64, v107, v172, v211] (.node [v43, v59, v62, v172, v196, v211] (.node [v43, v59, v61, v107, v172, v226] .nil .nil) (.node [v43, v59, v63, v107, v172, v226] .nil .nil)) (.node [v43, v59, v66, v107, v172, v226] (.node [v43, v59, v65, v107, v172, v226] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrr_ok : everyKey (rowOK 4 level4) level5lrlrr = true := by decide +kernel
def level5lrlr : BinaryTree (List W) := .node [v43, v59, v60, v107, v172, v196] level5lrlrl level5lrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlr_ok : everyKey (rowOK 4 level4) level5lrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrlrl && everyKey (rowOK 4 level4) level5lrlrr) = true
  rw [level5lrlrl_ok, level5lrlrr_ok]
  decide +kernel
def level5lrl : BinaryTree (List W) := .node [v43, v52, v107, v172, v196, v211] level5lrll level5lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrl_ok : everyKey (rowOK 4 level4) level5lrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrll && everyKey (rowOK 4 level4) level5lrlr) = true
  rw [level5lrll_ok, level5lrlr_ok]
  decide +kernel
def level5lrrlll : BinaryTree (List W) := (.node [v43, v59, v66, v172, v211, v226] (.node [v43, v59, v66, v172, v196, v226] .nil .nil) (.node [v43, v59, v66, v172, v226] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrlll_ok : everyKey (rowOK 4 level4) level5lrrlll = true := by decide +kernel
def level5lrrllr : BinaryTree (List W) := (.node [v43, v59, v82, v107, v172, v226] (.node [v43, v59, v81, v107, v172, v226] .nil .nil) (.node [v43, v59, v82, v191, v196, v211] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrllr_ok : everyKey (rowOK 4 level4) level5lrrllr = true := by decide +kernel
def level5lrrll : BinaryTree (List W) := .node [v43, v59, v73, v107, v172, v196] level5lrrlll level5lrrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrll_ok : everyKey (rowOK 4 level4) level5lrrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrlll && everyKey (rowOK 4 level4) level5lrrllr) = true
  rw [level5lrrlll_ok, level5lrrllr_ok]
  decide +kernel
def level5lrrlr : BinaryTree (List W) := (.node [v43, v59, v85, v172, v196, v226] (.node [v43, v59, v85, v137, v196, v211] (.node [v43, v59, v85, v107, v172, v226] .nil .nil) (.node [v43, v59, v85, v172, v196, v211] .nil .nil)) (.node [v43, v59, v85, v172, v226] (.node [v43, v59, v85, v172, v211, v226] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrlr_ok : everyKey (rowOK 4 level4) level5lrrlr = true := by decide +kernel
def level5lrrl : BinaryTree (List W) := .node [v43, v59, v83, v107, v172, v226] level5lrrll level5lrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrl_ok : everyKey (rowOK 4 level4) level5lrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrll && everyKey (rowOK 4 level4) level5lrrlr) = true
  rw [level5lrrll_ok, level5lrrlr_ok]
  decide +kernel
def level5lrrrll : BinaryTree (List W) := (.node [v43, v59, v88, v172, v196, v211] (.node [v43, v59, v86, v172, v196, v211] .nil .nil) (.node [v43, v59, v89, v172, v196, v211] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrll_ok : everyKey (rowOK 4 level4) level5lrrrll = true := by decide +kernel
def level5lrrrlr : BinaryTree (List W) := (.node [v43, v59, v92, v107, v172, v226] (.node [v43, v59, v91, v172, v196, v211] .nil .nil) (.node [v43, v59, v92, v172, v205, v211] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrlr_ok : everyKey (rowOK 4 level4) level5lrrrlr = true := by decide +kernel
def level5lrrrl : BinaryTree (List W) := .node [v43, v59, v90, v172, v196, v211] level5lrrrll level5lrrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrl_ok : everyKey (rowOK 4 level4) level5lrrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrrll && everyKey (rowOK 4 level4) level5lrrrlr) = true
  rw [level5lrrrll_ok, level5lrrrlr_ok]
  decide +kernel
def level5lrrrr : BinaryTree (List W) := (.node [v43, v59, v96, v172, v196, v211] (.node [v43, v59, v95, v107, v172, v226] (.node [v43, v59, v94, v172, v196, v211] .nil .nil) (.node [v43, v59, v95, v172, v196, v220] .nil .nil)) (.node [v43, v59, v98, v172, v196, v211] (.node [v43, v59, v97, v172, v196, v211] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrr_ok : everyKey (rowOK 4 level4) level5lrrrr = true := by decide +kernel
def level5lrrr : BinaryTree (List W) := .node [v43, v59, v93, v107, v172, v211] level5lrrrl level5lrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrr_ok : everyKey (rowOK 4 level4) level5lrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrrl && everyKey (rowOK 4 level4) level5lrrrr) = true
  rw [level5lrrrl_ok, level5lrrrr_ok]
  decide +kernel
def level5lrr : BinaryTree (List W) := .node [v43, v59, v85, v188, v196, v211] level5lrrl level5lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrr_ok : everyKey (rowOK 4 level4) level5lrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrl && everyKey (rowOK 4 level4) level5lrrr) = true
  rw [level5lrrl_ok, level5lrrr_ok]
  decide +kernel
def level5lr : BinaryTree (List W) := .node [v43, v59, v66, v172, v196, v211] level5lrl level5lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lr_ok : everyKey (rowOK 4 level4) level5lr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrl && everyKey (rowOK 4 level4) level5lrr) = true
  rw [level5lrl_ok, level5lrr_ok]
  decide +kernel
def level5l : BinaryTree (List W) := .node [v36, v59, v85, v172, v196, v211] level5ll level5lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5l_ok : everyKey (rowOK 4 level4) level5l = true := by
  change (_ && everyKey (rowOK 4 level4) level5ll && everyKey (rowOK 4 level4) level5lr) = true
  rw [level5ll_ok, level5lr_ok]
  decide +kernel
def level5rlllll : BinaryTree (List W) := (.node [v43, v59, v99, v172, v196, v226] (.node [v43, v59, v99, v172, v196, v211] .nil .nil) (.node [v43, v59, v99, v172, v211, v226] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlllll_ok : everyKey (rowOK 4 level4) level5rlllll = true := by decide +kernel
def level5rllllr : BinaryTree (List W) := (.node [v43, v59, v107, v113, v172, v196] (.node [v43, v59, v102, v172, v196, v211] .nil .nil) (.node [v43, v59, v107, v116, v172, v226] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllllr_ok : everyKey (rowOK 4 level4) level5rllllr = true := by decide +kernel
def level5rllll : BinaryTree (List W) := .node [v43, v59, v99, v172, v226] level5rlllll level5rllllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllll_ok : everyKey (rowOK 4 level4) level5rllll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlllll && everyKey (rowOK 4 level4) level5rllllr) = true
  rw [level5rlllll_ok, level5rllllr_ok]
  decide +kernel
def level5rlllr : BinaryTree (List W) := (.node [v43, v59, v107, v125, v172, v196] (.node [v43, v59, v107, v120, v172, v226] (.node [v43, v59, v107, v118, v172, v211] .nil .nil) (.node [v43, v59, v107, v122, v172, v226] .nil .nil)) (.node [v43, v59, v107, v137, v172, v226] (.node [v43, v59, v107, v135, v172, v226] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlllr_ok : everyKey (rowOK 4 level4) level5rlllr = true := by decide +kernel
def level5rlll : BinaryTree (List W) := .node [v43, v59, v107, v117, v172, v226] level5rllll level5rlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlll_ok : everyKey (rowOK 4 level4) level5rlll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rllll && everyKey (rowOK 4 level4) level5rlllr) = true
  rw [level5rllll_ok, level5rlllr_ok]
  decide +kernel
def level5rllrll : BinaryTree (List W) := (.node [v43, v59, v107, v137, v211, v226] (.node [v43, v59, v107, v137, v196, v226] .nil .nil) (.node [v43, v59, v107, v137, v226] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrll_ok : everyKey (rowOK 4 level4) level5rllrll = true := by decide +kernel
def level5rllrlr : BinaryTree (List W) := (.node [v43, v59, v107, v141, v196, v211] (.node [v43, v59, v107, v140, v196, v211] .nil .nil) (.node [v43, v59, v107, v142, v196, v211] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrlr_ok : everyKey (rowOK 4 level4) level5rllrlr = true := by decide +kernel
def level5rllrl : BinaryTree (List W) := .node [v43, v59, v107, v138, v196, v211] level5rllrll level5rllrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrl_ok : everyKey (rowOK 4 level4) level5rllrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rllrll && everyKey (rowOK 4 level4) level5rllrlr) = true
  rw [level5rllrll_ok, level5rllrlr_ok]
  decide +kernel
def level5rllrr : BinaryTree (List W) := (.node [v43, v59, v107, v151, v172, v226] (.node [v43, v59, v107, v147, v172, v211] (.node [v43, v59, v107, v146, v172, v226] .nil .nil) (.node [v43, v59, v107, v149, v172, v226] .nil .nil)) (.node [v43, v59, v107, v156, v172, v226] (.node [v43, v59, v107, v154, v172, v196] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrr_ok : everyKey (rowOK 4 level4) level5rllrr = true := by decide +kernel
def level5rllr : BinaryTree (List W) := .node [v43, v59, v107, v143, v196, v211] level5rllrl level5rllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllr_ok : everyKey (rowOK 4 level4) level5rllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rllrl && everyKey (rowOK 4 level4) level5rllrr) = true
  rw [level5rllrl_ok, level5rllrr_ok]
  decide +kernel
def level5rll : BinaryTree (List W) := .node [v43, v59, v107, v137, v196, v211] level5rlll level5rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rll_ok : everyKey (rowOK 4 level4) level5rll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlll && everyKey (rowOK 4 level4) level5rllr) = true
  rw [level5rlll_ok, level5rllr_ok]
  decide +kernel
def level5rlrlll : BinaryTree (List W) := (.node [v43, v59, v107, v158, v172, v211] (.node [v43, v59, v107, v157, v209, v211] .nil .nil) (.node [v43, v59, v107, v159, v196, v211] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrlll_ok : everyKey (rowOK 4 level4) level5rlrlll = true := by decide +kernel
def level5rlrllr : BinaryTree (List W) := (.node [v43, v59, v107, v161, v196, v211] (.node [v43, v59, v107, v160, v196, v224] .nil .nil) (.node [v43, v59, v107, v162, v196, v211] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrllr_ok : everyKey (rowOK 4 level4) level5rlrllr = true := by decide +kernel
def level5rlrll : BinaryTree (List W) := .node [v43, v59, v107, v160, v172, v226] level5rlrlll level5rlrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrll_ok : everyKey (rowOK 4 level4) level5rlrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrlll && everyKey (rowOK 4 level4) level5rlrllr) = true
  rw [level5rlrlll_ok, level5rlrllr_ok]
  decide +kernel
def level5rlrlr : BinaryTree (List W) := (.node [v43, v59, v107, v164, v211, v226] (.node [v43, v59, v107, v164, v196, v211] (.node [v43, v59, v107, v164, v172, v226] .nil .nil) (.node [v43, v59, v107, v164, v196, v226] .nil .nil)) (.node [v43, v59, v107, v167, v196, v211] (.node [v43, v59, v107, v164, v226] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrlr_ok : everyKey (rowOK 4 level4) level5rlrlr = true := by decide +kernel
def level5rlrl : BinaryTree (List W) := .node [v43, v59, v107, v163, v196, v211] level5rlrll level5rlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrl_ok : everyKey (rowOK 4 level4) level5rlrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrll && everyKey (rowOK 4 level4) level5rlrlr) = true
  rw [level5rlrll_ok, level5rlrlr_ok]
  decide +kernel
def level5rlrrll : BinaryTree (List W) := (.node [v43, v59, v107, v172, v190, v226] (.node [v43, v59, v107, v172, v188, v226] .nil .nil) (.node [v43, v59, v107, v172, v191, v226] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrll_ok : everyKey (rowOK 4 level4) level5rlrrll = true := by decide +kernel
def level5rlrrlr : BinaryTree (List W) := (.node [v43, v59, v107, v172, v195, v226] (.node [v43, v59, v107, v172, v193, v196] .nil .nil) (.node [v43, v59, v107, v172, v196, v211] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrlr_ok : everyKey (rowOK 4 level4) level5rlrrlr = true := by decide +kernel
def level5rlrrl : BinaryTree (List W) := .node [v43, v59, v107, v172, v192, v211] level5rlrrll level5rlrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrl_ok : everyKey (rowOK 4 level4) level5rlrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrrll && everyKey (rowOK 4 level4) level5rlrrlr) = true
  rw [level5rlrrll_ok, level5rlrrlr_ok]
  decide +kernel
def level5rlrrr : BinaryTree (List W) := (.node [v43, v59, v107, v172, v196, v218] (.node [v43, v59, v107, v172, v196, v214] (.node [v43, v59, v107, v172, v196, v213] .nil .nil) (.node [v43, v59, v107, v172, v196, v216] .nil .nil)) (.node [v43, v59, v107, v172, v196, v221] (.node [v43, v59, v107, v172, v196, v219] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrr_ok : everyKey (rowOK 4 level4) level5rlrrr = true := by decide +kernel
def level5rlrr : BinaryTree (List W) := .node [v43, v59, v107, v172, v196, v212] level5rlrrl level5rlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrr_ok : everyKey (rowOK 4 level4) level5rlrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrrl && everyKey (rowOK 4 level4) level5rlrrr) = true
  rw [level5rlrrl_ok, level5rlrrr_ok]
  decide +kernel
def level5rlr : BinaryTree (List W) := .node [v43, v59, v107, v172, v178, v196] level5rlrl level5rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlr_ok : everyKey (rowOK 4 level4) level5rlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrl && everyKey (rowOK 4 level4) level5rlrr) = true
  rw [level5rlrl_ok, level5rlrr_ok]
  decide +kernel
def level5rl : BinaryTree (List W) := .node [v43, v59, v107, v157, v172, v226] level5rll level5rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rl_ok : everyKey (rowOK 4 level4) level5rl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rll && everyKey (rowOK 4 level4) level5rlr) = true
  rw [level5rll_ok, level5rlr_ok]
  decide +kernel
def level5rrllll : BinaryTree (List W) := (.node [v43, v59, v107, v172, v196, v226] (.node [v43, v59, v107, v172, v196, v223] .nil .nil) (.node [v43, v59, v107, v172, v197, v211] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrllll_ok : everyKey (rowOK 4 level4) level5rrllll = true := by decide +kernel
def level5rrlllr : BinaryTree (List W) := (.node [v43, v59, v107, v172, v200, v226] (.node [v43, v59, v107, v172, v199, v211] .nil .nil) (.node [v43, v59, v107, v172, v201, v211] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlllr_ok : everyKey (rowOK 4 level4) level5rrlllr = true := by decide +kernel
def level5rrlll : BinaryTree (List W) := .node [v43, v59, v107, v172, v198, v211] level5rrllll level5rrlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlll_ok : everyKey (rowOK 4 level4) level5rrlll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrllll && everyKey (rowOK 4 level4) level5rrlllr) = true
  rw [level5rrllll_ok, level5rrlllr_ok]
  decide +kernel
def level5rrllr : BinaryTree (List W) := (.node [v43, v59, v107, v172, v206, v211] (.node [v43, v59, v107, v172, v204, v211] (.node [v43, v59, v107, v172, v203, v211] .nil .nil) (.node [v43, v59, v107, v172, v205, v226] .nil .nil)) (.node [v43, v59, v107, v172, v208, v211] (.node [v43, v59, v107, v172, v207, v211] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrllr_ok : everyKey (rowOK 4 level4) level5rrllr = true := by decide +kernel
def level5rrll : BinaryTree (List W) := .node [v43, v59, v107, v172, v202, v226] level5rrlll level5rrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrll_ok : everyKey (rowOK 4 level4) level5rrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrlll && everyKey (rowOK 4 level4) level5rrllr) = true
  rw [level5rrlll_ok, level5rrllr_ok]
  decide +kernel
def level5rrlrll : BinaryTree (List W) := (.node [v43, v59, v107, v172, v215, v226] (.node [v43, v59, v107, v172, v211, v226] .nil .nil) (.node [v43, v59, v107, v172, v217, v226] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrll_ok : everyKey (rowOK 4 level4) level5rrlrll = true := by decide +kernel
def level5rrlrlr : BinaryTree (List W) := (.node [v43, v59, v107, v172, v226] (.node [v43, v59, v107, v172, v224, v226] .nil .nil) (.node [v43, v59, v107, v172, v226, v226] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrlr_ok : everyKey (rowOK 4 level4) level5rrlrlr = true := by decide +kernel
def level5rrlrl : BinaryTree (List W) := .node [v43, v59, v107, v172, v220, v226] level5rrlrll level5rrlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrl_ok : everyKey (rowOK 4 level4) level5rrlrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrlrll && everyKey (rowOK 4 level4) level5rrlrlr) = true
  rw [level5rrlrll_ok, level5rrlrlr_ok]
  decide +kernel
def level5rrlrr : BinaryTree (List W) := (.node [v43, v59, v107, v176, v196, v211] (.node [v43, v59, v107, v172, v226, v230] (.node [v43, v59, v107, v172, v226, v228] .nil .nil) (.node [v43, v59, v107, v172, v226, v231] .nil .nil)) (.node [v43, v59, v107, v179, v196, v211] (.node [v43, v59, v107, v177, v196, v211] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrr_ok : everyKey (rowOK 4 level4) level5rrlrr = true := by decide +kernel
def level5rrlr : BinaryTree (List W) := .node [v43, v59, v107, v172, v226, v227] level5rrlrl level5rrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlr_ok : everyKey (rowOK 4 level4) level5rrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrlrl && everyKey (rowOK 4 level4) level5rrlrr) = true
  rw [level5rrlrl_ok, level5rrlrr_ok]
  decide +kernel
def level5rrl : BinaryTree (List W) := .node [v43, v59, v107, v172, v209, v226] level5rrll level5rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrl_ok : everyKey (rowOK 4 level4) level5rrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrll && everyKey (rowOK 4 level4) level5rrlr) = true
  rw [level5rrll_ok, level5rrlr_ok]
  decide +kernel
def level5rrrlll : BinaryTree (List W) := (.node [v43, v59, v107, v182, v196, v211] (.node [v43, v59, v107, v181, v196, v211] .nil .nil) (.node [v43, v59, v107, v183, v196, v211] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrlll_ok : everyKey (rowOK 4 level4) level5rrrlll = true := by decide +kernel
def level5rrrllr : BinaryTree (List W) := (.node [v43, v59, v107, v188, v196, v226] (.node [v43, v59, v107, v188, v196, v211] .nil .nil) (.node [v43, v59, v107, v188, v211, v226] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrllr_ok : everyKey (rowOK 4 level4) level5rrrllr = true := by decide +kernel
def level5rrrll : BinaryTree (List W) := .node [v43, v59, v107, v184, v196, v211] level5rrrlll level5rrrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrll_ok : everyKey (rowOK 4 level4) level5rrrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrlll && everyKey (rowOK 4 level4) level5rrrllr) = true
  rw [level5rrrlll_ok, level5rrrllr_ok]
  decide +kernel
def level5rrrlr : BinaryTree (List W) := (.node [v43, v59, v114, v172, v196, v211] (.node [v43, v59, v111, v172, v196, v211] (.node [v43, v59, v107, v189, v196, v211] .nil .nil) (.node [v43, v59, v112, v172, v196, v211] .nil .nil)) (.node [v43, v59, v128, v172, v196, v211] (.node [v43, v59, v115, v172, v196, v211] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrlr_ok : everyKey (rowOK 4 level4) level5rrrlr = true := by decide +kernel
def level5rrrl : BinaryTree (List W) := .node [v43, v59, v107, v188, v226] level5rrrll level5rrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrl_ok : everyKey (rowOK 4 level4) level5rrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrll && everyKey (rowOK 4 level4) level5rrrlr) = true
  rw [level5rrrll_ok, level5rrrlr_ok]
  decide +kernel
def level5rrrrl : BinaryTree (List W) := (.node [v43, v59, v135, v172, v196, v211] (.node [v43, v59, v131, v172, v196, v211] (.node [v43, v59, v130, v172, v196, v211] .nil .nil) (.node [v43, v59, v135, v137, v196, v211] .nil .nil)) (.node [v43, v59, v135, v172, v211, v226] (.node [v43, v59, v135, v172, v196, v226] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrl_ok : everyKey (rowOK 4 level4) level5rrrrl = true := by decide +kernel
def level5rrrrr : BinaryTree (List W) := (.node [v43, v79, v107, v172, v196, v211] (.node [v43, v59, v155, v172, v196, v211] (.node [v43, v59, v135, v188, v196, v211] .nil .nil) (.node [v43, v78, v107, v172, v196, v211] .nil .nil)) (.node [v59, v107, v137, v188, v196, v211] (.node [v59, v85, v135, v172, v196, v211] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrr_ok : everyKey (rowOK 4 level4) level5rrrrr = true := by decide +kernel
def level5rrrr : BinaryTree (List W) := .node [v43, v59, v135, v172, v226] level5rrrrl level5rrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrr_ok : everyKey (rowOK 4 level4) level5rrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrrl && everyKey (rowOK 4 level4) level5rrrrr) = true
  rw [level5rrrrl_ok, level5rrrrr_ok]
  decide +kernel
def level5rrr : BinaryTree (List W) := .node [v43, v59, v129, v172, v196, v211] level5rrrl level5rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrr_ok : everyKey (rowOK 4 level4) level5rrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrl && everyKey (rowOK 4 level4) level5rrrr) = true
  rw [level5rrrl_ok, level5rrrr_ok]
  decide +kernel
def level5rr : BinaryTree (List W) := .node [v43, v59, v107, v180, v196, v211] level5rrl level5rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rr_ok : everyKey (rowOK 4 level4) level5rr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrl && everyKey (rowOK 4 level4) level5rrr) = true
  rw [level5rrl_ok, level5rrr_ok]
  decide +kernel
def level5r : BinaryTree (List W) := .node [v43, v59, v107, v172, v196, v222] level5rl level5rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5r_ok : everyKey (rowOK 4 level4) level5r = true := by
  change (_ && everyKey (rowOK 4 level4) level5rl && everyKey (rowOK 4 level4) level5rr) = true
  rw [level5rl_ok, level5rr_ok]
  decide +kernel
def level5 : BinaryTree (List W) := .node [v43, v59, v99, v107, v172, v226] level5l level5r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5_ok : everyKey (rowOK 4 level4) level5 = true := by
  change (_ && everyKey (rowOK 4 level4) level5l && everyKey (rowOK 4 level4) level5r) = true
  rw [level5l_ok, level5r_ok]
  decide +kernel
theorem closed5 : Closed 5 level5 := closed_next 4 (by decide) level5 level4 closed4 level5_ok
def level6llll : BinaryTree (List W) := (.node [v7, v43, v59, v107, v172, v196, v211] (.node [v6, v43, v59, v107, v172, v196, v211] (.node [v5, v43, v59, v107, v172, v196, v211] .nil .nil) .nil) (.node [v8, v43, v59, v107, v172, v196, v211] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llll_ok : everyKey (rowOK 5 level5) level6llll = true := by decide +kernel
def level6lllr : BinaryTree (List W) := (.node [v10, v43, v59, v107, v172, v196, v211] (.node [v9, v43, v59, v107, v172, v211] .nil .nil) (.node [v11, v43, v59, v107, v172, v196, v211] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllr_ok : everyKey (rowOK 5 level5) level6lllr = true := by decide +kernel
def level6lll : BinaryTree (List W) := .node [v9, v43, v59, v107, v172, v196, v211] level6llll level6lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lll_ok : everyKey (rowOK 5 level5) level6lll = true := by
  change (_ && everyKey (rowOK 5 level5) level6llll && everyKey (rowOK 5 level5) level6lllr) = true
  rw [level6llll_ok, level6lllr_ok]
  decide +kernel
def level6llrl : BinaryTree (List W) := (.node [v14, v43, v59, v107, v172, v196, v211] (.node [v14, v43, v59, v107, v172, v196] (.node [v13, v43, v59, v107, v172, v196, v211] .nil .nil) .nil) (.node [v16, v43, v59, v107, v172, v196, v211] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrl_ok : everyKey (rowOK 5 level5) level6llrl = true := by decide +kernel
def level6llrr : BinaryTree (List W) := (.node [v20, v43, v59, v107, v172, v196, v211] (.node [v18, v43, v59, v107, v172, v196, v211] .nil .nil) (.node [v21, v43, v59, v107, v172, v196, v211] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrr_ok : everyKey (rowOK 5 level5) level6llrr = true := by decide +kernel
def level6llr : BinaryTree (List W) := .node [v17, v43, v59, v107, v172, v196, v211] level6llrl level6llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llr_ok : everyKey (rowOK 5 level5) level6llr = true := by
  change (_ && everyKey (rowOK 5 level5) level6llrl && everyKey (rowOK 5 level5) level6llrr) = true
  rw [level6llrl_ok, level6llrr_ok]
  decide +kernel
def level6ll : BinaryTree (List W) := .node [v12, v43, v59, v107, v172, v196, v211] level6lll level6llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6ll_ok : everyKey (rowOK 5 level5) level6ll = true := by
  change (_ && everyKey (rowOK 5 level5) level6lll && everyKey (rowOK 5 level5) level6llr) = true
  rw [level6lll_ok, level6llr_ok]
  decide +kernel
def level6lrll : BinaryTree (List W) := (.node [v35, v43, v59, v107, v172, v196, v211] (.node [v26, v43, v59, v107, v172, v196, v211] (.node [v24, v43, v59, v107, v172, v196, v211] .nil .nil) .nil) (.node [v36, v43, v59, v107, v172, v196, v211] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrll_ok : everyKey (rowOK 5 level5) level6lrll = true := by decide +kernel
def level6lrlr : BinaryTree (List W) := (.node [v40, v43, v59, v107, v172, v196, v211] (.node [v38, v43, v59, v107, v172, v196, v211] .nil .nil) (.node [v43, v48, v59, v107, v172, v196, v211] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlr_ok : everyKey (rowOK 5 level5) level6lrlr = true := by decide +kernel
def level6lrl : BinaryTree (List W) := .node [v37, v43, v59, v107, v172, v196, v211] level6lrll level6lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrl_ok : everyKey (rowOK 5 level5) level6lrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrll && everyKey (rowOK 5 level5) level6lrlr) = true
  rw [level6lrll_ok, level6lrlr_ok]
  decide +kernel
def level6lrrl : BinaryTree (List W) := (.node [v43, v54, v59, v107, v172, v196, v211] (.node [v43, v50, v59, v107, v172, v196, v211] .nil .nil) (.node [v43, v56, v59, v107, v172, v196, v211] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrl_ok : everyKey (rowOK 5 level5) level6lrrl = true := by decide +kernel
def level6lrrr : BinaryTree (List W) := (.node [v43, v59, v65, v107, v172, v196, v211] (.node [v43, v59, v63, v107, v172, v196, v211] .nil .nil) (.node [v43, v59, v81, v107, v172, v196, v211] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrr_ok : everyKey (rowOK 5 level5) level6lrrr = true := by decide +kernel
def level6lrr : BinaryTree (List W) := .node [v43, v59, v61, v107, v172, v196, v211] level6lrrl level6lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrr_ok : everyKey (rowOK 5 level5) level6lrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrrl && everyKey (rowOK 5 level5) level6lrrr) = true
  rw [level6lrrl_ok, level6lrrr_ok]
  decide +kernel
def level6lr : BinaryTree (List W) := .node [v43, v49, v59, v107, v172, v196, v211] level6lrl level6lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lr_ok : everyKey (rowOK 5 level5) level6lr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrl && everyKey (rowOK 5 level5) level6lrr) = true
  rw [level6lrl_ok, level6lrr_ok]
  decide +kernel
def level6l : BinaryTree (List W) := .node [v22, v43, v59, v107, v172, v196, v211] level6ll level6lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6l_ok : everyKey (rowOK 5 level5) level6l = true := by
  change (_ && everyKey (rowOK 5 level5) level6ll && everyKey (rowOK 5 level5) level6lr) = true
  rw [level6ll_ok, level6lr_ok]
  decide +kernel
def level6rlll : BinaryTree (List W) := (.node [v43, v59, v85, v172, v196, v211] (.node [v43, v59, v85, v107, v172, v196, v211] (.node [v43, v59, v83, v107, v172, v196, v211] .nil .nil) .nil) (.node [v43, v59, v92, v107, v172, v196, v211] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlll_ok : everyKey (rowOK 5 level5) level6rlll = true := by decide +kernel
def level6rllr : BinaryTree (List W) := (.node [v43, v59, v107, v117, v172, v196, v211] (.node [v43, v59, v107, v116, v172, v196, v211] .nil .nil) (.node [v43, v59, v107, v120, v172, v196, v211] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllr_ok : everyKey (rowOK 5 level5) level6rllr = true := by decide +kernel
def level6rll : BinaryTree (List W) := .node [v43, v59, v95, v107, v172, v196, v211] level6rlll level6rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rll_ok : everyKey (rowOK 5 level5) level6rll = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlll && everyKey (rowOK 5 level5) level6rllr) = true
  rw [level6rlll_ok, level6rllr_ok]
  decide +kernel
def level6rlrl : BinaryTree (List W) := (.node [v43, v59, v107, v146, v172, v196, v211] (.node [v43, v59, v107, v137, v196, v211] (.node [v43, v59, v107, v137, v172, v196, v211] .nil .nil) .nil) (.node [v43, v59, v107, v149, v172, v196, v211] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrl_ok : everyKey (rowOK 5 level5) level6rlrl = true := by decide +kernel
def level6rlrr : BinaryTree (List W) := (.node [v43, v59, v107, v160, v172, v196, v211] (.node [v43, v59, v107, v157, v172, v196, v211] .nil .nil) (.node [v43, v59, v107, v172, v188, v196, v211] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrr_ok : everyKey (rowOK 5 level5) level6rlrr = true := by decide +kernel
def level6rlr : BinaryTree (List W) := .node [v43, v59, v107, v156, v172, v196, v211] level6rlrl level6rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlr_ok : everyKey (rowOK 5 level5) level6rlr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlrl && everyKey (rowOK 5 level5) level6rlrr) = true
  rw [level6rlrl_ok, level6rlrr_ok]
  decide +kernel
def level6rl : BinaryTree (List W) := .node [v43, v59, v107, v135, v172, v196, v211] level6rll level6rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rl_ok : everyKey (rowOK 5 level5) level6rl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rll && everyKey (rowOK 5 level5) level6rlr) = true
  rw [level6rll_ok, level6rlr_ok]
  decide +kernel
def level6rrll : BinaryTree (List W) := (.node [v43, v59, v107, v172, v196, v200, v211] (.node [v43, v59, v107, v172, v195, v196, v211] (.node [v43, v59, v107, v172, v191, v196, v211] .nil .nil) .nil) (.node [v43, v59, v107, v172, v196, v202, v211] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrll_ok : everyKey (rowOK 5 level5) level6rrll = true := by decide +kernel
def level6rrlr : BinaryTree (List W) := (.node [v43, v59, v107, v172, v196, v211, v215] (.node [v43, v59, v107, v172, v196, v209, v211] .nil .nil) (.node [v43, v59, v107, v172, v196, v211, v217] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlr_ok : everyKey (rowOK 5 level5) level6rrlr = true := by decide +kernel
def level6rrl : BinaryTree (List W) := .node [v43, v59, v107, v172, v196, v205, v211] level6rrll level6rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrl_ok : everyKey (rowOK 5 level5) level6rrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrll && everyKey (rowOK 5 level5) level6rrlr) = true
  rw [level6rrll_ok, level6rrlr_ok]
  decide +kernel
def level6rrrl : BinaryTree (List W) := (.node [v43, v59, v107, v172, v196, v211, v226] (.node [v43, v59, v107, v172, v196, v211, v224] .nil .nil) (.node [v43, v59, v107, v172, v196, v226] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrl_ok : everyKey (rowOK 5 level5) level6rrrl = true := by decide +kernel
def level6rrrr : BinaryTree (List W) := (.node [v43, v59, v107, v188, v196, v211] (.node [v43, v59, v107, v172, v226] .nil .nil) (.node [v43, v59, v135, v172, v196, v211] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrr_ok : everyKey (rowOK 5 level5) level6rrrr = true := by decide +kernel
def level6rrr : BinaryTree (List W) := .node [v43, v59, v107, v172, v211, v226] level6rrrl level6rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrr_ok : everyKey (rowOK 5 level5) level6rrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrrl && everyKey (rowOK 5 level5) level6rrrr) = true
  rw [level6rrrl_ok, level6rrrr_ok]
  decide +kernel
def level6rr : BinaryTree (List W) := .node [v43, v59, v107, v172, v196, v211, v220] level6rrl level6rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rr_ok : everyKey (rowOK 5 level5) level6rr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrl && everyKey (rowOK 5 level5) level6rrr) = true
  rw [level6rrl_ok, level6rrr_ok]
  decide +kernel
def level6r : BinaryTree (List W) := .node [v43, v59, v107, v172, v190, v196, v211] level6rl level6rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6r_ok : everyKey (rowOK 5 level5) level6r = true := by
  change (_ && everyKey (rowOK 5 level5) level6rl && everyKey (rowOK 5 level5) level6rr) = true
  rw [level6rl_ok, level6rr_ok]
  decide +kernel
def level6 : BinaryTree (List W) := .node [v43, v59, v82, v107, v172, v196, v211] level6l level6r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6_ok : everyKey (rowOK 5 level5) level6 = true := by
  change (_ && everyKey (rowOK 5 level5) level6l && everyKey (rowOK 5 level5) level6r) = true
  rw [level6l_ok, level6r_ok]
  decide +kernel
theorem closed6 : Closed 6 level6 := closed_next 5 (by decide) level6 level5 closed5 level6_ok
def level7 : BinaryTree (List W) := (.node [v43, v59, v107, v172, v196, v211] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7_ok : everyKey (rowOK 6 level6) level7 = true := by decide +kernel
theorem closed7 : Closed 7 level7 := closed_next 6 (by decide) level7 level6 closed6 level7_ok

theorem lower : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z 7 ins.toFinset :=
  @no_build 7 level7 ins (by decide +kernel) (by decide) closed7 (by decide +kernel)
def witness : List Gate := [⟨.or,[2,3]⟩,⟨.or,[4,5]⟩,⟨.and,[6,7]⟩,⟨.or,[0,8]⟩,⟨.and,[2,3]⟩,⟨.or,[0,10]⟩,⟨.and,[7,11]⟩,⟨.or,[1,12]⟩,⟨.and,[9,13]⟩]
theorem upper : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 9 ∧ ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xfeeafeeafeea8888 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact ⟨witness,14,by simp [witness],rfl,by decide +kernel⟩
end PEqualNP.Outside.L_meta_12693_aux

open PEqualNP.Outside.L_meta_12693_aux in
theorem PEqualNP.Outside.L_meta_12693 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813546 * 2 ^ 32 + 4276783240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813546 * 2 ^ 32 + 4276783240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  have code : 4276813546 * 2 ^ 32 + 4276783240 = 0xfeeafeeafeea8888 := by decide
  simp only [code] at h ⊢
  obtain ⟨C,legal,size,computes⟩ := h
  obtain ⟨gs,o,mono,bound,ev⟩ := replace 0xfeeafeeafeea8888 9 ins (by decide +kernel) sampled rfl lower upper C.gates C.output legal computes
  exact ⟨⟨gs,o⟩,mono,bound.trans size,ev⟩
