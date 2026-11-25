import PEqualNP.Defs

-- The live-wire search and its circuit compiler follow the merged L-meta-8639.
namespace PEqualNP.Outside.L_meta_13201_aux

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

-- The upper and lower halves represent opposite target labels on 32 pairs of assignments.
abbrev W := BitVec 64
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 32 := ((x >>> 32) ^^^ x).setWidth 32
def cuts (ws : List W) : BitVec 32 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 32) ++ (0 : BitVec 32)
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

def differs (i : Fin 32) (w : W) : Prop :=
  w.getLsbD (32+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 32) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 32+i.val < 64 := by omega
  have hi' : i.val < 64 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 32) :
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
  change (cuts ws)[j] = (BitVec.allOnes 32)[j]
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
  · change reachable av (BitVec.allOnes 64 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 64)
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

private def bit (k : Fin 64) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 64) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 64) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#64)[k.val] = false; simp
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
    (row : ∀ j : Fin 64, Nat.testBit T (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
    (width : ins.length = 6) (rejection : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z n ins.toFinset)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 6, if x i then 2^(i : ℕ) else 0)) : n < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ ins, holds ins.toFinset u := fun u hu =>
    .inr (.inr ⟨u,List.mem_toFinset.mpr hu,.inl rfl⟩)
  have evaluate (k : Fin 64) :
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
    (row : ∀ j : Fin 64, Nat.testBit T (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
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

def v0 : W := 0x200000000
def v1 : W := 0x88e0000003e
def v2 : W := 0x444300000000
def v3 : W := 0x80960000003e
def v4 : W := 0x881a0000003e
def v5 : W := 0x889c0000003e
def v6 : W := 0x889e0000003e
def v7 : W := 0xccdf0000003e
def v8 : W := 0x113c4000003c0
def v9 : W := 0x19bde000003fe
def v10 : W := 0x23d0800003c00
def v11 : W := 0x2bd9e00003c3e
def v12 : W := 0x3e2100003c000
def v13 : W := 0x3ea9e0003c03e
def v14 : W := 0x10004000000000
def v15 : W := 0x20008400000000
def v16 : W := 0x20889e0000003e
def v17 : W := 0x3c002000fc0000
def v18 : W := 0x100040000000000
def v19 : W := 0x114044300000000
def v20 : W := 0x200080800000000
def v21 : W := 0x200889e0000003e
def v22 : W := 0x228002000000000
def v23 : W := 0x22808ae0000003e
def v24 : W := 0x30c00200f0c0000
def v25 : W := 0x440110000000000
def v26 : W := 0x47011c400f003c0
def v27 : W := 0x66800200ffc0000
def v28 : W := 0x7401d080f003c00
def v29 : W := 0x77c00200ffc0000
def v30 : W := 0x77c04630ffc0000
def v31 : W := 0x77c11e40ffc03c0
def v32 : W := 0x77c1d280ffc3c00
def v33 : W := 0x77fe2300fffc000
def v34 : W := 0x1000400000000000
def v35 : W := 0x1014404300000000
def v36 : W := 0x1104440300000000
def v37 : W := 0x1114000000000000
def v38 : W := 0x1114444100000000
def v39 : W := 0x1114444300000000
def v40 : W := 0x1114ccdf0000003e
def v41 : W := 0x113444c700000000
def v42 : W := 0x13144c4b00000000
def v43 : W := 0x133c446300000000
def v44 : W := 0x1554554300000000
def v45 : W := 0x177c00200ffc0000
def v46 : W := 0x177c44630ffc0000
def v47 : W := 0x2000801000000000
def v48 : W := 0x2000889e0000003e
def v49 : W := 0x2028002000000000
def v50 : W := 0x202880b60000003e
def v51 : W := 0x2208002000000000
def v52 : W := 0x2208883a0000003e
def v53 : W := 0x2228002000000000
def v54 : W := 0x2228002200000000
def v55 : W := 0x222800a400000000
def v56 : W := 0x2228082800000000
def v57 : W := 0x2228803000000000
def v58 : W := 0x222888bc0000003e
def v59 : W := 0x222888be0000003e
def v60 : W := 0x2228ccff0000003e
def v61 : W := 0x223888fe0000003e
def v62 : W := 0x23288cbe0000003e
def v63 : W := 0x233c8cff0000003e
def v64 : W := 0x266899be0000003e
def v65 : W := 0x277c00200ffc0000
def v66 : W := 0x300c0020f00c0000
def v67 : W := 0x3114c45300000000
def v68 : W := 0x313c446300000000
def v69 : W := 0x3228c8be0000003e
def v70 : W := 0x323cc8ff0000003e
def v71 : W := 0x331c446300000000
def v72 : W := 0x332cccbf0000003e
def v73 : W := 0x333c002000000000
def v74 : W := 0x333c446300000000
def v75 : W := 0x333c44e700000000
def v76 : W := 0x333c4c6b00000000
def v77 : W := 0x333c88be0000003e
def v78 : W := 0x333cc47300000000
def v79 : W := 0x333cccfd0000003e
def v80 : W := 0x333cccff0000003e
def v81 : W := 0x4081020000000000
def v82 : W := 0x40b102c400f003c0
def v83 : W := 0x44c1138400f003c0
def v84 : W := 0x44d1134000f003c0
def v85 : W := 0x44d113c400f003c0
def v86 : W := 0x44e1138400f003c0
def v87 : W := 0x44e113c400f003c0
def v88 : W := 0x44f0000000f00000
def v89 : W := 0x44f1138400f003c0
def v90 : W := 0x44f113c400f003c0
def v91 : W := 0x44f113c600f003c0
def v92 : W := 0x44f157c700f003c0
def v93 : W := 0x44f19bde00f003fe
def v94 : W := 0x44fd13e400fc03c0
def v95 : W := 0x45f117c400f003c0
def v96 : W := 0x45f517c700f003c0
def v97 : W := 0x46f11bcc00f003c0
def v98 : W := 0x46f913e400f003c0
def v99 : W := 0x47fc00200ffc0000
def v100 : W := 0x47fd13e40ffc03c0
def v101 : W := 0x5195464300000000
def v102 : W := 0x54f153c400f003c0
def v103 : W := 0x54f553c700f003c0
def v104 : W := 0x55e5578700f003c0
def v105 : W := 0x55f513c400f003c0
def v106 : W := 0x55f557c500f003c0
def v107 : W := 0x55f557c700f003c0
def v108 : W := 0x60a80020f0fc0000
def v109 : W := 0x62a98abe0000003e
def v110 : W := 0x64f193d400f003c0
def v111 : W := 0x64f913e400f003c0
def v112 : W := 0x66d99b7a00f003fe
def v113 : W := 0x66e913a400f003c0
def v114 : W := 0x66f8002000f00000
def v115 : W := 0x66f913e400f003c0
def v116 : W := 0x66f913e600f003c0
def v117 : W := 0x66f91bec00f003c0
def v118 : W := 0x66f993f400f003c0
def v119 : W := 0x66f99bfe00f003fe
def v120 : W := 0x7081c210f003c000
def v121 : W := 0x70bc0020f0fc0000
def v122 : W := 0x70bc4063f0fc0000
def v123 : W := 0x70bd02e4f0fc03c0
def v124 : W := 0x70bdc230f0ffc000
def v125 : W := 0x70be3d28f0fc3c00
def v126 : W := 0x71bc0020f0fc0000
def v127 : W := 0x71bc4463f0fc0000
def v128 : W := 0x72bc0020f0fc0000
def v129 : W := 0x74fc0020f0fc0000
def v130 : W := 0x74fd13e4f0fc03c0
def v131 : W := 0x77c1df18ff03fc00
def v132 : W := 0x77fc0020fffc0000
def v133 : W := 0x77fd13e400f003c0
def v134 : W := 0x77fd57e700f003c0
def v135 : W := 0x8802200000000000
def v136 : W := 0x8b022c080f003c00
def v137 : W := 0x8c4239080f003c00
def v138 : W := 0x8d4235000f003c00
def v139 : W := 0x8d423d080f003c00
def v140 : W := 0x8e4239080f003c00
def v141 : W := 0x8e423d080f003c00
def v142 : W := 0x8f4000000f000000
def v143 : W := 0x8f4239080f003c00
def v144 : W := 0x8f423d080f003c00
def v145 : W := 0x8f423d0a0f003c00
def v146 : W := 0x8f427d4b0f003c00
def v147 : W := 0x8f42bd9e0f003c3e
def v148 : W := 0x8f4e3d280f0c3c00
def v149 : W := 0x8f523d480f003c00
def v150 : W := 0x8f563d4b0f003c00
def v151 : W := 0x8f623d8c0f003c00
def v152 : W := 0x8f6a3d280f003c00
def v153 : W := 0x8f7c00200ffc0000
def v154 : W := 0x8f7e3d280ffc3c00
def v155 : W := 0x9916644300000000
def v156 : W := 0x9e56794b0f003c00
def v157 : W := 0x9f427d080f003c00
def v158 : W := 0x9f467d0b0f003c00
def v159 : W := 0x9f563d080f003c00
def v160 : W := 0x9f567d490f003c00
def v161 : W := 0x9f567d4b0f003c00
def v162 : W := 0xaa080020ff0c0000
def v163 : W := 0xaa2aa8be0000003e
def v164 : W := 0xad6ab5b60f003c3e
def v165 : W := 0xae6a39280f003c00
def v166 : W := 0xaf42bd180f003c00
def v167 : W := 0xaf4a3d280f003c00
def v168 : W := 0xaf6800200f000000
def v169 : W := 0xaf6a3d280f003c00
def v170 : W := 0xaf6a3d2a0f003c00
def v171 : W := 0xaf6a3dac0f003c00
def v172 : W := 0xaf6abd380f003c00
def v173 : W := 0xaf6abdbe0f003c3e
def v174 : W := 0xb802e010f003c000
def v175 : W := 0xbb0c0020ff0c0000
def v176 : W := 0xbb0c4423ff0c0000
def v177 : W := 0xbb0d13e4ff0c03c0
def v178 : W := 0xbb0e2c28ff0c3c00
def v179 : W := 0xbb0ee030ff0fc000
def v180 : W := 0xbb1c0020ff0c0000
def v181 : W := 0xbb1c4463ff0c0000
def v182 : W := 0xbb2c0020ff0c0000
def v183 : W := 0xbc72f1d4f0f3c3c0
def v184 : W := 0xbf4c0020ff0c0000
def v185 : W := 0xbf4e3d28ff0c3c00
def v186 : W := 0xbf7c0020fffc0000
def v187 : W := 0xbf7e3d280f003c00
def v188 : W := 0xbf7e7d6b0f003c00
def v189 : W := 0xc883a210f003c000
def v190 : W := 0xcbb32ecc0ff03fc0
def v191 : W := 0xccf333c400f003c0
def v192 : W := 0xcfc33f080f003c00
def v193 : W := 0xcff33fcc0ff03fc0
def v194 : W := 0xd8836200f003c000
def v195 : W := 0xd883e210f003c000
def v196 : W := 0xdaab6aaef003c03e
def v197 : W := 0xddd40000fffc0000
def v198 : W := 0xddd4889efffc003e
def v199 : W := 0xdffc0020fffc0000
def v200 : W := 0xe883a210f003c000
def v201 : W := 0xe883e210f003c000
def v202 : W := 0xe997a653f003c000
def v203 : W := 0xeaaba230f003c000
def v204 : W := 0xeee80020fffc0000
def v205 : W := 0xeee84463fffc0000
def v206 : W := 0xeee913a4fffc03c0
def v207 : W := 0xeeea3928fffc3c00
def v208 : W := 0xeeeba230ffffc000
def v209 : W := 0xeef80020fffc0000
def v210 : W := 0xeef913e4fffc03c0
def v211 : W := 0xefe80020fffc0000
def v212 : W := 0xefea3d28fffc3c00
def v213 : W := 0xeffc0020fffc0000
def v214 : W := 0xf8800000f0000000
def v215 : W := 0xf883a210f003c000
def v216 : W := 0xf883e210f003c000
def v217 : W := 0xf883e212f003c000
def v218 : W := 0xf883e653f003c000
def v219 : W := 0xf883ea9ef003c03e
def v220 : W := 0xf88fe230f00fc000
def v221 : W := 0xf893e250f003c000
def v222 : W := 0xf897e253f003c000
def v223 : W := 0xf8a3e294f003c000
def v224 : W := 0xf8abe230f003c000
def v225 : W := 0xf8bc0020f0fc0000
def v226 : W := 0xf8bfe230f0ffc000
def v227 : W := 0xf983e610f003c000
def v228 : W := 0xf987e613f003c000
def v229 : W := 0xf997e210f003c000
def v230 : W := 0xf997e651f003c000
def v231 : W := 0xf997e653f003c000
def v232 : W := 0xfa83ea18f003c000
def v233 : W := 0xfa8be230f003c000
def v234 : W := 0xfaa80020f0000000
def v235 : W := 0xfaabe230f003c000
def v236 : W := 0xfaabe232f003c000
def v237 : W := 0xfaabe2b4f003c000
def v238 : W := 0xfaabea38f003c000
def v239 : W := 0xfaabeabef003c03e
def v240 : W := 0xfb8c0020ff0c0000
def v241 : W := 0xfb8fe230ff0fc000
def v242 : W := 0xfbbc0020fffc0000
def v243 : W := 0xfbbfe230f003c000
def v244 : W := 0xfbbfe673f003c000
def v245 : W := 0xfcc3f310f003c000
def v246 : W := 0xfcf3f3d4f0f3c3c0
def v247 : W := 0xfdfc0020fffc0000
def v248 : W := 0xfee80020fffc0000
def v249 : W := 0xfeebe230ffffc000
def v250 : W := 0xfefc0020fffc0000
def v251 : W := 0xffc3ff18ff03fc00
def v252 : W := 0xffdc0020fffc0000
def v253 : W := 0xffec0020fffc0000
def v254 : W := 0xfffc0020fffc0000
def v255 : W := 0xfffc0022fffc0000
def v256 : W := 0xfffc0060fffc0000
def v257 : W := 0xfffc00a4fffc0000
def v258 : W := 0xfffc0420fffc0000
def v259 : W := 0xfffc0463fffc0000
def v260 : W := 0xfffc0828fffc0000
def v261 : W := 0xfffc1120fffc0000
def v262 : W := 0xfffc11e4fffc03c0
def v263 : W := 0xfffc1d28fffc3c00
def v264 : W := 0xfffc4020fffc0000
def v265 : W := 0xfffc4063fffc0000
def v266 : W := 0xfffc4423fffc0000
def v267 : W := 0xfffc4461fffc0000
def v268 : W := 0xfffc4463fffc0000
def v269 : W := 0xfffc8030fffc0000
def v270 : W := 0xfffc88befffc003e
def v271 : W := 0xfffd0220fffc0000
def v272 : W := 0xfffd02e4fffc03c0
def v273 : W := 0xfffd1360fffc03c0
def v274 : W := 0xfffd13a4fffc03c0
def v275 : W := 0xfffd13e4fffc03c0
def v276 : W := 0xfffd57e7fffc03c0
def v277 : W := 0xfffdc230ffffc000
def v278 : W := 0xfffe2020fffc0000
def v279 : W := 0xfffe2c28fffc3c00
def v280 : W := 0xfffe3520fffc3c00
def v281 : W := 0xfffe3928fffc3c00
def v282 : W := 0xfffe3d28fffc3c00
def v283 : W := 0xfffe7d6bfffc3c00
def v284 : W := 0xfffee030ffffc000
def v285 : W := 0xffff3fecfffc3fc0
def v286 : W := 0xffff6220ffffc000
def v287 : W := 0xffffa230ffffc000
def v288 : W := 0xffffe230ffffc000
def v289 : W := 0xffffe673ffffc000
def v290 : W := 0xfffff3f4ffffc3c0
def v291 : W := 0xffffff38fffffc00

def ins : List W := [v39, v59, v90, v144, v216, v254]
theorem sampled : ∀ j : Fin 64, Nat.testBit 0xfffefeeefffefeea (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
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
def level3lll : BinaryTree (List W) := (.node [v39, v117, v173, v216] (.node [v39, v90, v173, v238] (.node [v39, v90, v172, v239] .nil .nil) .nil) (.node [v39, v118, v144, v239] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level3lll_ok : everyKey (rowOK 2 level2) level3lll = true := by decide +kernel
def level3llr : BinaryTree (List W) := (.node [v59, v90, v188, v231] (.node [v59, v90, v161, v244] (.node [v39, v119, v171, v216] .nil .nil) .nil) (.node [v59, v90, v188, v244] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level3llr_ok : everyKey (rowOK 2 level2) level3llr = true := by decide +kernel
def level3ll : BinaryTree (List W) := .node [v39, v119, v144, v237] level3lll level3llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level3ll_ok : everyKey (rowOK 2 level2) level3ll = true := by
  change (_ && everyKey (rowOK 2 level2) level3lll && everyKey (rowOK 2 level2) level3llr) = true
  rw [level3lll_ok, level3llr_ok]
  decide +kernel
def level3lrl : BinaryTree (List W) := (.node [v59, v107, v188, v216] (.node [v59, v107, v169, v231] (.node [v59, v107, v161, v235] .nil .nil) .nil) (.node [v59, v115, v161, v231] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level3lrl_ok : everyKey (rowOK 2 level2) level3lrl = true := by decide +kernel
def level3lrr : BinaryTree (List W) := (.node [v59, v134, v188, v216] (.node [v59, v134, v161, v216] (.node [v59, v134, v144, v244] .nil .nil) .nil) (.node [v75, v119, v144, v216] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level3lrr_ok : everyKey (rowOK 2 level2) level3lrr = true := by decide +kernel
def level3lr : BinaryTree (List W) := .node [v59, v134, v144, v231] level3lrl level3lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level3lr_ok : everyKey (rowOK 2 level2) level3lr = true := by
  change (_ && everyKey (rowOK 2 level2) level3lrl && everyKey (rowOK 2 level2) level3lrr) = true
  rw [level3lrl_ok, level3lrr_ok]
  decide +kernel
def level3l : BinaryTree (List W) := .node [v59, v107, v144, v244] level3ll level3lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level3l_ok : everyKey (rowOK 2 level2) level3l = true := by
  change (_ && everyKey (rowOK 2 level2) level3ll && everyKey (rowOK 2 level2) level3lr) = true
  rw [level3ll_ok, level3lr_ok]
  decide +kernel
def level3rll : BinaryTree (List W) := (.node [v80, v90, v144, v244] (.node [v80, v90, v144, v236] (.node [v78, v90, v144, v239] .nil .nil) .nil) (.node [v80, v90, v161, v235] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level3rll_ok : everyKey (rowOK 2 level2) level3rll = true := by decide +kernel
def level3rlr : BinaryTree (List W) := (.node [v80, v90, v187, v231] (.node [v80, v90, v170, v216] (.node [v80, v90, v169, v231] .nil .nil) .nil) (.node [v80, v90, v188, v216] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level3rlr_ok : everyKey (rowOK 2 level2) level3rlr = true := by decide +kernel
def level3rl : BinaryTree (List W) := .node [v80, v90, v161, v243] level3rll level3rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level3rl_ok : everyKey (rowOK 2 level2) level3rl = true := by
  change (_ && everyKey (rowOK 2 level2) level3rll && everyKey (rowOK 2 level2) level3rlr) = true
  rw [level3rll_ok, level3rlr_ok]
  decide +kernel
def level3rrl : BinaryTree (List W) := (.node [v80, v107, v187, v216] (.node [v80, v107, v169, v216] (.node [v80, v107, v144, v243] .nil .nil) .nil) (.node [v80, v115, v144, v231] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level3rrl_ok : everyKey (rowOK 2 level2) level3rrl = true := by decide +kernel
def level3rrr : BinaryTree (List W) := (.node [v80, v133, v161, v216] (.node [v80, v133, v144, v231] (.node [v80, v116, v144, v216] .nil .nil) .nil) (.node [v80, v134, v144, v216] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level3rrr_ok : everyKey (rowOK 2 level2) level3rrr = true := by decide +kernel
def level3rr : BinaryTree (List W) := .node [v80, v115, v161, v216] level3rrl level3rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level3rr_ok : everyKey (rowOK 2 level2) level3rr = true := by
  change (_ && everyKey (rowOK 2 level2) level3rrl && everyKey (rowOK 2 level2) level3rrr) = true
  rw [level3rrl_ok, level3rrr_ok]
  decide +kernel
def level3r : BinaryTree (List W) := .node [v80, v107, v144, v235] level3rl level3rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level3r_ok : everyKey (rowOK 2 level2) level3r = true := by
  change (_ && everyKey (rowOK 2 level2) level3rl && everyKey (rowOK 2 level2) level3rr) = true
  rw [level3rl_ok, level3rr_ok]
  decide +kernel
def level3 : BinaryTree (List W) := .node [v76, v90, v173, v216] level3l level3r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level3_ok : everyKey (rowOK 2 level2) level3 = true := by
  change (_ && everyKey (rowOK 2 level2) level3l && everyKey (rowOK 2 level2) level3r) = true
  rw [level3l_ok, level3r_ok]
  decide +kernel
theorem closed3 : Closed 3 level3 := closed_next 2 (by decide) level3 level2 closed2 level3_ok
def level4llllll : BinaryTree (List W) := (.node [v6, v59, v90, v161, v231] (.node [v5, v80, v90, v144, v216] (.node [v5, v74, v90, v144, v216] .nil .nil) .nil) (.node [v6, v59, v107, v144, v231] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llllll_ok : everyKey (rowOK 3 level3) level4llllll = true := by decide +kernel
def level4lllllr : BinaryTree (List W) := (.node [v6, v80, v90, v161, v216] (.node [v6, v80, v90, v144, v231] (.node [v6, v74, v90, v144, v216] .nil .nil) .nil) (.node [v6, v80, v107, v144, v216] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lllllr_ok : everyKey (rowOK 3 level3) level4lllllr = true := by decide +kernel
def level4lllll : BinaryTree (List W) := .node [v6, v59, v107, v161, v216] level4llllll level4lllllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lllll_ok : everyKey (rowOK 3 level3) level4lllll = true := by
  change (_ && everyKey (rowOK 3 level3) level4llllll && everyKey (rowOK 3 level3) level4lllllr) = true
  rw [level4llllll_ok, level4lllllr_ok]
  decide +kernel
def level4llllrl : BinaryTree (List W) := (.node [v27, v59, v90, v161, v231] (.node [v7, v80, v107, v144, v216] (.node [v7, v80, v90, v161, v216] .nil .nil) .nil) (.node [v27, v59, v107, v144, v231] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llllrl_ok : everyKey (rowOK 3 level3) level4llllrl = true := by decide +kernel
def level4llllrr : BinaryTree (List W) := (.node [v29, v59, v107, v144, v231] (.node [v29, v59, v90, v161, v231] .nil .nil) (.node [v29, v59, v107, v161, v216] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llllrr_ok : everyKey (rowOK 3 level3) level4llllrr = true := by decide +kernel
def level4llllr : BinaryTree (List W) := .node [v27, v80, v90, v144, v231] level4llllrl level4llllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llllr_ok : everyKey (rowOK 3 level3) level4llllr = true := by
  change (_ && everyKey (rowOK 3 level3) level4llllrl && everyKey (rowOK 3 level3) level4llllrr) = true
  rw [level4llllrl_ok, level4llllrr_ok]
  decide +kernel
def level4llll : BinaryTree (List W) := .node [v7, v80, v90, v144, v231] level4lllll level4llllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llll_ok : everyKey (rowOK 3 level3) level4llll = true := by
  change (_ && everyKey (rowOK 3 level3) level4lllll && everyKey (rowOK 3 level3) level4llllr) = true
  rw [level4lllll_ok, level4llllr_ok]
  decide +kernel
def level4lllrll : BinaryTree (List W) := (.node [v30, v80, v90, v144, v216] (.node [v29, v80, v107, v144, v216] (.node [v29, v80, v90, v161, v216] .nil .nil) .nil) (.node [v33, v39, v59, v90, v144] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lllrll_ok : everyKey (rowOK 3 level3) level4lllrll = true := by decide +kernel
def level4lllrlr : BinaryTree (List W) := (.node [v39, v58, v90, v144, v235] (.node [v39, v57, v90, v144, v239] (.node [v39, v56, v90, v173, v216] .nil .nil) .nil) (.node [v39, v58, v90, v169, v216] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lllrlr_ok : everyKey (rowOK 3 level3) level4lllrlr = true := by decide +kernel
def level4lllrl : BinaryTree (List W) := .node [v39, v55, v119, v144, v216] level4lllrll level4lllrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lllrl_ok : everyKey (rowOK 3 level3) level4lllrl = true := by
  change (_ && everyKey (rowOK 3 level3) level4lllrll && everyKey (rowOK 3 level3) level4lllrlr) = true
  rw [level4lllrll_ok, level4lllrlr_ok]
  decide +kernel
def level4lllrrl : BinaryTree (List W) := (.node [v39, v59, v86, v144, v235] (.node [v39, v59, v85, v169, v216] (.node [v39, v59, v85, v144, v235] .nil .nil) .nil) (.node [v39, v59, v86, v169, v216] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lllrrl_ok : everyKey (rowOK 3 level3) level4lllrrl = true := by decide +kernel
def level4lllrrr : BinaryTree (List W) := (.node [v39, v59, v90, v139, v235] (.node [v39, v59, v90, v131, v254] .nil .nil) (.node [v39, v59, v90, v140, v235] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lllrrr_ok : everyKey (rowOK 3 level3) level4lllrrr = true := by decide +kernel
def level4lllrr : BinaryTree (List W) := .node [v39, v59, v90, v125, v216] level4lllrrl level4lllrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lllrr_ok : everyKey (rowOK 3 level3) level4lllrr = true := by
  change (_ && everyKey (rowOK 3 level3) level4lllrrl && everyKey (rowOK 3 level3) level4lllrrr) = true
  rw [level4lllrrl_ok, level4lllrrr_ok]
  decide +kernel
def level4lllr : BinaryTree (List W) := .node [v39, v58, v115, v144, v216] level4lllrl level4lllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lllr_ok : everyKey (rowOK 3 level3) level4lllr = true := by
  change (_ && everyKey (rowOK 3 level3) level4lllrl && everyKey (rowOK 3 level3) level4lllrr) = true
  rw [level4lllrl_ok, level4lllrr_ok]
  decide +kernel
def level4lll : BinaryTree (List W) := .node [v29, v80, v90, v144, v231] level4llll level4lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lll_ok : everyKey (rowOK 3 level3) level4lll = true := by
  change (_ && everyKey (rowOK 3 level3) level4llll && everyKey (rowOK 3 level3) level4lllr) = true
  rw [level4llll_ok, level4lllr_ok]
  decide +kernel
def level4llrlll : BinaryTree (List W) := (.node [v39, v59, v90, v144, v233] (.node [v39, v59, v90, v144, v224] (.node [v39, v59, v90, v144, v220] .nil .nil) .nil) (.node [v39, v59, v90, v144, v235] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llrlll_ok : everyKey (rowOK 3 level3) level4llrlll = true := by decide +kernel
def level4llrllr : BinaryTree (List W) := (.node [v39, v59, v90, v144, v243] (.node [v39, v59, v90, v144, v238] (.node [v39, v59, v90, v144, v237] .nil .nil) .nil) (.node [v39, v59, v90, v144, v244] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llrllr_ok : everyKey (rowOK 3 level3) level4llrllr = true := by decide +kernel
def level4llrll : BinaryTree (List W) := .node [v39, v59, v90, v144, v236] level4llrlll level4llrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llrll_ok : everyKey (rowOK 3 level3) level4llrll = true := by
  change (_ && everyKey (rowOK 3 level3) level4llrlll && everyKey (rowOK 3 level3) level4llrllr) = true
  rw [level4llrlll_ok, level4llrllr_ok]
  decide +kernel
def level4llrlrl : BinaryTree (List W) := (.node [v39, v59, v90, v165, v216] (.node [v39, v59, v90, v161, v235] (.node [v39, v59, v90, v152, v216] .nil .nil) .nil) (.node [v39, v59, v90, v167, v216] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llrlrl_ok : everyKey (rowOK 3 level3) level4llrlrl = true := by decide +kernel
def level4llrlrr : BinaryTree (List W) := (.node [v39, v59, v90, v169, v216] (.node [v39, v59, v90, v169, v200] .nil .nil) (.node [v39, v59, v90, v169, v231] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llrlrr_ok : everyKey (rowOK 3 level3) level4llrlrr = true := by decide +kernel
def level4llrlr : BinaryTree (List W) := .node [v39, v59, v90, v169, v195] level4llrlrl level4llrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llrlr_ok : everyKey (rowOK 3 level3) level4llrlr = true := by
  change (_ && everyKey (rowOK 3 level3) level4llrlrl && everyKey (rowOK 3 level3) level4llrlrr) = true
  rw [level4llrlrl_ok, level4llrlrr_ok]
  decide +kernel
def level4llrl : BinaryTree (List W) := .node [v39, v59, v90, v148, v216] level4llrll level4llrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llrl_ok : everyKey (rowOK 3 level3) level4llrl = true := by
  change (_ && everyKey (rowOK 3 level3) level4llrll && everyKey (rowOK 3 level3) level4llrlr) = true
  rw [level4llrll_ok, level4llrlr_ok]
  decide +kernel
def level4llrrll : BinaryTree (List W) := (.node [v39, v59, v90, v172, v216] (.node [v39, v59, v90, v171, v216] (.node [v39, v59, v90, v170, v216] .nil .nil) .nil) (.node [v39, v59, v90, v187, v216] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llrrll_ok : everyKey (rowOK 3 level3) level4llrrll = true := by decide +kernel
def level4llrrlr : BinaryTree (List W) := (.node [v39, v59, v107, v144, v235] (.node [v39, v59, v98, v144, v216] (.node [v39, v59, v94, v144, v216] .nil .nil) .nil) (.node [v39, v59, v107, v169, v216] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llrrlr_ok : everyKey (rowOK 3 level3) level4llrrlr = true := by decide +kernel
def level4llrrl : BinaryTree (List W) := .node [v39, v59, v90, v188, v216] level4llrrll level4llrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llrrl_ok : everyKey (rowOK 3 level3) level4llrrl = true := by
  change (_ && everyKey (rowOK 3 level3) level4llrrll && everyKey (rowOK 3 level3) level4llrrlr) = true
  rw [level4llrrll_ok, level4llrrlr_ok]
  decide +kernel
def level4llrrrl : BinaryTree (List W) := (.node [v39, v59, v115, v140, v216] (.node [v39, v59, v115, v139, v216] (.node [v39, v59, v113, v144, v216] .nil .nil) .nil) (.node [v39, v59, v115, v144, v195] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llrrrl_ok : everyKey (rowOK 3 level3) level4llrrrl = true := by decide +kernel
def level4llrrrr : BinaryTree (List W) := (.node [v39, v59, v115, v144, v231] (.node [v39, v59, v115, v144, v216] .nil .nil) (.node [v39, v59, v115, v144, v235] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llrrrr_ok : everyKey (rowOK 3 level3) level4llrrrr = true := by decide +kernel
def level4llrrr : BinaryTree (List W) := .node [v39, v59, v115, v144, v200] level4llrrrl level4llrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llrrr_ok : everyKey (rowOK 3 level3) level4llrrr = true := by
  change (_ && everyKey (rowOK 3 level3) level4llrrrl && everyKey (rowOK 3 level3) level4llrrrr) = true
  rw [level4llrrrl_ok, level4llrrrr_ok]
  decide +kernel
def level4llrr : BinaryTree (List W) := .node [v39, v59, v111, v144, v216] level4llrrl level4llrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llrr_ok : everyKey (rowOK 3 level3) level4llrr = true := by
  change (_ && everyKey (rowOK 3 level3) level4llrrl && everyKey (rowOK 3 level3) level4llrrr) = true
  rw [level4llrrl_ok, level4llrrr_ok]
  decide +kernel
def level4llr : BinaryTree (List W) := .node [v39, v59, v90, v169, v235] level4llrl level4llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llr_ok : everyKey (rowOK 3 level3) level4llr = true := by
  change (_ && everyKey (rowOK 3 level3) level4llrl && everyKey (rowOK 3 level3) level4llrr) = true
  rw [level4llrl_ok, level4llrr_ok]
  decide +kernel
def level4ll : BinaryTree (List W) := .node [v39, v59, v90, v144, v203] level4lll level4llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4ll_ok : everyKey (rowOK 3 level3) level4ll = true := by
  change (_ && everyKey (rowOK 3 level3) level4lll && everyKey (rowOK 3 level3) level4llr) = true
  rw [level4lll_ok, level4llr_ok]
  decide +kernel
def level4lrllll : BinaryTree (List W) := (.node [v39, v59, v117, v144, v216] (.node [v39, v59, v116, v144, v216] (.node [v39, v59, v115, v169, v216] .nil .nil) .nil) (.node [v39, v59, v118, v144, v216] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrllll_ok : everyKey (rowOK 3 level3) level4lrllll = true := by decide +kernel
def level4lrlllr : BinaryTree (List W) := (.node [v39, v59, v144, v183, v254] (.node [v39, v59, v144, v177, v216] (.node [v39, v59, v134, v144, v216] .nil .nil) .nil) (.node [v39, v59, v190, v216, v254] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrlllr_ok : everyKey (rowOK 3 level3) level4lrlllr = true := by decide +kernel
def level4lrlll : BinaryTree (List W) := .node [v39, v59, v133, v144, v216] level4lrllll level4lrlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrlll_ok : everyKey (rowOK 3 level3) level4lrlll = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrllll && everyKey (rowOK 3 level3) level4lrlllr) = true
  rw [level4lrllll_ok, level4lrlllr_ok]
  decide +kernel
def level4lrllrl : BinaryTree (List W) := (.node [v39, v64, v193, v216, v254] (.node [v39, v59, v193, v245, v254] (.node [v39, v59, v192, v246, v254] .nil .nil) .nil) (.node [v39, v80, v90, v144, v235] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrllrl_ok : everyKey (rowOK 3 level3) level4lrllrl = true := by decide +kernel
def level4lrllrr : BinaryTree (List W) := (.node [v39, v80, v90, v187, v216] (.node [v39, v80, v90, v169, v216] .nil .nil) (.node [v39, v80, v115, v144, v216] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrllrr_ok : everyKey (rowOK 3 level3) level4lrllrr = true := by decide +kernel
def level4lrllr : BinaryTree (List W) := .node [v39, v80, v90, v144, v243] level4lrllrl level4lrllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrllr_ok : everyKey (rowOK 3 level3) level4lrllr = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrllrl && everyKey (rowOK 3 level3) level4lrllrr) = true
  rw [level4lrllrl_ok, level4lrllrr_ok]
  decide +kernel
def level4lrll : BinaryTree (List W) := .node [v39, v59, v191, v251, v254] level4lrlll level4lrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrll_ok : everyKey (rowOK 3 level3) level4lrll = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrlll && everyKey (rowOK 3 level3) level4lrllr) = true
  rw [level4lrlll_ok, level4lrllr_ok]
  decide +kernel
def level4lrlrll : BinaryTree (List W) := (.node [v39, v90, v163, v251, v254] (.node [v39, v90, v144, v198, v216] (.node [v39, v90, v144, v196, v254] .nil .nil) .nil) (.node [v39, v90, v164, v216, v254] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrlrll_ok : everyKey (rowOK 3 level3) level4lrlrll = true := by decide +kernel
def level4lrlrlr : BinaryTree (List W) := (.node [v39, v109, v144, v246, v254] (.node [v39, v97, v173, v216, v254] (.node [v39, v90, v173, v232, v254] .nil .nil) .nil) (.node [v39, v110, v144, v239, v254] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrlrlr_ok : everyKey (rowOK 3 level3) level4lrlrlr = true := by decide +kernel
def level4lrlrl : BinaryTree (List W) := .node [v39, v90, v166, v239, v254] level4lrlrll level4lrlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrlrl_ok : everyKey (rowOK 3 level3) level4lrlrl = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrlrll && everyKey (rowOK 3 level3) level4lrlrlr) = true
  rw [level4lrlrll_ok, level4lrlrlr_ok]
  decide +kernel
def level4lrlrrl : BinaryTree (List W) := (.node [v40, v58, v90, v144, v216] (.node [v39, v119, v151, v216, v254] (.node [v39, v119, v144, v223, v254] .nil .nil) .nil) (.node [v40, v59, v90, v144, v231] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrlrrl_ok : everyKey (rowOK 3 level3) level4lrlrrl = true := by decide +kernel
def level4lrlrrr : BinaryTree (List W) := (.node [v41, v119, v144, v216, v254] (.node [v40, v59, v107, v144, v216] .nil .nil) (.node [v42, v90, v173, v216, v254] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrlrrr_ok : everyKey (rowOK 3 level3) level4lrlrrr = true := by decide +kernel
def level4lrlrr : BinaryTree (List W) := .node [v40, v59, v90, v161, v216] level4lrlrrl level4lrlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrlrr_ok : everyKey (rowOK 3 level3) level4lrlrr = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrlrrl && everyKey (rowOK 3 level3) level4lrlrrr) = true
  rw [level4lrlrrl_ok, level4lrlrrr_ok]
  decide +kernel
def level4lrlr : BinaryTree (List W) := .node [v39, v112, v144, v216, v254] level4lrlrl level4lrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrlr_ok : everyKey (rowOK 3 level3) level4lrlr = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrlrl && everyKey (rowOK 3 level3) level4lrlrr) = true
  rw [level4lrlrl_ok, level4lrlrr_ok]
  decide +kernel
def level4lrl : BinaryTree (List W) := .node [v39, v80, v133, v144, v216] level4lrll level4lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrl_ok : everyKey (rowOK 3 level3) level4lrl = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrll && everyKey (rowOK 3 level3) level4lrlr) = true
  rw [level4lrll_ok, level4lrlr_ok]
  decide +kernel
def level4lrrlll : BinaryTree (List W) := (.node [v46, v80, v90, v144, v216] (.node [v46, v59, v90, v144, v231] (.node [v44, v59, v193, v216, v254] .nil .nil) .nil) (.node [v53, v59, v90, v161, v231] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrrlll_ok : everyKey (rowOK 3 level3) level4lrrlll = true := by decide +kernel
def level4lrrllr : BinaryTree (List W) := (.node [v53, v80, v90, v161, v216] (.node [v53, v80, v90, v144, v231] (.node [v53, v59, v107, v161, v216] .nil .nil) .nil) (.node [v53, v80, v107, v144, v216] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrrllr_ok : everyKey (rowOK 3 level3) level4lrrllr = true := by decide +kernel
def level4lrrll : BinaryTree (List W) := .node [v53, v59, v107, v144, v231] level4lrrlll level4lrrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrrll_ok : everyKey (rowOK 3 level3) level4lrrll = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrrlll && everyKey (rowOK 3 level3) level4lrrllr) = true
  rw [level4lrrlll_ok, level4lrrllr_ok]
  decide +kernel
def level4lrrlrl : BinaryTree (List W) := (.node [v58, v107, v144, v231, v254] (.node [v58, v90, v161, v231, v254] (.node [v58, v74, v90, v144, v216] .nil .nil) .nil) (.node [v58, v107, v161, v216, v254] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrrlrl_ok : everyKey (rowOK 3 level3) level4lrrlrl = true := by decide +kernel
def level4lrrlrr : BinaryTree (List W) := (.node [v59, v74, v83, v144, v216] (.node [v59, v71, v90, v144, v216] .nil .nil) (.node [v59, v74, v85, v144, v216] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrrlrr_ok : everyKey (rowOK 3 level3) level4lrrlrr = true := by decide +kernel
def level4lrrlr : BinaryTree (List W) := .node [v59, v68, v90, v144, v216] level4lrrlrl level4lrrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrrlr_ok : everyKey (rowOK 3 level3) level4lrrlr = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrrlrl && everyKey (rowOK 3 level3) level4lrrlrr) = true
  rw [level4lrrlrl_ok, level4lrrlrr_ok]
  decide +kernel
def level4lrrl : BinaryTree (List W) := .node [v54, v80, v90, v144, v216] level4lrrll level4lrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrrl_ok : everyKey (rowOK 3 level3) level4lrrl = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrrll && everyKey (rowOK 3 level3) level4lrrlr) = true
  rw [level4lrrll_ok, level4lrrlr_ok]
  decide +kernel
def level4lrrrll : BinaryTree (List W) := (.node [v59, v74, v90, v140, v216] (.node [v59, v74, v90, v139, v216] (.node [v59, v74, v90, v137, v216] .nil .nil) .nil) (.node [v59, v74, v90, v144, v189] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrrrll_ok : everyKey (rowOK 3 level3) level4lrrrll = true := by decide +kernel
def level4lrrrlr : BinaryTree (List W) := (.node [v59, v74, v90, v144, v216] (.node [v59, v74, v90, v144, v200] .nil .nil) (.node [v59, v74, v90, v144, v231] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrrrlr_ok : everyKey (rowOK 3 level3) level4lrrrlr = true := by decide +kernel
def level4lrrrl : BinaryTree (List W) := .node [v59, v74, v90, v144, v195] level4lrrrll level4lrrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrrrl_ok : everyKey (rowOK 3 level3) level4lrrrl = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrrrll && everyKey (rowOK 3 level3) level4lrrrlr) = true
  rw [level4lrrrll_ok, level4lrrrlr_ok]
  decide +kernel
def level4lrrrrl : BinaryTree (List W) := (.node [v59, v74, v90, v169, v216] (.node [v59, v74, v90, v161, v216] (.node [v59, v74, v90, v144, v244] .nil .nil) .nil) (.node [v59, v74, v90, v188, v216] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrrrrl_ok : everyKey (rowOK 3 level3) level4lrrrrl = true := by decide +kernel
def level4lrrrrr : BinaryTree (List W) := (.node [v59, v74, v134, v144, v216] (.node [v59, v74, v115, v144, v216] .nil .nil) (.node [v59, v75, v90, v144, v216] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrrrrr_ok : everyKey (rowOK 3 level3) level4lrrrrr = true := by decide +kernel
def level4lrrrr : BinaryTree (List W) := .node [v59, v74, v107, v144, v216] level4lrrrrl level4lrrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrrrr_ok : everyKey (rowOK 3 level3) level4lrrrr = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrrrrl && everyKey (rowOK 3 level3) level4lrrrrr) = true
  rw [level4lrrrrl_ok, level4lrrrrr_ok]
  decide +kernel
def level4lrrr : BinaryTree (List W) := .node [v59, v74, v90, v144, v235] level4lrrrl level4lrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrrr_ok : everyKey (rowOK 3 level3) level4lrrr = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrrrl && everyKey (rowOK 3 level3) level4lrrrr) = true
  rw [level4lrrrl_ok, level4lrrrr_ok]
  decide +kernel
def level4lrr : BinaryTree (List W) := .node [v59, v74, v86, v144, v216] level4lrrl level4lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrr_ok : everyKey (rowOK 3 level3) level4lrr = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrrl && everyKey (rowOK 3 level3) level4lrrr) = true
  rw [level4lrrl_ok, level4lrrr_ok]
  decide +kernel
def level4lr : BinaryTree (List W) := .node [v43, v59, v90, v144, v216] level4lrl level4lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lr_ok : everyKey (rowOK 3 level3) level4lr = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrl && everyKey (rowOK 3 level3) level4lrr) = true
  rw [level4lrl_ok, level4lrr_ok]
  decide +kernel
def level4l : BinaryTree (List W) := .node [v39, v59, v115, v161, v216] level4ll level4lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4l_ok : everyKey (rowOK 3 level3) level4l = true := by
  change (_ && everyKey (rowOK 3 level3) level4ll && everyKey (rowOK 3 level3) level4lr) = true
  rw [level4ll_ok, level4lr_ok]
  decide +kernel
def level4rlllll : BinaryTree (List W) := (.node [v59, v90, v108, v161, v231] (.node [v59, v86, v161, v231, v254] (.node [v59, v78, v90, v144, v216] .nil .nil) .nil) (.node [v59, v90, v121, v161, v231] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlllll_ok : everyKey (rowOK 3 level3) level4rlllll = true := by decide +kernel
def level4rllllr : BinaryTree (List W) := (.node [v59, v90, v144, v208, v231] (.node [v59, v90, v144, v205, v216] (.node [v59, v90, v144, v202, v254] .nil .nil) .nil) (.node [v59, v90, v155, v251, v254] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rllllr_ok : everyKey (rowOK 3 level3) level4rllllr = true := by decide +kernel
def level4rllll : BinaryTree (List W) := .node [v59, v90, v127, v161, v216] level4rlllll level4rllllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rllll_ok : everyKey (rowOK 3 level3) level4rllll = true := by
  change (_ && everyKey (rowOK 3 level3) level4rlllll && everyKey (rowOK 3 level3) level4rllllr) = true
  rw [level4rlllll_ok, level4rllllr_ok]
  decide +kernel
def level4rlllrl : BinaryTree (List W) := (.node [v59, v90, v160, v231, v254] (.node [v59, v90, v158, v231, v254] (.node [v59, v90, v157, v231, v254] .nil .nil) .nil) (.node [v59, v90, v161, v175, v231] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlllrl_ok : everyKey (rowOK 3 level3) level4rlllrl = true := by decide +kernel
def level4rlllrr : BinaryTree (List W) := (.node [v59, v90, v161, v227, v254] (.node [v59, v90, v161, v207, v216] .nil .nil) (.node [v59, v90, v161, v228, v254] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlllrr_ok : everyKey (rowOK 3 level3) level4rlllrr = true := by decide +kernel
def level4rlllr : BinaryTree (List W) := .node [v59, v90, v161, v204, v231] level4rlllrl level4rlllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlllr_ok : everyKey (rowOK 3 level3) level4rlllr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rlllrl && everyKey (rowOK 3 level3) level4rlllrr) = true
  rw [level4rlllrl_ok, level4rlllrr_ok]
  decide +kernel
def level4rlll : BinaryTree (List W) := .node [v59, v90, v156, v216, v254] level4rllll level4rlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlll_ok : everyKey (rowOK 3 level3) level4rlll = true := by
  change (_ && everyKey (rowOK 3 level3) level4rllll && everyKey (rowOK 3 level3) level4rlllr) = true
  rw [level4rllll_ok, level4rlllr_ok]
  decide +kernel
def level4rllrll : BinaryTree (List W) := (.node [v59, v90, v161, v231, v275] (.node [v59, v90, v161, v231, v268] (.node [v59, v90, v161, v231, v254] .nil .nil) .nil) (.node [v59, v90, v161, v231, v282] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rllrll_ok : everyKey (rowOK 3 level3) level4rllrll = true := by decide +kernel
def level4rllrlr : BinaryTree (List W) := (.node [v59, v95, v161, v216, v254] (.node [v59, v90, v161, v231, v289] (.node [v59, v90, v161, v231, v288] .nil .nil) .nil) (.node [v59, v96, v161, v216, v254] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rllrlr_ok : everyKey (rowOK 3 level3) level4rllrlr = true := by decide +kernel
def level4rllrl : BinaryTree (List W) := .node [v59, v90, v161, v231, v283] level4rllrll level4rllrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rllrl_ok : everyKey (rowOK 3 level3) level4rllrl = true := by
  change (_ && everyKey (rowOK 3 level3) level4rllrll && everyKey (rowOK 3 level3) level4rllrlr) = true
  rw [level4rllrll_ok, level4rllrlr_ok]
  decide +kernel
def level4rllrrl : BinaryTree (List W) := (.node [v59, v104, v144, v216, v254] (.node [v59, v103, v144, v231, v254] (.node [v59, v102, v144, v231, v254] .nil .nil) .nil) (.node [v59, v106, v144, v231, v254] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rllrrl_ok : everyKey (rowOK 3 level3) level4rllrrl = true := by decide +kernel
def level4rllrrr : BinaryTree (List W) := (.node [v59, v107, v121, v144, v231] (.node [v59, v107, v108, v161, v216] .nil .nil) (.node [v59, v107, v121, v161, v216] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rllrrr_ok : everyKey (rowOK 3 level3) level4rllrrr = true := by decide +kernel
def level4rllrr : BinaryTree (List W) := .node [v59, v106, v161, v216, v254] level4rllrrl level4rllrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rllrr_ok : everyKey (rowOK 3 level3) level4rllrr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rllrrl && everyKey (rowOK 3 level3) level4rllrrr) = true
  rw [level4rllrrl_ok, level4rllrrr_ok]
  decide +kernel
def level4rllr : BinaryTree (List W) := .node [v59, v101, v144, v246, v254] level4rllrl level4rllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rllr_ok : everyKey (rowOK 3 level3) level4rllr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rllrl && everyKey (rowOK 3 level3) level4rllrr) = true
  rw [level4rllrl_ok, level4rllrr_ok]
  decide +kernel
def level4rll : BinaryTree (List W) := .node [v59, v90, v161, v230, v254] level4rlll level4rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rll_ok : everyKey (rowOK 3 level3) level4rll = true := by
  change (_ && everyKey (rowOK 3 level3) level4rlll && everyKey (rowOK 3 level3) level4rllr) = true
  rw [level4rlll_ok, level4rllr_ok]
  decide +kernel
def level4rlrlll : BinaryTree (List W) := (.node [v59, v107, v144, v181, v216] (.node [v59, v107, v144, v175, v231] (.node [v59, v107, v144, v162, v231] .nil .nil) .nil) (.node [v59, v107, v144, v204, v231] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlrlll_ok : everyKey (rowOK 3 level3) level4rlrlll = true := by decide +kernel
def level4rlrllr : BinaryTree (List W) := (.node [v59, v107, v144, v230, v254] (.node [v59, v107, v144, v222, v254] (.node [v59, v107, v144, v221, v254] .nil .nil) .nil) (.node [v59, v107, v144, v231, v254] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlrllr_ok : everyKey (rowOK 3 level3) level4rlrllr = true := by decide +kernel
def level4rlrll : BinaryTree (List W) := .node [v59, v107, v144, v206, v216] level4rlrlll level4rlrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlrll_ok : everyKey (rowOK 3 level3) level4rlrll = true := by
  change (_ && everyKey (rowOK 3 level3) level4rlrlll && everyKey (rowOK 3 level3) level4rlrllr) = true
  rw [level4rlrlll_ok, level4rlrllr_ok]
  decide +kernel
def level4rlrlrl : BinaryTree (List W) := (.node [v59, v107, v144, v231, v282] (.node [v59, v107, v144, v231, v276] (.node [v59, v107, v144, v231, v275] .nil .nil) .nil) (.node [v59, v107, v144, v231, v288] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlrlrl_ok : everyKey (rowOK 3 level3) level4rlrlrl = true := by decide +kernel
def level4rlrlrr : BinaryTree (List W) := (.node [v59, v107, v150, v216, v254] (.node [v59, v107, v149, v216, v254] .nil .nil) (.node [v59, v107, v160, v216, v254] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlrlrr_ok : everyKey (rowOK 3 level3) level4rlrlrr = true := by decide +kernel
def level4rlrlr : BinaryTree (List W) := .node [v59, v107, v144, v231, v289] level4rlrlrl level4rlrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlrlr_ok : everyKey (rowOK 3 level3) level4rlrlr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rlrlrl && everyKey (rowOK 3 level3) level4rlrlrr) = true
  rw [level4rlrlrl_ok, level4rlrlrr_ok]
  decide +kernel
def level4rlrl : BinaryTree (List W) := .node [v59, v107, v144, v231, v268] level4rlrll level4rlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlrl_ok : everyKey (rowOK 3 level3) level4rlrl = true := by
  change (_ && everyKey (rowOK 3 level3) level4rlrll && everyKey (rowOK 3 level3) level4rlrlr) = true
  rw [level4rlrll_ok, level4rlrlr_ok]
  decide +kernel
def level4rlrrll : BinaryTree (List W) := (.node [v59, v107, v161, v204, v216] (.node [v59, v107, v161, v200, v254] (.node [v59, v107, v161, v175, v216] .nil .nil) .nil) (.node [v59, v107, v161, v216, v254] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlrrll_ok : everyKey (rowOK 3 level3) level4rlrrll = true := by decide +kernel
def level4rlrrlr : BinaryTree (List W) := (.node [v59, v107, v161, v216, v282] (.node [v59, v107, v161, v216, v276] (.node [v59, v107, v161, v216, v275] .nil .nil) .nil) (.node [v59, v107, v161, v216, v283] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlrrlr_ok : everyKey (rowOK 3 level3) level4rlrrlr = true := by decide +kernel
def level4rlrrl : BinaryTree (List W) := .node [v59, v107, v161, v216, v268] level4rlrrll level4rlrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlrrl_ok : everyKey (rowOK 3 level3) level4rlrrl = true := by
  change (_ && everyKey (rowOK 3 level3) level4rlrrll && everyKey (rowOK 3 level3) level4rlrrlr) = true
  rw [level4rlrrll_ok, level4rlrrlr_ok]
  decide +kernel
def level4rlrrrl : BinaryTree (List W) := (.node [v62, v90, v161, v216, v254] (.node [v61, v107, v144, v216, v254] (.node [v59, v107, v161, v231, v254] .nil .nil) .nil) (.node [v63, v90, v161, v216, v254] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlrrrl_ok : everyKey (rowOK 3 level3) level4rlrrrl = true := by decide +kernel
def level4rlrrrr : BinaryTree (List W) := (.node [v69, v90, v144, v231, v254] (.node [v67, v90, v144, v239, v254] .nil .nil) (.node [v70, v90, v144, v231, v254] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlrrrr_ok : everyKey (rowOK 3 level3) level4rlrrrr = true := by decide +kernel
def level4rlrrr : BinaryTree (List W) := .node [v63, v107, v144, v216, v254] level4rlrrrl level4rlrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlrrr_ok : everyKey (rowOK 3 level3) level4rlrrr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rlrrrl && everyKey (rowOK 3 level3) level4rlrrrr) = true
  rw [level4rlrrrl_ok, level4rlrrrr_ok]
  decide +kernel
def level4rlrr : BinaryTree (List W) := .node [v59, v107, v161, v216, v288] level4rlrrl level4rlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlrr_ok : everyKey (rowOK 3 level3) level4rlrr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rlrrl && everyKey (rowOK 3 level3) level4rlrrr) = true
  rw [level4rlrrl_ok, level4rlrrr_ok]
  decide +kernel
def level4rlr : BinaryTree (List W) := .node [v59, v107, v161, v162, v216] level4rlrl level4rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlr_ok : everyKey (rowOK 3 level3) level4rlr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rlrl && everyKey (rowOK 3 level3) level4rlrr) = true
  rw [level4rlrl_ok, level4rlrr_ok]
  decide +kernel
def level4rl : BinaryTree (List W) := .node [v59, v107, v140, v231, v254] level4rll level4rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rl_ok : everyKey (rowOK 3 level3) level4rl = true := by
  change (_ && everyKey (rowOK 3 level3) level4rll && everyKey (rowOK 3 level3) level4rlr) = true
  rw [level4rll_ok, level4rlr_ok]
  decide +kernel
def level4rrllll : BinaryTree (List W) := (.node [v73, v80, v90, v144, v231] (.node [v72, v90, v161, v216, v254] (.node [v72, v90, v144, v231, v254] .nil .nil) .nil) (.node [v73, v80, v90, v161, v216] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrllll_ok : everyKey (rowOK 3 level3) level4rrllll = true := by decide +kernel
def level4rrlllr : BinaryTree (List W) := (.node [v77, v90, v144, v216, v268] (.node [v74, v90, v144, v216, v270] (.node [v74, v80, v90, v144, v216] .nil .nil) .nil) (.node [v79, v90, v144, v216, v254] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrlllr_ok : everyKey (rowOK 3 level3) level4rrlllr = true := by decide +kernel
def level4rrlll : BinaryTree (List W) := .node [v73, v80, v107, v144, v216] level4rrllll level4rrlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrlll_ok : everyKey (rowOK 3 level3) level4rrlll = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrllll && everyKey (rowOK 3 level3) level4rrlllr) = true
  rw [level4rrllll_ok, level4rrlllr_ok]
  decide +kernel
def level4rrllrl : BinaryTree (List W) := (.node [v80, v90, v108, v161, v216] (.node [v80, v86, v161, v216, v254] (.node [v80, v86, v144, v231, v254] .nil .nil) .nil) (.node [v80, v90, v121, v144, v231] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrllrl_ok : everyKey (rowOK 3 level3) level4rrllrl = true := by decide +kernel
def level4rrllrr : BinaryTree (List W) := (.node [v80, v90, v127, v144, v216] (.node [v80, v90, v122, v144, v216] .nil .nil) (.node [v80, v90, v140, v216, v268] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrllrr_ok : everyKey (rowOK 3 level3) level4rrllrr = true := by decide +kernel
def level4rrllr : BinaryTree (List W) := .node [v80, v90, v121, v161, v216] level4rrllrl level4rrllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrllr_ok : everyKey (rowOK 3 level3) level4rrllr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrllrl && everyKey (rowOK 3 level3) level4rrllrr) = true
  rw [level4rrllrl_ok, level4rrllrr_ok]
  decide +kernel
def level4rrll : BinaryTree (List W) := .node [v80, v86, v144, v216, v268] level4rrlll level4rrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrll_ok : everyKey (rowOK 3 level3) level4rrll = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrlll && everyKey (rowOK 3 level3) level4rrllr) = true
  rw [level4rrlll_ok, level4rrllr_ok]
  decide +kernel
def level4rrlrll : BinaryTree (List W) := (.node [v80, v90, v144, v181, v216] (.node [v80, v90, v144, v176, v216] (.node [v80, v90, v144, v175, v231] .nil .nil) .nil) (.node [v80, v90, v144, v200, v268] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrlrll_ok : everyKey (rowOK 3 level3) level4rrlrll = true := by decide +kernel
def level4rrlrlr : BinaryTree (List W) := (.node [v80, v90, v144, v216, v265] (.node [v80, v90, v144, v216, v259] (.node [v80, v90, v144, v216, v255] .nil .nil) .nil) (.node [v80, v90, v144, v216, v266] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrlrlr_ok : everyKey (rowOK 3 level3) level4rrlrlr = true := by decide +kernel
def level4rrlrl : BinaryTree (List W) := .node [v80, v90, v144, v204, v231] level4rrlrll level4rrlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrlrl_ok : everyKey (rowOK 3 level3) level4rrlrl = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrlrll && everyKey (rowOK 3 level3) level4rrlrlr) = true
  rw [level4rrlrll_ok, level4rrlrlr_ok]
  decide +kernel
def level4rrlrrl : BinaryTree (List W) := (.node [v80, v90, v144, v216, v289] (.node [v80, v90, v144, v216, v283] (.node [v80, v90, v144, v216, v276] .nil .nil) .nil) (.node [v80, v90, v144, v217, v254] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrlrrl_ok : everyKey (rowOK 3 level3) level4rrlrrl = true := by decide +kernel
def level4rrlrrr : BinaryTree (List W) := (.node [v80, v90, v144, v228, v254] (.node [v80, v90, v144, v222, v254] .nil .nil) (.node [v80, v90, v144, v231, v254] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrlrrr_ok : everyKey (rowOK 3 level3) level4rrlrrr = true := by decide +kernel
def level4rrlrr : BinaryTree (List W) := .node [v80, v90, v144, v218, v254] level4rrlrrl level4rrlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrlrr_ok : everyKey (rowOK 3 level3) level4rrlrr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrlrrl && everyKey (rowOK 3 level3) level4rrlrrr) = true
  rw [level4rrlrrl_ok, level4rrlrrr_ok]
  decide +kernel
def level4rrlr : BinaryTree (List W) := .node [v80, v90, v144, v216, v268] level4rrlrl level4rrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrlr_ok : everyKey (rowOK 3 level3) level4rrlr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrlrl && everyKey (rowOK 3 level3) level4rrlrr) = true
  rw [level4rrlrl_ok, level4rrlrr_ok]
  decide +kernel
def level4rrl : BinaryTree (List W) := .node [v80, v90, v140, v231, v254] level4rrll level4rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrl_ok : everyKey (rowOK 3 level3) level4rrl = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrll && everyKey (rowOK 3 level3) level4rrlr) = true
  rw [level4rrll_ok, level4rrlr_ok]
  decide +kernel
def level4rrrlll : BinaryTree (List W) := (.node [v80, v90, v144, v231, v288] (.node [v80, v90, v144, v231, v282] (.node [v80, v90, v144, v231, v275] .nil .nil) .nil) (.node [v80, v90, v144, v231, v289] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrrlll_ok : everyKey (rowOK 3 level3) level4rrrlll = true := by decide +kernel
def level4rrrllr : BinaryTree (List W) := (.node [v80, v90, v158, v216, v254] (.node [v80, v90, v150, v216, v254] (.node [v80, v90, v146, v216, v254] .nil .nil) .nil) (.node [v80, v90, v161, v175, v216] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrrllr_ok : everyKey (rowOK 3 level3) level4rrrllr = true := by decide +kernel
def level4rrrll : BinaryTree (List W) := .node [v80, v90, v145, v216, v254] level4rrrlll level4rrrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrrll_ok : everyKey (rowOK 3 level3) level4rrrll = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrrlll && everyKey (rowOK 3 level3) level4rrrllr) = true
  rw [level4rrrlll_ok, level4rrrllr_ok]
  decide +kernel
def level4rrrlrl : BinaryTree (List W) := (.node [v80, v90, v161, v216, v268] (.node [v80, v90, v161, v216, v254] (.node [v80, v90, v161, v204, v216] .nil .nil) .nil) (.node [v80, v90, v161, v216, v275] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrrlrl_ok : everyKey (rowOK 3 level3) level4rrrlrl = true := by decide +kernel
def level4rrrlrr : BinaryTree (List W) := (.node [v80, v90, v161, v216, v288] (.node [v80, v90, v161, v216, v283] .nil .nil) (.node [v80, v90, v161, v231, v254] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrrlrr_ok : everyKey (rowOK 3 level3) level4rrrlrr = true := by decide +kernel
def level4rrrlr : BinaryTree (List W) := .node [v80, v90, v161, v216, v282] level4rrrlrl level4rrrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrrlr_ok : everyKey (rowOK 3 level3) level4rrrlr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrrlrl && everyKey (rowOK 3 level3) level4rrrlrr) = true
  rw [level4rrrlrl_ok, level4rrrlrr_ok]
  decide +kernel
def level4rrrl : BinaryTree (List W) := .node [v80, v90, v161, v200, v254] level4rrrll level4rrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrrl_ok : everyKey (rowOK 3 level3) level4rrrl = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrrll && everyKey (rowOK 3 level3) level4rrrlr) = true
  rw [level4rrrll_ok, level4rrrlr_ok]
  decide +kernel
def level4rrrrll : BinaryTree (List W) := (.node [v80, v103, v144, v216, v254] (.node [v80, v96, v144, v216, v254] (.node [v80, v92, v144, v216, v254] .nil .nil) .nil) (.node [v80, v107, v121, v144, v216] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrrrll_ok : everyKey (rowOK 3 level3) level4rrrrll = true := by decide +kernel
def level4rrrrlr : BinaryTree (List W) := (.node [v80, v107, v144, v175, v216] (.node [v80, v107, v144, v162, v216] .nil .nil) (.node [v80, v107, v144, v200, v254] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrrrlr_ok : everyKey (rowOK 3 level3) level4rrrrlr = true := by decide +kernel
def level4rrrrl : BinaryTree (List W) := .node [v80, v107, v140, v216, v254] level4rrrrll level4rrrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrrrl_ok : everyKey (rowOK 3 level3) level4rrrrl = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrrrll && everyKey (rowOK 3 level3) level4rrrrlr) = true
  rw [level4rrrrll_ok, level4rrrrlr_ok]
  decide +kernel
def level4rrrrrl : BinaryTree (List W) := (.node [v80, v107, v144, v216, v275] (.node [v80, v107, v144, v216, v268] (.node [v80, v107, v144, v216, v254] .nil .nil) .nil) (.node [v80, v107, v144, v216, v276] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrrrrl_ok : everyKey (rowOK 3 level3) level4rrrrrl = true := by decide +kernel
def level4rrrrrr : BinaryTree (List W) := (.node [v80, v107, v144, v231, v254] (.node [v80, v107, v144, v216, v288] .nil .nil) (.node [v80, v107, v161, v216, v254] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrrrrr_ok : everyKey (rowOK 3 level3) level4rrrrrr = true := by decide +kernel
def level4rrrrr : BinaryTree (List W) := .node [v80, v107, v144, v216, v282] level4rrrrrl level4rrrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrrrr_ok : everyKey (rowOK 3 level3) level4rrrrr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrrrrl && everyKey (rowOK 3 level3) level4rrrrrr) = true
  rw [level4rrrrrl_ok, level4rrrrrr_ok]
  decide +kernel
def level4rrrr : BinaryTree (List W) := .node [v80, v107, v144, v204, v216] level4rrrrl level4rrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrrr_ok : everyKey (rowOK 3 level3) level4rrrr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrrrl && everyKey (rowOK 3 level3) level4rrrrr) = true
  rw [level4rrrrl_ok, level4rrrrr_ok]
  decide +kernel
def level4rrr : BinaryTree (List W) := .node [v80, v91, v144, v216, v254] level4rrrl level4rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrr_ok : everyKey (rowOK 3 level3) level4rrr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrrl && everyKey (rowOK 3 level3) level4rrrr) = true
  rw [level4rrrl_ok, level4rrrr_ok]
  decide +kernel
def level4rr : BinaryTree (List W) := .node [v80, v90, v144, v231, v268] level4rrl level4rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rr_ok : everyKey (rowOK 3 level3) level4rr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrl && everyKey (rowOK 3 level3) level4rrr) = true
  rw [level4rrl_ok, level4rrr_ok]
  decide +kernel
def level4r : BinaryTree (List W) := .node [v70, v107, v144, v216, v254] level4rl level4rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4r_ok : everyKey (rowOK 3 level3) level4r = true := by
  change (_ && everyKey (rowOK 3 level3) level4rl && everyKey (rowOK 3 level3) level4rr) = true
  rw [level4rl_ok, level4rr_ok]
  decide +kernel
def level4 : BinaryTree (List W) := .node [v59, v76, v90, v144, v216] level4l level4r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4_ok : everyKey (rowOK 3 level3) level4 = true := by
  change (_ && everyKey (rowOK 3 level3) level4l && everyKey (rowOK 3 level3) level4r) = true
  rw [level4l_ok, level4r_ok]
  decide +kernel
theorem closed4 : Closed 4 level4 := closed_next 3 (by decide) level4 level3 closed3 level4_ok
def level5llllll : BinaryTree (List W) := (.node [v2, v80, v90, v144, v216, v254] (.node [v1, v39, v59, v90, v144, v216] (.node [v0, v80, v90, v144, v216, v254] .nil .nil) (.node [v2, v59, v90, v144, v204, v216] .nil .nil)) (.node [v4, v39, v59, v90, v144, v216] (.node [v3, v39, v59, v90, v144, v216] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llllll_ok : everyKey (rowOK 4 level4) level5llllll = true := by decide +kernel
def level5lllllr : BinaryTree (List W) := (.node [v6, v39, v58, v90, v144, v216] (.node [v6, v39, v53, v90, v144, v216] (.node [v5, v39, v59, v90, v144, v216] .nil .nil) .nil) (.node [v6, v39, v59, v90, v140, v216] (.node [v6, v39, v59, v86, v144, v216] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllllr_ok : everyKey (rowOK 4 level4) level5lllllr = true := by decide +kernel
def level5lllll : BinaryTree (List W) := .node [v5, v39, v58, v90, v144, v216] level5llllll level5lllllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllll_ok : everyKey (rowOK 4 level4) level5lllll = true := by
  change (_ && everyKey (rowOK 4 level4) level5llllll && everyKey (rowOK 4 level4) level5lllllr) = true
  rw [level5llllll_ok, level5lllllr_ok]
  decide +kernel
def level5llllrl : BinaryTree (List W) := (.node [v6, v39, v59, v107, v144, v216] (.node [v6, v39, v59, v90, v144, v231] (.node [v6, v39, v59, v90, v144, v216] .nil .nil) (.node [v6, v39, v59, v90, v161, v216] .nil .nil)) (.node [v6, v39, v90, v144, v197, v216] (.node [v6, v39, v80, v90, v144, v216] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llllrl_ok : everyKey (rowOK 4 level4) level5llllrl = true := by decide +kernel
def level5llllrr : BinaryTree (List W) := (.node [v9, v39, v59, v90, v144, v216] (.node [v8, v39, v59, v144, v175, v216] (.node [v7, v39, v80, v90, v144, v216] .nil .nil) .nil) (.node [v11, v39, v59, v90, v144, v216] (.node [v10, v39, v59, v90, v121, v216] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llllrr_ok : everyKey (rowOK 4 level4) level5llllrr = true := by decide +kernel
def level5llllr : BinaryTree (List W) := .node [v7, v39, v59, v90, v144, v216] level5llllrl level5llllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llllr_ok : everyKey (rowOK 4 level4) level5llllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llllrl && everyKey (rowOK 4 level4) level5llllrr) = true
  rw [level5llllrl_ok, level5llllrr_ok]
  decide +kernel
def level5llll : BinaryTree (List W) := .node [v6, v39, v59, v90, v144, v200] level5lllll level5llllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llll_ok : everyKey (rowOK 4 level4) level5llll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lllll && everyKey (rowOK 4 level4) level5llllr) = true
  rw [level5lllll_ok, level5llllr_ok]
  decide +kernel
def level5lllrll : BinaryTree (List W) := (.node [v16, v39, v59, v90, v144, v216] (.node [v14, v59, v107, v144, v216, v254] (.node [v13, v39, v59, v90, v144, v216] .nil .nil) (.node [v15, v39, v119, v144, v216, v254] .nil .nil)) (.node [v18, v59, v90, v161, v216, v254] (.node [v17, v39, v59, v90, v144, v216] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrll_ok : everyKey (rowOK 4 level4) level5lllrll = true := by decide +kernel
def level5lllrlr : BinaryTree (List W) := (.node [v19, v80, v90, v144, v216, v254] (.node [v19, v59, v107, v144, v216, v254] (.node [v19, v59, v90, v161, v216, v254] .nil .nil) .nil) (.node [v21, v39, v59, v90, v144, v216] (.node [v20, v39, v90, v173, v216, v254] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrlr_ok : everyKey (rowOK 4 level4) level5lllrlr = true := by decide +kernel
def level5lllrl : BinaryTree (List W) := .node [v19, v59, v90, v144, v200, v254] level5lllrll level5lllrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrl_ok : everyKey (rowOK 4 level4) level5lllrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lllrll && everyKey (rowOK 4 level4) level5lllrlr) = true
  rw [level5lllrll_ok, level5lllrlr_ok]
  decide +kernel
def level5lllrrl : BinaryTree (List W) := (.node [v26, v39, v59, v144, v174, v254] (.node [v24, v39, v59, v90, v144, v216] (.node [v23, v39, v90, v144, v194, v254] .nil .nil) (.node [v25, v39, v59, v193, v216, v254] .nil .nil)) (.node [v27, v39, v59, v90, v144, v231] (.node [v27, v39, v59, v90, v144, v216] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrrl_ok : everyKey (rowOK 4 level4) level5lllrrl = true := by decide +kernel
def level5lllrrr : BinaryTree (List W) := (.node [v29, v39, v59, v90, v140, v216] (.node [v29, v39, v59, v86, v144, v216] (.node [v29, v39, v58, v90, v144, v216] .nil .nil) .nil) (.node [v29, v39, v59, v90, v144, v216] (.node [v29, v39, v59, v90, v144, v200] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrrr_ok : everyKey (rowOK 4 level4) level5lllrrr = true := by decide +kernel
def level5lllrr : BinaryTree (List W) := .node [v28, v39, v59, v90, v120, v254] level5lllrrl level5lllrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrr_ok : everyKey (rowOK 4 level4) level5lllrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lllrrl && everyKey (rowOK 4 level4) level5lllrrr) = true
  rw [level5lllrrl_ok, level5lllrrr_ok]
  decide +kernel
def level5lllr : BinaryTree (List W) := .node [v22, v39, v59, v90, v144, v216] level5lllrl level5lllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllr_ok : everyKey (rowOK 4 level4) level5lllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lllrl && everyKey (rowOK 4 level4) level5lllrr) = true
  rw [level5lllrl_ok, level5lllrr_ok]
  decide +kernel
def level5lll : BinaryTree (List W) := .node [v12, v29, v39, v59, v90, v144] level5llll level5lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lll_ok : everyKey (rowOK 4 level4) level5lll = true := by
  change (_ && everyKey (rowOK 4 level4) level5llll && everyKey (rowOK 4 level4) level5lllr) = true
  rw [level5llll_ok, level5lllr_ok]
  decide +kernel
def level5llrlll : BinaryTree (List W) := (.node [v29, v39, v80, v90, v144, v216] (.node [v29, v39, v59, v90, v161, v216] (.node [v29, v39, v59, v90, v144, v288] .nil .nil) (.node [v29, v39, v59, v107, v144, v216] .nil .nil)) (.node [v31, v39, v59, v90, v144, v216] (.node [v30, v39, v59, v90, v144, v216] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrlll_ok : everyKey (rowOK 4 level4) level5llrlll = true := by decide +kernel
def level5llrllr : BinaryTree (List W) := (.node [v35, v59, v90, v144, v231, v254] (.node [v35, v59, v90, v140, v216, v254] (.node [v34, v59, v90, v144, v231, v254] .nil .nil) .nil) (.node [v35, v80, v90, v144, v216, v254] (.node [v35, v59, v107, v144, v216, v254] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrllr_ok : everyKey (rowOK 4 level4) level5llrllr = true := by decide +kernel
def level5llrll : BinaryTree (List W) := .node [v32, v39, v59, v90, v144, v216] level5llrlll level5llrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrll_ok : everyKey (rowOK 4 level4) level5llrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrlll && everyKey (rowOK 4 level4) level5llrllr) = true
  rw [level5llrlll_ok, level5llrllr_ok]
  decide +kernel
def level5llrlrl : BinaryTree (List W) := (.node [v37, v59, v90, v144, v216, v268] (.node [v36, v59, v90, v161, v216, v254] (.node [v36, v59, v90, v144, v231, v254] .nil .nil) (.node [v36, v80, v90, v144, v216, v254] .nil .nil)) (.node [v38, v59, v90, v144, v216, v268] (.node [v38, v58, v90, v144, v216, v254] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrlrl_ok : everyKey (rowOK 4 level4) level5llrlrl = true := by decide +kernel
def level5llrlrr : BinaryTree (List W) := (.node [v39, v40, v59, v90, v144, v216] (.node [v38, v59, v107, v144, v216, v254] (.node [v38, v59, v90, v161, v216, v254] .nil .nil) .nil) (.node [v39, v45, v59, v90, v144, v216] (.node [v39, v45, v59, v90, v144, v200] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrlrr_ok : everyKey (rowOK 4 level4) level5llrlrr = true := by decide +kernel
def level5llrlr : BinaryTree (List W) := .node [v38, v59, v90, v144, v231, v254] level5llrlrl level5llrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrlr_ok : everyKey (rowOK 4 level4) level5llrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrlrl && everyKey (rowOK 4 level4) level5llrlrr) = true
  rw [level5llrlrl_ok, level5llrlrr_ok]
  decide +kernel
def level5llrl : BinaryTree (List W) := .node [v36, v59, v86, v144, v216, v254] level5llrll level5llrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrl_ok : everyKey (rowOK 4 level4) level5llrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrll && everyKey (rowOK 4 level4) level5llrlr) = true
  rw [level5llrll_ok, level5llrlr_ok]
  decide +kernel
def level5llrrll : BinaryTree (List W) := (.node [v39, v50, v90, v138, v216, v254] (.node [v39, v48, v59, v90, v144, v216] (.node [v39, v47, v90, v144, v239, v254] .nil .nil) (.node [v39, v49, v59, v90, v144, v216] .nil .nil)) (.node [v39, v52, v84, v144, v216, v254] (.node [v39, v51, v59, v90, v144, v216] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrll_ok : everyKey (rowOK 4 level4) level5llrrll = true := by decide +kernel
def level5llrrlr : BinaryTree (List W) := (.node [v39, v53, v59, v90, v139, v216] (.node [v39, v53, v59, v86, v144, v216] (.node [v39, v53, v59, v85, v144, v216] .nil .nil) .nil) (.node [v39, v53, v59, v90, v144, v195] (.node [v39, v53, v59, v90, v140, v216] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrlr_ok : everyKey (rowOK 4 level4) level5llrrlr = true := by decide +kernel
def level5llrrl : BinaryTree (List W) := .node [v39, v53, v58, v90, v144, v216] level5llrrll level5llrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrl_ok : everyKey (rowOK 4 level4) level5llrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrrll && everyKey (rowOK 4 level4) level5llrrlr) = true
  rw [level5llrrll_ok, level5llrrlr_ok]
  decide +kernel
def level5llrrrl : BinaryTree (List W) := (.node [v39, v53, v59, v90, v144, v235] (.node [v39, v53, v59, v90, v144, v231] (.node [v39, v53, v59, v90, v144, v216] .nil .nil) .nil) (.node [v39, v53, v59, v90, v169, v216] (.node [v39, v53, v59, v90, v161, v216] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrrl_ok : everyKey (rowOK 4 level4) level5llrrrl = true := by decide +kernel
def level5llrrrr : BinaryTree (List W) := (.node [v39, v53, v90, v144, v216, v270] (.node [v39, v53, v80, v90, v144, v216] (.node [v39, v53, v59, v115, v144, v216] .nil .nil) .nil) (.node [v39, v55, v59, v90, v144, v216] (.node [v39, v54, v59, v90, v144, v216] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrrr_ok : everyKey (rowOK 4 level4) level5llrrrr = true := by decide +kernel
def level5llrrr : BinaryTree (List W) := .node [v39, v53, v59, v107, v144, v216] level5llrrrl level5llrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrr_ok : everyKey (rowOK 4 level4) level5llrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrrrl && everyKey (rowOK 4 level4) level5llrrrr) = true
  rw [level5llrrrl_ok, level5llrrrr_ok]
  decide +kernel
def level5llrr : BinaryTree (List W) := .node [v39, v53, v59, v90, v144, v200] level5llrrl level5llrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrr_ok : everyKey (rowOK 4 level4) level5llrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrrl && everyKey (rowOK 4 level4) level5llrrr) = true
  rw [level5llrrl_ok, level5llrrr_ok]
  decide +kernel
def level5llr : BinaryTree (List W) := .node [v39, v46, v59, v90, v144, v216] level5llrl level5llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llr_ok : everyKey (rowOK 4 level4) level5llr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrl && everyKey (rowOK 4 level4) level5llrr) = true
  rw [level5llrl_ok, level5llrr_ok]
  decide +kernel
def level5ll : BinaryTree (List W) := .node [v29, v39, v59, v90, v144, v231] level5lll level5llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5ll_ok : everyKey (rowOK 4 level4) level5ll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lll && everyKey (rowOK 4 level4) level5llr) = true
  rw [level5lll_ok, level5llr_ok]
  decide +kernel
def level5lrllll : BinaryTree (List W) := (.node [v39, v58, v90, v140, v216, v254] (.node [v39, v58, v86, v144, v216, v254] (.node [v39, v57, v59, v90, v144, v216] .nil .nil) (.node [v39, v58, v90, v121, v144, v216] .nil .nil)) (.node [v39, v58, v90, v144, v200, v254] (.node [v39, v58, v90, v144, v175, v216] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrllll_ok : everyKey (rowOK 4 level4) level5lrllll = true := by decide +kernel
def level5lrlllr : BinaryTree (List W) := (.node [v39, v58, v90, v144, v216, v275] (.node [v39, v58, v90, v144, v216, v268] (.node [v39, v58, v90, v144, v216, v254] .nil .nil) .nil) (.node [v39, v58, v90, v144, v216, v288] (.node [v39, v58, v90, v144, v216, v282] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlllr_ok : everyKey (rowOK 4 level4) level5lrlllr = true := by decide +kernel
def level5lrlll : BinaryTree (List W) := .node [v39, v58, v90, v144, v204, v216] level5lrllll level5lrlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlll_ok : everyKey (rowOK 4 level4) level5lrlll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrllll && everyKey (rowOK 4 level4) level5lrlllr) = true
  rw [level5lrllll_ok, level5lrlllr_ok]
  decide +kernel
def level5lrllrl : BinaryTree (List W) := (.node [v39, v59, v66, v90, v144, v216] (.node [v39, v58, v107, v144, v216, v254] (.node [v39, v58, v90, v161, v216, v254] .nil .nil) (.node [v39, v59, v65, v90, v144, v216] .nil .nil)) (.node [v39, v59, v74, v90, v144, v216] (.node [v39, v59, v73, v90, v144, v216] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrllrl_ok : everyKey (rowOK 4 level4) level5lrllrl = true := by decide +kernel
def level5lrllrr : BinaryTree (List W) := (.node [v39, v59, v85, v144, v216, v254] (.node [v39, v59, v84, v144, v216, v275] (.node [v39, v59, v82, v136, v216, v254] .nil .nil) .nil) (.node [v39, v59, v86, v140, v216, v254] (.node [v39, v59, v86, v121, v144, v216] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrllrr_ok : everyKey (rowOK 4 level4) level5lrllrr = true := by decide +kernel
def level5lrllr : BinaryTree (List W) := .node [v39, v59, v81, v144, v246, v254] level5lrllrl level5lrllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrllr_ok : everyKey (rowOK 4 level4) level5lrllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrllrl && everyKey (rowOK 4 level4) level5lrllrr) = true
  rw [level5lrllrl_ok, level5lrllrr_ok]
  decide +kernel
def level5lrll : BinaryTree (List W) := .node [v39, v58, v90, v144, v231, v254] level5lrlll level5lrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrll_ok : everyKey (rowOK 4 level4) level5lrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrlll && everyKey (rowOK 4 level4) level5lrllr) = true
  rw [level5lrlll_ok, level5lrllr_ok]
  decide +kernel
def level5lrlrll : BinaryTree (List W) := (.node [v39, v59, v86, v144, v216, v254] (.node [v39, v59, v86, v144, v200, v254] (.node [v39, v59, v86, v144, v180, v216] .nil .nil) (.node [v39, v59, v86, v144, v204, v216] .nil .nil)) (.node [v39, v59, v86, v144, v216, v274] (.node [v39, v59, v86, v144, v216, v268] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrll_ok : everyKey (rowOK 4 level4) level5lrlrll = true := by decide +kernel
def level5lrlrlr : BinaryTree (List W) := (.node [v39, v59, v86, v144, v231, v254] (.node [v39, v59, v86, v144, v216, v288] (.node [v39, v59, v86, v144, v216, v282] .nil .nil) .nil) (.node [v39, v59, v87, v144, v216, v254] (.node [v39, v59, v86, v161, v216, v254] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrlr_ok : everyKey (rowOK 4 level4) level5lrlrlr = true := by decide +kernel
def level5lrlrl : BinaryTree (List W) := .node [v39, v59, v86, v144, v216, v275] level5lrlrll level5lrlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrl_ok : everyKey (rowOK 4 level4) level5lrlrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrlrll && everyKey (rowOK 4 level4) level5lrlrlr) = true
  rw [level5lrlrll_ok, level5lrlrlr_ok]
  decide +kernel
def level5lrlrrl : BinaryTree (List W) := (.node [v39, v59, v90, v99, v144, v216] (.node [v39, v59, v90, v93, v144, v216] (.node [v39, v59, v89, v144, v216, v254] .nil .nil) .nil) (.node [v39, v59, v90, v108, v144, v216] (.node [v39, v59, v90, v100, v144, v216] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrrl_ok : everyKey (rowOK 4 level4) level5lrlrrl = true := by decide +kernel
def level5lrlrrr : BinaryTree (List W) := (.node [v39, v59, v90, v121, v140, v216] (.node [v39, v59, v90, v115, v144, v216] (.node [v39, v59, v90, v114, v144, v216] .nil .nil) .nil) (.node [v39, v59, v90, v121, v144, v216] (.node [v39, v59, v90, v121, v144, v200] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrrr_ok : everyKey (rowOK 4 level4) level5lrlrrr = true := by decide +kernel
def level5lrlrr : BinaryTree (List W) := .node [v39, v59, v90, v108, v161, v216] level5lrlrrl level5lrlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrr_ok : everyKey (rowOK 4 level4) level5lrlrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrlrrl && everyKey (rowOK 4 level4) level5lrlrrr) = true
  rw [level5lrlrrl_ok, level5lrlrrr_ok]
  decide +kernel
def level5lrlr : BinaryTree (List W) := .node [v39, v59, v88, v144, v216, v275] level5lrlrl level5lrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlr_ok : everyKey (rowOK 4 level4) level5lrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrlrl && everyKey (rowOK 4 level4) level5lrlrr) = true
  rw [level5lrlrl_ok, level5lrlrr_ok]
  decide +kernel
def level5lrl : BinaryTree (List W) := .node [v39, v59, v86, v144, v175, v216] level5lrll level5lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrl_ok : everyKey (rowOK 4 level4) level5lrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrll && everyKey (rowOK 4 level4) level5lrlr) = true
  rw [level5lrll_ok, level5lrlr_ok]
  decide +kernel
def level5lrrlll : BinaryTree (List W) := (.node [v39, v59, v90, v123, v144, v216] (.node [v39, v59, v90, v121, v216, v282] (.node [v39, v59, v90, v121, v161, v216] .nil .nil) (.node [v39, v59, v90, v122, v144, v216] .nil .nil)) (.node [v39, v59, v90, v126, v140, v216] (.node [v39, v59, v90, v124, v144, v216] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrlll_ok : everyKey (rowOK 4 level4) level5lrrlll = true := by decide +kernel
def level5lrrllr : BinaryTree (List W) := (.node [v39, v59, v90, v129, v144, v216] (.node [v39, v59, v90, v128, v144, v216] (.node [v39, v59, v90, v127, v144, v216] .nil .nil) .nil) (.node [v39, v59, v90, v132, v144, v216] (.node [v39, v59, v90, v130, v144, v216] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrllr_ok : everyKey (rowOK 4 level4) level5lrrllr = true := by decide +kernel
def level5lrrll : BinaryTree (List W) := .node [v39, v59, v90, v126, v144, v216] level5lrrlll level5lrrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrll_ok : everyKey (rowOK 4 level4) level5lrrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrlll && everyKey (rowOK 4 level4) level5lrrllr) = true
  rw [level5lrrlll_ok, level5lrrllr_ok]
  decide +kernel
def level5lrrlrl : BinaryTree (List W) := (.node [v39, v59, v90, v140, v200, v254] (.node [v39, v59, v90, v139, v216, v254] (.node [v39, v59, v90, v138, v216, v282] .nil .nil) (.node [v39, v59, v90, v140, v175, v216] .nil .nil)) (.node [v39, v59, v90, v140, v216, v254] (.node [v39, v59, v90, v140, v204, v216] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrlrl_ok : everyKey (rowOK 4 level4) level5lrrlrl = true := by decide +kernel
def level5lrrlrr : BinaryTree (List W) := (.node [v39, v59, v90, v140, v216, v282] (.node [v39, v59, v90, v140, v216, v281] (.node [v39, v59, v90, v140, v216, v275] .nil .nil) .nil) (.node [v39, v59, v90, v140, v231, v254] (.node [v39, v59, v90, v140, v216, v288] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrlrr_ok : everyKey (rowOK 4 level4) level5lrrlrr = true := by decide +kernel
def level5lrrlr : BinaryTree (List W) := .node [v39, v59, v90, v140, v216, v268] level5lrrlrl level5lrrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrlr_ok : everyKey (rowOK 4 level4) level5lrrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrlrl && everyKey (rowOK 4 level4) level5lrrlrr) = true
  rw [level5lrrlrl_ok, level5lrrlrr_ok]
  decide +kernel
def level5lrrl : BinaryTree (List W) := .node [v39, v59, v90, v135, v251, v254] level5lrrll level5lrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrl_ok : everyKey (rowOK 4 level4) level5lrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrll && everyKey (rowOK 4 level4) level5lrrlr) = true
  rw [level5lrrll_ok, level5lrrlr_ok]
  decide +kernel
def level5lrrrll : BinaryTree (List W) := (.node [v39, v59, v90, v144, v153, v216] (.node [v39, v59, v90, v143, v216, v254] (.node [v39, v59, v90, v142, v216, v282] .nil .nil) (.node [v39, v59, v90, v144, v147, v216] .nil .nil)) (.node [v39, v59, v90, v144, v162, v216] (.node [v39, v59, v90, v144, v154, v216] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrll_ok : everyKey (rowOK 4 level4) level5lrrrll = true := by decide +kernel
def level5lrrrlr : BinaryTree (List W) := (.node [v39, v59, v90, v144, v175, v216] (.node [v39, v59, v90, v144, v175, v200] (.node [v39, v59, v90, v144, v169, v216] .nil .nil) .nil) (.node [v39, v59, v90, v144, v176, v216] (.node [v39, v59, v90, v144, v175, v231] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrlr_ok : everyKey (rowOK 4 level4) level5lrrrlr = true := by decide +kernel
def level5lrrrl : BinaryTree (List W) := .node [v39, v59, v90, v144, v168, v216] level5lrrrll level5lrrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrl_ok : everyKey (rowOK 4 level4) level5lrrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrrll && everyKey (rowOK 4 level4) level5lrrrlr) = true
  rw [level5lrrrll_ok, level5lrrrlr_ok]
  decide +kernel
def level5lrrrrl : BinaryTree (List W) := (.node [v39, v59, v90, v144, v181, v216] (.node [v39, v59, v90, v144, v180, v216] (.node [v39, v59, v90, v144, v179, v216] .nil .nil) .nil) (.node [v39, v59, v90, v144, v184, v216] (.node [v39, v59, v90, v144, v182, v216] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrrl_ok : everyKey (rowOK 4 level4) level5lrrrrl = true := by decide +kernel
def level5lrrrrr : BinaryTree (List W) := (.node [v39, v59, v90, v144, v195, v254] (.node [v39, v59, v90, v144, v194, v288] (.node [v39, v59, v90, v144, v186, v216] .nil .nil) .nil) (.node [v39, v59, v90, v144, v200, v204] (.node [v39, v59, v90, v144, v199, v216] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrrr_ok : everyKey (rowOK 4 level4) level5lrrrrr = true := by decide +kernel
def level5lrrrr : BinaryTree (List W) := .node [v39, v59, v90, v144, v185, v216] level5lrrrrl level5lrrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrr_ok : everyKey (rowOK 4 level4) level5lrrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrrrl && everyKey (rowOK 4 level4) level5lrrrrr) = true
  rw [level5lrrrrl_ok, level5lrrrrr_ok]
  decide +kernel
def level5lrrr : BinaryTree (List W) := .node [v39, v59, v90, v144, v178, v216] level5lrrrl level5lrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrr_ok : everyKey (rowOK 4 level4) level5lrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrrl && everyKey (rowOK 4 level4) level5lrrrr) = true
  rw [level5lrrrl_ok, level5lrrrr_ok]
  decide +kernel
def level5lrr : BinaryTree (List W) := .node [v39, v59, v90, v141, v216, v254] level5lrrl level5lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrr_ok : everyKey (rowOK 4 level4) level5lrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrl && everyKey (rowOK 4 level4) level5lrrr) = true
  rw [level5lrrl_ok, level5lrrr_ok]
  decide +kernel
def level5lr : BinaryTree (List W) := .node [v39, v59, v90, v121, v144, v231] level5lrl level5lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lr_ok : everyKey (rowOK 4 level4) level5lr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrl && everyKey (rowOK 4 level4) level5lrr) = true
  rw [level5lrl_ok, level5lrr_ok]
  decide +kernel
def level5l : BinaryTree (List W) := .node [v39, v56, v59, v90, v144, v216] level5ll level5lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5l_ok : everyKey (rowOK 4 level4) level5l = true := by
  change (_ && everyKey (rowOK 4 level4) level5ll && everyKey (rowOK 4 level4) level5lr) = true
  rw [level5ll_ok, level5lr_ok]
  decide +kernel
def level5rlllll : BinaryTree (List W) := (.node [v39, v59, v90, v144, v200, v287] (.node [v39, v59, v90, v144, v200, v275] (.node [v39, v59, v90, v144, v200, v268] .nil .nil) (.node [v39, v59, v90, v144, v200, v282] .nil .nil)) (.node [v39, v59, v90, v144, v201, v254] (.node [v39, v59, v90, v144, v200, v288] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlllll_ok : everyKey (rowOK 4 level4) level5rlllll = true := by decide +kernel
def level5rllllr : BinaryTree (List W) := (.node [v39, v59, v90, v144, v207, v216] (.node [v39, v59, v90, v144, v206, v216] (.node [v39, v59, v90, v144, v204, v231] .nil .nil) .nil) (.node [v39, v59, v90, v144, v209, v216] (.node [v39, v59, v90, v144, v208, v216] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllllr_ok : everyKey (rowOK 4 level4) level5rllllr = true := by decide +kernel
def level5rllll : BinaryTree (List W) := .node [v39, v59, v90, v144, v204, v216] level5rlllll level5rllllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllll_ok : everyKey (rowOK 4 level4) level5rllll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlllll && everyKey (rowOK 4 level4) level5rllllr) = true
  rw [level5rlllll_ok, level5rllllr_ok]
  decide +kernel
def level5rlllrl : BinaryTree (List W) := (.node [v39, v59, v90, v144, v214, v288] (.node [v39, v59, v90, v144, v212, v216] (.node [v39, v59, v90, v144, v211, v216] .nil .nil) (.node [v39, v59, v90, v144, v213, v216] .nil .nil)) (.node [v39, v59, v90, v144, v216, v219] (.node [v39, v59, v90, v144, v215, v254] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlllrl_ok : everyKey (rowOK 4 level4) level5rlllrl = true := by decide +kernel
def level5rlllrr : BinaryTree (List W) := (.node [v39, v59, v90, v144, v216, v235] (.node [v39, v59, v90, v144, v216, v234] (.node [v39, v59, v90, v144, v216, v226] .nil .nil) .nil) (.node [v39, v59, v90, v144, v216, v241] (.node [v39, v59, v90, v144, v216, v240] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlllrr_ok : everyKey (rowOK 4 level4) level5rlllrr = true := by decide +kernel
def level5rlllr : BinaryTree (List W) := .node [v39, v59, v90, v144, v216, v225] level5rlllrl level5rlllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlllr_ok : everyKey (rowOK 4 level4) level5rlllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlllrl && everyKey (rowOK 4 level4) level5rlllrr) = true
  rw [level5rlllrl_ok, level5rlllrr_ok]
  decide +kernel
def level5rlll : BinaryTree (List W) := .node [v39, v59, v90, v144, v210, v216] level5rllll level5rlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlll_ok : everyKey (rowOK 4 level4) level5rlll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rllll && everyKey (rowOK 4 level4) level5rlllr) = true
  rw [level5rllll_ok, level5rlllr_ok]
  decide +kernel
def level5rllrll : BinaryTree (List W) := (.node [v39, v59, v90, v144, v216, v250] (.node [v39, v59, v90, v144, v216, v248] (.node [v39, v59, v90, v144, v216, v247] .nil .nil) (.node [v39, v59, v90, v144, v216, v249] .nil .nil)) (.node [v39, v59, v90, v144, v216, v253] (.node [v39, v59, v90, v144, v216, v252] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrll_ok : everyKey (rowOK 4 level4) level5rllrll = true := by decide +kernel
def level5rllrlr : BinaryTree (List W) := (.node [v39, v59, v90, v144, v216, v257] (.node [v39, v59, v90, v144, v216, v256] (.node [v39, v59, v90, v144, v216, v255] .nil .nil) .nil) (.node [v39, v59, v90, v144, v216, v259] (.node [v39, v59, v90, v144, v216, v258] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrlr_ok : everyKey (rowOK 4 level4) level5rllrlr = true := by decide +kernel
def level5rllrl : BinaryTree (List W) := .node [v39, v59, v90, v144, v216, v254] level5rllrll level5rllrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrl_ok : everyKey (rowOK 4 level4) level5rllrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rllrll && everyKey (rowOK 4 level4) level5rllrlr) = true
  rw [level5rllrll_ok, level5rllrlr_ok]
  decide +kernel
def level5rllrrl : BinaryTree (List W) := (.node [v39, v59, v90, v144, v216, v263] (.node [v39, v59, v90, v144, v216, v262] (.node [v39, v59, v90, v144, v216, v261] .nil .nil) .nil) (.node [v39, v59, v90, v144, v216, v265] (.node [v39, v59, v90, v144, v216, v264] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrrl_ok : everyKey (rowOK 4 level4) level5rllrrl = true := by decide +kernel
def level5rllrrr : BinaryTree (List W) := (.node [v39, v59, v90, v144, v216, v269] (.node [v39, v59, v90, v144, v216, v268] (.node [v39, v59, v90, v144, v216, v267] .nil .nil) .nil) (.node [v39, v59, v90, v144, v216, v272] (.node [v39, v59, v90, v144, v216, v271] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrrr_ok : everyKey (rowOK 4 level4) level5rllrrr = true := by decide +kernel
def level5rllrr : BinaryTree (List W) := .node [v39, v59, v90, v144, v216, v266] level5rllrrl level5rllrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrr_ok : everyKey (rowOK 4 level4) level5rllrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rllrrl && everyKey (rowOK 4 level4) level5rllrrr) = true
  rw [level5rllrrl_ok, level5rllrrr_ok]
  decide +kernel
def level5rllr : BinaryTree (List W) := .node [v39, v59, v90, v144, v216, v260] level5rllrl level5rllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllr_ok : everyKey (rowOK 4 level4) level5rllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rllrl && everyKey (rowOK 4 level4) level5rllrr) = true
  rw [level5rllrl_ok, level5rllrr_ok]
  decide +kernel
def level5rll : BinaryTree (List W) := .node [v39, v59, v90, v144, v216, v242] level5rlll level5rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rll_ok : everyKey (rowOK 4 level4) level5rll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlll && everyKey (rowOK 4 level4) level5rllr) = true
  rw [level5rlll_ok, level5rllr_ok]
  decide +kernel
def level5rlrlll : BinaryTree (List W) := (.node [v39, v59, v90, v144, v216, v277] (.node [v39, v59, v90, v144, v216, v275] (.node [v39, v59, v90, v144, v216, v274] .nil .nil) (.node [v39, v59, v90, v144, v216, v276] .nil .nil)) (.node [v39, v59, v90, v144, v216, v279] (.node [v39, v59, v90, v144, v216, v278] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrlll_ok : everyKey (rowOK 4 level4) level5rlrlll = true := by decide +kernel
def level5rlrllr : BinaryTree (List W) := (.node [v39, v59, v90, v144, v216, v283] (.node [v39, v59, v90, v144, v216, v282] (.node [v39, v59, v90, v144, v216, v281] .nil .nil) .nil) (.node [v39, v59, v90, v144, v216, v285] (.node [v39, v59, v90, v144, v216, v284] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrllr_ok : everyKey (rowOK 4 level4) level5rlrllr = true := by decide +kernel
def level5rlrll : BinaryTree (List W) := .node [v39, v59, v90, v144, v216, v280] level5rlrlll level5rlrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrll_ok : everyKey (rowOK 4 level4) level5rlrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrlll && everyKey (rowOK 4 level4) level5rlrllr) = true
  rw [level5rlrlll_ok, level5rlrllr_ok]
  decide +kernel
def level5rlrlrl : BinaryTree (List W) := (.node [v39, v59, v90, v144, v216, v290] (.node [v39, v59, v90, v144, v216, v288] (.node [v39, v59, v90, v144, v216, v287] .nil .nil) (.node [v39, v59, v90, v144, v216, v289] .nil .nil)) (.node [v39, v59, v90, v144, v217, v254] (.node [v39, v59, v90, v144, v216, v291] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrlrl_ok : everyKey (rowOK 4 level4) level5rlrlrl = true := by decide +kernel
def level5rlrlrr : BinaryTree (List W) := (.node [v39, v59, v90, v144, v223, v254] (.node [v39, v59, v90, v144, v222, v254] (.node [v39, v59, v90, v144, v221, v254] .nil .nil) .nil) (.node [v39, v59, v90, v144, v228, v254] (.node [v39, v59, v90, v144, v227, v254] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrlrr_ok : everyKey (rowOK 4 level4) level5rlrlrr = true := by decide +kernel
def level5rlrlr : BinaryTree (List W) := .node [v39, v59, v90, v144, v218, v254] level5rlrlrl level5rlrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrlr_ok : everyKey (rowOK 4 level4) level5rlrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrlrl && everyKey (rowOK 4 level4) level5rlrlrr) = true
  rw [level5rlrlrl_ok, level5rlrlrr_ok]
  decide +kernel
def level5rlrl : BinaryTree (List W) := .node [v39, v59, v90, v144, v216, v286] level5rlrll level5rlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrl_ok : everyKey (rowOK 4 level4) level5rlrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrll && everyKey (rowOK 4 level4) level5rlrlr) = true
  rw [level5rlrll_ok, level5rlrlr_ok]
  decide +kernel
def level5rlrrll : BinaryTree (List W) := (.node [v39, v59, v90, v144, v231, v275] (.node [v39, v59, v90, v144, v231, v254] (.node [v39, v59, v90, v144, v230, v254] .nil .nil) (.node [v39, v59, v90, v144, v231, v268] .nil .nil)) (.node [v39, v59, v90, v144, v231, v288] (.node [v39, v59, v90, v144, v231, v282] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrll_ok : everyKey (rowOK 4 level4) level5rlrrll = true := by decide +kernel
def level5rlrrlr : BinaryTree (List W) := (.node [v39, v59, v90, v144, v235, v254] (.node [v39, v59, v90, v144, v235] (.node [v39, v59, v90, v144, v232, v254] .nil .nil) .nil) (.node [v39, v59, v90, v144, v245, v254] (.node [v39, v59, v90, v144, v239, v288] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrlr_ok : everyKey (rowOK 4 level4) level5rlrrlr = true := by decide +kernel
def level5rlrrl : BinaryTree (List W) := .node [v39, v59, v90, v144, v231, v289] level5rlrrll level5rlrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrl_ok : everyKey (rowOK 4 level4) level5rlrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrrll && everyKey (rowOK 4 level4) level5rlrrlr) = true
  rw [level5rlrrll_ok, level5rlrrlr_ok]
  decide +kernel
def level5rlrrrl : BinaryTree (List W) := (.node [v39, v59, v90, v150, v216, v254] (.node [v39, v59, v90, v149, v216, v254] (.node [v39, v59, v90, v146, v216, v254] .nil .nil) .nil) (.node [v39, v59, v90, v157, v216, v254] (.node [v39, v59, v90, v151, v216, v254] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrrl_ok : everyKey (rowOK 4 level4) level5rlrrrl = true := by decide +kernel
def level5rlrrrr : BinaryTree (List W) := (.node [v39, v59, v90, v161, v175, v216] (.node [v39, v59, v90, v160, v216, v254] (.node [v39, v59, v90, v159, v216, v254] .nil .nil) .nil) (.node [v39, v59, v90, v161, v204, v216] (.node [v39, v59, v90, v161, v200, v254] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrrr_ok : everyKey (rowOK 4 level4) level5rlrrrr = true := by decide +kernel
def level5rlrrr : BinaryTree (List W) := .node [v39, v59, v90, v158, v216, v254] level5rlrrrl level5rlrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrr_ok : everyKey (rowOK 4 level4) level5rlrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrrrl && everyKey (rowOK 4 level4) level5rlrrrr) = true
  rw [level5rlrrrl_ok, level5rlrrrr_ok]
  decide +kernel
def level5rlrr : BinaryTree (List W) := .node [v39, v59, v90, v145, v216, v254] level5rlrrl level5rlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrr_ok : everyKey (rowOK 4 level4) level5rlrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrrl && everyKey (rowOK 4 level4) level5rlrrr) = true
  rw [level5rlrrl_ok, level5rlrrr_ok]
  decide +kernel
def level5rlr : BinaryTree (List W) := .node [v39, v59, v90, v144, v229, v254] level5rlrl level5rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlr_ok : everyKey (rowOK 4 level4) level5rlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrl && everyKey (rowOK 4 level4) level5rlrr) = true
  rw [level5rlrl_ok, level5rlrr_ok]
  decide +kernel
def level5rl : BinaryTree (List W) := .node [v39, v59, v90, v144, v216, v273] level5rll level5rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rl_ok : everyKey (rowOK 4 level4) level5rl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rll && everyKey (rowOK 4 level4) level5rlr) = true
  rw [level5rll_ok, level5rlr_ok]
  decide +kernel
def level5rrllll : BinaryTree (List W) := (.node [v39, v59, v90, v161, v216, v283] (.node [v39, v59, v90, v161, v216, v275] (.node [v39, v59, v90, v161, v216, v268] .nil .nil) (.node [v39, v59, v90, v161, v216, v282] .nil .nil)) (.node [v39, v59, v90, v161, v231, v254] (.node [v39, v59, v90, v161, v216, v288] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrllll_ok : everyKey (rowOK 4 level4) level5rrllll = true := by decide +kernel
def level5rrlllr : BinaryTree (List W) := (.node [v39, v59, v90, v173, v216, v282] (.node [v39, v59, v90, v169, v216, v254] (.node [v39, v59, v90, v169, v216] .nil .nil) .nil) (.node [v39, v59, v91, v144, v216, v254] (.node [v39, v59, v90, v192, v216, v254] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlllr_ok : everyKey (rowOK 4 level4) level5rrlllr = true := by decide +kernel
def level5rrlll : BinaryTree (List W) := .node [v39, v59, v90, v166, v216, v254] level5rrllll level5rrlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlll_ok : everyKey (rowOK 4 level4) level5rrlll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrllll && everyKey (rowOK 4 level4) level5rrlllr) = true
  rw [level5rrllll_ok, level5rrlllr_ok]
  decide +kernel
def level5rrllrl : BinaryTree (List W) := (.node [v39, v59, v102, v144, v216, v254] (.node [v39, v59, v96, v144, v216, v254] (.node [v39, v59, v95, v144, v216, v254] .nil .nil) (.node [v39, v59, v97, v144, v216, v254] .nil .nil)) (.node [v39, v59, v105, v144, v216, v254] (.node [v39, v59, v103, v144, v216, v254] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrllrl_ok : everyKey (rowOK 4 level4) level5rrllrl = true := by decide +kernel
def level5rrllrr : BinaryTree (List W) := (.node [v39, v59, v107, v144, v162, v216] (.node [v39, v59, v107, v140, v216, v254] (.node [v39, v59, v107, v121, v144, v216] .nil .nil) .nil) (.node [v39, v59, v107, v144, v200, v254] (.node [v39, v59, v107, v144, v175, v216] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrllrr_ok : everyKey (rowOK 4 level4) level5rrllrr = true := by decide +kernel
def level5rrllr : BinaryTree (List W) := .node [v39, v59, v106, v144, v216, v254] level5rrllrl level5rrllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrllr_ok : everyKey (rowOK 4 level4) level5rrllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrllrl && everyKey (rowOK 4 level4) level5rrllrr) = true
  rw [level5rrllrl_ok, level5rrllrr_ok]
  decide +kernel
def level5rrll : BinaryTree (List W) := .node [v39, v59, v92, v144, v216, v254] level5rrlll level5rrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrll_ok : everyKey (rowOK 4 level4) level5rrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrlll && everyKey (rowOK 4 level4) level5rrllr) = true
  rw [level5rrlll_ok, level5rrllr_ok]
  decide +kernel
def level5rrlrll : BinaryTree (List W) := (.node [v39, v59, v107, v144, v216, v276] (.node [v39, v59, v107, v144, v216, v268] (.node [v39, v59, v107, v144, v216, v254] .nil .nil) (.node [v39, v59, v107, v144, v216, v275] .nil .nil)) (.node [v39, v59, v107, v144, v216, v288] (.node [v39, v59, v107, v144, v216, v282] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrll_ok : everyKey (rowOK 4 level4) level5rrlrll = true := by decide +kernel
def level5rrlrlr : BinaryTree (List W) := (.node [v39, v59, v115, v144, v216] (.node [v39, v59, v110, v144, v216, v254] (.node [v39, v59, v107, v161, v216, v254] .nil .nil) .nil) (.node [v39, v59, v119, v144, v216, v275] (.node [v39, v59, v115, v144, v216, v254] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrlr_ok : everyKey (rowOK 4 level4) level5rrlrlr = true := by decide +kernel
def level5rrlrl : BinaryTree (List W) := .node [v39, v59, v107, v144, v231, v254] level5rrlrll level5rrlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrl_ok : everyKey (rowOK 4 level4) level5rrlrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrlrll && everyKey (rowOK 4 level4) level5rrlrlr) = true
  rw [level5rrlrll_ok, level5rrlrlr_ok]
  decide +kernel
def level5rrlrrl : BinaryTree (List W) := (.node [v39, v61, v90, v144, v216, v254] (.node [v39, v60, v90, v144, v216, v254] (.node [v39, v59, v144, v191, v216, v254] .nil .nil) .nil) (.node [v39, v63, v90, v144, v216, v254] (.node [v39, v62, v90, v144, v216, v254] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrrl_ok : everyKey (rowOK 4 level4) level5rrlrrl = true := by decide +kernel
def level5rrlrrr : BinaryTree (List W) := (.node [v39, v72, v90, v144, v216, v254] (.node [v39, v70, v90, v144, v216, v254] (.node [v39, v69, v90, v144, v216, v254] .nil .nil) .nil) (.node [v39, v77, v90, v144, v216, v254] (.node [v39, v73, v80, v90, v144, v216] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrrr_ok : everyKey (rowOK 4 level4) level5rrlrrr = true := by decide +kernel
def level5rrlrr : BinaryTree (List W) := .node [v39, v64, v90, v144, v216, v254] level5rrlrrl level5rrlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrr_ok : everyKey (rowOK 4 level4) level5rrlrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrlrrl && everyKey (rowOK 4 level4) level5rrlrrr) = true
  rw [level5rrlrrl_ok, level5rrlrrr_ok]
  decide +kernel
def level5rrlr : BinaryTree (List W) := .node [v39, v59, v144, v175, v216, v275] level5rrlrl level5rrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlr_ok : everyKey (rowOK 4 level4) level5rrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrlrl && everyKey (rowOK 4 level4) level5rrlrr) = true
  rw [level5rrlrl_ok, level5rrlrr_ok]
  decide +kernel
def level5rrl : BinaryTree (List W) := .node [v39, v59, v107, v144, v204, v216] level5rrll level5rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrl_ok : everyKey (rowOK 4 level4) level5rrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrll && everyKey (rowOK 4 level4) level5rrlr) = true
  rw [level5rrll_ok, level5rrlr_ok]
  decide +kernel
def level5rrrlll : BinaryTree (List W) := (.node [v39, v80, v90, v144, v200, v254] (.node [v39, v80, v90, v140, v216, v254] (.node [v39, v80, v90, v121, v144, v216] .nil .nil) (.node [v39, v80, v90, v144, v175, v216] .nil .nil)) (.node [v39, v80, v90, v144, v216, v254] (.node [v39, v80, v90, v144, v204, v216] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrlll_ok : everyKey (rowOK 4 level4) level5rrrlll = true := by decide +kernel
def level5rrrllr : BinaryTree (List W) := (.node [v39, v80, v90, v144, v216, v288] (.node [v39, v80, v90, v144, v216, v282] (.node [v39, v80, v90, v144, v216, v275] .nil .nil) .nil) (.node [v39, v80, v90, v161, v216, v254] (.node [v39, v80, v90, v144, v231, v254] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrllr_ok : everyKey (rowOK 4 level4) level5rrrllr = true := by decide +kernel
def level5rrrll : BinaryTree (List W) := .node [v39, v80, v90, v144, v216, v268] level5rrrlll level5rrrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrll_ok : everyKey (rowOK 4 level4) level5rrrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrlll && everyKey (rowOK 4 level4) level5rrrllr) = true
  rw [level5rrrlll_ok, level5rrrllr_ok]
  decide +kernel
def level5rrrlrl : BinaryTree (List W) := (.node [v42, v59, v90, v144, v216, v254] (.node [v39, v90, v144, v163, v216, v254] (.node [v39, v90, v109, v144, v216, v254] .nil .nil) (.node [v41, v59, v90, v144, v216, v254] .nil .nil)) (.node [v53, v59, v74, v90, v144, v216] (.node [v44, v59, v90, v144, v216, v254] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrlrl_ok : everyKey (rowOK 4 level4) level5rrrlrl = true := by decide +kernel
def level5rrrlrr : BinaryTree (List W) := (.node [v59, v74, v90, v144, v216, v254] (.node [v59, v74, v90, v144, v216] (.node [v59, v67, v90, v144, v216, v254] .nil .nil) .nil) (.node [v59, v80, v90, v144, v231, v254] (.node [v59, v80, v90, v144, v216, v268] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrlrr_ok : everyKey (rowOK 4 level4) level5rrrlrr = true := by decide +kernel
def level5rrrlr : BinaryTree (List W) := .node [v58, v80, v90, v144, v216, v254] level5rrrlrl level5rrrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrlr_ok : everyKey (rowOK 4 level4) level5rrrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrlrl && everyKey (rowOK 4 level4) level5rrrlrr) = true
  rw [level5rrrlrl_ok, level5rrrlrr_ok]
  decide +kernel
def level5rrrl : BinaryTree (List W) := .node [v39, v80, v107, v144, v216, v254] level5rrrll level5rrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrl_ok : everyKey (rowOK 4 level4) level5rrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrll && everyKey (rowOK 4 level4) level5rrrlr) = true
  rw [level5rrrll_ok, level5rrrlr_ok]
  decide +kernel
def level5rrrrll : BinaryTree (List W) := (.node [v59, v90, v107, v144, v231, v254] (.node [v59, v86, v107, v144, v216, v254] (.node [v59, v80, v107, v144, v216, v254] .nil .nil) (.node [v59, v90, v101, v144, v216, v254] .nil .nil)) (.node [v59, v90, v140, v161, v216, v254] (.node [v59, v90, v107, v161, v216, v254] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrll_ok : everyKey (rowOK 4 level4) level5rrrrll = true := by decide +kernel
def level5rrrrlr : BinaryTree (List W) := (.node [v59, v90, v144, v204, v216, v268] (.node [v59, v90, v144, v200, v231, v254] (.node [v59, v90, v144, v161, v231, v254] .nil .nil) .nil) (.node [v59, v90, v161, v231, v254] (.node [v59, v90, v161, v216, v231, v254] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrlr_ok : everyKey (rowOK 4 level4) level5rrrrlr = true := by decide +kernel
def level5rrrrl : BinaryTree (List W) := .node [v59, v90, v144, v155, v216, v254] level5rrrrll level5rrrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrl_ok : everyKey (rowOK 4 level4) level5rrrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrrll && everyKey (rowOK 4 level4) level5rrrrlr) = true
  rw [level5rrrrll_ok, level5rrrrlr_ok]
  decide +kernel
def level5rrrrrl : BinaryTree (List W) := (.node [v59, v107, v161, v216, v254] (.node [v59, v107, v144, v231, v254] (.node [v59, v107, v144, v216, v231, v254] .nil .nil) .nil) (.node [v80, v90, v144, v161, v216, v254] (.node [v80, v90, v107, v144, v216, v254] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrrl_ok : everyKey (rowOK 4 level4) level5rrrrrl = true := by decide +kernel
def level5rrrrrr : BinaryTree (List W) := (.node [v80, v90, v144, v231, v254] (.node [v80, v90, v144, v216, v268] (.node [v80, v90, v144, v216, v254, v268] .nil .nil) .nil) (.node [v80, v107, v144, v216, v254] (.node [v80, v90, v161, v216, v254] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrrr_ok : everyKey (rowOK 4 level4) level5rrrrrr = true := by decide +kernel
def level5rrrrr : BinaryTree (List W) := .node [v80, v90, v144, v216, v231, v254] level5rrrrrl level5rrrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrr_ok : everyKey (rowOK 4 level4) level5rrrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrrrl && everyKey (rowOK 4 level4) level5rrrrrr) = true
  rw [level5rrrrrl_ok, level5rrrrrr_ok]
  decide +kernel
def level5rrrr : BinaryTree (List W) := .node [v59, v107, v144, v161, v216, v254] level5rrrrl level5rrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrr_ok : everyKey (rowOK 4 level4) level5rrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrrl && everyKey (rowOK 4 level4) level5rrrrr) = true
  rw [level5rrrrl_ok, level5rrrrr_ok]
  decide +kernel
def level5rrr : BinaryTree (List W) := .node [v59, v80, v90, v161, v216, v254] level5rrrl level5rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrr_ok : everyKey (rowOK 4 level4) level5rrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrl && everyKey (rowOK 4 level4) level5rrrr) = true
  rw [level5rrrl_ok, level5rrrr_ok]
  decide +kernel
def level5rr : BinaryTree (List W) := .node [v39, v80, v86, v144, v216, v254] level5rrl level5rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rr_ok : everyKey (rowOK 4 level4) level5rr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrl && everyKey (rowOK 4 level4) level5rrr) = true
  rw [level5rrl_ok, level5rrr_ok]
  decide +kernel
def level5r : BinaryTree (List W) := .node [v39, v59, v90, v161, v216, v254] level5rl level5rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5r_ok : everyKey (rowOK 4 level4) level5r = true := by
  change (_ && everyKey (rowOK 4 level4) level5rl && everyKey (rowOK 4 level4) level5rr) = true
  rw [level5rl_ok, level5rr_ok]
  decide +kernel
def level5 : BinaryTree (List W) := .node [v39, v59, v90, v144, v200, v254] level5l level5r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5_ok : everyKey (rowOK 4 level4) level5 = true := by
  change (_ && everyKey (rowOK 4 level4) level5l && everyKey (rowOK 4 level4) level5r) = true
  rw [level5l_ok, level5r_ok]
  decide +kernel
theorem closed5 : Closed 5 level5 := closed_next 4 (by decide) level5 level4 closed4 level5_ok
def level6llll : BinaryTree (List W) := (.node [v6, v39, v59, v90, v144, v216] (.node [v2, v39, v59, v90, v144, v216, v254] (.node [v0, v39, v59, v90, v144, v216, v254] .nil .nil) .nil) (.node [v6, v39, v59, v90, v144, v216, v254] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llll_ok : everyKey (rowOK 5 level5) level6llll = true := by decide +kernel
def level6lllr : BinaryTree (List W) := (.node [v14, v39, v59, v90, v144, v216, v254] (.node [v12, v39, v59, v90, v144, v216, v254] (.node [v10, v39, v59, v90, v144, v216, v254] .nil .nil) .nil) (.node [v15, v39, v59, v90, v144, v216, v254] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllr_ok : everyKey (rowOK 5 level5) level6lllr = true := by decide +kernel
def level6lll : BinaryTree (List W) := .node [v8, v39, v59, v90, v144, v216, v254] level6llll level6lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lll_ok : everyKey (rowOK 5 level5) level6lll = true := by
  change (_ && everyKey (rowOK 5 level5) level6llll && everyKey (rowOK 5 level5) level6lllr) = true
  rw [level6llll_ok, level6lllr_ok]
  decide +kernel
def level6llrl : BinaryTree (List W) := (.node [v23, v39, v59, v90, v144, v216, v254] (.node [v20, v39, v59, v90, v144, v216, v254] (.node [v19, v39, v59, v90, v144, v216, v254] .nil .nil) .nil) (.node [v25, v39, v59, v90, v144, v216, v254] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrl_ok : everyKey (rowOK 5 level5) level6llrl = true := by decide +kernel
def level6llrr : BinaryTree (List W) := (.node [v29, v39, v59, v90, v144, v216, v254] (.node [v29, v39, v59, v90, v144, v216] (.node [v28, v39, v59, v90, v144, v216, v254] .nil .nil) .nil) (.node [v34, v39, v59, v90, v144, v216, v254] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrr_ok : everyKey (rowOK 5 level5) level6llrr = true := by decide +kernel
def level6llr : BinaryTree (List W) := .node [v26, v39, v59, v90, v144, v216, v254] level6llrl level6llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llr_ok : everyKey (rowOK 5 level5) level6llr = true := by
  change (_ && everyKey (rowOK 5 level5) level6llrl && everyKey (rowOK 5 level5) level6llrr) = true
  rw [level6llrl_ok, level6llrr_ok]
  decide +kernel
def level6ll : BinaryTree (List W) := .node [v18, v39, v59, v90, v144, v216, v254] level6lll level6llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6ll_ok : everyKey (rowOK 5 level5) level6ll = true := by
  change (_ && everyKey (rowOK 5 level5) level6lll && everyKey (rowOK 5 level5) level6llr) = true
  rw [level6lll_ok, level6llr_ok]
  decide +kernel
def level6lrll : BinaryTree (List W) := (.node [v38, v39, v59, v90, v144, v216, v254] (.node [v37, v39, v59, v90, v144, v216, v254] (.node [v36, v39, v59, v90, v144, v216, v254] .nil .nil) .nil) (.node [v39, v47, v59, v90, v144, v216, v254] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrll_ok : everyKey (rowOK 5 level5) level6lrll = true := by decide +kernel
def level6lrlr : BinaryTree (List W) := (.node [v39, v53, v59, v90, v144, v216, v254] (.node [v39, v53, v59, v90, v144, v216] (.node [v39, v52, v59, v90, v144, v216, v254] .nil .nil) .nil) (.node [v39, v58, v59, v90, v144, v216, v254] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlr_ok : everyKey (rowOK 5 level5) level6lrlr = true := by decide +kernel
def level6lrl : BinaryTree (List W) := .node [v39, v50, v59, v90, v144, v216, v254] level6lrll level6lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrl_ok : everyKey (rowOK 5 level5) level6lrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrll && everyKey (rowOK 5 level5) level6lrlr) = true
  rw [level6lrll_ok, level6lrlr_ok]
  decide +kernel
def level6lrrl : BinaryTree (List W) := (.node [v39, v59, v82, v90, v144, v216, v254] (.node [v39, v59, v81, v90, v144, v216, v254] (.node [v39, v59, v80, v90, v144, v216, v254] .nil .nil) .nil) (.node [v39, v59, v84, v90, v144, v216, v254] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrl_ok : everyKey (rowOK 5 level5) level6lrrl = true := by decide +kernel
def level6lrrr : BinaryTree (List W) := (.node [v39, v59, v90, v107, v144, v216, v254] (.node [v39, v59, v88, v90, v144, v216, v254] (.node [v39, v59, v86, v144, v216, v254] .nil .nil) .nil) (.node [v39, v59, v90, v119, v144, v216, v254] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrr_ok : everyKey (rowOK 5 level5) level6lrrr = true := by decide +kernel
def level6lrr : BinaryTree (List W) := .node [v39, v59, v86, v90, v144, v216, v254] level6lrrl level6lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrr_ok : everyKey (rowOK 5 level5) level6lrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrrl && everyKey (rowOK 5 level5) level6lrrr) = true
  rw [level6lrrl_ok, level6lrrr_ok]
  decide +kernel
def level6lr : BinaryTree (List W) := .node [v39, v58, v90, v144, v216, v254] level6lrl level6lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lr_ok : everyKey (rowOK 5 level5) level6lr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrl && everyKey (rowOK 5 level5) level6lrr) = true
  rw [level6lrl_ok, level6lrr_ok]
  decide +kernel
def level6l : BinaryTree (List W) := .node [v35, v39, v59, v90, v144, v216, v254] level6ll level6lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6l_ok : everyKey (rowOK 5 level5) level6l = true := by
  change (_ && everyKey (rowOK 5 level5) level6ll && everyKey (rowOK 5 level5) level6lr) = true
  rw [level6ll_ok, level6lr_ok]
  decide +kernel
def level6rlll : BinaryTree (List W) := (.node [v39, v59, v90, v135, v144, v216, v254] (.node [v39, v59, v90, v121, v144, v216, v254] (.node [v39, v59, v90, v121, v144, v216] .nil .nil) .nil) (.node [v39, v59, v90, v136, v144, v216, v254] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlll_ok : everyKey (rowOK 5 level5) level6rlll = true := by decide +kernel
def level6rllr : BinaryTree (List W) := (.node [v39, v59, v90, v142, v144, v216, v254] (.node [v39, v59, v90, v140, v216, v254] (.node [v39, v59, v90, v140, v144, v216, v254] .nil .nil) .nil) (.node [v39, v59, v90, v144, v161, v216, v254] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllr_ok : everyKey (rowOK 5 level5) level6rllr = true := by decide +kernel
def level6rll : BinaryTree (List W) := .node [v39, v59, v90, v138, v144, v216, v254] level6rlll level6rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rll_ok : everyKey (rowOK 5 level5) level6rll = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlll && everyKey (rowOK 5 level5) level6rllr) = true
  rw [level6rlll_ok, level6rllr_ok]
  decide +kernel
def level6rlrl : BinaryTree (List W) := (.node [v39, v59, v90, v144, v175, v216, v254] (.node [v39, v59, v90, v144, v175, v216] (.node [v39, v59, v90, v144, v174, v216, v254] .nil .nil) .nil) (.node [v39, v59, v90, v144, v193, v216, v254] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrl_ok : everyKey (rowOK 5 level5) level6rlrl = true := by decide +kernel
def level6rlrr : BinaryTree (List W) := (.node [v39, v59, v90, v144, v200, v254] (.node [v39, v59, v90, v144, v200, v216, v254] (.node [v39, v59, v90, v144, v197, v216, v254] .nil .nil) .nil) (.node [v39, v59, v90, v144, v204, v216] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrr_ok : everyKey (rowOK 5 level5) level6rlrr = true := by decide +kernel
def level6rlr : BinaryTree (List W) := .node [v39, v59, v90, v144, v194, v216, v254] level6rlrl level6rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlr_ok : everyKey (rowOK 5 level5) level6rlr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlrl && everyKey (rowOK 5 level5) level6rlrr) = true
  rw [level6rlrl_ok, level6rlrr_ok]
  decide +kernel
def level6rl : BinaryTree (List W) := .node [v39, v59, v90, v144, v173, v216, v254] level6rll level6rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rl_ok : everyKey (rowOK 5 level5) level6rl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rll && everyKey (rowOK 5 level5) level6rlr) = true
  rw [level6rll_ok, level6rlr_ok]
  decide +kernel
def level6rrll : BinaryTree (List W) := (.node [v39, v59, v90, v144, v216, v239, v254] (.node [v39, v59, v90, v144, v216, v231, v254] (.node [v39, v59, v90, v144, v214, v216, v254] .nil .nil) .nil) (.node [v39, v59, v90, v144, v216, v246, v254] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrll_ok : everyKey (rowOK 5 level5) level6rrll = true := by decide +kernel
def level6rrlr : BinaryTree (List W) := (.node [v39, v59, v90, v144, v216, v254, v275] (.node [v39, v59, v90, v144, v216, v254, v270] (.node [v39, v59, v90, v144, v216, v254, v268] .nil .nil) .nil) (.node [v39, v59, v90, v144, v216, v254, v282] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlr_ok : everyKey (rowOK 5 level5) level6rrlr = true := by decide +kernel
def level6rrl : BinaryTree (List W) := .node [v39, v59, v90, v144, v216, v251, v254] level6rrll level6rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrl_ok : everyKey (rowOK 5 level5) level6rrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrll && everyKey (rowOK 5 level5) level6rrlr) = true
  rw [level6rrll_ok, level6rrlr_ok]
  decide +kernel
def level6rrrl : BinaryTree (List W) := (.node [v39, v59, v90, v144, v216, v282] (.node [v39, v59, v90, v144, v216, v275] (.node [v39, v59, v90, v144, v216, v268] .nil .nil) .nil) (.node [v39, v59, v90, v144, v216, v288] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrl_ok : everyKey (rowOK 5 level5) level6rrrl = true := by decide +kernel
def level6rrrr : BinaryTree (List W) := (.node [v39, v59, v107, v144, v216, v254] (.node [v39, v59, v90, v161, v216, v254] .nil .nil) (.node [v39, v80, v90, v144, v216, v254] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrr_ok : everyKey (rowOK 5 level5) level6rrrr = true := by decide +kernel
def level6rrr : BinaryTree (List W) := .node [v39, v59, v90, v144, v231, v254] level6rrrl level6rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrr_ok : everyKey (rowOK 5 level5) level6rrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrrl && everyKey (rowOK 5 level5) level6rrrr) = true
  rw [level6rrrl_ok, level6rrrr_ok]
  decide +kernel
def level6rr : BinaryTree (List W) := .node [v39, v59, v90, v144, v216, v254, v288] level6rrl level6rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rr_ok : everyKey (rowOK 5 level5) level6rr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrl && everyKey (rowOK 5 level5) level6rrr) = true
  rw [level6rrl_ok, level6rrr_ok]
  decide +kernel
def level6r : BinaryTree (List W) := .node [v39, v59, v90, v144, v204, v216, v254] level6rl level6rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6r_ok : everyKey (rowOK 5 level5) level6r = true := by
  change (_ && everyKey (rowOK 5 level5) level6rl && everyKey (rowOK 5 level5) level6rr) = true
  rw [level6rl_ok, level6rr_ok]
  decide +kernel
def level6 : BinaryTree (List W) := .node [v39, v59, v90, v120, v144, v216, v254] level6l level6r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6_ok : everyKey (rowOK 5 level5) level6 = true := by
  change (_ && everyKey (rowOK 5 level5) level6l && everyKey (rowOK 5 level5) level6r) = true
  rw [level6l_ok, level6r_ok]
  decide +kernel
theorem closed6 : Closed 6 level6 := closed_next 5 (by decide) level6 level5 closed5 level6_ok
def level7 : BinaryTree (List W) := (.node [v39, v59, v90, v144, v216, v254] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7_ok : everyKey (rowOK 6 level6) level7 = true := by decide +kernel
theorem closed7 : Closed 7 level7 := closed_next 6 (by decide) level7 level6 closed6 level7_ok

theorem lower : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z 7 ins.toFinset :=
  @no_build 7 level7 ins (by decide +kernel) (by decide) closed7 (by decide +kernel)
def witness : List Gate := [⟨.or,[2,5]⟩,⟨.and,[1,6]⟩,⟨.or,[0,7]⟩,⟨.or,[1,2]⟩,⟨.or,[3,4]⟩,⟨.and,[3,4]⟩,⟨.and,[9,10]⟩,⟨.or,[8,12]⟩,⟨.or,[11,13]⟩]
theorem upper : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 9 ∧ ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xfffefeeefffefeea (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact ⟨witness,14,by simp [witness],rfl,by decide +kernel⟩
end PEqualNP.Outside.L_meta_13201_aux

open PEqualNP.Outside.L_meta_13201_aux in
theorem PEqualNP.Outside.L_meta_13201 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4294901486 * 2 ^ 32 + 4294901482) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4294901486 * 2 ^ 32 + 4294901482) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  have code : 4294901486 * 2 ^ 32 + 4294901482 = 0xfffefeeefffefeea := by decide
  simp only [code] at h ⊢
  obtain ⟨C,legal,size,computes⟩ := h
  obtain ⟨gs,o,mono,bound,ev⟩ := replace 0xfffefeeefffefeea 9 ins (by decide +kernel) sampled rfl lower upper C.gates C.output legal computes
  exact ⟨⟨gs,o⟩,mono,bound.trans size,ev⟩
