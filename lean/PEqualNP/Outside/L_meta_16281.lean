import PEqualNP.Defs

-- The live-wire search and its circuit compiler follow the merged L-meta-8639.
namespace PEqualNP.Outside.L_meta_16281_aux

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
def v1 : W := 0x401010401472
def v2 : W := 0x1000811401452
def v3 : W := 0x1410800001662
def v4 : W := 0x141101140026a
def v5 : W := 0x200000242481524000024
def v6 : W := 0x410040005040841224000
def v7 : W := 0x510040021000011400042
def v8 : W := 0x510060020000000000000
def v9 : W := 0x532000104000051600010
def v10 : W := 0x48080a000109448080a4000
def v11 : W := 0x8408080000290c4280c8000
def v12 : W := 0x84080a00000000000000000
def v13 : W := 0x201004001000020211412991
def v14 : W := 0x2010040010000a1114400894
def v15 : W := 0x2010040010000a1315412995
def v16 : W := 0x20100400100800131540210c
def v17 : W := 0x20100400100802131541299d
def v18 : W := 0x2010040010080a0304112985
def v19 : W := 0x2010040010080a0315512995
def v20 : W := 0x2010040010080a1314512995
def v21 : W := 0x2010040010080a131551298d
def v22 : W := 0x201104001420000010400042
def v23 : W := 0x201126001900020010400890
def v24 : W := 0x201204001640401114400066
def v25 : W := 0x201244001640000104000004
def v26 : W := 0x201514021000000211402100
def v27 : W := 0x40000040400014880806d400
def v28 : W := 0x400000444021040800025442
def v29 : W := 0x400000644020040000024000
def v30 : W := 0x40002240410020a002049410
def v31 : W := 0x400022404104040840225410
def v32 : W := 0x40002240410434a0caa6c000
def v33 : W := 0x400122404120000010401452
def v34 : W := 0x400122404920000000000000
def v35 : W := 0x400532444124040040224000
def v36 : W := 0x400532444125040851625452
def v37 : W := 0x484080e0400014800806c000
def v38 : W := 0x601126405520000010401452
def v39 : W := 0x601126405920020010400890
def v40 : W := 0x601126405920020010401cd2
def v41 : W := 0x601126405d20000010400042
def v42 : W := 0x60126640574020a106049414
def v43 : W := 0x8200220009002a2002000890
def v44 : W := 0x8a400000000228a422048000
def v45 : W := 0x8a4040000800000000000000
def v46 : W := 0x8a4240000242080524000004
def v47 : W := 0x8a488180000030a08a848000
def v48 : W := 0x8a4881800002884420180000
def v49 : W := 0xa210440018000a0104000884
def v50 : W := 0xa210440018080a0304112985
def v51 : W := 0xca402240490020a002048000
def v52 : W := 0xea5226405f4060b116448066
def v53 : W := 0x1000000042001150808024200
def v54 : W := 0x1000080a42000140008024000
def v55 : W := 0x1000418042081010001000208
def v56 : W := 0x10004180420841400c8a24000
def v57 : W := 0x2010122000100203012400010
def v58 : W := 0x2010518000080001011400008
def v59 : W := 0x201053a0001842020c2a00000
def v60 : W := 0x2211144001000001114400004
def v61 : W := 0x221153e00118c2a23c6b12985
def v62 : W := 0x2830040000000283106000004
def v63 : W := 0x2830162000900202002000000
def v64 : W := 0x2a311660019002a3116400894
def v65 : W := 0x2a311660019002a3317412995
def v66 : W := 0x2a311660019082a3316512995
def v67 : W := 0x2e311664059002ab116449c94
def v68 : W := 0x2e311664059202a3116400894
def v69 : W := 0x2e311664059202a3116401cd6
def v70 : W := 0x2eb51664059002ab116448894
def v71 : W := 0x4000200080660400000000062
def v72 : W := 0x4084200080242408420048020
def v73 : W := 0x4400000484020408000049462
def v74 : W := 0x4484000484020008000048000
def v75 : W := 0x5000000082000518008048220
def v76 : W := 0x50000000c2020000000000000
def v77 : W := 0x50000000c2021410000000262
def v78 : W := 0x5084080882000108008048000
def v79 : W := 0x54000004c602014800806c000
def v80 : W := 0x54000004c602155880806d662
def v81 : W := 0x54005324c612555885966d672
def v82 : W := 0x5484080ec602014800806c000
def v83 : W := 0x5484080ec602155880806d662
def v84 : W := 0x601000008000060b002048020
def v85 : W := 0x6010100080020401010400062
def v86 : W := 0x6010140080020000000000000
def v87 : W := 0x6010240080240401104000024
def v88 : W := 0x6211344081660401114400066
def v89 : W := 0x641012248412020a002048000
def v90 : W := 0x641012248412060b012449472
def v91 : W := 0x64105324c412564b85366d472
def v92 : W := 0x66111264851206ab116449cf6
def v93 : W := 0x661112648552060b012449472
def v94 : W := 0x661112648592062b012449cf2
def v95 : W := 0x661116648512060b116449476
def v96 : W := 0x661132648576060b116449476
def v97 : W := 0x6611366485760401114401476
def v98 : W := 0x661136648576060b116448066
def v99 : W := 0x661136648576060b116449476
def v100 : W := 0x6611366485f60401114400066
def v101 : W := 0x68b404008000020a002048000
def v102 : W := 0x68b424008024268b526048024
def v103 : W := 0x68b42c0880242f8f52e0c8024
def v104 : W := 0x68b4ac1880242e8f5261c8024
def v105 : W := 0x6a31366081f606a31164008f6
def v106 : W := 0x6ab534408166268b536448066
def v107 : W := 0x6ab5366081b426ab5364488b4
def v108 : W := 0x6cb416248492020a002048000
def v109 : W := 0x6cb416248492060b012449472
def v110 : W := 0x6cb436248436268b536449476
def v111 : W := 0x6cb4362484b6268b526048024
def v112 : W := 0x6e311664859202ab116448894
def v113 : W := 0x6e311664859206ab116449cf6
def v114 : W := 0x6e31366485f606ab116449cf6
def v115 : W := 0x6eb516648592020b116448004
def v116 : W := 0x6eb516648592022a012448890
def v117 : W := 0x6eb51664859202aa106048884
def v118 : W := 0x6eb51664859202ab116448894
def v119 : W := 0x6eb51664859206ab116449cf6
def v120 : W := 0x6eb5166485d2020a012448042
def v121 : W := 0x6eb536648576268b536449476
def v122 : W := 0x6eb5366485b626ab5364488b4
def v123 : W := 0x6eb5366485b626ab536449cf6
def v124 : W := 0x6eb5366485f6020a106048004
def v125 : W := 0x6eb5366485f6060b116448066
def v126 : W := 0x6eb5366485f6060b116449476
def v127 : W := 0x6eb5366485f606ab1164488f6
def v128 : W := 0x6eb5366485f6268b536448066
def v129 : W := 0x701000808208030a08a848000
def v130 : W := 0x7010008082080411000000228
def v131 : W := 0x70105180c20a0000000000000
def v132 : W := 0x70105180c20a141101140026a
def v133 : W := 0x721175c0c36e141111540026e
def v134 : W := 0x74101224c612175b81a46d672
def v135 : W := 0x74105184c60a155981946d66a
def v136 : W := 0x741053a4c61a161b01344967a
def v137 : W := 0x741053a4c61a434a0caa6c000
def v138 : W := 0x741053a4c61a474b0dae6d472
def v139 : W := 0x741053a4c61a534a8dbe6d452
def v140 : W := 0x741053a4c61a545185162567a
def v141 : W := 0x741053a4c61a575a8caa6d662
def v142 : W := 0x741053a4c61a575a8dbe6d672
def v143 : W := 0x741053a4c61a575b0dbe6c26a
def v144 : W := 0x741053a4c61a575b8dae6d672
def v145 : W := 0x741053a4c61a575b8dbe6d66a
def v146 : W := 0x741053a4c61a575b8dbe6d67a
def v147 : W := 0x74945baec61a434a0caa6c000
def v148 : W := 0x761153e4c71ac3ea3ceb7e985
def v149 : W := 0x761153e4c71ad7fabceb7ffe7
def v150 : W := 0x76955beec71ac3ea3ceb7e985
def v151 : W := 0x7cb41e2ec692034a00a06c000
def v152 : W := 0x7cb457a4c69a434a0caa6c000
def v153 : W := 0x8100200000242c14420080220
def v154 : W := 0x810020000024841110400022c
def v155 : W := 0x810020000024a884524180004
def v156 : W := 0x8184280800242804420080000
def v157 : W := 0x9100080802000914008080200
def v158 : W := 0xd100200082240410000000220
def v159 : W := 0xd184280882242d1c4280c8220
def v160 : W := 0xd584280cc6263d5cc280ed662
def v161 : W := 0xd584280ec6262d5c4280ec220
def v162 : W := 0xe9b4240080242e9f5260c8224
def v163 : W := 0xe9b424008024ae8f5261c8024
def v164 : W := 0xe9b42c0880242e8f5260c8024
def v165 : W := 0xf1102080822cab8e5ae9c8004
def v166 : W := 0xf9b42c0882242f9f52e0c8224
def v167 : W := 0x10002000040421000000000042
def v168 : W := 0x10002410060001000201002100
def v169 : W := 0x10002410060005040a41226100
def v170 : W := 0x1004a000000011000a01012101
def v171 : W := 0x1004a000240011040800024000
def v172 : W := 0x1004a410040015040a41236101
def v173 : W := 0x10203004001401000211402142
def v174 : W := 0x10203004021400000200002100
def v175 : W := 0x10203514061421000211402142
def v176 : W := 0x10603536465525040a51627552
def v177 : W := 0x12a7b1662419112e3916424894
def v178 : W := 0x162137540e1661401315402166
def v179 : W := 0x1721351c0e34a141121140236a
def v180 : W := 0x18102000000009010201002308
def v181 : W := 0x18102200000640000000000000
def v182 : W := 0x18102200000641410000000262
def v183 : W := 0x1814a000000011814800080200
def v184 : W := 0x1814a000000018804200192101
def v185 : W := 0x1814a080a00010804000080000
def v186 : W := 0x18303204001648000304002104
def v187 : W := 0x1830320400164941131540236e
def v188 : W := 0x1830371406166941131540236e
def v189 : W := 0x19102000042001010000000200
def v190 : W := 0x1914a080a420119548080a4200
def v191 : W := 0x1914a41804209c9442c8bb6101
def v192 : W := 0x1bb7b1e6a43911bf791e4a4a94
def v193 : W := 0x1d1022000c2661410000000262
def v194 : W := 0x1d14a280ac2671d548080a4262
def v195 : W := 0x1d1862808c2663d1c4280c8262
def v196 : W := 0x1d1ce280ac2253d5cc280ec220
def v197 : W := 0x1d3032040c366941131540236e
def v198 : W := 0x1d3037140e3661410211402362
def v199 : W := 0x1d3cf3a6ac3b53d7cc384ecab0
def v200 : W := 0x1d5022004c666155880806d662
def v201 : W := 0x1d54a080ec6031d5c8080ed662
def v202 : W := 0x1d586280ec666155800806c262
def v203 : W := 0x1d5ce080ec603195c8080ec200
def v204 : W := 0x1e31334408166941131540236e
def v205 : W := 0x1ef7b1e6e85930eaf1164c9cf6
def v206 : W := 0x1efff166485931abf9164c8a94
def v207 : W := 0x1f1127180c26e141101140026a
def v208 : W := 0x1f3133440c3661411114400266
def v209 : W := 0x1f31371c0c36e8000304002104
def v210 : W := 0x1f31371c0c36e941131540236e
def v211 : W := 0x1f31371c0e36e141121140236a
def v212 : W := 0x1f31371c0e36e941131540236e
def v213 : W := 0x1f31375c0c36e141111540026e
def v214 : W := 0x1f31375c0c36e941131540236e
def v215 : W := 0x200000000180020a0420001c90
def v216 : W := 0x20000200018642400420001462
def v217 : W := 0x20048000018010020800011c91
def v218 : W := 0x20048000018012804c20081400
def v219 : W := 0x200480000180128a4420190881
def v220 : W := 0x20084200018642000420000000
def v221 : W := 0x200cc080a18012804420080000
def v222 : W := 0x20201004019400020010401cd2
def v223 : W := 0x20201004019c00020000000880
def v224 : W := 0x202012040196420a0524000884
def v225 : W := 0x202012040196424a1534401cf6
def v226 : W := 0x2040000041c420000000001442
def v227 : W := 0x2040002241c900020000001c90
def v228 : W := 0x2044800061c010040800025400
def v229 : W := 0x2044802241c116bee4eabfc881
def v230 : W := 0x2048400041c002008420049400
def v231 : W := 0x204cc080e1c01294cc280ed400
def v232 : W := 0x2060102641dd00020000001c90
def v233 : W := 0x2060102641dd00020010401cd2
def v234 : W := 0x2060112641d520020010401cd2
def v235 : W := 0x2060112641d900020010401c90
def v236 : W := 0x2060112641dd20020000000880
def v237 : W := 0x2060112641dd20020010401cd2
def v238 : W := 0x2060112641dd200a1114401cd6
def v239 : W := 0x2060112641dd2022a012449cd2
def v240 : W := 0x2060112641dd20421010401cf2
def v241 : W := 0x2060112641dd21020811401cd2
def v242 : W := 0x2060112641dd220a0430401cd2
def v243 : W := 0x2060122641d7426ab536449cf6
def v244 : W := 0x2060122641df424a1534401cf6
def v245 : W := 0x2060132641d7624a1534401cf6
def v246 : W := 0x2060132641df60421114401cf6
def v247 : W := 0x2060132641df620a0534401cd6
def v248 : W := 0x2060132641df62420430401cf2
def v249 : W := 0x2060132641df624a1534401cf6
def v250 : W := 0x2060136641df60020114401cd6
def v251 : W := 0x2060153645dd21020011401cd2
def v252 : W := 0x2060153645dd25060851625cd2
def v253 : W := 0x2060153647dd20020010401cd2
def v254 : W := 0x2064912641dd30020010411cd3
def v255 : W := 0x2064912641dd30020810401cd2
def v256 : W := 0x2064912641dd30020810411cd3
def v257 : W := 0x2064912641dd31020811411cd3
def v258 : W := 0x2064912661dd30020010401cd2
def v259 : W := 0x2064912661dd30060810425cd2
def v260 : W := 0x2064953647dd30020810411cd3
def v261 : W := 0x2068512641dd22028430449cd2
def v262 : W := 0x2068532641df62020430401cd2
def v263 : W := 0x208a40000188020a0420000880
def v264 : W := 0x20aa5244019e420a0524000884
def v265 : W := 0x20aa5244019e424a1534401cf6
def v266 : W := 0x20ca402241c9022aa422049c90
def v267 : W := 0x20cec0a2e1c912beec2a0edc90
def v268 : W := 0x20e2112641dd202a2012401cd2
def v269 : W := 0x20e2116641dd200a0114401cd6
def v270 : W := 0x20ea502641d9022ab536449c94
def v271 : W := 0x20ea502641dd022aa422049c90
def v272 : W := 0x20ea502641dd022aa432449cd2
def v273 : W := 0x20ea506641d9022aa526049c94
def v274 : W := 0x20ea512641d9022aa432449c90
def v275 : W := 0x20ea512641dd2022a012449cd2
def v276 : W := 0x20ea512641dd220a0430401cd2
def v277 : W := 0x20ea512641dd222aa432449cd2
def v278 : W := 0x20ea516641dd20020010401cd2
def v279 : W := 0x20ea522641df422aa526049c94
def v280 : W := 0x20ea522641df426ab536449cf6
def v281 : W := 0x20ea526641df420a0524001c94
def v282 : W := 0x20ea526641df422aa526048884
def v283 : W := 0x20ea526641df422aa526049c94
def v284 : W := 0x20ea526641df426ab536449cf6
def v285 : W := 0x20ea532641df626ab536449cf6
def v286 : W := 0x20ea536641df620a0524000884
def v287 : W := 0x20ea536641df620a0534401cd6
def v288 : W := 0x20ea536641df622aa536449cd6
def v289 : W := 0x20ea536641df624a1534401cf6
def v290 : W := 0x2261112641dd20223012401cd2
def v291 : W := 0x2261116641dd20021114401cd6
def v292 : W := 0x22a31366019f426a3536401cf6
def v293 : W := 0x22ab5366019f422a3536400894
def v294 : W := 0x22e3116641d9002a3116401c94
def v295 : W := 0x22e3116641dd20222012401cd2
def v296 : W := 0x22e3116641dd202a3116401cd6
def v297 : W := 0x22e3136641df626a3536401cf6
def v298 : W := 0x22eb516641d9022ab536449c94
def v299 : W := 0x22eb516641dd222ab536449cd6
def v300 : W := 0x22eb536641df422ab536449c94
def v301 : W := 0x22eb536641df426ab536449cf6
def v302 : W := 0x22eb536641df622a3536401cd6
def v303 : W := 0x2448420049c662408420049462
def v304 : W := 0x244cc280e9c672d4cc280ed462
def v305 : W := 0x2460112649dd20428010449cf2
def v306 : W := 0x2460132649df60420010401cf2
def v307 : W := 0x2468512649dd20028010449cd2
def v308 : W := 0x2468520449d6624a9534449cf6
def v309 : W := 0x2468532649df62428430449cf2
def v310 : W := 0x2468532649df624a9534449cf6
def v311 : W := 0x24ca422249cf626aa422049cf2
def v312 : W := 0x24ea522649df626ab536449cf6
def v313 : W := 0x24ea524449de624a8524049ce6
def v314 : W := 0x24ea526649df626aa526049cf6
def v315 : W := 0x24ea532649df626aa432449cf2
def v316 : W := 0x24ea536649df624a8534449cf6
def v317 : W := 0x254842004de663558c2806d662
def v318 : W := 0x25484280ede66254842806d462
def v319 : W := 0x254cc080ede03294cc280ed400
def v320 : W := 0x254cc080ede033d5cc280ed662
def v321 : W := 0x262113440996624a1534401cf6
def v322 : W := 0x2649432249c76260b432449472
def v323 : W := 0x2661112649d52062b012449cf2
def v324 : W := 0x2661112649dd2022a012449cd2
def v325 : W := 0x2661112649dd20421010401cf2
def v326 : W := 0x2661112649dd2062b012449cf2
def v327 : W := 0x2661116649dd20020010401cd2
def v328 : W := 0x2661132649d7622aa526048884
def v329 : W := 0x2661132649d7626ab536449cf6
def v330 : W := 0x2661132649df626ab536449cf6
def v331 : W := 0x2661136649d7626ab536449cf6
def v332 : W := 0x2661136649df60421114401cf6
def v333 : W := 0x2661136649df6062b116449cf6
def v334 : W := 0x2661136649df624a1534401cf6
def v335 : W := 0x2669532649d7626ab536449cf6
def v336 : W := 0x2669532649df6262b432449cf2
def v337 : W := 0x2669534449d662409534449466
def v338 : W := 0x2669536649d76260b536449476
def v339 : W := 0x2669536649df62429534449cf6
def v340 : W := 0x26ab52440996426ab536449cf6
def v341 : W := 0x26ab5244099e426ab5260488a4
def v342 : W := 0x26ab5344099e624a15344008e6
def v343 : W := 0x26cb412249c9226ab432449cf2
def v344 : W := 0x26cb416249c9222aa422049c90
def v345 : W := 0x26cb424049c66268b526049466
def v346 : W := 0x26cb426249cb426ab526049cb4
def v347 : W := 0x26cb436249cf6260a422049462
def v348 : W := 0x26e3116649dd206ab116449cf6
def v349 : W := 0x26e3136649df606a3116401cf6
def v350 : W := 0x26e3136649df626ab536449cf6
def v351 : W := 0x26eb512649dd226ab432449cf2
def v352 : W := 0x26eb516649d9222ab536449c94
def v353 : W := 0x26eb516649d9226ab536449cf6
def v354 : W := 0x26eb516649dd2022a002048880
def v355 : W := 0x26eb516649dd2022a012449cd2
def v356 : W := 0x26eb516649dd202ab116449cd6
def v357 : W := 0x26eb516649dd2062b012449cf2
def v358 : W := 0x26eb516649dd222aa432449cd2
def v359 : W := 0x26eb526649df426ab526049cb4
def v360 : W := 0x26eb526649df426ab536449cf6
def v361 : W := 0x26eb532649df626ab536449cf6
def v362 : W := 0x26eb536649d7626ab536449cf6
def v363 : W := 0x26eb536649db426ab536449cb4
def v364 : W := 0x26eb536649df6062b116449cf6
def v365 : W := 0x26eb536649df622aa526048884
def v366 : W := 0x26eb536649df622aa526049c94
def v367 : W := 0x26eb536649df622aa536449cd6
def v368 : W := 0x26eb536649df622ab536448894
def v369 : W := 0x26eb536649df624a1534401cf6
def v370 : W := 0x26eb536649df6260b536449466
def v371 : W := 0x26eb536649df6262a432449cf2
def v372 : W := 0x26eb536649df626aa526049ce6
def v373 : W := 0x26eb536649df626ab5260488a4
def v374 : W := 0x26eb536649df626ab5364488e6
def v375 : W := 0x26eb536649df626ab536449cf6
def v376 : W := 0x26eb536649df636abd37449cf6
def v377 : W := 0x26eb536649df636bb537449efe
def v378 : W := 0x26eb536649df636bbd36449ef6
def v379 : W := 0x26eb53e6c9df62faf53e4c9cf6
def v380 : W := 0x26eb53e6e9df626ab536449cf6
def v381 : W := 0x26eb57764ddf636ab537449cf6
def v382 : W := 0x26eb57764ddf676ebd7766dcf6
def v383 : W := 0x26eb57764fdf626ab536449cf6
def v384 : W := 0x26eb577e49dfe26ab537449cfe
def v385 : W := 0x26eb5be7c9df627ab5bec49cf6
def v386 : W := 0x26eb5be7c9df62eaf5365c9cf6
def v387 : W := 0x26efd36649df726abd36459cf7
def v388 : W := 0x26efd36649df72eaf5365d9cf7
def v389 : W := 0x26efd36649df72eafd364c9cf6
def v390 : W := 0x26efd3e6e9df72eaf5364c9cf6
def v391 : W := 0x26efd3e6e9df72fefd3e4edcf6
def v392 : W := 0x2761153e4dfda1431011401efa
def v393 : W := 0x27eb536649ff627bb53e449ef6
def v394 : W := 0x27eb53664dff626ab536449cf6
def v395 : W := 0x27eb53664dff636bb536449ef6
def v396 : W := 0x27eb53664dff637fbd3e46def6
def v397 : W := 0x27eb536e49ffe26bb536449efe
def v398 : W := 0x27eb536e49ffe27ab5bec49cf6
def v399 : W := 0x27eb53e6c9ff627ab53e449cf6
def v400 : W := 0x27eb53e6edff627eb53e46dcf6
def v401 : W := 0x27eb577e4dffe26ab536449cf6
def v402 : W := 0x27eb577e4dffe36bb537449efe
def v403 : W := 0x27eb577e4dffe67eb5fee6dcf6
def v404 : W := 0x297011a6c1fd20934018481ed2
def v405 : W := 0x2d584280c9e662d1c4280c9662
def v406 : W := 0x2d5cc280e9e252d5cc280ed620
def v407 : W := 0x2d7853a6c9ff62d3c4384c9ef2
def v408 : W := 0x2efb536649df62ebf5364c9ef6
def v409 : W := 0x2efb536649df6a6bb536449efe
def v410 : W := 0x2efb536649df6aeaf5365c9cf6
def v411 : W := 0x2efb53e6c9df62eaf5364c9cf6
def v412 : W := 0x2ffb536649ff626bb536449ef6
def v413 : W := 0x2ffb53e6c9ff62fbf53e4c9ef6
def v414 : W := 0x3004a000018411000800001442
def v415 : W := 0x3004a000218410000000000000
def v416 : W := 0x3004a200018653400c20001462
def v417 : W := 0x300ce200218652000420000000
def v418 : W := 0x3024b004019410020200012981
def v419 : W := 0x3024b004019411020a11413dd3
def v420 : W := 0x3024b2040196534a1f35413df7
def v421 : W := 0x3024b514079431020a11413dd3
def v422 : W := 0x3044a00065c431040800025442
def v423 : W := 0x3044a20065c673440c20025462
def v424 : W := 0x3044a53265c535040851625452
def v425 : W := 0x304ce080e5c43394cc280ed442
def v426 : W := 0x304ce20065c673040c20025442
def v427 : W := 0x3060312645dd21020010401cd2
def v428 : W := 0x3060353647dd21020211403dd2
def v429 : W := 0x3064b00465d431060a11437dd3
def v430 : W := 0x3064b02641d515060a51637dd3
def v431 : W := 0x3064b02641dd11020a11413dd3
def v432 : W := 0x3064b12641d531020a11413dd3
def v433 : W := 0x3064b12641dd30020010401cd2
def v434 : W := 0x3064b12641dd30020210413dd3
def v435 : W := 0x3064b12641dd31020810401cd2
def v436 : W := 0x3064b12641dd31020810411cd3
def v437 : W := 0x3064b12641dd31020811401cd2
def v438 : W := 0x3064b12641dd31020a11413dd3
def v439 : W := 0x3064b12645dd31020810401cd2
def v440 : W := 0x3064b12661dd30020010401cd2
def v441 : W := 0x3064b12661dd31020810401cd2
def v442 : W := 0x3064b12665dd31020010401cd2
def v443 : W := 0x3064b12665dd31060810425cd2
def v444 : W := 0x3064b12665dd31060a11437dd3
def v445 : W := 0x3064b51467d431040a11427542
def v446 : W := 0x3064b53645d534060240236981
def v447 : W := 0x3064b53645d535060a51637dd3
def v448 : W := 0x3064b53645dd35060a51637dd3
def v449 : W := 0x3064b53647d535060a51637dd3
def v450 : W := 0x3064b53647dd31020a11413dd3
def v451 : W := 0x3064b53665d535060a51637dd3
def v452 : W := 0x3064b53665dd35060851625cd2
def v453 : W := 0x3064b53667d535040a51627552
def v454 : W := 0x3064b53667dd31060a11427dd2
def v455 : W := 0x32c7a04065c4312c3906025446
def v456 : W := 0x3444a2006dc671440800025462
def v457 : W := 0x344ce20049c673408c20049462
def v458 : W := 0x344ce20069c672408420049462
def v459 : W := 0x344ce2006dc673448c2006d462
def v460 : W := 0x344ce280edc673d4cc280ed462
def v461 : W := 0x3544a0006de43155880806d662
def v462 : W := 0x354ce080ede43114880806d442
def v463 : W := 0x354ce2006de673558c2806d662
def v464 : W := 0x354ce280ede673548c2806d462
def v465 : W := 0x364de7326dc77764bc7366d472
def v466 : W := 0x36eb73664ddf636ab536449cf6
def v467 : W := 0x36eb77764fdf636ab73744bdf6
def v468 : W := 0x36eff36649df736abd36449cf6
def v469 : W := 0x36eff36649df736abf3745bdf7
def v470 : W := 0x36eff36669df726ab536449cf6
def v471 : W := 0x36eff3666ddf736ebd3646dcf6
def v472 : W := 0x3814a200018651410800001662
def v473 : W := 0x3814a200018652804420080000
def v474 : W := 0x3814a200018652804c20081400
def v475 : W := 0x3814a200018652c04420081462
def v476 : W := 0x3814a200018652c14420080220
def v477 : W := 0x3814a200018653804c20081442
def v478 : W := 0x3814a200018653814c20080200
def v479 : W := 0x3814a200018653c14420080262
def v480 : W := 0x3814a200018653c14c20081662
def v481 : W := 0x3814a200018653c14c31481672
def v482 : W := 0x3814a200018653c15c30481672
def v483 : W := 0x3814a200018653c15c3148166a
def v484 : W := 0x3814a200058673c14c20081662
def v485 : W := 0x3814a200218650000000000000
def v486 : W := 0x3814a200218652804420080000
def v487 : W := 0x3814a200218653c14c20081662
def v488 : W := 0x3814a200258653c54c200a5662
def v489 : W := 0x3814a280a18652804420080000
def v490 : W := 0x3814a280a18653c14c20081662
def v491 : W := 0x3814a280a18653d54c280a5662
def v492 : W := 0x381ce200018652804420080000
def v493 : W := 0x381ce200018653c14c20081662
def v494 : W := 0x381ce280818652804420080000
def v495 : W := 0x381ce280818653c14c20081662
def v496 : W := 0x381ce280818653d1cc280c9662
def v497 : W := 0x381ce280a18652804420080000
def v498 : W := 0x381ce280a18652804c20081400
def v499 : W := 0x381ce280a1865290c4280c8000
def v500 : W := 0x381ce280a18652944c280a4000
def v501 : W := 0x381ce280a18652c04420081462
def v502 : W := 0x381ce280a18652c14420080220
def v503 : W := 0x381ce280a18653804c20081442
def v504 : W := 0x381ce280a18653814c20080200
def v505 : W := 0x381ce280a18653c14420080262
def v506 : W := 0x381ce280a18653c14c20081662
def v507 : W := 0x381ce280a58653844c200a4000
def v508 : W := 0x381ce280a58673804420080042
def v509 : W := 0x3830320401964b4b1735403ffe
def v510 : W := 0x3834b204019653c34e31493ff3
def v511 : W := 0x3834b204019653cb5d34481ef6
def v512 : W := 0x3834b204019659431b15413fff
def v513 : W := 0x3834b20401965a8a4724192985
def v514 : W := 0x3834b20401965aca5734593df7
def v515 : W := 0x3834b20401965b8a4f35593dd7
def v516 : W := 0x3834b20401965bc15f3548376e
def v517 : W := 0x3834b20401965bcb4f24193fe7
def v518 : W := 0x3834b20401965bcb5735592bef
def v519 : W := 0x3834b20401965bcb5735593fff
def v520 : W := 0x3834b20401965bcb5f35593fff
def v521 : W := 0x383cf284a1965a8a4724192985
def v522 : W := 0x3854a20041c653d5cc280ed662
def v523 : W := 0x3854a20041c673c14c20081662
def v524 : W := 0x3854a20045c673c54c200a5662
def v525 : W := 0x3854a20061c653c54c200a5662
def v526 : W := 0x3854a20065c671040800025442
def v527 : W := 0x3854a20065c671450800025662
def v528 : W := 0x3854a20065c673844c200a5442
def v529 : W := 0x3854a20065c673c54c200a5662
def v530 : W := 0x3854a73245c777c54c716a5672
def v531 : W := 0x385ce20041c653c1cc200c9662
def v532 : W := 0x385ce280e1c65280c4200c9400
def v533 : W := 0x385ce280e1c652844c200a5400
def v534 : W := 0x385ce280e1c65294c4280ec000
def v535 : W := 0x385ce280e1c65294cc280ed400
def v536 : W := 0x385ce280e1c653d5cc280ed662
def v537 : W := 0x385ce280e1c672804420081442
def v538 : W := 0x385ce280e5c6728444200a4000
def v539 : W := 0x385ce280e5c673844c200a5442
def v540 : W := 0x385ce280e5c67394cc280ed442
def v541 : W := 0x385ce280e5c673c54c200a5662
def v542 : W := 0x385ce280e5c673d5cc280ed662
def v543 : W := 0x385ce7b2e5c777844c716a5452
def v544 : W := 0x3874b32641df73c34c30481ef2
def v545 : W := 0x387cf3a6e1df72824430481cd2
def v546 : W := 0x389ee2c0a18e52804420080000
def v547 : W := 0x389eea81a18652884420180000
def v548 : W := 0x38bef244019e5a8a4724192985
def v549 : W := 0x38bef2c4a19e528a4524080884
def v550 : W := 0x3914a20005a653c14c20081662
def v551 : W := 0x3914a20005a653d54c280a5662
def v552 : W := 0x3914a28081a653d14c28081662
def v553 : W := 0x3914a280a5a653954c280a4200
def v554 : W := 0x3914a280a5a653d54c280a5662
def v555 : W := 0x391ce280a1a652914428080200
def v556 : W := 0x391ce280a5a6529444280a4000
def v557 : W := 0x391ce280a5a653814420080200
def v558 : W := 0x391ce280a5a653954c280a4200
def v559 : W := 0x391ce280a5a653d54c280a5662
def v560 : W := 0x3954a080e5e4319548080a5642
def v561 : W := 0x3954a280e5e673d54c280a5662
def v562 : W := 0x395ce080e5e01395cc280ed600
def v563 : W := 0x395ce280e5e65395cc280ed600
def v564 : W := 0x395ce280e5e653d5cc280ed662
def v565 : W := 0x395ce280e5e673954c280a5642
def v566 : W := 0x3c14a200098673c14c20081662
def v567 : W := 0x3c1ce200098653c1cc200c9662
def v568 : W := 0x3c1ce280a98652c0c4200c8020
def v569 : W := 0x3c1ce280a98672c04420080062
def v570 : W := 0x3c54a20049c673c1cc200c9662
def v571 : W := 0x3c5ce20049c672c0c4200c9462
def v572 : W := 0x3c5ce20049c673c1cc200c9662
def v573 : W := 0x3c5ce2006dc673c5cc200ed662
def v574 : W := 0x3c5ce280e9c67280c4200c8000
def v575 : W := 0x3c5ce280e9c672c0c4200c9462
def v576 : W := 0x3c5ce280e9c672d4cc280ed462
def v577 : W := 0x3c5ce280e9c673c1cc200c9662
def v578 : W := 0x3c5ce280e9c673d5cc280ed662
def v579 : W := 0x3c5ce280edc673c4cc200ed462
def v580 : W := 0x3d14a20009a653c14c20081662
def v581 : W := 0x3d14a20009a653d1cc280c9662
def v582 : W := 0x3d14a2000da671410800001662
def v583 : W := 0x3d14a2000da673c14420080262
def v584 : W := 0x3d14a2000da673c14c20081662
def v585 : W := 0x3d14a2002da671410000000262
def v586 : W := 0x3d14a280ada673d54c280a5662
def v587 : W := 0x3d1ce28089a652d1c4280c8220
def v588 : W := 0x3d1ce28089a653d1cc280c9662
def v589 : W := 0x3d1ce2808da673d1cc280c9662
def v590 : W := 0x3d1ce280a9a65290c4280c8000
def v591 : W := 0x3d1ce280a9a652c14420080220
def v592 : W := 0x3d1ce280a9a652d1c4280c8220
def v593 : W := 0x3d1ce280a9a653d1cc280c9662
def v594 : W := 0x3d1ce280ada653d5cc280ec220
def v595 : W := 0x3d1ce280ada653d5cc280ed662
def v596 : W := 0x3d1ce280ada672804420080000
def v597 : W := 0x3d1ce280ada673c14420080262
def v598 : W := 0x3d1ce280ada673c14c20081662
def v599 : W := 0x3d1ce280ada673d1c4280c8262
def v600 : W := 0x3d1ce280ada673d54c280a4262
def v601 : W := 0x3d54a2004de67294c4280ec000
def v602 : W := 0x3d54a2004de673d5cc280ed662
def v603 : W := 0x3d54a2006de671450800025662
def v604 : W := 0x3d54a2006de67155880806d662
def v605 : W := 0x3d54a2006de673c54c200a5662
def v606 : W := 0x3d54a2006de673d5cc280ed662
def v607 : W := 0x3d54a280ede671d548080a5662
def v608 : W := 0x3d54a280ede673d5cc280ed662
def v609 : W := 0x3d5862004de663418420049662
def v610 : W := 0x3d5ce2004de673c1cc200c9662
def v611 : W := 0x3d5ce2004de673d5cc280ed662
def v612 : W := 0x3d5ce2006de673458c2006d662
def v613 : W := 0x3d5ce280c9e673d1cc280c9662
def v614 : W := 0x3d5ce280cde673d5cc280ed662
def v615 : W := 0x3d5ce280e9e652d5cc280ed620
def v616 : W := 0x3d5ce280e9e653d5cc280ed662
def v617 : W := 0x3d5ce280e9e672d1c4280c9662
def v618 : W := 0x3d5ce280ede253d5cc280ed620
def v619 : W := 0x3d5ce280ede67155880806d662
def v620 : W := 0x3d5ce280ede67294c4280ec000
def v621 : W := 0x3d5ce280ede67294cc280ed400
def v622 : W := 0x3d5ce280ede672d4c4280ed462
def v623 : W := 0x3d5ce280ede672d5c4280ec220
def v624 : W := 0x3d5ce280ede67394cc280ed442
def v625 : W := 0x3d5ce280ede67395cc280ec200
def v626 : W := 0x3d5ce280ede673c1c4200c9662
def v627 : W := 0x3d5ce280ede673c54c200a5662
def v628 : W := 0x3d5ce280ede673d5c4280ec262
def v629 : W := 0x3d5ce280ede673d5cc280ed662
def v630 : W := 0x3d5ce280ede673d5cc394ed672
def v631 : W := 0x3d5ce280ede673d5dc384ed672
def v632 : W := 0x3d5ce280ede673d5dc394ed66a
def v633 : W := 0x3d5ce2a2ede773f5ec2a0ed672
def v634 : W := 0x3d5ce2a2ede777d5cc682ed672
def v635 : W := 0x3d5ce2a2ede777f5eceaaed662
def v636 : W := 0x3d5ce3a2ede773d5cc384ed672
def v637 : W := 0x3d5ce3a2edef73d5cc280ed662
def v638 : W := 0x3d5ce690ede677d5cc692ed662
def v639 : W := 0x3d5ce698ede6f3d5cc290ed66a
def v640 : W := 0x3d5ce698ede6f7d5cce8aed662
def v641 : W := 0x3d5ce790ede673d5cc394ed662
def v642 : W := 0x3d5ce790efe673d5cc280ed662
def v643 : W := 0x3d5ce7b2ede777d5cc682ed662
def v644 : W := 0x3d5ce7b2ede777d5cc796ed672
def v645 : W := 0x3d7033264dff61430010401ef2
def v646 : W := 0x3d7cf284edf673d7ce394ffff3
def v647 : W := 0x3d7cf284edf673dfdd3c4edef6
def v648 : W := 0x3d7cf284edf67bd5df3d4ef76e
def v649 : W := 0x3d7cf284edf67bdfcf2c1fffe7
def v650 : W := 0x3d7cf384edf673d5cc384ed662
def v651 : W := 0x3d7cf3a6edff73d7cc384edef2
def v652 : W := 0x3d7cf794eff673d5ce394ef762
def v653 : W := 0x3ddee280ede673fdec2a0ed662
def v654 : W := 0x3ddee2a2edef73f5ec2a0ed662
def v655 : W := 0x3ddee2a2edef73ffec2a0edef2
def v656 : W := 0x3ddee2c0edee73d5cc280ed662
def v657 : W := 0x3ddeea81ede673ddcc281ed662
def v658 : W := 0x3ddeea81ede673f5ecaa8ed662
def v659 : W := 0x3dfef2c4edfe73dfcd2c0edee6
def v660 : W := 0x3e55a32249c773e1fc324c9672
def v661 : W := 0x3e5de3a2e9c772e0f4324c9472
def v662 : W := 0x3edfe36249cf73e1ec220c9662
def v663 : W := 0x3edfe3e2e9cf72a0e4220c8000
def v664 : W := 0x3efb736649df626ab536449cf6
def v665 : W := 0x3efb736649df636bb536449ef6
def v666 : W := 0x3efb736649df6b6bb73744bffe
def v667 : W := 0x3efff36649df72eaf5364c9cf6
def v668 : W := 0x3efff36649df73ebfd364c9ef6
def v669 : W := 0x3efff36649df7aeaf7365dbdf7
def v670 : W := 0x3efff3e6e9df72eaf5364c9cf6
def v671 : W := 0x3efff3e6e9df73ebfd364c9ef6
def v672 : W := 0x3f15a7180da6f3c15c3148166a
def v673 : W := 0x3f1de798ada6f3c1543148026a
def v674 : W := 0x3f55a73a4de7f6b4e4eaaec000
def v675 : W := 0x3f55a73a4de7f7f5eceaaed662
def v676 : W := 0x3f55a73a6de7f545185162567a
def v677 : W := 0x3f5de280ede673f5fc2a0ed662
def v678 : W := 0x3f5de288ede6f3d5dc280ed66a
def v679 : W := 0x3f5de288ede6f3f5ecaa8ed662
def v680 : W := 0x3f5de380ede673d5dc384ed662
def v681 : W := 0x3f5de3a2ede773f5ec2a0ed662
def v682 : W := 0x3f5de3a2ede773f5fc3a4ed672
def v683 : W := 0x3f5de3c0ede673d5cc280ed662
def v684 : W := 0x3f5de798ede6f3d5cc280ed662
def v685 : W := 0x3f5de798ede6f3d5dc394ed66a
def v686 : W := 0x3f5de7b2ede777f5fc7b6ed672
def v687 : W := 0x3f5de7baede7f3f5fc3b4ed67a
def v688 : W := 0x3f5de7baede7f6b4e4eaaec000
def v689 : W := 0x3f5de7baede7f7d5dc796ed67a
def v690 : W := 0x3f5de7baede7f7f5eceaaed662
def v691 : W := 0x3f5de7baede7f7f5ecfbeed672
def v692 : W := 0x3f5de7baede7f7f5fcfaeed672
def v693 : W := 0x3f5de7baede7f7f5fcfbeed66a
def v694 : W := 0x3f75b73e4df7febee7eebfe985
def v695 : W := 0x3f7df3c4edf673d5dd3c4ed666
def v696 : W := 0x3fdfe2c0ede673f5ec2a0ed662
def v697 : W := 0x3fdfe2c0ede673fdfd2e0ed666
def v698 : W := 0x3fdfe3e2edef73f5ec2a0ed662
def v699 : W := 0x3fdfe3e2edef73f5fc3a4ed672
def v700 : W := 0x3fdfe7faedeff7f5eceaaed662
def v701 : W := 0x3ffb73664dff636bb536449ef6
def v702 : W := 0x3ffb73e6cdff63fbf53e4c9ef6
def v703 : W := 0x3ffb777e4dffe36bb537449efe
def v704 : W := 0x3ffff3664dff73ebfd364c9ef6
def v705 : W := 0x3ffff3e6c9ff73fbfd3e4c9ef6
def v706 : W := 0x3ffff3e6e9ff72fbf53e4c9ef6
def v707 : W := 0x3ffff3e6edff73ebf5364c9ef6
def v708 : W := 0x3ffff3e6edff73fffd3e4edef6
def v709 : W := 0x40000000320800000000000000
def v710 : W := 0x40000022100904020040210891
def v711 : W := 0x40000410120004000241212101
def v712 : W := 0x40000410160005040a41236101
def v713 : W := 0x40000410360004040040224000
def v714 : W := 0x40000410360004040241236101
def v715 : W := 0x40000532120904000040200000
def v716 : W := 0x40000881b000041400c8a24000
def v717 : W := 0x40048000300014040840234001
def v718 : W := 0x40048410320014040a41236101
def v719 : W := 0x40048881b00010804000190001
def v720 : W := 0x40201004121800020200012981
def v721 : W := 0x402010041218080a0304112985
def v722 : W := 0x40201536121904020251612991
def v723 : W := 0x402015361219040a1355612995
def v724 : W := 0x4020153612190c02135561299d
def v725 : W := 0x4020153612190c0a0355712995
def v726 : W := 0x40400022704904040040224000
def v727 : W := 0x40400532764924040040224000
def v728 : W := 0x40400532764925040851625452
def v729 : W := 0x40601536565925060a51637dd3
def v730 : W := 0x40601536765924060251636991
def v731 : W := 0x408208011008000a0000110881
def v732 : W := 0x408208231009042020c2a00000
def v733 : W := 0x408a4881b00800000000000000
def v734 : W := 0x40a210441218000a0304012985
def v735 : W := 0x40a215761219040a0355612995
def v736 : W := 0x40a218051018080a0304112985
def v737 : W := 0x40ca48a3f0490434a0caa6c000
def v738 : W := 0x40ca4db3f6492434a0caa6c000
def v739 : W := 0x42211576121904021355612995
def v740 : W := 0x42a311661219002a3316412995
def v741 : W := 0x42a315761219042a3357612995
def v742 : W := 0x454845b2fe692414804826c000
def v743 : W := 0x45ca48a3fc692434a0caa6c000
def v744 : W := 0x46cb45727e492424a04226c000
def v745 : W := 0x46cb49e3f8492434a0caa6c000
def v746 : W := 0x46e315765e59256ebb5767fdf7
def v747 : W := 0x46eb55767e59242eb35767e995
def v748 : W := 0x4741053a7e69a434a0caa6c000
def v749 : W := 0x47cb4dbbfc69a434a0caa6c000
def v750 : W := 0x48701736765b66c746716b6bb1
def v751 : W := 0x487857b6d65b67864e716b7dd3
def v752 : W := 0x4d3857b69a3b46d3c6796dabb1
def v753 : W := 0x50002410360005040241226100
def v754 : W := 0x5004a000300015040a41236101
def v755 : W := 0x5004a000320010000200012101
def v756 : W := 0x5004a000320014040a40236101
def v757 : W := 0x5004a410360014040240236101
def v758 : W := 0x5004a410360015040a41236101
def v759 : W := 0x5004a410360015040a51637553
def v760 : W := 0x5004a410360435040a41236143
def v761 : W := 0x5004a410360815040a41236101
def v762 : W := 0x5004a490b60015944a492b6101
def v763 : W := 0x5004a510360035040a41236101
def v764 : W := 0x5004a510360035040a51636143
def v765 : W := 0x5004ac91b60015140ac9a36101
def v766 : W := 0x5004ac91b60015844a413b6101
def v767 : W := 0x50203536161d250202516129d3
def v768 : W := 0x5024b514361435040a51636143
def v769 : W := 0x5024b536361915060a51636991
def v770 : W := 0x5044a532764135040a51637553
def v771 : W := 0x5044a532764935040a41236101
def v772 : W := 0x50603536765d25040251626142
def v773 : W := 0x5104a410362015150a49236301
def v774 : W := 0x5104a418362095050a41236309
def v775 : W := 0x5104a418362095140ac9a36101
def v776 : W := 0x5104a490b62015140a49236101
def v777 : W := 0x568fe6503e02576cbf6727e125
def v778 : W := 0x5705a5183e20b5451a5163636b
def v779 : W := 0x58102881b0000d1502c9a26308
def v780 : W := 0x5814a410360015854a412b6301
def v781 : W := 0x5814a41036001d050a41236309
def v782 : W := 0x5814a41036001d844a413b6101
def v783 : W := 0x5814a490b60015844a412b6101
def v784 : W := 0x58fa7aa7f05f4d75b3dfe6e36e
def v785 : W := 0x5914a410362015050a41236301
def v786 : W := 0x5914a490b62015954a492b6301
def v787 : W := 0x5d14a6103e2675450a41236363
def v788 : W := 0x5d1ce690be2257d5ce692fe321
def v789 : W := 0x5f932f191c2ee14b1011510aeb
def v790 : W := 0x60048000318810020000010881
def v791 : W := 0x6044802271c914060840235c91
def v792 : W := 0x6044853275c935060851635cd3
def v793 : W := 0x6044853277c934060840235c91
def v794 : W := 0x604cc0a2f1c91696cc682fdc91
def v795 : W := 0x6060112673dd20020010401cd2
def v796 : W := 0x6060153653dd24020251613dd3
def v797 : W := 0x6060153677dd24060050625cd2
def v798 : W := 0x6064902671d914060a51637d91
def v799 : W := 0x6064902671dd14060840235c91
def v800 : W := 0x6064902671dd14060850635cd3
def v801 : W := 0x6064902673d914060a40237d91
def v802 : W := 0x6064912671d914060850635c91
def v803 : W := 0x6064912671dd30020010411cd3
def v804 : W := 0x6064912671dd30020810411cd3
def v805 : W := 0x6064912671dd34060850635cd3
def v806 : W := 0x6064912673dd30020010411cd3
def v807 : W := 0x6064953673d914060a51637d91
def v808 : W := 0x6064953673dd34060a51637dd3
def v809 : W := 0x6064953675dd31020011411cd3
def v810 : W := 0x6064953675dd35060851635cd3
def v811 : W := 0x6064953677d934060a51637d91
def v812 : W := 0x6064953677d935060a51637dd3
def v813 : W := 0x6064953677dd34060850635cd3
def v814 : W := 0x608ec881b188128a4420190881
def v815 : W := 0x60aedac5b19e528a4524190885
def v816 : W := 0x60ca48a3f1c9063ea4eaa6dc90
def v817 : W := 0x60cec02271c9162eac6227dc91
def v818 : W := 0x60cec881f1c8129ecc281fdc81
def v819 : W := 0x60cec8a3f1c912aae4221d9c91
def v820 : W := 0x60cec8a3f1c91436a8caa7dc91
def v821 : W := 0x60cec8a3f1c9168e4c603b5c91
def v822 : W := 0x60cec8a3f1c916b4eceaaed400
def v823 : W := 0x60cec8a3f1c916b6eceaafdc91
def v824 : W := 0x60cec8a3f1c916bee4eabfc881
def v825 : W := 0x60cec8a3f1c916bee4eabfdc91
def v826 : W := 0x60cec8a3f1c916beeceaaedc90
def v827 : W := 0x60cec8a3f1c916beeceabfdc81
def v828 : W := 0x60cec8a3f1c916beeceabfdc91
def v829 : W := 0x60eed8a7f1d91eb4ffffeef50c
def v830 : W := 0x60eed9a7f1dd328a4430591cd3
def v831 : W := 0x644846105bc66640866125b563
def v832 : W := 0x66eb53667bdf626ab536449cf6
def v833 : W := 0x66eb57765bdf666ab77765bdf7
def v834 : W := 0x66eb57767fdf666eb57666dcf6
def v835 : W := 0x66eb5b6759df626ab536559cf7
def v836 : W := 0x66eb5be7f9df626ab536449cf6
def v837 : W := 0x66eb5be7f9df667eb5fee6dcf6
def v838 : W := 0x66efd36679df726ab536459cf7
def v839 : W := 0x66efd36679df766ebd7667dcf7
def v840 : W := 0x66efdbe7f9df72eaf5365d9cf7
def v841 : W := 0x678fcd99bda8b3cb5431590aeb
def v842 : W := 0x67efdffffdfff3ebf5375d9eff
def v843 : W := 0x6d584690dbe666d1c6692db763
def v844 : W := 0x7004a410378015060a41237d91
def v845 : W := 0x7004a410378415040a41236101
def v846 : W := 0x7004a410378415040a41237543
def v847 : W := 0x7004a410378815060a41236981
def v848 : W := 0x7024b004339c10020200012981
def v849 : W := 0x7024b004339c11020a11413dd3
def v850 : W := 0x7024b414379415060a51637dd3
def v851 : W := 0x7024b414379c15060a41236981
def v852 : W := 0x7024b514379c310202114129c3
def v853 : W := 0x7024b536139d15020a51613dd3
def v854 : W := 0x7024b536339d14020251612991
def v855 : W := 0x7044a02275cd35060840235cd3
def v856 : W := 0x7044a41077c435040a41237543
def v857 : W := 0x7044a43277c915060a41237d91
def v858 : W := 0x7044a53277cd35040840225442
def v859 : W := 0x7064b00477dc31060a00037dc3
def v860 : W := 0x7064b02671dd14060a40237d91
def v861 : W := 0x7064b02671dd15060a51637dd3
def v862 : W := 0x7064b02673dd10020200013d91
def v863 : W := 0x7064b02673dd14060240236981
def v864 : W := 0x7064b02673dd14060a40237d91
def v865 : W := 0x7064b02673dd15060a51637dd3
def v866 : W := 0x7064b02675dd35060a51637dd3
def v867 : W := 0x7064b02677dd35060a40237dd3
def v868 : W := 0x7064b12671dd30020010411cd3
def v869 : W := 0x7064b12671dd35060a51637dd3
def v870 : W := 0x7064b12673dd30020010401cd2
def v871 : W := 0x7064b12673dd30020200012981
def v872 : W := 0x7064b12673dd30020210413dd3
def v873 : W := 0x7064b12673dd31020a11413dd3
def v874 : W := 0x7064b12673dd34060a50637dd3
def v875 : W := 0x7064b12675dd35060850635cd3
def v876 : W := 0x7064b12677dd31060a10437dd3
def v877 : W := 0x7064b43677dd15060a41237d91
def v878 : W := 0x7064b43677dd15060a51637dd3
def v879 : W := 0x7064b53653dd35020a51613dd3
def v880 : W := 0x7064b53657dd35060a51637dd3
def v881 : W := 0x7064b53673dd14060a51637d91
def v882 : W := 0x7064b53673dd15060a51637dd3
def v883 : W := 0x7064b53673dd34020251613dd3
def v884 : W := 0x7064b53675dd35060a51637dd3
def v885 : W := 0x7064b53677d535060a51637dd3
def v886 : W := 0x7064b53677d915060a51637d91
def v887 : W := 0x7064b53677dd31020211413dd3
def v888 : W := 0x7064b53677dd34060240236981
def v889 : W := 0x7064b53677dd34060250637dd3
def v890 : W := 0x7064b53677dd34060251636991
def v891 : W := 0x7064b53677dd34060a40237d91
def v892 : W := 0x7064b53677dd35040a51627542
def v893 : W := 0x7064b53677dd350602516369c3
def v894 : W := 0x7064b53677dd35060850625cd2
def v895 : W := 0x7064b53677dd35060a40237dc3
def v896 : W := 0x7064b53677dd35060a41236981
def v897 : W := 0x7064b53677dd35060a51637dd3
def v898 : W := 0x7064b53677dd35461a51637df3
def v899 : W := 0x7064b53677dd35470a51637ff3
def v900 : W := 0x7064b53677dd35471a51637ffb
def v901 : W := 0x7064b73677df774e1f75637df7
def v902 : W := 0x7064bdb7f7dd35160ad9e37dd3
def v903 : W := 0x706cf5b6f7dd35060a51637dd3
def v904 : W := 0x706cf5b6f7dd3796ce796ffdd3
def v905 : W := 0x708eec91b788178e4e613b6981
def v906 : W := 0x70aef244339e520a0724012985
def v907 : W := 0x70aef885b39c128a4620192981
def v908 : W := 0x70e6bd3777dd350e0a51737dd3
def v909 : W := 0x70eef53677dd372eae7367fdd3
def v910 : W := 0x70eef57677dd35060a51637dd3
def v911 : W := 0x70eef77677df770e0f75637dd7
def v912 : W := 0x70eefdb7f7dd35060a51637dd3
def v913 : W := 0x70eefdb7f7dd3536aadbe7fdd3
def v914 : W := 0x70eefdb7f7dd378e4e717b7dd3
def v915 : W := 0x7164b53677fd35170a59637fd3
def v916 : W := 0x7164b53e77fdb5070a51637fdb
def v917 : W := 0x7164b53e77fdb5160ad9e37dd3
def v918 : W := 0x7164b5b6f7fd35160a59637dd3
def v919 : W := 0x7265b53e77ddb5061a51637ddb
def v920 : W := 0x72e7b57677dd352e3b57637dd7
def v921 : W := 0x7464b7367fdf75460a51637df3
def v922 : W := 0x746cf7367fdf77468e7167fdf3
def v923 : W := 0x7564b5367ffd35060a51637dd3
def v924 : W := 0x7564b5367ffd35470a51637ff3
def v925 : W := 0x7564b5367ffd35578a5967fff3
def v926 : W := 0x756cf5b6fffd35168a5967fdd3
def v927 : W := 0x7665b5367fdd35461a51637df3
def v928 : W := 0x7665b5367fdd3566ba5367fdf3
def v929 : W := 0x7665b5767fdd35060a51637dd3
def v930 : W := 0x7665b7767fdf75461b55637df7
def v931 : W := 0x76cfe7727fcf7764ac6226d462
def v932 : W := 0x76eff3667bdf726ab73645bdf7
def v933 : W := 0x76eff5767fdd3526aa5367fdd3
def v934 : W := 0x76eff7767fdf776ebf7767fdf7
def v935 : W := 0x7765b53e7ffdb5060a51637dd3
def v936 : W := 0x7765b53e7ffdb536aadbe7fdd3
def v937 : W := 0x7765b53e7ffdb5471a51637ffb
def v938 : W := 0x7814a610378657c54e612b7763
def v939 : W := 0x781ce280b38e52804420080000
def v940 : W := 0x781ce690b78657844e612b6101
def v941 : W := 0x7834b204339e5a8a4724192985
def v942 : W := 0x783cf284b39e52824620092981
def v943 : W := 0x7854a73277cf77c54c602a5662
def v944 : W := 0x785ce7b2f7cf768444602a4000
def v945 : W := 0x7874b53677dd3d070a51637fdb
def v946 : W := 0x7874b73677df75060a51637dd3
def v947 : W := 0x7874b73677df75470a51637ff3
def v948 : W := 0x7874b73677df77c74e716b7ff3
def v949 : W := 0x7874b73677df7d471b55637fff
def v950 : W := 0x7874b73677df7f8e4f757b7dd7
def v951 : W := 0x787cf7b6f7df77864e716b7dd3
def v952 : W := 0x789eea81b18e52804420080000
def v953 : W := 0x789eea81b18e528a4420190881
def v954 : W := 0x78befa85b19e5a8a4724192985
def v955 : W := 0x78befa85b39e528a4620192981
def v956 : W := 0x78befa85b39e5a8a4724192985
def v957 : W := 0x78befac5b19e528a4524190885
def v958 : W := 0x78befac5b19e5a8a4724192985
def v959 : W := 0x78deeaa3f1cf56b4e4eaaec000
def v960 : W := 0x78deeaa3f1cf57f5eceaaed662
def v961 : W := 0x7974b53677fd35070a51637fd3
def v962 : W := 0x7974b5b6f7fd35974a596b7fd3
def v963 : W := 0x7d5ce280ffee73d5cc280ed662
def v964 : W := 0x7d5ce2a2fdef77d5cc682ed662
def v965 : W := 0x7d5ce2a2fdef77d7cc682fdef3
def v966 : W := 0x7d5ce690ffe677d5cc682ed662
def v967 : W := 0x7d5ce690ffe677d5ce692ff763
def v968 : W := 0x7d5ce7b2ffef77d5cc682ed662
def v969 : W := 0x7d5ce7b2ffef77d5cc796ed672
def v970 : W := 0x7d5cea81fde677d5cce8aed662
def v971 : W := 0x7d74b7367fff75470a51637ff3
def v972 : W := 0x7d7cf284fffe73d7ce280fffe3
def v973 : W := 0x7d7cf7b6ffff77d7ce796ffff3
def v974 : W := 0x7ddeea81fdee73d5cc280ed662
def v975 : W := 0x7ddeea81fdee73dfcc281fdee3
def v976 : W := 0x7ddeeaa3fdef77f5eceaaed662
def v977 : W := 0x7ddeefb3ffef77f5eceaaed662
def v978 : W := 0x7efffbe7f9df72eaf5365d9cf7
def v979 : W := 0x7f5de7baffeff7f5eceaaed662
def v980 : W := 0x7f75b73e7ffff5471a51637ffb
def v981 : W := 0x7fdfe7f2ffef77f5ec6a2ed662
def v982 : W := 0x7fdfebe3fdef77f5eceaaed662
def v983 : W := 0x7fdfefbbfdeff7f5eceaaed662
def v984 : W := 0x7ffff7f6ffff77ffff7f6ffff7
def v985 : W := 0x80000040020000000000000000
def v986 : W := 0x80000418020088000201002108
def v987 : W := 0x80201044021008000304002104
def v988 : W := 0x802010440210080a0304112985
def v989 : W := 0x80820841000008080104100004
def v990 : W := 0x808a48c1800000000000000000
def v991 : W := 0x80a218450010080a0304112985
def v992 : W := 0x81000418062080000000000000
def v993 : W := 0x81000889802080100088800000
def v994 : W := 0x8201004800008800110400000c
def v995 : W := 0x82010558020080000000000000
def v996 : W := 0x8221155c02108800131540210c
def v997 : W := 0x8221155c02108802131541299d
def v998 : W := 0x8221155c0210880a131551298d
def v999 : W := 0x82830849000080202082800000
def v1000 : W := 0x82a3157e0219882a331740299c
def v1001 : W := 0x8621175c0a16e840131540216e
def v1002 : W := 0x87010048082080000000000000
def v1003 : W := 0x870105580e20a0000000000000
def v1004 : W := 0x870105580e20a141101140026a
def v1005 : W := 0x8721155c0e30a800131540210c
def v1006 : W := 0x8721155c0e30a941131540236e
def v1007 : W := 0x8721175c0e36e0401114400066
def v1008 : W := 0x8741057a4e61a434a0caa6c000
def v1009 : W := 0x874945d8ee60a014800806c000
def v1010 : W := 0x878b48c988208030a08a848000
def v1011 : W := 0x878b4ac98822c278b5ae848024
def v1012 : W := 0x878b4dd98e20a030a08a848000
def v1013 : W := 0x87cb457a4e69a020a002048000
def v1014 : W := 0x87cb48c9ec60a034a08a86c000
def v1015 : W := 0x87cb49ebc869a030a08a848000
def v1016 : W := 0x87cb4dfbcc61a434a0caa6c000
def v1017 : W := 0x88100240000248000104000004
def v1018 : W := 0x88100881800008804000180000
def v1019 : W := 0x889a4ac180024a884524180004
def v1020 : W := 0x889a4ac180024aa8e5261c8004
def v1021 : W := 0x889a4ac180024ab8e5ae9c8004
def v1022 : W := 0x88da4ff3c4436f8c4d757a5456
def v1023 : W := 0x89100008002088010000000208
def v1024 : W := 0x8d9a4ac188224ad9c52c1c8224
def v1025 : W := 0x8e9b4ac188024aa8e5261c8004
def v1026 : W := 0x8e9b4ac188024ae8f5261c8024
def v1027 : W := 0x8f1102480822c841110400022c
def v1028 : W := 0x8f1107580c22e941111540026e
def v1029 : W := 0x8f1107580e22e841110400022c
def v1030 : W := 0x8f1942c88822cad1d52c0c822c
def v1031 : W := 0x8f31134c0836e841111440026e
def v1032 : W := 0x8f31175c0a32c841131540232c
def v1033 : W := 0x8f31175c0c36e941111540026e
def v1034 : W := 0x8f31175c0e32e841131540232c
def v1035 : W := 0x8f31175c0e32e941131540236e
def v1036 : W := 0x8f31175c0e36e841111440026e
def v1037 : W := 0x8f9b42480822ca69b52604822c
def v1038 : W := 0x8f9b42c88822caf9f52e0c822c
def v1039 : W := 0x8f9b4ac188224af9f52e1c8224
def v1040 : W := 0x8f9b4ac98822c2f1e4aa8c8220
def v1041 : W := 0x8f9b4ac98822c2f9f5ae8c8224
def v1042 : W := 0x8f9b4ac98822c871b18e84822c
def v1043 : W := 0x8f9b4ac98822cab8e5ae9c8004
def v1044 : W := 0x8f9b4ac98822cac9552418022c
def v1045 : W := 0x8f9b4ac98822cae9f5261c822c
def v1046 : W := 0x8f9b4ac98822caf1f5ae8c822c
def v1047 : W := 0x8f9b4ac98822caf8f5ae9c8024
def v1048 : W := 0x8f9b4ac98822caf9e5ae9c8224
def v1049 : W := 0x8f9b4ac98822caf9f5ae9c822c
def v1050 : W := 0x8fbb5acd8832c2f3e6bbcdabb1
def v1051 : W := 0x8ffb5befc87fe871b19ec4826e
def v1052 : W := 0x9221355c0614a900131540214e
def v1053 : W := 0x9721355c0e34a1000211402142
def v1054 : W := 0x97cfe9ebc869b130aa8b85a101
def v1055 : W := 0x98102000020008000200002100
def v1056 : W := 0x98303244021648000304002104
def v1057 : W := 0x9830324402164941131540236e
def v1058 : W := 0x98303754061669000315402146
def v1059 : W := 0x98ba7ac582164a884724182104
def v1060 : W := 0x99102418062089010201002308
def v1061 : W := 0x9910241806208d050a41226308
def v1062 : W := 0x9910241806208d1502c9a26308
def v1063 : W := 0x9914a498a62099954a090a6308
def v1064 : W := 0x9930351c0634a901021140234a
def v1065 : W := 0x9930361c0636c941131540236e
def v1066 : W := 0x9930365c0636c901030500230c
def v1067 : W := 0x9a31375c0216c800131540210c
def v1068 : W := 0x9a31375c0216c941131540236e
def v1069 : W := 0x9b31355c06308901131540230c
def v1070 : W := 0x9d1026180e26e941020100236a
def v1071 : W := 0x9d3032440e3669410304002366
def v1072 : W := 0x9e3133440a1668401314402166
def v1073 : W := 0x9f1122480c26e941110400026e
def v1074 : W := 0x9f1125180e20a941121140236a
def v1075 : W := 0x9f1125580e20a9010201002308
def v1076 : W := 0x9f1126580e22c941130500232c
def v1077 : W := 0x9f1127580e26e1410000000262
def v1078 : W := 0x9f31324c0836c941131540236e
def v1079 : W := 0x9f31324c0a36c841130400232c
def v1080 : W := 0x9f31365c0e36c941130500232c
def v1081 : W := 0x9f31365c0e36c941131540236e
def v1082 : W := 0x9f31371c0e36e941131540236e
def v1083 : W := 0x9f31375c0c36e941131540236e
def v1084 : W := 0x9f31375c0e32c941131540232c
def v1085 : W := 0x9f31375c0e36e1410211402362
def v1086 : W := 0x9f31375c0e36e1411114400266
def v1087 : W := 0x9f31375c0e36e8000304002104
def v1088 : W := 0x9f31375c0e36e800131540210c
def v1089 : W := 0x9f31375c0e36e8401314402166
def v1090 : W := 0x9f31375c0e36e841130400232c
def v1091 : W := 0x9f31375c0e36e9000315402146
def v1092 : W := 0x9f31375c0e36e901030500230c
def v1093 : W := 0x9f31375c0e36e9410304002366
def v1094 : W := 0x9f31375c0e36e941131540236e
def v1095 : W := 0x9f31375c0e36e941131540377e
def v1096 : W := 0x9f31375c0e36e9411b1540376e
def v1097 : W := 0x9f31375c0e36e9411b1540377e
def v1098 : W := 0x9f35b75c0e36f9411b1541236f
def v1099 : W := 0x9f35b7dcae36f9d55b1d4a636e
def v1100 : W := 0x9f3977dc8e36ebd1d73d4ca36e
def v1101 : W := 0x9f3977dcae36e941131540236e
def v1102 : W := 0x9f51253a4e61a961b21344b77a
def v1103 : W := 0x9f71375c4e76e9559b1d46f76e
def v1104 : W := 0x9f71377e4e77e941131540377e
def v1105 : W := 0x9f71377e4e77e961b31744b77e
def v1106 : W := 0x9f71377e4e77ed451b5562777e
def v1107 : W := 0x9f71377e4e77ed75b3dfe6e36e
def v1108 : W := 0x9f71377e4e7fe941131540236e
def v1109 : W := 0x9f7977dcee76e955931d46e36e
def v1110 : W := 0x9fb3377e0e3fe96b3317402bfe
def v1111 : W := 0x9fb33f5d0e36e949131550236e
def v1112 : W := 0x9fbb775c0e36eb69b73744a36e
def v1113 : W := 0x9fbb775c0e3ee941131540236e
def v1114 : W := 0x9fbb7fdd8e36e941131540236e
def v1115 : W := 0x9fbb7fdd8e36e971b39fc4a36e
def v1116 : W := 0x9fbb7fdd8e36ebc9573558236e
def v1117 : W := 0x9fdb657a4e69a921a20304a308
def v1118 : W := 0x9ffb777e4e7fe961b31744a36e
def v1119 : W := 0xa26dd5dce3d09a94df3d4ef50c
def v1120 : W := 0xa6eb53664bdf626ab536449cf6
def v1121 : W := 0xa6eb536e49dfea6ab536449cfe
def v1122 : W := 0xa6eb577e4bdfe26ab536449cf6
def v1123 : W := 0xa6eb577e4bdfea6ab73744bdfe
def v1124 : W := 0xa6eb5b6749df6a6ab536549cf6
def v1125 : W := 0xa6eb5b6f49dfe26ab5b6c49cf6
def v1126 : W := 0xa6eb5be7c9df626ab536449cf6
def v1127 : W := 0xa725955c0fb0ba805f3548350c
def v1128 : W := 0xa72dd5dcafb0bbc1573548236e
def v1129 : W := 0xa761157e4ffda0020010401cd2
def v1130 : W := 0xa7eb536e49ffe26ab536449cf6
def v1131 : W := 0xa7eb577e4fffe26ab536449cf6
def v1132 : W := 0xa7eb577e4fffe36bb537449efe
def v1133 : W := 0xa7eb59efc9fda032a09ac49cd2
def v1134 : W := 0xa7eb5befc9ffe27ab5bec49cf6
def v1135 : W := 0xa7eb5fffcfffe27ab5bec49cf6
def v1136 : W := 0xa87019a7c1dd28824010581cd2
def v1137 : W := 0xa8ba5ac5819e4a8a4524180884
def v1138 : W := 0xa8ba5ed5859e4f8e4d653a4884
def v1139 : W := 0xa8fa5be7c1df6a8a4534581cd6
def v1140 : W := 0xaefb536649df6a6ab536449cf6
def v1141 : W := 0xaefb5be7c9df6aeaf5365c9cf6
def v1142 : W := 0xaf71136e49ffe8431114401efe
def v1143 : W := 0xaffb536e49ffea6bb536449efe
def v1144 : W := 0xaffb53eec9ffeafbf53e4c9efe
def v1145 : W := 0xaffb577e4dffeb6bb537449efe
def v1146 : W := 0xaffb577e4fffea6bb536449efe
def v1147 : W := 0xaffb5be7c9ff6afbf53e5c9ef6
def v1148 : W := 0xaffb5befc9ffe2fbf5becc9ef6
def v1149 : W := 0xaffb5befc9ffea7bb5bec49efe
def v1150 : W := 0xaffb5befc9ffeabae5ae9c8884
def v1151 : W := 0xaffb5befc9ffeaebf5365c9efe
def v1152 : W := 0xaffb5befc9ffeafaf5bedc9cf6
def v1153 : W := 0xb0c6ad7365c53d0c0955725456
def v1154 : W := 0xb7aff8cd89b49132aa9bc5bdd3
def v1155 : W := 0xb81ce2c0a38652804420080000
def v1156 : W := 0xb81cea81a1865a804420180000
def v1157 : W := 0xb834b24403965a8a4724192985
def v1158 : W := 0xb83cf2c4a3965a804724082104
def v1159 : W := 0xb89eeac1a18652804420080000
def v1160 : W := 0xb89eeac1a1865a884524180004
def v1161 : W := 0xb8ba7244039e4a0a0724002984
def v1162 : W := 0xb8befac581965a8a4724192985
def v1163 : W := 0xb9da643a47e98b2ba62304bf98
def v1164 : W := 0xbd5ce288ede6fbd5cc280ed66a
def v1165 : W := 0xbd5ce2c0efe673d5cc280ed662
def v1166 : W := 0xbd5ce698efe6f3d5cc280ed662
def v1167 : W := 0xbd5ce698efe6fbd5ce290ef76a
def v1168 : W := 0xbd5cea81ede67bd5cc281ed662
def v1169 : W := 0xbd5cea89ede6f3d5cca88ed662
def v1170 : W := 0xbd7cf2c4eff67bd5cf2c0ef766
def v1171 : W := 0xbddeeac1ede673d5cc280ed662
def v1172 : W := 0xbddeeac1ede67bddcd2c1ed666
def v1173 : W := 0xbefb73664bdf6a6ab73644bdf6
def v1174 : W := 0xbefffbe7e9df7aeaf5365c9cf6
def v1175 : W := 0xbf15a7580fa6f3c14c20081662
def v1176 : W := 0xbf1de7d8afa6f2804420080000
def v1177 : W := 0xbf31375c0fb6eb4b1735403ffe
def v1178 : W := 0xbf35b75c0fb6f9411b1540376e
def v1179 : W := 0xbf35b75c0fb6f9431b15413fff
def v1180 : W := 0xbf35b75c0fb6fbc15f3548376e
def v1181 : W := 0xbf35b75c0fb6fbcb5735592bef
def v1182 : W := 0xbf35b75c2fb6f941131540236e
def v1183 : W := 0xbf3df7dcafb6fbc1573548236e
def v1184 : W := 0xbf51267a4febc9431305003fbc
def v1185 : W := 0xbf5de2c8ede6f3d5cc280ed662
def v1186 : W := 0xbf5de2c8ede6fbd5dd2c0ed66e
def v1187 : W := 0xbf5de7d8efe6f3d5cc280ed662
def v1188 : W := 0xbf5de7d8efe6f3d5dc394ed66a
def v1189 : W := 0xbf5de7faefe7f7f5eceaaed662
def v1190 : W := 0xbf71375c4ff6e941131540376e
def v1191 : W := 0xbf71377e4fffe9431315403ffe
def v1192 : W := 0xbf75b75c6ff6f9451b1542776e
def v1193 : W := 0xbf79775c4ff6eb41973544b76e
def v1194 : W := 0xbf7df7dceff6fbd5df3d4ef76e
def v1195 : W := 0xbf9feac989a6d3f1ecaa8c9662
def v1196 : W := 0xbf9feac9a9a6d2b0e4aa8c8000
def v1197 : W := 0xbfbb775c0fbeeb4b1735402bee
def v1198 : W := 0xbfdfe7faefeff3f5ec2a0ed662
def v1199 : W := 0xbfdfeac9ede6f3f5ecaa8ed662
def v1200 : W := 0xbfdfebebedeff3f5ecaa8ed662
def v1201 : W := 0xbfdfefd9efe6f3f5ecaa8ed662
def v1202 : W := 0xbfdfeffbede7f7f5eceaaed662
def v1203 : W := 0xbffb736e4dffeb6bb536449efe
def v1204 : W := 0xbffb777e4fffe36bb536449ef6
def v1205 : W := 0xbffb777e4fffeb6bb73744bffe
def v1206 : W := 0xbffff7feeffffbffff3f4efffe
def v1207 : W := 0xc0000801120008000200112101
def v1208 : W := 0xc0000881b20000000000000000
def v1209 : W := 0xc0000c191200840000c0a00000
def v1210 : W := 0xc0201044121808020304012985
def v1211 : W := 0xc020157612190c020355612995
def v1212 : W := 0xc02018051210080a0304112985
def v1213 : W := 0xc0820841120800000000000000
def v1214 : W := 0xc08a48c1b20800000000000000
def v1215 : W := 0xc0a218451218080a0304112985
def v1216 : W := 0xc0a218451218080a0315512995
def v1217 : W := 0xc0a218451218080a1314512995
def v1218 : W := 0xc0a218451218080a131551298d
def v1219 : W := 0xc0a218453218080a0304112985
def v1220 : W := 0xc0a218671219082a2306112995
def v1221 : W := 0xc0a2186712190c0a0344312995
def v1222 : W := 0xc0a2186712190c2a23c6b12985
def v1223 : W := 0xc0a218c5b218080a0304112985
def v1224 : W := 0xc0a219671219080a0314512995
def v1225 : W := 0xc0a21c5512180c0a0345312985
def v1226 : W := 0xc0a21c5d1218880a030511298d
def v1227 : W := 0xc0a21c5d12188c0a03c4b12985
def v1228 : W := 0xc0a21d551218080a0315512985
def v1229 : W := 0xc0a21d7712190c0a0344312985
def v1230 : W := 0xc0a21d7712190c0a0355712995
def v1231 : W := 0xc0aa58451218080a0304112985
def v1232 : W := 0xc0aa58c59218080a0304112985
def v1233 : W := 0xc0aa58c592180a8a4724192985
def v1234 : W := 0xc0aa58c5b218080a0304112985
def v1235 : W := 0xc0aa58c5b218094b0b04113fe7
def v1236 : W := 0xc0ca48e3f2490434a0caa6c000
def v1237 : W := 0xc0ca4df3f64924040040224000
def v1238 : W := 0xc0e21d7756592d0e0b55737dd7
def v1239 : W := 0xc0e21d7776592c0e0344336985
def v1240 : W := 0xc0ea58e7f2590c3ea3ceb7e985
def v1241 : W := 0xc0ea5df7f6592c0e0355736995
def v1242 : W := 0xc1000c99b620841400c8a24000
def v1243 : W := 0xc1000c99b620841402c9a36101
def v1244 : W := 0xc1000c99b6208c1402c8b36101
def v1245 : W := 0xc1000c99b6208c1402c9a26108
def v1246 : W := 0xc1400dbbf669a41400c8a24000
def v1247 : W := 0xc18a4cd9b628841400c8a24000
def v1248 : W := 0xc1a21cddb6388c1e03ccb36985
def v1249 : W := 0xc1ca4cbbf6698434a0caa6c000
def v1250 : W := 0xc221155c12188802131541298d
def v1251 : W := 0xc221157e12198c02135561299d
def v1252 : W := 0xc2830d7b1209842020c2a00000
def v1253 : W := 0xc28b4dfbb209842020c2a00000
def v1254 : W := 0xc2a3157e12198c2a335761299d
def v1255 : W := 0xc2a318451218082a3306112985
def v1256 : W := 0xc2a3184d1218880a130411298d
def v1257 : W := 0xc2a3184d1218882a2386912985
def v1258 : W := 0xc2a319451218080a1314512985
def v1259 : W := 0xc2a319671219082a2306112985
def v1260 : W := 0xc2a319671219082a3316512995
def v1261 : W := 0xc2a31d5d1218880a0304112985
def v1262 : W := 0xc2a31d5d1218880a131551298d
def v1263 : W := 0xc2a31d7712190c2a3357712995
def v1264 : W := 0xc2a31d7f1219842222d3e12991
def v1265 : W := 0xc2a31d7f1219842a31d6e00894
def v1266 : W := 0xc2a31d7f1219842a33d7e12995
def v1267 : W := 0xc2a31d7f1219882a331751299d
def v1268 : W := 0xc2a31d7f12198c0a135571299d
def v1269 : W := 0xc2a31d7f12198c2033d7e0210c
def v1270 : W := 0xc2a31d7f12198c2233d7e1299d
def v1271 : W := 0xc2a31d7f12198c2a23c6b12985
def v1272 : W := 0xc2a31d7f12198c2a23d7f12995
def v1273 : W := 0xc2a31d7f12198c2a33d6f12995
def v1274 : W := 0xc2a31d7f12198c2a33d7f1298d
def v1275 : W := 0xc2c30d7b7649a42420c2a24000
def v1276 : W := 0xc2cb4dfbf2498434a0caa6c000
def v1277 : W := 0xc3830dfbb629843420caa24000
def v1278 : W := 0xc5484c99fe60a41480c8a6c000
def v1279 : W := 0xc5ca48c1fe682014800806c000
def v1280 : W := 0xc5e218455e78295f8b0c17ffe7
def v1281 : W := 0xc5ea58c5fe78281e830c17e985
def v1282 : W := 0xc6cb49e3fa492020a002048000
def v1283 : W := 0xc6cb4d7b5a49a420a0c2a48000
def v1284 : W := 0xc6e319675a59286ab31655bdf7
def v1285 : W := 0xc6eb59675a59282aa30615a985
def v1286 : W := 0xc6eb59e7fa59282ab31655a995
def v1287 : W := 0xc7010dd9be20a41400c8a24000
def v1288 : W := 0xc7211fddbe36e45411dce24066
def v1289 : W := 0xc741057a7e69a4040040224000
def v1290 : W := 0xc7410dbbfe61a434a0caa6c000
def v1291 : W := 0xc761157e5e79ad471b55637fff
def v1292 : W := 0xc761157e7e79ac06135563699d
def v1293 : W := 0xc7830d7b1e29a42020c2a00000
def v1294 : W := 0xc78b48c9ba288030a08a848000
def v1295 : W := 0xc78b4cd9be208434a0caa6c000
def v1296 : W := 0xc78b4dd9be28a0000000000000
def v1297 : W := 0xc78b4dfb9a298430a0caa48000
def v1298 : W := 0xc7a31d5d1e38a80a0304112985
def v1299 : W := 0xc7a31d5d1e38a94b1315512bef
def v1300 : W := 0xc7ab58cd9a38883aa38e95a985
def v1301 : W := 0xc7ab5dddbe38a80a131551298d
def v1302 : W := 0xc7c30d7b5e69a434a0caa6c000
def v1303 : W := 0xc7cb48ebf8698434a0caa6c000
def v1304 : W := 0xc7cb4dfbda69a430a0caa48000
def v1305 : W := 0xc7cb4dfbde69a434a0caa6c000
def v1306 : W := 0xc7cb4dfbfe69a020a002048000
def v1307 : W := 0xc7cb4dfbfe69a4040040224000
def v1308 : W := 0xc7cb4dfbfe69a434a0caa6c000
def v1309 : W := 0xc7cb4dfbfe69a474b0dae6d472
def v1310 : W := 0xc7cb4dfbfe69a534a8dbe6d452
def v1311 : W := 0xc7cb4dfbfe69a575a8caa6d662
def v1312 : W := 0xc7cb4dfbfe69a575b0dbe6c26a
def v1313 : W := 0xc7cb4ffbfe6be67cb5eea6c024
def v1314 : W := 0xc7e31d7f5e79ac3ea3ceb7e985
def v1315 : W := 0xc7eb5dfffe79a436a2dbe7e991
def v1316 : W := 0xc7eb5dfffe79a43eb1dee6c894
def v1317 : W := 0xc7eb5dfffe79a43eb3dfe7e995
def v1318 : W := 0xc7eb5dfffe79ac34b3dfe6e10c
def v1319 : W := 0xc7eb5dfffe79ac36b3dfe7e99d
def v1320 : W := 0xc7eb5dfffe79ac3ea3ceb7e985
def v1321 : W := 0xc7eb5dfffe79ac3ea3dff7e995
def v1322 : W := 0xc7eb5dfffe79ac3eb3def7e995
def v1323 : W := 0xc7eb5dfffe79ac3eb3dff7e98d
def v1324 : W := 0xc7eb5ffffe7fe474b1dee6c066
def v1325 : W := 0xc89a4ac1b20a4a884524180004
def v1326 : W := 0xc8b218c59218088a4304192985
def v1327 : W := 0xc8ba5ac5921a4a8a4724192985
def v1328 : W := 0xc8da4ff3f64b6e8c45643a4004
def v1329 : W := 0xcf35934c3836fc45195463426f
def v1330 : W := 0xcfdb4ffbfe6be6f5e4eaaec220
def v1331 : W := 0xcfdb4ffbfe6bec75b1cea6c22c
def v1332 : W := 0xcfdb4ffbfe6beebce5eebec004
def v1333 : W := 0xd004a41836009d040a41236109
def v1334 : W := 0xd004ac1136001d040a41336101
def v1335 : W := 0xd004ac19360095040ac1a36101
def v1336 : W := 0xd004ac91b60015040a41236101
def v1337 : W := 0xd08eecd1b60815040a41236101
def v1338 : W := 0xd1002c99b620851402c9a26100
def v1339 : W := 0xd104a418362095040a41236101
def v1340 : W := 0xd104ac99b620941402c8a36101
def v1341 : W := 0xd104ac99b62095140ac9a36101
def v1342 : W := 0xd705a5583e20b5040a41236101
def v1343 : W := 0xd78fecd9be209534aacba7e101
def v1344 : W := 0xd78feed9be22d77cbfefa7e125
def v1345 : W := 0xd7cfedfbfe69b534a8caa6c000
def v1346 : W := 0xd7cfedfbfe69b534aacba7e101
def v1347 : W := 0xd7eb7dfffe7da534a2dbe6e142
def v1348 : W := 0xd814a41036001d040a41236101
def v1349 : W := 0xd814a881b20018804200192101
def v1350 : W := 0xd814a881b2001c844a403b6101
def v1351 : W := 0xd814a881b2001c9442c8bb6101
def v1352 : W := 0xd814ac91b6001c8442403b6101
def v1353 : W := 0xd814ac91b6001d844a413b6101
def v1354 : W := 0xd834bac5b21658804304192105
def v1355 : W := 0xd89ee8c1b20818804200192101
def v1356 : W := 0xd89eeac1b2025a884724192105
def v1357 : W := 0xd89eeed1b6025f8c4f653b6105
def v1358 : W := 0xd8b23a45121e480a0304112985
def v1359 : W := 0xd8b6b8c5b218188a4304192985
def v1360 : W := 0xd8ba7ac5b21e48000304002104
def v1361 : W := 0xd8deebe3f2437a884734593557
def v1362 : W := 0xd8fa7ae7f25f4c34a3cea6e104
def v1363 : W := 0xd910241836208d050241226308
def v1364 : W := 0xd9102c99b6208c1402c8a26100
def v1365 : W := 0xd9102c99b6208d1502c9a26308
def v1366 : W := 0xd914a41836209d050a41236309
def v1367 : W := 0xd914a498b6209d954a492b6309
def v1368 : W := 0xd914a881b62019954a081b6301
def v1369 : W := 0xd914ac91b6201d954a493b6301
def v1370 : W := 0xd914ac99b620959548c8aa4200
def v1371 : W := 0xd914ac99b62095954ac9ab6301
def v1372 : W := 0xd914ac99b62099814201192309
def v1373 : W := 0xd914ac99b6209c9442c8bb6101
def v1374 : W := 0xd914ac99b6209d150ac9a36309
def v1375 : W := 0xd914ac99b6209d854a413b6309
def v1376 : W := 0xd914ac99b6209d944ac9bb6101
def v1377 : W := 0xd914ac99b6209d9542c9bb6309
def v1378 : W := 0xd914ac99b6209d954ac8bb6301
def v1379 : W := 0xd914ac99b6209d954ac9aa6308
def v1380 : W := 0xd934bc9db630959f59dcea4a94
def v1381 : W := 0xde55a9a3fa4138e0f2125db573
def v1382 : W := 0xdedfe9e3fa4938a0e2021da101
def v1383 : W := 0xdf15a6583e22dd451b4523632d
def v1384 : W := 0xdf31375c3e3ee941131540236e
def v1385 : W := 0xdf31377e1e3fed431355612bff
def v1386 : W := 0xdf313f5d1e36e941131551236f
def v1387 : W := 0xdf313fddbe36e941131540236e
def v1388 : W := 0xdf313fddbe36ed5513dde2636e
def v1389 : W := 0xdf35b75c3e36f941131541236f
def v1390 : W := 0xdf35b75c3e36fd451b5563636f
def v1391 : W := 0xdf35bfddbe36f9c1531559236f
def v1392 : W := 0xdf71377e7e7fed45135562636e
def v1393 : W := 0xdf9b6ed9be22cd75b3cfa6e32c
def v1394 : W := 0xdf9fe6583e22df6dbf6727e32d
def v1395 : W := 0xdf9feed9be22debce7eebfe105
def v1396 : W := 0xdfb33f5d1e3ee941131540236e
def v1397 : W := 0xdfb33f5d1e3ee94b1315512bef
def v1398 : W := 0xdfb33f7f1e3fed6133d7e0236e
def v1399 : W := 0xdfbb7fddbe3ee941131540236e
def v1400 : W := 0xdfdb6dfbfe69ad35a2cba6e308
def v1401 : W := 0xdfdb6ffbfe6fe434a0caa6c000
def v1402 : W := 0xdfdb6ffbfe6fe575a0caa6c262
def v1403 : W := 0xdfdfedfbfe69b5b5e8caaec200
def v1404 : W := 0xdfdfedfbfe69bcb4e2cabfe101
def v1405 : W := 0xdffb7ffffe7fec34a3cea6e104
def v1406 : W := 0xdffb7ffffe7fed75b3dfe6e36e
def v1407 : W := 0xe08ec8c1b388128a4420190881
def v1408 : W := 0xe0aa5a45139e4a0a0724112985
def v1409 : W := 0xe0aa5ac5b39e420a0524000884
def v1410 : W := 0xe0aed8c5b3981a8a4724192985
def v1411 : W := 0xe0ea59e7f3dd20020010401cd2
def v1412 : W := 0xe1201e9db7b6c65e15fce25cf6
def v1413 : W := 0xe1aa5eddb7bec61e05eca24884
def v1414 : W := 0xe6494b235bc76a60b63255b573
def v1415 : W := 0xe6eb5b675bdf626ab536449cf6
def v1416 : W := 0xe6eb5b675bdf6a6ab73655bdf7
def v1417 : W := 0xe6eb5be7fbdf626ab536449cf6
def v1418 : W := 0xe6eb5f7f5bdfe66ab5f6e49cf6
def v1419 : W := 0xe6efdbe7fbdf72eaf5365d9cf7
def v1420 : W := 0xe78fcdd9bfa8b28a4420190881
def v1421 : W := 0xe78fcdd9bfa8b3cb5431590aeb
def v1422 : W := 0xe7ab5cddbfb48436a0dae6dcd2
def v1423 : W := 0xe7cb4dfbffe9a63ea4eaa6dc90
def v1424 : W := 0xe7cb4ffbffefe674a4eaa6d462
def v1425 : W := 0xe7cfcdfbffe9b436a8caa7dc91
def v1426 : W := 0xe7cfcdfbffe9b6b4eceaaed400
def v1427 : W := 0xe7cfcdfbffe9b6bee4eabfc881
def v1428 : W := 0xe7eb5beffbffe27ab5bec49cf6
def v1429 : W := 0xe7eb5dfffffda436a0dae6dcd2
def v1430 : W := 0xe7eb5fffffffe26ab536449cf6
def v1431 : W := 0xe7eb5fffffffe63ea5eea6c884
def v1432 : W := 0xe7eb5fffffffe67eb5fee6dcf6
def v1433 : W := 0xe89ecac1b18a5a8a4524190885
def v1434 : W := 0xeefb5be7fbdf6aeaf5365c9cf6
def v1435 : W := 0xeeffdbe7f9df7aeaf5365d9cf7
def v1436 : W := 0xef55826a79ebdc471944235ebd
def v1437 : W := 0xf064b53e77ddbd060a51637ddb
def v1438 : W := 0xf064b57677dd35060a51637dd3
def v1439 : W := 0xf064bd3777dd3d060a51737dd3
def v1440 : W := 0xf064bd3f77ddb5060ad1e37dd3
def v1441 : W := 0xf064bdb7f7dd35060a51637dd3
def v1442 : W := 0xf0a6b845339c180a0304112985
def v1443 : W := 0xf0aef8c5b39c10020200012981
def v1444 : W := 0xf0e6bd7777dd35060a51637dd3
def v1445 : W := 0xf0e6bd7777dd3d0e0b55737dd7
def v1446 : W := 0xf0eefdf7f7dd35060a51637dd3
def v1447 : W := 0xf164b53e77fdb5060a51637dd3
def v1448 : W := 0xf164bdbff7fdb5160ad9e37dd3
def v1449 : W := 0xf1eefdfff7fdb5160ad9e37dd3
def v1450 : W := 0xf265b57e77ddb5060a51637dd3
def v1451 : W := 0xf265b57e77ddbd061b55637ddf
def v1452 : W := 0xf2e7bd7f77ddb5262ad3e37dd3
def v1453 : W := 0xf765b57e7ffdb5060a51637dd3
def v1454 : W := 0xf765b57e7ffdb5471a51637ffb
def v1455 : W := 0xf765bdfffffdb5160ad9e37dd3
def v1456 : W := 0xf7aff8cdbbbc9032a28a85a981
def v1457 : W := 0xf7cfedfbffedb434a0caa6c000
def v1458 : W := 0xf7cfedfbffedb534a8caa6d442
def v1459 : W := 0xf7cfeffbffeff774aceaa6d462
def v1460 : W := 0xf7effdfffffdb436a2caa7e981
def v1461 : W := 0xf7effdfffffdb5060a51637dd3
def v1462 : W := 0xf7effdfffffdb536aadbe7fdd3
def v1463 : W := 0xf7effffffffff77ebfffe7fdf7
def v1464 : W := 0xf81cea81b38652804420080000
def v1465 : W := 0xf81cea81b3865a804620192101
def v1466 : W := 0xf834b244339e58020304012985
def v1467 : W := 0xf834b885b39c18824200192981
def v1468 : W := 0xf834ba85b3965a8a4724192985
def v1469 : W := 0xf874b53677dd3d060a51637dd3
def v1470 : W := 0xf874b77677df7d060b55637dd7
def v1471 : W := 0xf874bdb7f7dd3d864a517b7dd3
def v1472 : W := 0xf89ee881b3881a8a4620192981
def v1473 : W := 0xf89eeac1b38e52804420080000
def v1474 : W := 0xf89eeac1b38e53c14c20081662
def v1475 : W := 0xf8b6ba45139e5a8a4724192985
def v1476 : W := 0xf8befa85b39e5a8a4724192985
def v1477 : W := 0xf8befac5b19e5a8a4724192985
def v1478 : W := 0xf8befac5b3965a8a4724192985
def v1479 : W := 0xf8befac5b39e52824620092981
def v1480 : W := 0xf8befac5b39e528a4524080884
def v1481 : W := 0xf8befac5b39e58020304012985
def v1482 : W := 0xf8befac5b39e5a804724082104
def v1483 : W := 0xf8befac5b39e5a8a4724192985
def v1484 : W := 0xf8befac5b39e5aca5734593df7
def v1485 : W := 0xf8befac5b39e5b8a4f35593dd7
def v1486 : W := 0xf8befac5b39e5bcb4f24193fe7
def v1487 : W := 0xf8befac5b39e5bcb5735592bef
def v1488 : W := 0xf8befed5b79e5f8e4f653b6985
def v1489 : W := 0xf8befeddb39eda8a472519298d
def v1490 : W := 0xf8beffd5b79e7a8a4724192985
def v1491 : W := 0xf8beffd5b79e7b8a47355929c7
def v1492 : W := 0xf8befff7b39f5e8a4775792995
def v1493 : W := 0xf8dee8a3f3c91aaae6221dbd91
def v1494 : W := 0xf8deeae3f3cf56b4eceaaed400
def v1495 : W := 0xf8deeff3f7cf77844c602a5442
def v1496 : W := 0xf8fefac5f3de5a9ecf2c1ffd85
def v1497 : W := 0xf8fefac5f7de7b8e4f241b7dc7
def v1498 : W := 0xf8fefae7f3df5aaae7261dbd95
def v1499 : W := 0xf8fefae7f3df5e8e4f643b7d95
def v1500 : W := 0xf8fefae7f3df5ebee7eebfe985
def v1501 : W := 0xf8fefbe7f3df7a8a4724192985
def v1502 : W := 0xf8fefbe7f3df7a8a4734593dd7
def v1503 : W := 0xf8fefff7f7df7e8e47643b6985
def v1504 : W := 0xf8fefff7f7df7f8e4f757b7dd7
def v1505 : W := 0xf914ae99b7a6d7d54ce8aa5662
def v1506 : W := 0xf91cee99b7a6d69444e8aa4000
def v1507 : W := 0xf974b53e77fdbd070a51637fdb
def v1508 : W := 0xf974bdbff7fdbd170ad9e37fdb
def v1509 : W := 0xf99eeed9b7aed7954ce8aa4200
def v1510 : W := 0xf9befac5b7be5b9f4f2c1b6b85
def v1511 : W := 0xf9befeddb7beda8a4724192985
def v1512 : W := 0xf9befeddb7bedb8b4725192b8d
def v1513 : W := 0xf9befeddb7bede9e47ecbb6985
def v1514 : W := 0xfa97af7b138fd7e16ce2a81662
def v1515 : W := 0xfa9feffbb38fd6a064e2a80000
def v1516 : W := 0xfabffacdb39eda8a572419298d
def v1517 : W := 0xfabffbe7b39f5aaa7736592995
def v1518 : W := 0xfabfffddb39eda8a4724192985
def v1519 : W := 0xfabfffddb39eda8a573559298d
def v1520 : W := 0xfabfffffb39fdeaa67e6b92985
def v1521 : W := 0xfcfefac5fbde7acac7241dbde7
def v1522 : W := 0xfd5cea81ffe673d5cc280ed662
def v1523 : W := 0xfd5cea81ffe67bd5ce281ff763
def v1524 : W := 0xfd5cee99ffe6f7d5cce8aed662
def v1525 : W := 0xfd5cefbbffeff7d5cce8aed662
def v1526 : W := 0xfd74b73e7ffffd470a51637ffb
def v1527 : W := 0xfdbefac5bbbe5adbc72c1daba5
def v1528 : W := 0xfdbefac5bfbe7a8a4724192985
def v1529 : W := 0xfdbefac5bfbe7bcb4724192be7
def v1530 : W := 0xfddeeac1ffee73d5cc280ed662
def v1531 : W := 0xfddeeae3ffef77f5eceaaed662
def v1532 : W := 0xfddeeebbffeff7f5eceaaed662
def v1533 : W := 0xfddeeed9ffeef7d5cce8aed662
def v1534 : W := 0xfddeeff3ffef77d5cc682ed662
def v1535 : W := 0xfdfefac5fffe7a9ec72c1fe985
def v1536 : W := 0xfdfefac5fffe7bdfcf2c1fffe7
def v1537 : W := 0xfdfefff7ffff7fdfcf7d7ffff7
def v1538 : W := 0xfebffac5bb9e5aeaf7261da9a5
def v1539 : W := 0xfebffbc5bb9e7a8a4724192985
def v1540 : W := 0xfebffbc5bb9e7aca57345929e7
def v1541 : W := 0xfedfebe3fbcf72e0e4220c9462
def v1542 : W := 0xfefffbe7fbdf72eaf5364c9cf6
def v1543 : W := 0xfefffbe7fbdf7aaae7261da985
def v1544 : W := 0xfefffbe7fbdf7aeaf7365dbdf7
def v1545 : W := 0xfefffff7ffdf7feeff777ffdf7
def v1546 : W := 0xff35b75c3fbef9431315412bef
def v1547 : W := 0xff55a77a7feff5450840225662
def v1548 : W := 0xff5de7faffeff7d5cc682ed662
def v1549 : W := 0xff5defbbffe7f7f5eceaaed662
def v1550 : W := 0xff5defd9ffe6f7d5cce8aed662
def v1551 : W := 0xff75b53e7ffdbd471a51637ffb
def v1552 : W := 0xff75b57e7ffdbd070a51637fdb
def v1553 : W := 0xff75b77e7ffff5470a51637ff3
def v1554 : W := 0xff75b77e7ffffd471b55637fff
def v1555 : W := 0xff7df7feffffffd7df7d6fffff
def v1556 : W := 0xff9feac9bbaed2f1e4aa8c8220
def v1557 : W := 0xff9fefd9bfaef3c14420080262
def v1558 : W := 0xffbffacdbbbeda8a4724192985
def v1559 : W := 0xffbffacdbbbedabae7ae9da985
def v1560 : W := 0xffbffacdbbbedacb5724192bad
def v1561 : W := 0xffbfffddbfbefa8a4724192985
def v1562 : W := 0xffbfffddbfbefbcb5735592bef
def v1563 : W := 0xffd7af7b5feff6b4e4eaaec000
def v1564 : W := 0xffdfeac9ffeef3f5ecaa8ed662
def v1565 : W := 0xffdfeaebfdeff7f5eceaaed662
def v1566 : W := 0xffdfebe3ffef73f5ec2a0ed662
def v1567 : W := 0xffdfeed9ffe6f7f5eceaaed662
def v1568 : W := 0xffdfefd9ffeef3d5cc280ed662
def v1569 : W := 0xffdfeffbffeff434a0caa6c000
def v1570 : W := 0xffdfeffbffeff575a8caa6d662
def v1571 : W := 0xffdfeffbffeff6b4e4eaaec000
def v1572 : W := 0xffdfeffbffeff6b4eceaaed400
def v1573 : W := 0xffdfeffbffeff6f4e4eaaed462
def v1574 : W := 0xffdfeffbffeff6f5e4eaaec220
def v1575 : W := 0xffdfeffbffeff7b4eceaaed442
def v1576 : W := 0xffdfeffbffeff7b5eceaaec200
def v1577 : W := 0xffdfeffbffeff7f5e4eaaec262
def v1578 : W := 0xffdfeffbffeff7f5eceaaed662
def v1579 : W := 0xffdfeffbffeff7f5ecfbeed672
def v1580 : W := 0xffdfeffbffeff7f5fcfaeed672
def v1581 : W := 0xffdfeffbffeff7f5fcfbeed66a
def v1582 : W := 0xfffb7fffffffef7fb7ffe6fffe
def v1583 : W := 0xfffff77e7fffff6fbf7767ffff
def v1584 : W := 0xfffffbe7ffff7bffff3e5ffff7
def v1585 : W := 0xffffffddfffefbdfdf3d5fffef
def v1586 : W := 0xfffffffffffff7f7eefbeffff3
def v1587 : W := 0xfffffffffffff7fffdfeeedef6
def v1588 : W := 0xfffffffffffffbebf7375dbfff
def v1589 : W := 0xfffffffffffffd77bbdfe7ffff
def v1590 : W := 0xfffffffffffffebee7eebfe985
def v1591 : W := 0xfffffffffffffefef7fefffdf7
def v1592 : W := 0xffffffffffffffbeeffffffdd7
def v1593 : W := 0xffffffffffffffcf5f757b7fff
def v1594 : W := 0xfffffffffffffff5ffffeef76e
def v1595 : W := 0xffffffffffffffffefeebfffe7
def v1596 : W := 0xfffffffffffffffff7ffffebef
def ins : List W := [v1308, v1483, v1094, v897, v629, v375]
theorem sampled : ∀ j : Fin 104, Nat.testBit 0xeee8eaa8ece8a8a8 (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
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
def level3 : BinaryTree (List W) := (.node [v435, v1094, v1483, v1514] (.node [v256, v629, v784, v1483] (.node [v237, v1094, v1460, v1473] (.node [v237, v1094, v1443, v1571] .nil .nil) (.node [v237, v1094, v1483, v1569] .nil .nil)) (.node [v262, v1094, v1457, v1483] (.node [v260, v629, v784, v1483] .nil .nil) (.node [v375, v897, v1405, v1557] .nil .nil))) (.node [v545, v1182, v1308, v1483] (.node [v544, v1178, v1308, v1483] (.node [v440, v1094, v1280, v1308] .nil .nil) (.node [v545, v1094, v1457, v1483] .nil .nil)) (.node [v629, v809, v841, v1308] (.node [v629, v803, v841, v1308] .nil .nil) (.node [v645, v1192, v1308, v1483] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level3_ok : everyKey (rowOK 2 level2) level3 = true := by decide +kernel
theorem closed3 : Closed 3 level3 := closed_next 2 (by decide) level3 level2 closed2 level3_ok
def level4llll : BinaryTree (List W) := (.node [v118, v897, v1094, v1458, v1483] (.node [v99, v629, v841, v897, v1308] (.node [v61, v375, v694, v897, v1094] (.node [v42, v629, v841, v897, v1308] (.node [v18, v375, v694, v897, v1094] .nil .nil) (.node [v52, v629, v784, v897, v1483] .nil .nil)) (.node [v64, v440, v1094, v1308, v1483] (.node [v64, v435, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v113, v897, v1094, v1457, v1483] (.node [v113, v443, v1094, v1308, v1483] (.node [v113, v440, v1094, v1308, v1483] .nil .nil) (.node [v113, v897, v1094, v1280, v1308] .nil .nil)) (.node [v118, v443, v1094, v1308, v1483] (.node [v118, v435, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v165, v375, v629, v694, v1094] (.node [v148, v375, v513, v897, v1094] (.node [v125, v629, v784, v897, v1483] (.node [v118, v897, v1094, v1483, v1514] .nil .nil) (.node [v132, v629, v803, v814, v1308] .nil .nil)) (.node [v150, v375, v897, v1094, v1483] (.node [v149, v375, v897, v1094, v1308] .nil .nil) .nil)) (.node [v175, v375, v1308, v1483, v1547] (.node [v175, v375, v676, v1308, v1483] (.node [v166, v192, v1094, v1308, v1483] .nil .nil) .nil) (.node [v191, v629, v694, v897, v1094] (.node [v177, v897, v1094, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llll_ok : everyKey (rowOK 3 level3) level4llll = true := by decide +kernel
def level4lllr : BinaryTree (List W) := (.node [v237, v416, v1094, v1308, v1483] (.node [v209, v375, v629, v694, v897] (.node [v205, v897, v1094, v1308, v1483] (.node [v193, v237, v1192, v1308, v1483] (.node [v192, v897, v1094, v1308, v1483] .nil .nil) (.node [v199, v897, v1094, v1308, v1483] .nil .nil)) (.node [v207, v375, v453, v1308, v1483] (.node [v206, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v216, v435, v1094, v1308, v1483] (.node [v211, v375, v424, v1308, v1483] (.node [v210, v375, v629, v694, v897] .nil .nil) .nil) (.node [v229, v375, v629, v694, v897] (.node [v220, v440, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v237, v459, v1094, v1308, v1483] (.node [v237, v456, v1094, v1308, v1483] (.node [v237, v423, v1094, v1308, v1483] (.node [v237, v417, v1094, v1308, v1483] .nil .nil) (.node [v237, v426, v1094, v1308, v1483] .nil .nil)) (.node [v237, v458, v1094, v1308, v1483] (.node [v237, v457, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v237, v465, v1094, v1308, v1483] (.node [v237, v464, v1094, v1308, v1483] (.node [v237, v463, v1094, v1308, v1483] .nil .nil) .nil) (.node [v237, v480, v1094, v1330, v1483] (.node [v237, v472, v1094, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lllr_ok : everyKey (rowOK 3 level3) level4lllr = true := by decide +kernel
def level4lll : BinaryTree (List W) := .node [v192, v443, v1094, v1308, v1483] level4llll level4lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lll_ok : everyKey (rowOK 3 level3) level4lll = true := by
  change (_ && everyKey (rowOK 3 level3) level4llll && everyKey (rowOK 3 level3) level4lllr) = true
  rw [level4llll_ok, level4lllr_ok]
  decide +kernel
def level4llrl : BinaryTree (List W) := (.node [v237, v604, v1094, v1308, v1483] (.node [v237, v497, v1182, v1308, v1483] (.node [v237, v497, v1094, v1308, v1442] (.node [v237, v485, v1094, v1308, v1483] (.node [v237, v480, v1178, v1308, v1483] .nil .nil) (.node [v237, v497, v1094, v1308, v1327] .nil .nil)) (.node [v237, v497, v1094, v1457, v1483] (.node [v237, v497, v1094, v1308, v1443] .nil .nil) .nil)) (.node [v237, v582, v1094, v1308, v1483] (.node [v237, v527, v1094, v1308, v1483] (.node [v237, v526, v1094, v1308, v1483] .nil .nil) .nil) (.node [v237, v603, v1094, v1308, v1483] (.node [v237, v585, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v237, v629, v1094, v1154, v1483] (.node [v237, v629, v784, v897, v1483] (.node [v237, v619, v1094, v1308, v1483] (.node [v237, v612, v1094, v1308, v1483] .nil .nil) (.node [v237, v629, v694, v897, v1094] .nil .nil)) (.node [v237, v629, v1022, v1094, v1308] (.node [v237, v629, v841, v897, v1308] .nil .nil) .nil)) (.node [v237, v629, v1094, v1457, v1483] (.node [v237, v629, v1094, v1345, v1483] (.node [v237, v629, v1094, v1308, v1481] .nil .nil) .nil) (.node [v237, v629, v1178, v1308, v1483] (.node [v237, v629, v1098, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llrl_ok : everyKey (rowOK 3 level3) level4llrl = true := by decide +kernel
def level4llrr : BinaryTree (List W) := (.node [v237, v1094, v1308, v1483, v1547] (.node [v237, v897, v1094, v1483, v1514] (.node [v237, v752, v1094, v1308, v1483] (.node [v237, v629, v1308, v1436, v1483] (.node [v237, v629, v1308, v1389, v1483] .nil .nil) (.node [v237, v676, v1094, v1308, v1483] .nil .nil)) (.node [v237, v897, v1094, v1280, v1308] (.node [v237, v848, v1094, v1308, v1473] .nil .nil) .nil)) (.node [v237, v1094, v1233, v1308, v1483] (.node [v237, v931, v1094, v1308, v1483] (.node [v237, v897, v1119, v1308, v1483] .nil .nil) .nil) (.node [v237, v1094, v1308, v1459, v1483] (.node [v237, v1094, v1308, v1326, v1483] .nil .nil) .nil))) (.node [v249, v629, v1094, v1154, v1483] (.node [v237, v1094, v1462, v1483, v1571] (.node [v237, v1094, v1346, v1483, v1578] (.node [v237, v1094, v1308, v1483, v1570] .nil .nil) (.node [v237, v1094, v1460, v1483, v1578] .nil .nil)) (.node [v248, v422, v1094, v1308, v1483] (.node [v248, v414, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v255, v629, v1094, v1308, v1483] (.node [v255, v480, v1094, v1308, v1483] (.node [v254, v629, v1094, v1308, v1483] .nil .nil) .nil) (.node [v256, v497, v1094, v1308, v1483] (.node [v256, v480, v1094, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llrr_ok : everyKey (rowOK 3 level3) level4llrr = true := by decide +kernel
def level4llr : BinaryTree (List W) := .node [v237, v629, v1182, v1308, v1483] level4llrl level4llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4llr_ok : everyKey (rowOK 3 level3) level4llr = true := by
  change (_ && everyKey (rowOK 3 level3) level4llrl && everyKey (rowOK 3 level3) level4llrr) = true
  rw [level4llrl_ok, level4llrr_ok]
  decide +kernel
def level4ll : BinaryTree (List W) := .node [v237, v480, v1094, v1458, v1483] level4lll level4llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4ll_ok : everyKey (rowOK 3 level3) level4ll = true := by
  change (_ && everyKey (rowOK 3 level3) level4lll && everyKey (rowOK 3 level3) level4llr) = true
  rw [level4lll_ok, level4llr_ok]
  decide +kernel
def level4lrll : BinaryTree (List W) := (.node [v287, v629, v1022, v1094, v1308] (.node [v262, v415, v1094, v1308, v1483] (.node [v257, v629, v1094, v1308, v1483] (.node [v256, v1094, v1215, v1308, v1483] (.node [v256, v629, v1094, v1308, v1483] .nil .nil) (.node [v256, v1094, v1308, v1483, v1578] .nil .nil)) (.node [v258, v629, v1094, v1308, v1483] (.node [v258, v497, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v280, v629, v784, v897, v1483] (.node [v264, v897, v1094, v1308, v1541] (.node [v262, v422, v1094, v1308, v1483] .nil .nil) (.node [v277, v629, v1308, v1436, v1483] .nil .nil)) (.node [v283, v897, v1094, v1308, v1473] (.node [v283, v629, v841, v897, v1308] .nil .nil) .nil))) (.node [v306, v603, v1094, v1308, v1483] (.node [v303, v440, v1094, v1308, v1483] (.node [v298, v897, v1119, v1308, v1483] (.node [v296, v752, v1094, v1308, v1483] .nil .nil) (.node [v303, v435, v1094, v1308, v1483] .nil .nil)) (.node [v306, v422, v1094, v1308, v1483] (.node [v303, v443, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v309, v603, v1094, v1308, v1483] (.node [v309, v424, v1094, v1308, v1483] (.node [v309, v422, v1094, v1308, v1483] .nil .nil) .nil) (.node [v309, v858, v1094, v1308, v1483] (.node [v309, v752, v1094, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrll_ok : everyKey (rowOK 3 level3) level4lrll = true := by decide +kernel
def level4lrlr : BinaryTree (List W) := (.node [v371, v858, v1094, v1308, v1483] (.node [v347, v443, v1094, v1308, v1483] (.node [v329, v629, v694, v897, v1094] (.node [v326, v629, v1022, v1094, v1308] (.node [v322, v452, v1094, v1308, v1483] .nil .nil) (.node [v328, v629, v694, v897, v1094] .nil .nil)) (.node [v336, v424, v1094, v1308, v1483] (.node [v332, v629, v1308, v1436, v1483] .nil .nil) .nil)) (.node [v355, v629, v1094, v1154, v1483] (.node [v347, v897, v1094, v1308, v1480] (.node [v347, v894, v1094, v1308, v1483] .nil .nil) .nil) (.node [v365, v897, v1094, v1308, v1473] (.node [v365, v629, v694, v897, v1094] .nil .nil) .nil))) (.node [v375, v480, v784, v897, v1483] (.node [v375, v455, v1094, v1308, v1483] (.node [v375, v446, v629, v694, v1094] (.node [v372, v897, v1094, v1308, v1473] .nil .nil) (.node [v375, v447, v629, v694, v1094] .nil .nil)) (.node [v375, v480, v694, v897, v1094] (.node [v375, v473, v694, v897, v1094] .nil .nil) .nil)) (.node [v375, v480, v1094, v1154, v1483] (.node [v375, v480, v1022, v1094, v1308] (.node [v375, v480, v841, v897, v1308] .nil .nil) .nil) (.node [v375, v497, v694, v897, v1094] (.node [v375, v480, v1308, v1436, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrlr_ok : everyKey (rowOK 3 level3) level4lrlr = true := by decide +kernel
def level4lrl : BinaryTree (List W) := .node [v322, v443, v1094, v1308, v1483] level4lrll level4lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrl_ok : everyKey (rowOK 3 level3) level4lrl = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrll && everyKey (rowOK 3 level3) level4lrlr) = true
  rw [level4lrll_ok, level4lrlr_ok]
  decide +kernel
def level4lrrl : BinaryTree (List W) := (.node [v375, v592, v1022, v1094, v1308] (.node [v375, v529, v1094, v1154, v1483] (.node [v375, v497, v1308, v1436, v1483] (.node [v375, v497, v1022, v1094, v1308] (.node [v375, v497, v841, v897, v1308] .nil .nil) (.node [v375, v497, v1094, v1154, v1483] .nil .nil)) (.node [v375, v513, v674, v897, v1094] (.node [v375, v506, v694, v897, v1094] .nil .nil) .nil)) (.node [v375, v539, v1022, v1094, v1308] (.node [v375, v536, v784, v897, v1483] (.node [v375, v535, v841, v897, v1308] .nil .nil) .nil) (.node [v375, v588, v1094, v1154, v1483] (.node [v375, v584, v784, v897, v1483] .nil .nil) .nil))) (.node [v375, v629, v694, v888, v1094] (.node [v375, v603, v1308, v1436, v1483] (.node [v375, v601, v694, v897, v1094] (.node [v375, v597, v841, v897, v1308] .nil .nil) (.node [v375, v602, v694, v897, v1094] .nil .nil)) (.node [v375, v629, v694, v824, v897] (.node [v375, v620, v694, v897, v1094] .nil .nil) .nil)) (.node [v375, v629, v694, v897, v1399] (.node [v375, v629, v694, v897, v1094] (.node [v375, v629, v694, v897, v1087] .nil .nil) .nil) (.node [v375, v629, v694, v1094, v1446] (.node [v375, v629, v694, v1043, v1094] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrrl_ok : everyKey (rowOK 3 level3) level4lrrl = true := by decide +kernel
def level4lrrr : BinaryTree (List W) := (.node [v375, v644, v1022, v1094, v1308] (.node [v375, v629, v841, v937, v1308] (.node [v375, v629, v784, v1453, v1483] (.node [v375, v629, v784, v897, v1483] (.node [v375, v629, v784, v897, v954] .nil .nil) (.node [v375, v629, v784, v897, v1561] .nil .nil)) (.node [v375, v629, v841, v897, v1308] (.node [v375, v629, v841, v864, v1308] .nil .nil) .nil)) (.node [v375, v629, v1022, v1094, v1308] (.node [v375, v629, v897, v1308, v1421] (.node [v375, v629, v888, v1087, v1214] .nil .nil) .nil) (.node [v375, v629, v1308, v1436, v1483] (.node [v375, v629, v1094, v1154, v1483] .nil .nil) .nil))) (.node [v375, v750, v1094, v1308, v1483] (.node [v375, v694, v897, v1094, v1271] (.node [v375, v690, v694, v897, v1094] (.node [v375, v685, v841, v897, v1308] .nil .nil) (.node [v375, v694, v897, v1094, v1215] .nil .nil)) (.node [v375, v694, v897, v1094, v1578] (.node [v375, v694, v897, v1094, v1530] .nil .nil) .nil)) (.node [v375, v784, v897, v976, v1483] (.node [v375, v752, v1094, v1308, v1483] (.node [v375, v751, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v784, v897, v1215, v1483] (.node [v375, v784, v897, v1187, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrrr_ok : everyKey (rowOK 3 level3) level4lrrr = true := by decide +kernel
def level4lrr : BinaryTree (List W) := .node [v375, v629, v784, v861, v1483] level4lrrl level4lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lrr_ok : everyKey (rowOK 3 level3) level4lrr = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrrl && everyKey (rowOK 3 level3) level4lrrr) = true
  rw [level4lrrl_ok, level4lrrr_ok]
  decide +kernel
def level4lr : BinaryTree (List W) := .node [v375, v497, v784, v897, v1483] level4lrl level4lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4lr_ok : everyKey (rowOK 3 level3) level4lr = true := by
  change (_ && everyKey (rowOK 3 level3) level4lrl && everyKey (rowOK 3 level3) level4lrr) = true
  rw [level4lrl_ok, level4lrr_ok]
  decide +kernel
def level4l : BinaryTree (List W) := .node [v256, v629, v1003, v1406, v1483] level4ll level4lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4l_ok : everyKey (rowOK 3 level3) level4l = true := by
  change (_ && everyKey (rowOK 3 level3) level4ll && everyKey (rowOK 3 level3) level4lr) = true
  rw [level4ll_ok, level4lr_ok]
  decide +kernel
def level4rlll : BinaryTree (List W) := (.node [v375, v897, v1056, v1308, v1557] (.node [v375, v848, v1094, v1308, v1495] (.node [v375, v841, v897, v1215, v1308] (.node [v375, v807, v1119, v1308, v1483] (.node [v375, v789, v897, v1308, v1483] .nil .nil) (.node [v375, v829, v897, v1308, v1483] .nil .nil)) (.node [v375, v841, v897, v1308, v1578] (.node [v375, v841, v897, v1262, v1308] .nil .nil) .nil)) (.node [v375, v888, v1094, v1308, v1473] (.node [v375, v858, v1094, v1308, v1479] (.node [v375, v858, v1085, v1308, v1483] .nil .nil) (.node [v375, v864, v1094, v1308, v1473] .nil .nil)) (.node [v375, v895, v1094, v1308, v1473] (.node [v375, v892, v1077, v1308, v1483] .nil .nil) .nil))) (.node [v375, v897, v1094, v1320, v1473] (.node [v375, v897, v1094, v1234, v1571] (.node [v375, v897, v1087, v1308, v1473] (.node [v375, v897, v1077, v1308, v1482] .nil .nil) (.node [v375, v897, v1093, v1308, v1473] .nil .nil)) (.node [v375, v897, v1094, v1280, v1308] (.node [v375, v897, v1094, v1235, v1308] .nil .nil) .nil)) (.node [v375, v897, v1094, v1443, v1571] (.node [v375, v897, v1094, v1405, v1473] (.node [v375, v897, v1094, v1360, v1571] .nil .nil) .nil) (.node [v375, v897, v1094, v1483, v1514] (.node [v375, v897, v1094, v1460, v1473] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlll_ok : everyKey (rowOK 3 level3) level4rlll = true := by decide +kernel
def level4rllr : BinaryTree (List W) := (.node [v375, v897, v1406, v1561, v1578] (.node [v375, v897, v1183, v1401, v1483] (.node [v375, v897, v1127, v1308, v1483] (.node [v375, v897, v1101, v1483, v1571] (.node [v375, v897, v1094, v1483, v1569] .nil .nil) (.node [v375, v897, v1119, v1308, v1483] .nil .nil)) (.node [v375, v897, v1176, v1406, v1483] (.node [v375, v897, v1128, v1308, v1483] .nil .nil) .nil)) (.node [v375, v897, v1399, v1530, v1590] (.node [v375, v897, v1399, v1483, v1571] (.node [v375, v897, v1187, v1406, v1561] .nil .nil) .nil) (.node [v375, v897, v1405, v1562, v1578] (.node [v375, v897, v1399, v1578, v1590] .nil .nil) .nil))) (.node [v375, v1022, v1094, v1230, v1308] (.node [v375, v968, v1094, v1154, v1483] (.node [v375, v944, v1094, v1462, v1483] (.node [v375, v903, v1094, v1483, v1571] .nil .nil) (.node [v375, v951, v1094, v1457, v1483] .nil .nil)) (.node [v375, v1022, v1094, v1215, v1308] (.node [v375, v971, v1119, v1308, v1483] .nil .nil) .nil)) (.node [v375, v1094, v1153, v1308, v1483] (.node [v375, v1050, v1094, v1308, v1483] (.node [v375, v1022, v1094, v1308, v1578] .nil .nil) .nil) (.node [v375, v1094, v1154, v1215, v1483] (.node [v375, v1094, v1154, v1199, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rllr_ok : everyKey (rowOK 3 level3) level4rllr = true := by decide +kernel
def level4rll : BinaryTree (List W) := .node [v375, v897, v1094, v1483, v1563] level4rlll level4rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rll_ok : everyKey (rowOK 3 level3) level4rll = true := by
  change (_ && everyKey (rowOK 3 level3) level4rlll && everyKey (rowOK 3 level3) level4rllr) = true
  rw [level4rlll_ok, level4rllr_ok]
  decide +kernel
def level4rlrl : BinaryTree (List W) := (.node [v422, v544, v1094, v1308, v1483] (.node [v405, v443, v1094, v1308, v1483] (.node [v375, v1308, v1436, v1483, v1578] (.node [v375, v1215, v1308, v1436, v1483] (.node [v375, v1094, v1446, v1483, v1571] .nil .nil) (.node [v375, v1251, v1308, v1436, v1483] .nil .nil)) (.node [v404, v629, v1094, v1308, v1483] (.node [v402, v629, v841, v897, v1308] .nil .nil) .nil)) (.node [v414, v544, v1094, v1308, v1483] (.node [v413, v752, v1094, v1308, v1483] (.node [v407, v422, v1094, v1308, v1483] .nil .nil) .nil) (.node [v419, v629, v1094, v1343, v1483] (.node [v415, v545, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v435, v473, v1094, v1308, v1483] (.node [v433, v480, v1094, v1308, v1483] (.node [v422, v645, v1094, v1308, v1483] (.node [v422, v545, v1094, v1308, v1483] .nil .nil) (.node [v433, v473, v1094, v1308, v1483] .nil .nil)) (.node [v433, v629, v1094, v1308, v1483] (.node [v433, v497, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v435, v480, v1094, v1483, v1578] (.node [v435, v480, v1094, v1308, v1483] (.node [v435, v480, v1094, v1252, v1483] .nil .nil) .nil) (.node [v435, v572, v1094, v1308, v1483] (.node [v435, v497, v1094, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlrl_ok : everyKey (rowOK 3 level3) level4rlrl = true := by decide +kernel
def level4rlrr : BinaryTree (List W) := (.node [v439, v629, v1094, v1308, v1483] (.node [v437, v1094, v1215, v1308, v1483] (.node [v435, v1094, v1308, v1483, v1578] (.node [v435, v1094, v1215, v1308, v1483] (.node [v435, v629, v1094, v1308, v1483] .nil .nil) (.node [v435, v1094, v1234, v1308, v1483] .nil .nil)) (.node [v437, v629, v1094, v1308, v1483] (.node [v436, v629, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v438, v629, v1094, v1346, v1483] (.node [v438, v629, v1036, v1308, v1483] (.node [v437, v1094, v1308, v1320, v1483] .nil .nil) .nil) (.node [v439, v584, v1094, v1308, v1483] (.node [v438, v629, v1094, v1412, v1483] .nil .nil) .nil))) (.node [v440, v592, v1094, v1308, v1483] (.node [v440, v497, v1094, v1308, v1483] (.node [v440, v480, v1094, v1308, v1483] (.node [v440, v473, v1094, v1308, v1483] .nil .nil) (.node [v440, v497, v1094, v1215, v1308] .nil .nil)) (.node [v440, v575, v1094, v1308, v1483] (.node [v440, v497, v1094, v1308, v1536] .nil .nil) .nil)) (.node [v440, v1094, v1308, v1483, v1571] (.node [v440, v1094, v1215, v1308, v1483] (.node [v440, v629, v1094, v1308, v1483] .nil .nil) .nil) (.node [v441, v506, v1094, v1308, v1483] (.node [v440, v1094, v1308, v1483, v1578] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlrr_ok : everyKey (rowOK 3 level3) level4rlrr = true := by decide +kernel
def level4rlr : BinaryTree (List W) := .node [v435, v588, v1094, v1308, v1483] level4rlrl level4rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rlr_ok : everyKey (rowOK 3 level3) level4rlr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rlrl && everyKey (rowOK 3 level3) level4rlrr) = true
  rw [level4rlrl_ok, level4rlrr_ok]
  decide +kernel
def level4rl : BinaryTree (List W) := .node [v375, v1094, v1154, v1483, v1578] level4rll level4rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rl_ok : everyKey (rowOK 3 level3) level4rl = true := by
  change (_ && everyKey (rowOK 3 level3) level4rll && everyKey (rowOK 3 level3) level4rlr) = true
  rw [level4rll_ok, level4rlr_ok]
  decide +kernel
def level4rrll : BinaryTree (List W) := (.node [v480, v897, v1163, v1308, v1483] (.node [v443, v609, v1094, v1308, v1483] (.node [v443, v558, v1094, v1308, v1483] (.node [v442, v629, v1094, v1308, v1483] (.node [v442, v597, v1094, v1308, v1483] .nil .nil) (.node [v443, v554, v1094, v1308, v1483] .nil .nil)) (.node [v443, v575, v1094, v1308, v1483] (.node [v443, v572, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v480, v803, v1094, v1308, v1483] (.node [v459, v777, v1094, v1308, v1483] (.node [v443, v629, v1094, v1304, v1483] .nil .nil) (.node [v480, v777, v1094, v1308, v1483] .nil .nil)) (.node [v480, v897, v1094, v1412, v1483] (.node [v480, v897, v1094, v1308, v1381] .nil .nil) .nil))) (.node [v558, v897, v1094, v1308, v1381] (.node [v497, v897, v1094, v1412, v1483] (.node [v497, v803, v1094, v1308, v1483] (.node [v497, v777, v1094, v1308, v1483] .nil .nil) (.node [v497, v897, v1094, v1308, v1381] .nil .nil)) (.node [v554, v897, v1094, v1412, v1483] (.node [v497, v897, v1163, v1308, v1483] .nil .nil) .nil)) (.node [v629, v694, v758, v897, v1094] (.node [v575, v897, v1094, v1308, v1381] (.node [v572, v897, v1094, v1412, v1483] .nil .nil) .nil) (.node [v629, v694, v897, v1094, v1417] (.node [v629, v694, v897, v1094, v1373] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrll_ok : everyKey (rowOK 3 level3) level4rrll = true := by decide +kernel
def level4rrlr : BinaryTree (List W) := (.node [v629, v805, v1308, v1390, v1483] (.node [v629, v784, v897, v1131, v1483] (.node [v629, v758, v1308, v1436, v1483] (.node [v629, v758, v1022, v1094, v1308] (.node [v629, v758, v841, v897, v1308] .nil .nil) (.node [v629, v758, v1094, v1154, v1483] .nil .nil)) (.node [v629, v779, v784, v897, v1483] (.node [v629, v777, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v629, v803, v1094, v1308, v1483] (.node [v629, v791, v1308, v1383, v1483] (.node [v629, v784, v897, v1365, v1483] .nil .nil) .nil) (.node [v629, v805, v1163, v1308, v1483] (.node [v629, v804, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v629, v872, v1033, v1308, v1483] (.node [v629, v848, v1094, v1139, v1308] (.node [v629, v840, v841, v897, v1308] (.node [v629, v806, v1094, v1308, v1483] .nil .nil) (.node [v629, v841, v842, v897, v1308] .nil .nil)) (.node [v629, v870, v1094, v1308, v1483] (.node [v629, v868, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v629, v897, v1054, v1094, v1483] (.node [v629, v872, v1094, v1308, v1381] (.node [v629, v872, v1094, v1137, v1308] .nil .nil) .nil) (.node [v629, v897, v1094, v1308, v1361] (.node [v629, v897, v1094, v1138, v1308] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrlr_ok : everyKey (rowOK 3 level3) level4rrlr = true := by decide +kernel
def level4rrl : BinaryTree (List W) := .node [v629, v758, v784, v897, v1483] level4rrll level4rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrl_ok : everyKey (rowOK 3 level3) level4rrl = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrll && everyKey (rowOK 3 level3) level4rrlr) = true
  rw [level4rrll_ok, level4rrlr_ok]
  decide +kernel
def level4rrrl : BinaryTree (List W) := (.node [v629, v1094, v1308, v1394, v1483] (.node [v629, v1022, v1094, v1308, v1353] (.node [v629, v897, v1184, v1308, v1483] (.node [v629, v897, v1094, v1422, v1483] (.node [v629, v897, v1094, v1412, v1483] .nil .nil) (.node [v629, v897, v1163, v1308, v1483] .nil .nil)) (.node [v629, v1022, v1094, v1141, v1308] (.node [v629, v897, v1308, v1329, v1483] .nil .nil) .nil)) (.node [v629, v1094, v1136, v1308, v1483] (.node [v629, v1094, v1134, v1154, v1483] (.node [v629, v1026, v1094, v1308, v1381] .nil .nil) .nil) (.node [v629, v1094, v1308, v1344, v1483] (.node [v629, v1094, v1154, v1341, v1483] .nil .nil) .nil))) (.node [v651, v897, v1190, v1308, v1483] (.node [v629, v1308, v1366, v1436, v1483] (.node [v629, v1143, v1308, v1436, v1483] (.node [v629, v1094, v1412, v1448, v1483] .nil .nil) (.node [v629, v1163, v1308, v1483, v1507] .nil .nil)) (.node [v650, v897, v1191, v1308, v1483] (.node [v645, v897, v1194, v1308, v1483] .nil .nil) .nil)) (.node [v682, v897, v1094, v1308, v1381] (.node [v670, v897, v1094, v1280, v1308] (.node [v668, v897, v1094, v1483, v1514] .nil .nil) .nil) (.node [v701, v897, v1119, v1308, v1483] (.node [v698, v897, v1094, v1412, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrrl_ok : everyKey (rowOK 3 level3) level4rrrl = true := by decide +kernel
def level4rrrr : BinaryTree (List W) := (.node [v870, v1094, v1308, v1473, v1483] (.node [v777, v1094, v1215, v1308, v1483] (.node [v758, v897, v1094, v1280, v1308] (.node [v752, v758, v1094, v1308, v1483] (.node [v741, v777, v1094, v1308, v1483] .nil .nil) (.node [v752, v786, v1094, v1308, v1483] .nil .nil)) (.node [v758, v897, v1119, v1308, v1483] (.node [v758, v897, v1094, v1483, v1514] .nil .nil) .nil)) (.node [v803, v1094, v1308, v1483, v1578] (.node [v803, v1094, v1215, v1308, v1483] (.node [v777, v1094, v1308, v1483, v1578] .nil .nil) .nil) (.node [v843, v897, v1094, v1308, v1483] (.node [v831, v897, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v897, v1094, v1308, v1381, v1578] (.node [v897, v1094, v1215, v1412, v1483] (.node [v897, v938, v1094, v1483, v1578] (.node [v870, v1094, v1308, v1483, v1578] .nil .nil) (.node [v897, v1094, v1215, v1308, v1381] .nil .nil)) (.node [v897, v1094, v1308, v1380, v1483] (.node [v897, v1094, v1260, v1308, v1381] .nil .nil) .nil)) (.node [v897, v1094, v1412, v1483, v1578] (.node [v897, v1094, v1412, v1483, v1524] (.node [v897, v1094, v1308, v1414, v1483] .nil .nil) .nil) (.node [v897, v1163, v1308, v1483, v1578] (.node [v897, v1163, v1215, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrrr_ok : everyKey (rowOK 3 level3) level4rrrr = true := by decide +kernel
def level4rrr : BinaryTree (List W) := .node [v701, v971, v1194, v1308, v1483] level4rrrl level4rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rrr_ok : everyKey (rowOK 3 level3) level4rrr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrrl && everyKey (rowOK 3 level3) level4rrrr) = true
  rw [level4rrrl_ok, level4rrrr_ok]
  decide +kernel
def level4rr : BinaryTree (List W) := .node [v629, v897, v1094, v1308, v1381] level4rrl level4rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4rr_ok : everyKey (rowOK 3 level3) level4rr = true := by
  change (_ && everyKey (rowOK 3 level3) level4rrl && everyKey (rowOK 3 level3) level4rrr) = true
  rw [level4rrl_ok, level4rrr_ok]
  decide +kernel
def level4r : BinaryTree (List W) := .node [v441, v629, v1094, v1308, v1483] level4rl level4rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4r_ok : everyKey (rowOK 3 level3) level4r = true := by
  change (_ && everyKey (rowOK 3 level3) level4rl && everyKey (rowOK 3 level3) level4rr) = true
  rw [level4rl_ok, level4rr_ok]
  decide +kernel
def level4 : BinaryTree (List W) := .node [v375, v784, v897, v1483, v1578] level4l level4r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4_ok : everyKey (rowOK 3 level3) level4 = true := by
  change (_ && everyKey (rowOK 3 level3) level4l && everyKey (rowOK 3 level3) level4r) = true
  rw [level4l_ok, level4r_ok]
  decide +kernel
theorem closed4 : Closed 4 level4 := closed_next 3 (by decide) level4 level3 closed3 level4_ok
def level5llllll : BinaryTree (List W) := (.node [v22, v629, v897, v1191, v1308, v1483] (.node [v18, v141, v375, v897, v1094, v1308] (.node [v14, v897, v1094, v1308, v1370, v1483] (.node [v11, v237, v629, v1094, v1308, v1483] (.node [v6, v629, v897, v1094, v1137, v1308] (.node [v3, v375, v897, v1094, v1234, v1308] .nil .nil) .nil) (.node [v13, v375, v1040, v1094, v1308, v1483] (.node [v12, v375, v897, v1094, v1483, v1571] .nil .nil) .nil)) (.node [v17, v375, v897, v1094, v1308, v1483] (.node [v16, v375, v822, v897, v1308, v1483] (.node [v15, v375, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v18, v137, v375, v513, v897, v1094] .nil .nil))) (.node [v18, v375, v897, v1094, v1320, v1483] (.node [v18, v375, v897, v1094, v1308, v1473] (.node [v18, v237, v897, v1094, v1308, v1483] (.node [v18, v147, v375, v897, v1094, v1483] .nil .nil) .nil) (.node [v18, v375, v897, v1094, v1308, v1483] .nil .nil)) (.node [v20, v375, v897, v1094, v1308, v1483] (.node [v19, v375, v897, v1094, v1308, v1483] (.node [v18, v758, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v21, v375, v897, v1094, v1308, v1483] .nil .nil)))) (.node [v36, v375, v629, v1022, v1094, v1308] (.node [v36, v326, v629, v1019, v1094, v1308] (.node [v34, v629, v897, v1094, v1429, v1483] (.node [v33, v629, v897, v1094, v1308, v1356] (.node [v23, v196, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v36, v237, v629, v1019, v1094, v1308] .nil .nil)) (.node [v36, v375, v592, v1019, v1094, v1308] (.node [v36, v375, v497, v1019, v1094, v1308] (.node [v36, v375, v480, v1019, v1094, v1308] .nil .nil) .nil) (.node [v36, v375, v629, v1019, v1094, v1308] .nil .nil))) (.node [v36, v375, v1019, v1094, v1308, v1578] (.node [v36, v375, v897, v1094, v1308, v1473] (.node [v36, v375, v644, v1019, v1094, v1308] (.node [v36, v375, v629, v1094, v1308, v1325] .nil .nil) .nil) (.node [v36, v375, v1019, v1094, v1215, v1308] .nil .nil)) (.node [v38, v629, v897, v1094, v1308, v1483] (.node [v36, v629, v1019, v1094, v1141, v1308] (.node [v36, v629, v758, v1019, v1094, v1308] .nil .nil) .nil) (.node [v39, v480, v897, v1094, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llllll_ok : everyKey (rowOK 4 level4) level5llllll = true := by decide +kernel
def level5lllllr : BinaryTree (List W) := (.node [v64, v629, v872, v1094, v1308, v1483] (.node [v64, v192, v897, v1094, v1308, v1483] (.node [v49, v897, v1094, v1308, v1416, v1483] (.node [v41, v629, v897, v1094, v1308, v1483] (.node [v40, v629, v897, v1094, v1308, v1483] (.node [v40, v497, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v48, v237, v629, v1094, v1308, v1483] .nil .nil)) (.node [v64, v171, v897, v1094, v1308, v1483] (.node [v62, v375, v422, v1094, v1308, v1483] (.node [v50, v375, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v64, v190, v897, v1094, v1308, v1483] .nil .nil))) (.node [v64, v438, v629, v1094, v1308, v1483] (.node [v64, v237, v422, v1094, v1308, v1483] (.node [v64, v196, v897, v1094, v1308, v1483] (.node [v64, v194, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v64, v375, v443, v1094, v1308, v1483] .nil .nil)) (.node [v64, v572, v897, v1094, v1308, v1483] (.node [v64, v558, v897, v1094, v1308, v1483] (.node [v64, v554, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v64, v575, v897, v1094, v1308, v1483] .nil .nil)))) (.node [v67, v629, v897, v1094, v1308, v1483] (.node [v64, v897, v1094, v1308, v1370, v1483] (.node [v64, v796, v897, v1094, v1308, v1483] (.node [v64, v670, v897, v1094, v1308, v1483] (.node [v64, v668, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v64, v833, v897, v1094, v1308, v1483] .nil .nil)) (.node [v66, v375, v897, v1094, v1308, v1483] (.node [v65, v375, v897, v1094, v1308, v1483] (.node [v64, v897, v1094, v1308, v1416, v1483] .nil .nil) .nil) (.node [v67, v597, v897, v1094, v1308, v1483] .nil .nil))) (.node [v70, v584, v897, v1094, v1308, v1483] (.node [v69, v592, v897, v1094, v1308, v1483] (.node [v68, v629, v897, v1094, v1308, v1483] (.node [v68, v588, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v69, v629, v897, v1094, v1308, v1483] .nil .nil)) (.node [v80, v375, v897, v1094, v1215, v1308] (.node [v80, v237, v897, v1094, v1215, v1308] (.node [v70, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v80, v375, v897, v1094, v1234, v1308] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllllr_ok : everyKey (rowOK 4 level4) level5lllllr = true := by decide +kernel
def level5lllll : BinaryTree (List W) := .node [v39, v629, v897, v1094, v1308, v1483] level5llllll level5lllllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllll_ok : everyKey (rowOK 4 level4) level5lllll = true := by
  change (_ && everyKey (rowOK 4 level4) level5llllll && everyKey (rowOK 4 level4) level5lllllr) = true
  rw [level5llllll_ok, level5lllllr_ok]
  decide +kernel
def level5llllrl : BinaryTree (List W) := (.node [v90, v443, v629, v1094, v1308, v1483] (.node [v88, v497, v897, v1205, v1308, v1483] (.node [v82, v375, v897, v1094, v1483, v1571] (.node [v82, v237, v897, v1094, v1483, v1578] (.node [v81, v375, v897, v1094, v1215, v1308] (.node [v80, v758, v897, v1094, v1215, v1308] .nil .nil) .nil) (.node [v82, v375, v897, v1094, v1483, v1514] .nil .nil)) (.node [v88, v438, v629, v1094, v1308, v1483] (.node [v82, v758, v897, v1094, v1483, v1578] (.node [v82, v375, v897, v1094, v1483, v1578] .nil .nil) .nil) (.node [v88, v480, v897, v1205, v1308, v1483] .nil .nil))) (.node [v88, v629, v897, v1191, v1308, v1483] (.node [v88, v629, v897, v1118, v1308, v1483] (.node [v88, v629, v897, v1105, v1308, v1483] (.node [v88, v629, v872, v1094, v1308, v1483] .nil .nil) .nil) (.node [v88, v629, v897, v1163, v1308, v1483] .nil .nil)) (.node [v88, v897, v1205, v1308, v1483, v1578] (.node [v88, v897, v1205, v1215, v1308, v1483] (.node [v88, v629, v897, v1205, v1308, v1483] .nil .nil) .nil) (.node [v90, v375, v897, v1094, v1308, v1473] .nil .nil)))) (.node [v90, v629, v897, v1094, v1308, v1472] (.node [v90, v629, v897, v1094, v1308, v1349] (.node [v90, v558, v897, v1094, v1308, v1349] (.node [v90, v497, v897, v1094, v1308, v1349] (.node [v90, v480, v897, v1094, v1308, v1349] .nil .nil) .nil) (.node [v90, v629, v805, v1094, v1308, v1483] .nil .nil)) (.node [v90, v629, v897, v1094, v1308, v1381] (.node [v90, v629, v897, v1094, v1308, v1356] (.node [v90, v629, v897, v1094, v1308, v1355] .nil .nil) .nil) (.node [v90, v629, v897, v1094, v1308, v1465] .nil .nil))) (.node [v92, v897, v1094, v1308, v1473, v1483] (.node [v90, v897, v1094, v1308, v1349, v1578] (.node [v90, v897, v1094, v1215, v1308, v1349] (.node [v90, v682, v897, v1094, v1308, v1349] .nil .nil) .nil) (.node [v92, v629, v897, v1094, v1308, v1483] .nil .nil)) (.node [v94, v629, v897, v1094, v1308, v1483] (.node [v93, v629, v897, v1094, v1308, v1483] (.node [v92, v897, v1094, v1308, v1483, v1578] .nil .nil) .nil) (.node [v95, v629, v897, v1094, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llllrl_ok : everyKey (rowOK 4 level4) level5llllrl = true := by decide +kernel
def level5llllrr : BinaryTree (List W) := (.node [v102, v758, v1094, v1215, v1308, v1483] (.node [v102, v375, v459, v1094, v1308, v1483] (.node [v99, v497, v897, v1094, v1308, v1483] (.node [v99, v132, v629, v814, v897, v1308] (.node [v98, v629, v897, v1094, v1308, v1483] (.node [v97, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v99, v480, v897, v1094, v1308, v1483] .nil .nil)) (.node [v99, v897, v1094, v1308, v1483, v1578] (.node [v99, v897, v1094, v1215, v1308, v1483] (.node [v99, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v100, v629, v897, v1094, v1308, v1483] .nil .nil))) (.node [v102, v629, v758, v1094, v1308, v1483] (.node [v102, v480, v758, v1094, v1308, v1483] (.node [v102, v413, v629, v1094, v1308, v1483] (.node [v102, v375, v603, v1094, v1308, v1483] .nil .nil) .nil) (.node [v102, v497, v758, v1094, v1308, v1483] .nil .nil)) (.node [v102, v629, v1094, v1308, v1341, v1483] (.node [v102, v629, v1094, v1141, v1308, v1483] (.node [v102, v629, v777, v1094, v1308, v1483] .nil .nil) .nil) (.node [v102, v629, v1094, v1308, v1366, v1483] .nil .nil)))) (.node [v108, v629, v897, v1094, v1316, v1483] (.node [v108, v443, v629, v1094, v1308, v1483] (.node [v104, v375, v629, v1094, v1308, v1483] (.node [v103, v375, v629, v1094, v1308, v1483] (.node [v102, v758, v1094, v1308, v1483, v1578] .nil .nil) .nil) (.node [v104, v629, v840, v1094, v1308, v1483] .nil .nil)) (.node [v108, v554, v897, v1094, v1432, v1483] (.node [v108, v497, v897, v1094, v1432, v1483] (.node [v108, v480, v897, v1094, v1432, v1483] .nil .nil) .nil) (.node [v108, v629, v805, v1094, v1308, v1483] .nil .nil))) (.node [v108, v629, v897, v1094, v1432, v1483] (.node [v108, v629, v897, v1094, v1429, v1483] (.node [v108, v629, v897, v1094, v1412, v1483] (.node [v108, v629, v897, v1094, v1324, v1483] .nil .nil) .nil) (.node [v108, v629, v897, v1094, v1431, v1483] .nil .nil)) (.node [v108, v897, v1094, v1432, v1483, v1578] (.node [v108, v897, v1094, v1215, v1432, v1483] (.node [v108, v698, v897, v1094, v1432, v1483] .nil .nil) .nil) (.node [v112, v506, v897, v1094, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llllrr_ok : everyKey (rowOK 4 level4) level5llllrr = true := by decide +kernel
def level5llllr : BinaryTree (List W) := .node [v96, v629, v897, v1094, v1308, v1483] level5llllrl level5llllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llllr_ok : everyKey (rowOK 4 level4) level5llllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llllrl && everyKey (rowOK 4 level4) level5llllrr) = true
  rw [level5llllrl_ok, level5llllrr_ok]
  decide +kernel
def level5llll : BinaryTree (List W) := .node [v80, v375, v897, v1094, v1280, v1308] level5lllll level5llllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llll_ok : everyKey (rowOK 4 level4) level5llll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lllll && everyKey (rowOK 4 level4) level5llllr) = true
  rw [level5lllll_ok, level5llllr_ok]
  decide +kernel
def level5lllrll : BinaryTree (List W) := (.node [v114, v629, v897, v1094, v1308, v1483] (.node [v113, v558, v897, v1094, v1308, v1483] (.node [v113, v473, v897, v1094, v1308, v1483] (.node [v113, v415, v897, v1094, v1308, v1483] (.node [v113, v190, v897, v1094, v1308, v1483] (.node [v113, v185, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v113, v422, v897, v1094, v1308, v1483] .nil .nil)) (.node [v113, v497, v897, v1094, v1308, v1483] (.node [v113, v497, v897, v1094, v1215, v1308] (.node [v113, v480, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v113, v497, v897, v1094, v1308, v1536] .nil .nil))) (.node [v113, v729, v897, v1094, v1308, v1483] (.node [v113, v708, v897, v1094, v1308, v1483] (.node [v113, v670, v897, v1094, v1308, v1483] (.node [v113, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v113, v722, v897, v1094, v1308, v1483] .nil .nil)) (.node [v113, v897, v1094, v1308, v1483, v1578] (.node [v113, v897, v1094, v1308, v1483, v1571] (.node [v113, v897, v1094, v1215, v1308, v1483] .nil .nil) .nil) (.node [v114, v497, v897, v1094, v1308, v1483] .nil .nil)))) (.node [v118, v473, v897, v1094, v1308, v1483] (.node [v117, v897, v1094, v1308, v1320, v1483] (.node [v117, v629, v897, v1094, v1308, v1483] (.node [v116, v629, v897, v1094, v1308, v1483] (.node [v115, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v117, v897, v1094, v1215, v1308, v1483] .nil .nil)) (.node [v118, v414, v897, v1094, v1308, v1483] (.node [v118, v190, v897, v1094, v1308, v1483] (.node [v118, v183, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v118, v422, v897, v1094, v1308, v1483] .nil .nil))) (.node [v118, v554, v897, v1094, v1308, v1483] (.node [v118, v480, v897, v1094, v1483, v1578] (.node [v118, v480, v897, v1094, v1308, v1483] (.node [v118, v480, v897, v1094, v1252, v1483] .nil .nil) .nil) (.node [v118, v497, v897, v1094, v1308, v1483] .nil .nil)) (.node [v118, v708, v897, v1094, v1308, v1483] (.node [v118, v668, v897, v1094, v1308, v1483] (.node [v118, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v118, v722, v897, v1094, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrll_ok : everyKey (rowOK 4 level4) level5lllrll = true := by decide +kernel
def level5lllrlr : BinaryTree (List W) := (.node [v125, v897, v1094, v1308, v1483, v1578] (.node [v122, v480, v897, v1094, v1308, v1483] (.node [v119, v480, v897, v1094, v1308, v1483] (.node [v118, v897, v1094, v1308, v1483, v1578] (.node [v118, v897, v1094, v1234, v1308, v1483] (.node [v118, v897, v1094, v1215, v1308, v1483] .nil .nil) .nil) (.node [v119, v473, v897, v1094, v1308, v1483] .nil .nil)) (.node [v120, v629, v897, v1094, v1308, v1483] (.node [v119, v629, v897, v1094, v1308, v1483] (.node [v119, v497, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v121, v629, v897, v1094, v1308, v1483] .nil .nil))) (.node [v125, v480, v897, v1094, v1308, v1483] (.node [v123, v629, v897, v1094, v1308, v1483] (.node [v123, v497, v897, v1094, v1308, v1483] (.node [v122, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v124, v629, v897, v1094, v1308, v1483] .nil .nil)) (.node [v125, v629, v897, v1094, v1308, v1483] (.node [v125, v629, v897, v1003, v1406, v1483] (.node [v125, v497, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v125, v897, v1094, v1215, v1308, v1483] .nil .nil)))) (.node [v132, v375, v629, v814, v864, v1308] (.node [v132, v237, v629, v814, v897, v1308] (.node [v127, v629, v897, v1094, v1308, v1483] (.node [v127, v480, v897, v1094, v1308, v1483] (.node [v126, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v128, v629, v897, v1094, v1308, v1483] .nil .nil)) (.node [v132, v375, v497, v814, v897, v1308] (.node [v132, v375, v480, v814, v897, v1308] (.node [v132, v283, v629, v814, v897, v1308] .nil .nil) .nil) (.node [v132, v375, v535, v814, v897, v1308] .nil .nil))) (.node [v132, v375, v685, v814, v897, v1308] (.node [v132, v375, v629, v841, v897, v1308] (.node [v132, v375, v629, v814, v937, v1308] (.node [v132, v375, v629, v814, v897, v1308] .nil .nil) .nil) (.node [v132, v375, v629, v897, v1308, v1407] .nil .nil)) (.node [v132, v375, v897, v1094, v1308, v1473] (.node [v132, v375, v814, v897, v1308, v1578] (.node [v132, v375, v814, v897, v1215, v1308] .nil .nil) .nil) (.node [v132, v402, v629, v814, v897, v1308] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrlr_ok : everyKey (rowOK 4 level4) level5lllrlr = true := by decide +kernel
def level5lllrl : BinaryTree (List W) := .node [v118, v730, v897, v1094, v1308, v1483] level5lllrll level5lllrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrl_ok : everyKey (rowOK 4 level4) level5lllrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lllrll && everyKey (rowOK 4 level4) level5lllrlr) = true
  rw [level5lllrll_ok, level5lllrlr_ok]
  decide +kernel
def level5lllrrl : BinaryTree (List W) := (.node [v141, v375, v897, v1094, v1215, v1308] (.node [v137, v375, v506, v513, v897, v1094] (.node [v136, v629, v897, v1094, v1308, v1349] (.node [v134, v375, v897, v1094, v1215, v1308] (.node [v133, v629, v897, v1205, v1308, v1483] (.node [v132, v629, v814, v840, v897, v1308] .nil .nil) .nil) (.node [v135, v375, v897, v1094, v1215, v1308] .nil .nil)) (.node [v137, v375, v480, v513, v897, v1094] (.node [v137, v375, v473, v513, v897, v1094] (.node [v137, v237, v513, v629, v897, v1094] .nil .nil) .nil) (.node [v137, v375, v497, v513, v897, v1094] .nil .nil))) (.node [v137, v375, v629, v694, v897, v1094] (.node [v137, v375, v513, v897, v1094, v1215] (.node [v137, v375, v513, v690, v897, v1094] (.node [v137, v375, v513, v629, v897, v1094] .nil .nil) .nil) (.node [v137, v375, v513, v897, v1094, v1578] .nil .nil)) (.node [v139, v375, v497, v897, v1094, v1308] (.node [v138, v375, v497, v897, v1094, v1308] (.node [v137, v513, v629, v758, v897, v1094] .nil .nil) .nil) (.node [v140, v375, v629, v1019, v1094, v1308] .nil .nil)))) (.node [v151, v375, v897, v1094, v1483, v1578] (.node [v144, v375, v897, v1094, v1308, v1578] (.node [v143, v375, v497, v897, v1094, v1308] (.node [v142, v375, v897, v1094, v1308, v1578] (.node [v142, v375, v629, v897, v1094, v1308] .nil .nil) .nil) (.node [v144, v375, v629, v897, v1094, v1308] .nil .nil)) (.node [v146, v375, v629, v897, v1094, v1308] (.node [v145, v375, v897, v1094, v1308, v1578] (.node [v145, v375, v629, v897, v1094, v1308] .nil .nil) .nil) (.node [v147, v375, v897, v1094, v1483, v1578] .nil .nil))) (.node [v156, v237, v497, v1094, v1308, v1483] (.node [v153, v375, v730, v1094, v1308, v1483] (.node [v153, v237, v629, v1094, v1308, v1483] (.node [v153, v237, v480, v1094, v1308, v1483] .nil .nil) .nil) (.node [v155, v237, v629, v1094, v1308, v1483] .nil .nil)) (.node [v157, v237, v629, v1094, v1308, v1483] (.node [v156, v375, v729, v1094, v1308, v1483] (.node [v156, v237, v629, v1094, v1308, v1483] .nil .nil) .nil) (.node [v159, v237, v422, v1094, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrrl_ok : everyKey (rowOK 4 level4) level5lllrrl = true := by decide +kernel
def level5lllrrr : BinaryTree (List W) := (.node [v162, v480, v668, v1094, v1308, v1483] (.node [v159, v375, v729, v1094, v1308, v1483] (.node [v159, v237, v1094, v1308, v1483, v1578] (.node [v159, v237, v722, v1094, v1308, v1483] (.node [v159, v237, v629, v1094, v1308, v1483] (.node [v159, v237, v497, v1094, v1308, v1483] .nil .nil) .nil) (.node [v159, v237, v1094, v1215, v1308, v1483] .nil .nil)) (.node [v159, v375, v697, v1094, v1308, v1483] (.node [v159, v309, v629, v1094, v1308, v1483] (.node [v159, v296, v722, v1094, v1308, v1483] .nil .nil) .nil) (.node [v159, v375, v722, v1094, v1308, v1483] .nil .nil))) (.node [v159, v722, v758, v1094, v1308, v1483] (.node [v159, v407, v629, v1094, v1308, v1483] (.node [v159, v375, v752, v1094, v1308, v1483] (.node [v159, v375, v730, v1094, v1308, v1483] .nil .nil) .nil) (.node [v159, v413, v722, v1094, v1308, v1483] .nil .nil)) (.node [v162, v375, v480, v1094, v1308, v1483] (.node [v161, v237, v629, v1094, v1308, v1483] (.node [v160, v237, v629, v1094, v1308, v1483] .nil .nil) .nil) (.node [v162, v375, v629, v1094, v1308, v1483] .nil .nil)))) (.node [v166, v375, v497, v1094, v1308, v1483] (.node [v164, v497, v670, v1094, v1308, v1483] (.node [v164, v375, v497, v1094, v1308, v1483] (.node [v163, v375, v629, v1094, v1308, v1483] (.node [v162, v629, v668, v1094, v1308, v1483] .nil .nil) .nil) (.node [v164, v375, v629, v1094, v1308, v1483] .nil .nil)) (.node [v166, v303, v708, v1094, v1308, v1483] (.node [v166, v237, v629, v1094, v1308, v1483] (.node [v164, v629, v670, v1094, v1308, v1483] .nil .nil) .nil) (.node [v166, v375, v480, v1094, v1308, v1483] .nil .nil))) (.node [v166, v629, v758, v1094, v1308, v1483] (.node [v166, v375, v1094, v1308, v1483, v1578] (.node [v166, v375, v1094, v1215, v1308, v1483] (.node [v166, v375, v629, v1094, v1308, v1483] .nil .nil) .nil) (.node [v166, v413, v629, v1094, v1308, v1483] .nil .nil)) (.node [v170, v237, v629, v1094, v1308, v1483] (.node [v169, v629, v897, v1094, v1308, v1483] (.node [v168, v629, v897, v1308, v1390, v1483] .nil .nil) .nil) (.node [v170, v438, v629, v1094, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrrr_ok : everyKey (rowOK 4 level4) level5lllrrr = true := by decide +kernel
def level5lllrr : BinaryTree (List W) := .node [v159, v237, v480, v1094, v1308, v1483] level5lllrrl level5lllrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrr_ok : everyKey (rowOK 4 level4) level5lllrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lllrrl && everyKey (rowOK 4 level4) level5lllrrr) = true
  rw [level5lllrrl_ok, level5lllrrr_ok]
  decide +kernel
def level5lllr : BinaryTree (List W) := .node [v132, v629, v758, v814, v897, v1308] level5lllrl level5lllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllr_ok : everyKey (rowOK 4 level4) level5lllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lllrl && everyKey (rowOK 4 level4) level5lllrr) = true
  rw [level5lllrl_ok, level5lllrr_ok]
  decide +kernel
def level5lll : BinaryTree (List W) := .node [v112, v629, v897, v1094, v1308, v1483] level5llll level5lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lll_ok : everyKey (rowOK 4 level4) level5lll = true := by
  change (_ && everyKey (rowOK 4 level4) level5llll && everyKey (rowOK 4 level4) level5lllr) = true
  rw [level5llll_ok, level5lllr_ok]
  decide +kernel
def level5llrlll : BinaryTree (List W) := (.node [v186, v375, v629, v897, v1308, v1562] (.node [v175, v375, v629, v1308, v1436, v1483] (.node [v175, v237, v629, v1308, v1483, v1554] (.node [v171, v897, v967, v1094, v1308, v1483] (.node [v171, v443, v629, v1094, v1308, v1483] (.node [v171, v237, v629, v1094, v1308, v1483] .nil .nil) .nil) (.node [v172, v629, v897, v1094, v1308, v1483] (.node [v172, v447, v629, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v175, v375, v497, v1308, v1483, v1554] (.node [v175, v375, v480, v1308, v1483, v1554] (.node [v175, v332, v629, v1308, v1483, v1554] .nil .nil) .nil) (.node [v175, v375, v603, v1308, v1483, v1554] .nil .nil))) (.node [v175, v629, v758, v1308, v1483, v1554] (.node [v175, v375, v1251, v1308, v1483, v1554] (.node [v175, v375, v1215, v1308, v1483, v1554] (.node [v175, v375, v629, v1308, v1483, v1554] .nil .nil) .nil) (.node [v175, v375, v1308, v1483, v1554, v1578] .nil .nil)) (.node [v181, v375, v897, v1183, v1308, v1483] (.node [v179, v375, v629, v1308, v1483, v1554] (.node [v175, v629, v1308, v1366, v1483, v1554] .nil .nil) .nil) (.node [v182, v375, v897, v1180, v1308, v1483] .nil .nil)))) (.node [v187, v375, v737, v897, v1215, v1483] (.node [v187, v375, v629, v737, v897, v1483] (.node [v187, v375, v497, v737, v897, v1483] (.node [v187, v375, v480, v737, v897, v1483] (.node [v187, v237, v629, v737, v897, v1483] .nil .nil) .nil) (.node [v187, v375, v584, v737, v897, v1483] .nil .nil)) (.node [v187, v375, v629, v897, v1308, v1561] (.node [v187, v375, v629, v897, v1236, v1483] (.node [v187, v375, v629, v784, v897, v1483] .nil .nil) .nil) (.node [v187, v375, v737, v897, v976, v1483] .nil .nil))) (.node [v190, v897, v967, v1094, v1308, v1483] (.node [v190, v192, v897, v1094, v1308, v1483] (.node [v187, v629, v737, v758, v897, v1483] (.node [v187, v375, v737, v897, v1483, v1578] .nil .nil) .nil) (.node [v190, v443, v629, v1094, v1308, v1483] .nil .nil)) (.node [v192, v629, v897, v1094, v1308, v1483] (.node [v192, v375, v897, v1094, v1308, v1483] (.node [v192, v303, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v192, v708, v897, v1094, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrlll_ok : everyKey (rowOK 4 level4) level5llrlll = true := by decide +kernel
def level5llrllr : BinaryTree (List W) := (.node [v210, v237, v629, v897, v1308, v1483] (.node [v193, v375, v971, v1194, v1308, v1483] (.node [v193, v375, v897, v1119, v1308, v1483] (.node [v193, v298, v897, v1194, v1308, v1483] (.node [v193, v237, v897, v1194, v1308, v1483] (.node [v193, v237, v422, v1094, v1308, v1483] .nil .nil) .nil) (.node [v193, v375, v807, v1194, v1308, v1483] .nil .nil)) (.node [v193, v375, v897, v1192, v1308, v1483] (.node [v193, v375, v897, v1183, v1308, v1483] (.node [v193, v375, v897, v1180, v1308, v1483] .nil .nil) .nil) (.node [v193, v375, v897, v1194, v1308, v1483] .nil .nil))) (.node [v196, v237, v422, v1094, v1308, v1483] (.node [v195, v237, v629, v1094, v1308, v1483] (.node [v193, v758, v897, v1194, v1308, v1483] (.node [v193, v701, v897, v1194, v1308, v1483] .nil .nil) .nil) (.node [v195, v375, v722, v1094, v1308, v1483] .nil .nil)) (.node [v207, v375, v897, v1194, v1308, v1483] (.node [v207, v375, v731, v897, v1308, v1483] (.node [v198, v375, v629, v1308, v1483, v1554] .nil .nil) .nil) (.node [v208, v629, v897, v1205, v1308, v1483] .nil .nil)))) (.node [v210, v375, v897, v1308, v1483, v1530] (.node [v210, v375, v602, v897, v1308, v1483] (.node [v210, v375, v480, v897, v1308, v1483] (.node [v210, v375, v447, v629, v1308, v1483] (.node [v210, v329, v629, v897, v1308, v1483] .nil .nil) .nil) (.node [v210, v375, v497, v897, v1308, v1483] .nil .nil)) (.node [v210, v375, v629, v1308, v1446, v1483] (.node [v210, v375, v629, v897, v1308, v1483] (.node [v210, v375, v629, v897, v1214, v1590] .nil .nil) .nil) (.node [v210, v375, v897, v1215, v1308, v1483] .nil .nil))) (.node [v211, v375, v897, v1215, v1308, v1483] (.node [v210, v629, v897, v1308, v1417, v1483] (.node [v210, v629, v758, v897, v1308, v1483] (.node [v210, v375, v897, v1308, v1483, v1578] .nil .nil) .nil) (.node [v211, v375, v629, v897, v1308, v1483] .nil .nil)) (.node [v213, v375, v897, v1215, v1308, v1483] (.node [v213, v375, v629, v897, v1308, v1483] (.node [v212, v375, v629, v897, v1308, v1483] .nil .nil) .nil) (.node [v214, v375, v629, v897, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrllr_ok : everyKey (rowOK 4 level4) level5llrllr = true := by decide +kernel
def level5llrll : BinaryTree (List W) := .node [v192, v897, v1094, v1308, v1483] level5llrlll level5llrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrll_ok : everyKey (rowOK 4 level4) level5llrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrlll && everyKey (rowOK 4 level4) level5llrllr) = true
  rw [level5llrlll_ok, level5llrllr_ok]
  decide +kernel
def level5llrlrl : BinaryTree (List W) := (.node [v225, v897, v1094, v1242, v1483, v1524] (.node [v225, v497, v897, v1094, v1242, v1483] (.node [v222, v629, v897, v1094, v1295, v1483] (.node [v220, v670, v897, v1094, v1308, v1483] (.node [v218, v375, v897, v1005, v1308, v1483] (.node [v217, v237, v629, v1094, v1308, v1483] .nil .nil) .nil) (.node [v221, v375, v897, v1006, v1308, v1483] .nil .nil)) (.node [v225, v438, v629, v1094, v1308, v1483] (.node [v225, v438, v629, v1094, v1242, v1483] (.node [v223, v629, v897, v1094, v1308, v1502] .nil .nil) .nil) (.node [v225, v480, v897, v1094, v1242, v1483] .nil .nil))) (.node [v225, v629, v897, v1094, v1287, v1483] (.node [v225, v629, v897, v1094, v1242, v1483] (.node [v225, v629, v872, v1094, v1308, v1483] (.node [v225, v572, v897, v1094, v1242, v1483] .nil .nil) .nil) (.node [v225, v629, v897, v1094, v1247, v1483] .nil .nil)) (.node [v225, v629, v1094, v1242, v1448, v1483] (.node [v225, v629, v897, v1094, v1412, v1483] (.node [v225, v629, v897, v1094, v1295, v1483] .nil .nil) .nil) (.node [v225, v897, v1094, v1215, v1242, v1483] .nil .nil)))) (.node [v231, v758, v897, v996, v1308, v1483] (.node [v231, v237, v897, v996, v1308, v1483] (.node [v227, v629, v897, v1076, v1308, v1483] (.node [v226, v651, v897, v1094, v1308, v1483] (.node [v225, v897, v1094, v1242, v1483, v1578] .nil .nil) .nil) (.node [v228, v237, v629, v1094, v1308, v1483] .nil .nil)) (.node [v231, v375, v897, v1006, v1308, v1483] (.node [v231, v375, v897, v1005, v1308, v1483] (.node [v231, v375, v897, v996, v1308, v1483] .nil .nil) .nil) (.node [v231, v375, v897, v1119, v1308, v1483] .nil .nil))) (.node [v234, v447, v629, v1094, v1308, v1483] (.node [v233, v629, v861, v1094, v1308, v1483] (.node [v232, v629, v897, v1094, v1308, v1483] (.node [v232, v629, v864, v1094, v1308, v1483] .nil .nil) .nil) (.node [v233, v629, v897, v1094, v1308, v1483] .nil .nil)) (.node [v235, v629, v897, v1094, v1308, v1483] (.node [v235, v629, v807, v1094, v1308, v1483] (.node [v234, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v236, v629, v888, v1094, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrlrl_ok : everyKey (rowOK 4 level4) level5llrlrl = true := by decide +kernel
def level5llrlrr : BinaryTree (List W) := (.node [v237, v419, v1094, v1308, v1483, v1578] (.node [v237, v415, v629, v1094, v1308, v1483] (.node [v237, v407, v629, v1094, v1308, v1483] (.node [v237, v375, v603, v1094, v1308, v1483] (.node [v237, v375, v459, v1094, v1308, v1483] (.node [v237, v303, v422, v1094, v1308, v1483] .nil .nil) .nil) (.node [v237, v405, v629, v1094, v1308, v1483] .nil .nil)) (.node [v237, v414, v629, v1094, v1308, v1483] (.node [v237, v414, v480, v1094, v1308, v1483] (.node [v237, v413, v629, v1094, v1308, v1483] .nil .nil) .nil) (.node [v237, v415, v497, v1094, v1308, v1483] .nil .nil))) (.node [v237, v419, v629, v1094, v1295, v1483] (.node [v237, v419, v497, v1094, v1308, v1483] (.node [v237, v419, v480, v1094, v1308, v1483] (.node [v237, v418, v629, v1094, v1308, v1483] .nil .nil) .nil) (.node [v237, v419, v629, v1010, v1094, v1483] .nil .nil)) (.node [v237, v419, v629, v1094, v1462, v1483] (.node [v237, v419, v629, v1094, v1429, v1483] (.node [v237, v419, v629, v1094, v1308, v1483] .nil .nil) .nil) (.node [v237, v419, v1094, v1215, v1308, v1483] .nil .nil)))) (.node [v237, v422, v1094, v1308, v1483, v1578] (.node [v237, v422, v629, v1094, v1308, v1483] (.node [v237, v422, v480, v1094, v1308, v1483] (.node [v237, v421, v629, v1094, v1308, v1483] (.node [v237, v420, v629, v1094, v1308, v1483] .nil .nil) .nil) (.node [v237, v422, v497, v1094, v1308, v1483] .nil .nil)) (.node [v237, v422, v996, v1094, v1308, v1483] (.node [v237, v422, v973, v1094, v1308, v1483] (.node [v237, v422, v651, v1094, v1308, v1483] .nil .nil) .nil) (.node [v237, v422, v1094, v1215, v1308, v1483] .nil .nil))) (.node [v237, v443, v629, v1094, v1308, v1483] (.node [v237, v429, v629, v1094, v1308, v1483] (.node [v237, v424, v1094, v1215, v1308, v1483] (.node [v237, v424, v629, v1094, v1308, v1483] .nil .nil) .nil) (.node [v237, v438, v629, v1094, v1308, v1483] .nil .nil)) (.node [v237, v459, v629, v1094, v1308, v1483] (.node [v237, v447, v629, v1094, v1308, v1483] (.node [v237, v445, v629, v1094, v1308, v1483] .nil .nil) .nil) (.node [v237, v459, v897, v1094, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrlrr_ok : everyKey (rowOK 4 level4) level5llrlrr = true := by decide +kernel
def level5llrlr : BinaryTree (List W) := .node [v236, v629, v897, v1094, v1308, v1483] level5llrlrl level5llrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrlr_ok : everyKey (rowOK 4 level4) level5llrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrlrl && everyKey (rowOK 4 level4) level5llrlrr) = true
  rw [level5llrlrl_ok, level5llrlrr_ok]
  decide +kernel
def level5llrl : BinaryTree (List W) := .node [v216, v668, v897, v1094, v1308, v1483] level5llrll level5llrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrl_ok : everyKey (rowOK 4 level4) level5llrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrll && everyKey (rowOK 4 level4) level5llrlr) = true
  rw [level5llrll_ok, level5llrlr_ok]
  decide +kernel
def level5llrrll : BinaryTree (List W) := (.node [v237, v497, v897, v1094, v1215, v1308] (.node [v237, v480, v897, v1094, v1252, v1483] (.node [v237, v471, v629, v1094, v1308, v1483] (.node [v237, v462, v629, v1094, v1308, v1483] (.node [v237, v461, v629, v1094, v1308, v1483] (.node [v237, v459, v1094, v1308, v1483] .nil .nil) .nil) (.node [v237, v469, v629, v1094, v1308, v1483] .nil .nil)) (.node [v237, v480, v791, v1094, v1308, v1483] (.node [v237, v480, v758, v1094, v1308, v1483] (.node [v237, v473, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v237, v480, v848, v1094, v1308, v1483] .nil .nil))) (.node [v237, v480, v1094, v1308, v1462, v1483] (.node [v237, v480, v934, v1094, v1308, v1483] (.node [v237, v480, v897, v1094, v1483, v1578] (.node [v237, v480, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v237, v480, v1019, v1094, v1308, v1483] .nil .nil)) (.node [v237, v497, v791, v1094, v1308, v1483] (.node [v237, v497, v758, v1094, v1308, v1483] (.node [v237, v480, v1094, v1308, v1483, v1554] .nil .nil) .nil) (.node [v237, v497, v848, v1094, v1308, v1483] .nil .nil)))) (.node [v237, v529, v897, v1094, v1308, v1483] (.node [v237, v497, v1094, v1308, v1462, v1483] (.node [v237, v497, v934, v1094, v1308, v1483] (.node [v237, v497, v897, v1094, v1308, v1536] (.node [v237, v497, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v237, v497, v1019, v1094, v1308, v1483] .nil .nil)) (.node [v237, v512, v629, v1094, v1308, v1483] (.node [v237, v506, v897, v1094, v1308, v1483] (.node [v237, v497, v1094, v1308, v1483, v1554] .nil .nil) .nil) (.node [v237, v523, v897, v1094, v1308, v1483] .nil .nil))) (.node [v237, v554, v897, v1094, v1308, v1483] (.node [v237, v537, v897, v1094, v1308, v1483] (.node [v237, v536, v897, v1094, v1308, v1483] (.node [v237, v535, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v237, v539, v897, v1094, v1308, v1483] .nil .nil)) (.node [v237, v575, v897, v1094, v1308, v1483] (.node [v237, v572, v897, v1094, v1308, v1483] (.node [v237, v558, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v237, v584, v897, v1094, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrll_ok : everyKey (rowOK 4 level4) level5llrrll = true := by decide +kernel
def level5llrrlr : BinaryTree (List W) := (.node [v237, v629, v777, v1094, v1308, v1483] (.node [v237, v618, v897, v1094, v1308, v1483] (.node [v237, v602, v897, v1094, v1308, v1483] (.node [v237, v595, v897, v1094, v1308, v1483] (.node [v237, v594, v897, v1094, v1308, v1483] (.node [v237, v592, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v237, v597, v897, v1094, v1308, v1483] .nil .nil)) (.node [v237, v603, v1094, v1308, v1483] (.node [v237, v603, v897, v1094, v1308, v1483] (.node [v237, v603, v629, v1094, v1308, v1483] .nil .nil) .nil) (.node [v237, v603, v1094, v1308, v1483, v1554] .nil .nil))) (.node [v237, v629, v758, v1094, v1308, v1483] (.node [v237, v629, v727, v1094, v1462, v1483] (.node [v237, v629, v717, v1094, v1308, v1483] (.node [v237, v620, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v237, v629, v755, v1094, v1308, v1483] .nil .nil)) (.node [v237, v629, v770, v1094, v1308, v1483] (.node [v237, v629, v769, v1094, v1308, v1483] (.node [v237, v629, v768, v1094, v1308, v1483] .nil .nil) .nil) (.node [v237, v629, v771, v1094, v1308, v1483] .nil .nil)))) (.node [v237, v629, v807, v1094, v1308, v1483] (.node [v237, v629, v791, v1191, v1308, v1483] (.node [v237, v629, v791, v1076, v1308, v1483] (.node [v237, v629, v791, v1027, v1308, v1483] (.node [v237, v629, v790, v1094, v1308, v1483] .nil .nil) .nil) (.node [v237, v629, v791, v1094, v1308, v1483] .nil .nil)) (.node [v237, v629, v793, v1094, v1308, v1483] (.node [v237, v629, v792, v1094, v1308, v1483] (.node [v237, v629, v791, v1308, v1483, v1554] .nil .nil) .nil) (.node [v237, v629, v805, v1094, v1308, v1483] .nil .nil))) (.node [v237, v629, v848, v1019, v1094, v1308] (.node [v237, v629, v824, v897, v1308, v1483] (.node [v237, v629, v820, v1094, v1308, v1483] (.node [v237, v629, v817, v1094, v1308, v1483] .nil .nil) .nil) (.node [v237, v629, v839, v1094, v1308, v1483] .nil .nil)) (.node [v237, v629, v848, v1094, v1308, v1502] (.node [v237, v629, v848, v1094, v1308, v1483] (.node [v237, v629, v848, v1094, v1308, v1356] .nil .nil) .nil) (.node [v237, v629, v848, v1094, v1308, v1504] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrlr_ok : everyKey (rowOK 4 level4) level5llrrlr = true := by decide +kernel
def level5llrrl : BinaryTree (List W) := .node [v237, v588, v897, v1094, v1308, v1483] level5llrrll level5llrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrl_ok : everyKey (rowOK 4 level4) level5llrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrrll && everyKey (rowOK 4 level4) level5llrrlr) = true
  rw [level5llrrll_ok, level5llrrlr_ok]
  decide +kernel
def level5llrrrl : BinaryTree (List W) := (.node [v237, v629, v897, v1084, v1308, v1483] (.node [v237, v629, v859, v1094, v1308, v1483] (.node [v237, v629, v854, v1094, v1308, v1483] (.node [v237, v629, v852, v1094, v1308, v1483] (.node [v237, v629, v851, v1094, v1308, v1483] (.node [v237, v629, v850, v1094, v1308, v1483] .nil .nil) .nil) (.node [v237, v629, v853, v1094, v1308, v1483] .nil .nil)) (.node [v237, v629, v857, v1094, v1308, v1483] (.node [v237, v629, v856, v1094, v1308, v1483] (.node [v237, v629, v855, v1094, v1308, v1483] .nil .nil) .nil) (.node [v237, v629, v858, v1094, v1308, v1483] .nil .nil))) (.node [v237, v629, v897, v954, v1094, v1308] (.node [v237, v629, v872, v1094, v1308, v1483] (.node [v237, v629, v864, v1094, v1308, v1483] (.node [v237, v629, v861, v1094, v1308, v1483] .nil .nil) .nil) (.node [v237, v629, v888, v1094, v1308, v1483] .nil .nil)) (.node [v237, v629, v897, v1080, v1308, v1483] (.node [v237, v629, v897, v1056, v1308, v1562] (.node [v237, v629, v897, v1003, v1406, v1483] .nil .nil) .nil) (.node [v237, v629, v897, v1081, v1308, v1483] .nil .nil)))) (.node [v237, v629, v897, v1308, v1399, v1483] (.node [v237, v629, v897, v1094, v1308, v1501] (.node [v237, v629, v897, v1094, v1308, v1478] (.node [v237, v629, v897, v1094, v1214, v1590] (.node [v237, v629, v897, v1087, v1308, v1483] .nil .nil) .nil) (.node [v237, v629, v897, v1094, v1308, v1483] .nil .nil)) (.node [v237, v629, v897, v1108, v1308, v1483] (.node [v237, v629, v897, v1104, v1308, v1483] (.node [v237, v629, v897, v1094, v1308, v1561] .nil .nil) .nil) (.node [v237, v629, v897, v1190, v1308, v1483] .nil .nil))) (.node [v237, v629, v913, v1094, v1308, v1483] (.node [v237, v629, v909, v1094, v1308, v1483] (.node [v237, v629, v906, v1094, v1308, v1483] (.node [v237, v629, v901, v1094, v1308, v1483] .nil .nil) .nil) (.node [v237, v629, v911, v1094, v1308, v1483] .nil .nil)) (.node [v237, v629, v925, v1094, v1308, v1483] (.node [v237, v629, v922, v1094, v1308, v1483] (.node [v237, v629, v920, v1094, v1308, v1483] .nil .nil) .nil) (.node [v237, v629, v926, v1094, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrrl_ok : everyKey (rowOK 4 level4) level5llrrrl = true := by decide +kernel
def level5llrrrr : BinaryTree (List W) := (.node [v237, v629, v1094, v1137, v1308, v1483] (.node [v237, v629, v1019, v1094, v1308, v1483] (.node [v237, v629, v936, v1094, v1308, v1483] (.node [v237, v629, v933, v1094, v1308, v1483] (.node [v237, v629, v932, v1094, v1308, v1483] (.node [v237, v629, v930, v1094, v1308, v1483] .nil .nil) .nil) (.node [v237, v629, v934, v1094, v1308, v1483] .nil .nil)) (.node [v237, v629, v971, v1094, v1308, v1483] (.node [v237, v629, v949, v1094, v1308, v1483] (.node [v237, v629, v937, v1094, v1308, v1483] .nil .nil) .nil) (.node [v237, v629, v1018, v1094, v1308, v1483] .nil .nil))) (.node [v237, v629, v1043, v1094, v1308, v1483] (.node [v237, v629, v1030, v1094, v1308, v1483] (.node [v237, v629, v1026, v1094, v1308, v1483] (.node [v237, v629, v1024, v1094, v1308, v1483] .nil .nil) .nil) (.node [v237, v629, v1040, v1094, v1308, v1483] .nil .nil)) (.node [v237, v629, v1094, v1100, v1308, v1483] (.node [v237, v629, v1059, v1094, v1308, v1483] (.node [v237, v629, v1044, v1094, v1308, v1483] .nil .nil) .nil) (.node [v237, v629, v1094, v1116, v1308, v1483] .nil .nil)))) (.node [v237, v629, v1094, v1308, v1343, v1483] (.node [v237, v629, v1094, v1308, v1325, v1483] (.node [v237, v629, v1094, v1179, v1308, v1483] (.node [v237, v629, v1094, v1141, v1308, v1483] (.node [v237, v629, v1094, v1139, v1308, v1483] .nil .nil) .nil) (.node [v237, v629, v1094, v1192, v1308, v1483] .nil .nil)) (.node [v237, v629, v1094, v1308, v1332, v1483] (.node [v237, v629, v1094, v1308, v1330, v1483] (.node [v237, v629, v1094, v1308, v1327, v1483] .nil .nil) .nil) (.node [v237, v629, v1094, v1308, v1341, v1483] .nil .nil))) (.node [v237, v629, v1094, v1308, v1425, v1483] (.node [v237, v629, v1094, v1308, v1383, v1483] (.node [v237, v629, v1094, v1308, v1366, v1483] (.node [v237, v629, v1094, v1308, v1346, v1483] .nil .nil) .nil) (.node [v237, v629, v1094, v1308, v1390, v1483] .nil .nil)) (.node [v237, v629, v1094, v1308, v1445, v1483] (.node [v237, v629, v1094, v1308, v1443, v1483] (.node [v237, v629, v1094, v1308, v1442, v1483] .nil .nil) .nil) (.node [v237, v629, v1094, v1308, v1446, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrrr_ok : everyKey (rowOK 4 level4) level5llrrrr = true := by decide +kernel
def level5llrrr : BinaryTree (List W) := .node [v237, v629, v928, v1094, v1308, v1483] level5llrrrl level5llrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrrr_ok : everyKey (rowOK 4 level4) level5llrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrrrl && everyKey (rowOK 4 level4) level5llrrrr) = true
  rw [level5llrrrl_ok, level5llrrrr_ok]
  decide +kernel
def level5llrr : BinaryTree (List W) := .node [v237, v629, v849, v1094, v1308, v1483] level5llrrl level5llrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrr_ok : everyKey (rowOK 4 level4) level5llrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrrl && everyKey (rowOK 4 level4) level5llrrr) = true
  rw [level5llrrl_ok, level5llrrr_ok]
  decide +kernel
def level5llr : BinaryTree (List W) := .node [v237, v459, v934, v1094, v1308, v1483] level5llrl level5llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llr_ok : everyKey (rowOK 4 level4) level5llr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrl && everyKey (rowOK 4 level4) level5llrr) = true
  rw [level5llrl_ok, level5llrr_ok]
  decide +kernel
def level5ll : BinaryTree (List W) := .node [v170, v629, v897, v1015, v1094, v1483] level5lll level5llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5ll_ok : everyKey (rowOK 4 level4) level5ll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lll && everyKey (rowOK 4 level4) level5llr) = true
  rw [level5lll_ok, level5llr_ok]
  decide +kernel
def level5lrllll : BinaryTree (List W) := (.node [v237, v690, v897, v1094, v1308, v1483] (.node [v237, v629, v1094, v1308, v1483, v1546] (.node [v237, v629, v1094, v1308, v1462, v1483] (.node [v237, v629, v1094, v1308, v1453, v1483] (.node [v237, v629, v1094, v1308, v1452, v1483] (.node [v237, v629, v1094, v1308, v1451, v1483] .nil .nil) .nil) (.node [v237, v629, v1094, v1308, v1460, v1483] (.node [v237, v629, v1094, v1308, v1458, v1483] .nil .nil) .nil)) (.node [v237, v629, v1094, v1308, v1470, v1483] (.node [v237, v629, v1094, v1308, v1466, v1483] (.node [v237, v629, v1094, v1308, v1463, v1483] .nil .nil) .nil) (.node [v237, v629, v1094, v1308, v1483, v1507] .nil .nil))) (.node [v237, v637, v897, v1094, v1308, v1483] (.node [v237, v629, v1094, v1308, v1483, v1589] (.node [v237, v629, v1094, v1308, v1483, v1583] (.node [v237, v629, v1094, v1308, v1483, v1554] .nil .nil) .nil) (.node [v237, v636, v897, v1094, v1308, v1483] .nil .nil)) (.node [v237, v682, v897, v1094, v1308, v1483] (.node [v237, v650, v897, v1094, v1308, v1483] (.node [v237, v644, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v237, v685, v897, v1094, v1308, v1483] .nil .nil)))) (.node [v237, v858, v1094, v1308, v1483, v1578] (.node [v237, v758, v1094, v1308, v1483, v1578] (.node [v237, v741, v934, v1094, v1308, v1483] (.node [v237, v741, v897, v1094, v1308, v1483] (.node [v237, v698, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v237, v758, v1094, v1215, v1308, v1483] .nil .nil)) (.node [v237, v848, v1094, v1215, v1308, v1483] (.node [v237, v791, v1094, v1308, v1483, v1578] (.node [v237, v791, v1094, v1215, v1308, v1483] .nil .nil) .nil) (.node [v237, v848, v1094, v1308, v1483, v1578] .nil .nil))) (.node [v237, v897, v1094, v1215, v1308, v1483] (.node [v237, v897, v1094, v1187, v1308, v1483] (.node [v237, v897, v976, v1094, v1308, v1483] (.node [v237, v897, v968, v1094, v1308, v1483] .nil .nil) .nil) (.node [v237, v897, v1094, v1199, v1308, v1483] .nil .nil)) (.node [v237, v897, v1094, v1234, v1308, v1483] (.node [v237, v897, v1094, v1230, v1308, v1483] (.node [v237, v897, v1094, v1224, v1308, v1483] .nil .nil) .nil) (.node [v237, v897, v1094, v1251, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrllll_ok : everyKey (rowOK 4 level4) level5lrllll = true := by decide +kernel
def level5lrlllr : BinaryTree (List W) := (.node [v237, v1094, v1308, v1483, v1554, v1578] (.node [v237, v934, v1094, v1215, v1308, v1483] (.node [v237, v897, v1094, v1308, v1483, v1524] (.node [v237, v897, v1094, v1308, v1320, v1483] (.node [v237, v897, v1094, v1271, v1308, v1483] (.node [v237, v897, v1094, v1262, v1308, v1483] .nil .nil) .nil) (.node [v237, v897, v1094, v1308, v1473, v1483] .nil .nil)) (.node [v237, v897, v1094, v1308, v1483, v1571] (.node [v237, v897, v1094, v1308, v1483, v1567] (.node [v237, v897, v1094, v1308, v1483, v1530] .nil .nil) .nil) (.node [v237, v897, v1094, v1308, v1483, v1578] .nil .nil))) (.node [v237, v1094, v1215, v1308, v1445, v1483] (.node [v237, v1019, v1094, v1308, v1483, v1578] (.node [v237, v1019, v1094, v1215, v1308, v1483] (.node [v237, v934, v1094, v1308, v1483, v1578] .nil .nil) .nil) (.node [v237, v1040, v1094, v1308, v1483, v1578] .nil .nil)) (.node [v237, v1094, v1251, v1308, v1483, v1554] (.node [v237, v1094, v1215, v1308, v1483, v1554] (.node [v237, v1094, v1215, v1308, v1462, v1483] .nil .nil) .nil) (.node [v237, v1094, v1308, v1462, v1483, v1578] .nil .nil)))) (.node [v245, v629, v897, v1094, v1308, v1483] (.node [v240, v629, v1043, v1094, v1308, v1483] (.node [v239, v629, v897, v1094, v1308, v1483] (.node [v238, v897, v1094, v1308, v1483, v1578] (.node [v238, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v240, v629, v897, v1094, v1308, v1483] .nil .nil)) (.node [v243, v629, v897, v1094, v1308, v1483] (.node [v242, v629, v897, v1094, v1308, v1483] (.node [v241, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v244, v629, v897, v1094, v1308, v1483] .nil .nil))) (.node [v249, v419, v629, v1010, v1094, v1483] (.node [v248, v480, v897, v1094, v1308, v1483] (.node [v247, v629, v897, v1094, v1308, v1483] (.node [v246, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v248, v629, v897, v1094, v1308, v1483] .nil .nil)) (.node [v249, v497, v897, v1094, v1308, v1483] (.node [v249, v480, v897, v1094, v1308, v1483] (.node [v249, v419, v629, v1094, v1308, v1483] .nil .nil) .nil) (.node [v249, v529, v897, v1094, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlllr_ok : everyKey (rowOK 4 level4) level5lrlllr = true := by decide +kernel
def level5lrlll : BinaryTree (List W) := .node [v237, v897, v1094, v1260, v1308, v1483] level5lrllll level5lrlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlll_ok : everyKey (rowOK 4 level4) level5lrlll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrllll && everyKey (rowOK 4 level4) level5lrlllr) = true
  rw [level5lrllll_ok, level5lrlllr_ok]
  decide +kernel
def level5lrllrl : BinaryTree (List W) := (.node [v264, v375, v897, v1094, v1308, v1473] (.node [v253, v629, v897, v1094, v1308, v1483] (.node [v249, v897, v1094, v1215, v1308, v1483] (.node [v249, v629, v1094, v1308, v1462, v1483] (.node [v249, v629, v1019, v1094, v1308, v1483] (.node [v249, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v249, v897, v1094, v1199, v1308, v1483] .nil .nil)) (.node [v251, v629, v897, v1094, v1308, v1483] (.node [v250, v629, v897, v1094, v1308, v1483] (.node [v249, v897, v1094, v1308, v1483, v1578] .nil .nil) .nil) (.node [v252, v629, v758, v1094, v1308, v1483] .nil .nil))) (.node [v256, v629, v1094, v1308, v1483] (.node [v256, v629, v1094, v1308, v1365, v1483] (.node [v256, v629, v897, v1094, v1308, v1483] (.node [v256, v375, v629, v1094, v1308, v1483] .nil .nil) .nil) (.node [v256, v629, v1094, v1308, v1406, v1483] .nil .nil)) (.node [v262, v497, v897, v1094, v1308, v1483] (.node [v261, v629, v897, v1094, v1308, v1483] (.node [v259, v375, v629, v1094, v1308, v1483] .nil .nil) .nil) (.node [v262, v629, v897, v1094, v1308, v1483] .nil .nil)))) (.node [v264, v629, v897, v1094, v1308, v1543] (.node [v264, v629, v872, v1094, v1308, v1483] (.node [v264, v497, v897, v1094, v1308, v1544] (.node [v264, v480, v897, v1094, v1308, v1544] (.node [v264, v438, v629, v1094, v1308, v1483] .nil .nil) .nil) (.node [v264, v575, v897, v1094, v1308, v1544] .nil .nil)) (.node [v264, v629, v897, v1094, v1308, v1498] (.node [v264, v629, v897, v1094, v1308, v1381] (.node [v264, v629, v872, v1094, v1308, v1544] .nil .nil) .nil) (.node [v264, v629, v897, v1094, v1308, v1502] .nil .nil))) (.node [v264, v897, v1094, v1308, v1544, v1578] (.node [v264, v897, v1094, v1215, v1308, v1544] (.node [v264, v629, v1026, v1094, v1308, v1544] (.node [v264, v629, v897, v1094, v1308, v1544] .nil .nil) .nil) (.node [v264, v897, v1094, v1260, v1308, v1544] .nil .nil)) (.node [v266, v497, v897, v1060, v1308, v1483] (.node [v266, v480, v897, v1060, v1308, v1483] (.node [v266, v443, v629, v1094, v1308, v1483] .nil .nil) .nil) (.node [v266, v629, v805, v1060, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrllrl_ok : everyKey (rowOK 4 level4) level5lrllrl = true := by decide +kernel
def level5lrllrr : BinaryTree (List W) := (.node [v275, v629, v897, v1094, v1308, v1483] (.node [v268, v629, v897, v1094, v1308, v1483] (.node [v266, v629, v897, v1076, v1308, v1483] (.node [v266, v629, v897, v1074, v1308, v1483] (.node [v266, v629, v897, v1070, v1308, v1483] (.node [v266, v629, v897, v1060, v1308, v1483] .nil .nil) .nil) (.node [v266, v629, v897, v1075, v1308, v1483] .nil .nil)) (.node [v266, v897, v1060, v1215, v1308, v1483] (.node [v266, v629, v1060, v1308, v1483, v1507] (.node [v266, v629, v897, v1163, v1308, v1483] .nil .nil) .nil) (.node [v266, v897, v1060, v1308, v1483, v1578] .nil .nil))) (.node [v271, v629, v897, v1094, v1308, v1483] (.node [v270, v629, v897, v1094, v1308, v1483] (.node [v269, v897, v1094, v1215, v1308, v1483] (.node [v269, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v270, v897, v1094, v1308, v1483, v1578] .nil .nil)) (.node [v273, v897, v1094, v1215, v1308, v1483] (.node [v273, v629, v897, v1094, v1308, v1483] (.node [v272, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v274, v629, v897, v1094, v1308, v1483] .nil .nil)))) (.node [v278, v629, v897, v1094, v1308, v1483] (.node [v277, v629, v791, v1094, v1308, v1483] (.node [v277, v497, v897, v1094, v1308, v1483] (.node [v277, v480, v897, v1094, v1308, v1483] (.node [v276, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v277, v629, v791, v1027, v1308, v1483] .nil .nil)) (.node [v277, v897, v1094, v1215, v1308, v1483] (.node [v277, v629, v1094, v1308, v1483, v1554] (.node [v277, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v277, v897, v1094, v1308, v1483, v1578] .nil .nil))) (.node [v280, v536, v897, v1094, v1308, v1483] (.node [v280, v480, v897, v1094, v1308, v1483] (.node [v279, v629, v897, v1094, v1308, v1483] (.node [v278, v629, v1094, v1308, v1446, v1483] .nil .nil) .nil) (.node [v280, v497, v897, v1094, v1308, v1483] .nil .nil)) (.node [v280, v629, v897, v1003, v1406, v1483] (.node [v280, v629, v897, v954, v1094, v1308] (.node [v280, v629, v861, v1094, v1308, v1483] .nil .nil) .nil) (.node [v280, v629, v897, v1094, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrllrr_ok : everyKey (rowOK 4 level4) level5lrllrr = true := by decide +kernel
def level5lrllr : BinaryTree (List W) := .node [v266, v629, v805, v1094, v1308, v1483] level5lrllrl level5lrllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrllr_ok : everyKey (rowOK 4 level4) level5lrllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrllrl && everyKey (rowOK 4 level4) level5lrllrr) = true
  rw [level5lrllrl_ok, level5lrllrr_ok]
  decide +kernel
def level5lrll : BinaryTree (List W) := .node [v249, v629, v848, v1094, v1308, v1483] level5lrlll level5lrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrll_ok : everyKey (rowOK 4 level4) level5lrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrlll && everyKey (rowOK 4 level4) level5lrllr) = true
  rw [level5lrlll_ok, level5lrllr_ok]
  decide +kernel
def level5lrlrll : BinaryTree (List W) := (.node [v287, v480, v897, v1094, v1308, v1483] (.node [v283, v629, v864, v1094, v1308, v1483] (.node [v281, v629, v897, v1094, v1308, v1483] (.node [v280, v897, v1094, v1215, v1308, v1483] (.node [v280, v897, v1094, v1187, v1308, v1483] (.node [v280, v629, v1094, v1308, v1453, v1483] .nil .nil) .nil) (.node [v280, v897, v1094, v1308, v1483, v1578] .nil .nil)) (.node [v283, v497, v897, v1094, v1308, v1483] (.node [v283, v480, v897, v1094, v1308, v1483] (.node [v282, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v283, v535, v897, v1094, v1308, v1483] .nil .nil))) (.node [v283, v897, v1094, v1308, v1483, v1578] (.node [v283, v685, v897, v1094, v1308, v1483] (.node [v283, v629, v937, v1094, v1308, v1483] (.node [v283, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v283, v897, v1094, v1215, v1308, v1483] .nil .nil)) (.node [v286, v629, v897, v1094, v1308, v1483] (.node [v285, v629, v897, v1094, v1308, v1483] (.node [v284, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v287, v419, v629, v1094, v1308, v1483] .nil .nil)))) (.node [v287, v897, v1094, v1308, v1483, v1578] (.node [v287, v629, v897, v1094, v1308, v1483] (.node [v287, v629, v848, v1094, v1308, v1483] (.node [v287, v539, v897, v1094, v1308, v1483] (.node [v287, v497, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v287, v629, v848, v1094, v1308, v1504] .nil .nil)) (.node [v287, v897, v1094, v1215, v1308, v1483] (.node [v287, v629, v1094, v1308, v1462, v1483] (.node [v287, v629, v1019, v1094, v1308, v1483] .nil .nil) .nil) (.node [v287, v897, v1094, v1230, v1308, v1483] .nil .nil))) (.node [v294, v629, v897, v1094, v1308, v1483] (.node [v290, v629, v897, v1094, v1308, v1483] (.node [v289, v629, v897, v1094, v1308, v1483] (.node [v288, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v291, v629, v897, v1094, v1308, v1483] .nil .nil)) (.node [v296, v480, v897, v1094, v1308, v1483] (.node [v296, v422, v897, v1094, v1308, v1483] (.node [v295, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v296, v497, v897, v1094, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrll_ok : everyKey (rowOK 4 level4) level5lrlrll = true := by decide +kernel
def level5lrlrlr : BinaryTree (List W) := (.node [v303, v443, v708, v1094, v1308, v1483] (.node [v298, v629, v971, v1094, v1308, v1483] (.node [v298, v422, v897, v1094, v1308, v1483] (.node [v296, v897, v1094, v1308, v1483, v1578] (.node [v296, v897, v1094, v1215, v1308, v1483] (.node [v296, v722, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v297, v629, v897, v1094, v1308, v1483] .nil .nil)) (.node [v298, v629, v807, v1094, v1308, v1483] (.node [v298, v497, v897, v1094, v1308, v1483] (.node [v298, v480, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v298, v629, v897, v1094, v1308, v1483] .nil .nil))) (.node [v300, v629, v897, v1094, v1308, v1483] (.node [v298, v897, v1094, v1308, v1483, v1578] (.node [v298, v897, v1094, v1215, v1308, v1483] (.node [v298, v722, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v299, v629, v897, v1094, v1308, v1483] .nil .nil)) (.node [v303, v375, v443, v1094, v1308, v1483] (.node [v302, v629, v897, v1094, v1308, v1483] (.node [v301, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v303, v443, v629, v1094, v1308, v1483] .nil .nil)))) (.node [v306, v629, v897, v1094, v1308, v1483] (.node [v303, v668, v897, v1094, v1308, v1483] (.node [v303, v471, v897, v1094, v1308, v1483] (.node [v303, v443, v1094, v1308, v1483] (.node [v303, v443, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v303, v651, v897, v1094, v1308, v1483] .nil .nil)) (.node [v303, v711, v897, v1094, v1308, v1483] (.node [v303, v708, v897, v1094, v1308, v1483] (.node [v303, v670, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v305, v629, v897, v1094, v1308, v1483] .nil .nil))) (.node [v309, v422, v897, v1094, v1308, v1483] (.node [v309, v375, v422, v1094, v1308, v1483] (.node [v307, v629, v897, v1094, v1308, v1483] (.node [v306, v629, v971, v1094, v1308, v1483] .nil .nil) .nil) (.node [v309, v422, v629, v1094, v1308, v1483] .nil .nil)) (.node [v309, v480, v897, v1094, v1308, v1483] (.node [v309, v422, v1094, v1308, v1483] (.node [v309, v422, v973, v1094, v1308, v1483] .nil .nil) .nil) (.node [v309, v497, v897, v1094, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrlr_ok : everyKey (rowOK 4 level4) level5lrlrlr = true := by decide +kernel
def level5lrlrl : BinaryTree (List W) := .node [v296, v629, v897, v1094, v1308, v1483] level5lrlrll level5lrlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrl_ok : everyKey (rowOK 4 level4) level5lrlrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrlrll && everyKey (rowOK 4 level4) level5lrlrlr) = true
  rw [level5lrlrll_ok, level5lrlrlr_ok]
  decide +kernel
def level5lrlrrl : BinaryTree (List W) := (.node [v326, v629, v897, v1094, v1308, v1483] (.node [v316, v629, v897, v1094, v1308, v1483] (.node [v309, v897, v1094, v1308, v1483, v1578] (.node [v309, v722, v897, v1094, v1308, v1483] (.node [v309, v629, v1094, v1308, v1483, v1554] (.node [v309, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v309, v897, v1094, v1215, v1308, v1483] .nil .nil)) (.node [v314, v629, v897, v1094, v1308, v1483] (.node [v312, v629, v897, v1094, v1308, v1483] (.node [v310, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v315, v629, v897, v1094, v1308, v1483] .nil .nil))) (.node [v325, v629, v897, v1094, v1308, v1483] (.node [v323, v629, v897, v1094, v1308, v1483] (.node [v322, v897, v1094, v1207, v1308, v1483] (.node [v322, v708, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v324, v629, v897, v1094, v1308, v1483] .nil .nil)) (.node [v326, v497, v897, v1094, v1308, v1483] (.node [v326, v480, v897, v1094, v1308, v1483] (.node [v325, v629, v937, v1094, v1308, v1483] .nil .nil) .nil) (.node [v326, v629, v791, v1094, v1308, v1483] .nil .nil)))) (.node [v329, v629, v897, v1094, v1214, v1590] (.node [v327, v629, v1094, v1308, v1453, v1483] (.node [v326, v897, v1094, v1308, v1483, v1578] (.node [v326, v897, v1094, v1215, v1308, v1483] (.node [v326, v629, v1094, v1308, v1483, v1554] .nil .nil) .nil) (.node [v327, v629, v897, v1094, v1308, v1483] .nil .nil)) (.node [v329, v497, v897, v1094, v1308, v1483] (.node [v329, v480, v897, v1094, v1308, v1483] (.node [v329, v447, v629, v1094, v1308, v1483] .nil .nil) .nil) (.node [v329, v602, v897, v1094, v1308, v1483] .nil .nil))) (.node [v329, v897, v1094, v1308, v1483, v1530] (.node [v329, v629, v1094, v1308, v1446, v1483] (.node [v329, v629, v897, v1308, v1399, v1483] (.node [v329, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v329, v897, v1094, v1215, v1308, v1483] .nil .nil)) (.node [v331, v629, v897, v1094, v1308, v1483] (.node [v330, v629, v897, v1094, v1308, v1483] (.node [v329, v897, v1094, v1308, v1483, v1578] .nil .nil) .nil) (.node [v332, v419, v629, v1094, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrrl_ok : everyKey (rowOK 4 level4) level5lrlrrl = true := by decide +kernel
def level5lrlrrr : BinaryTree (List W) := (.node [v347, v897, v1094, v1308, v1483, v1587] (.node [v333, v629, v897, v1094, v1308, v1483] (.node [v332, v629, v1019, v1094, v1308, v1483] (.node [v332, v629, v848, v1094, v1308, v1483] (.node [v332, v603, v897, v1094, v1308, v1483] (.node [v332, v497, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v332, v629, v897, v1094, v1308, v1483] .nil .nil)) (.node [v332, v897, v1094, v1251, v1308, v1483] (.node [v332, v897, v1094, v1215, v1308, v1483] (.node [v332, v629, v1094, v1308, v1462, v1483] .nil .nil) .nil) (.node [v332, v897, v1094, v1308, v1483, v1578] .nil .nil))) (.node [v336, v897, v1094, v1215, v1308, v1483] (.node [v335, v897, v1094, v1215, v1308, v1483] (.node [v335, v629, v897, v1094, v1308, v1483] (.node [v334, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v336, v629, v897, v1094, v1308, v1483] .nil .nil)) (.node [v339, v629, v897, v1094, v1308, v1483] (.node [v338, v897, v1094, v1215, v1308, v1483] (.node [v338, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v347, v708, v897, v1094, v1308, v1483] .nil .nil)))) (.node [v353, v629, v897, v1094, v1308, v1483] (.node [v350, v629, v897, v1094, v1308, v1483] (.node [v349, v629, v897, v1094, v1308, v1483] (.node [v348, v629, v897, v1094, v1308, v1483] (.node [v348, v497, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v350, v497, v897, v1094, v1308, v1483] .nil .nil)) (.node [v352, v629, v897, v1094, v1308, v1483] (.node [v352, v480, v897, v1094, v1308, v1483] (.node [v351, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v353, v497, v897, v1094, v1308, v1483] .nil .nil))) (.node [v355, v629, v791, v1094, v1308, v1483] (.node [v355, v497, v897, v1094, v1308, v1483] (.node [v355, v480, v897, v1094, v1308, v1483] (.node [v354, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v355, v629, v727, v1094, v1462, v1483] .nil .nil)) (.node [v355, v897, v1094, v1215, v1308, v1483] (.node [v355, v629, v1094, v1308, v1483, v1554] (.node [v355, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v355, v897, v1094, v1308, v1483, v1578] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrrr_ok : everyKey (rowOK 4 level4) level5lrlrrr = true := by decide +kernel
def level5lrlrr : BinaryTree (List W) := .node [v332, v480, v897, v1094, v1308, v1483] level5lrlrrl level5lrlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrr_ok : everyKey (rowOK 4 level4) level5lrlrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrlrrl && everyKey (rowOK 4 level4) level5lrlrrr) = true
  rw [level5lrlrrl_ok, level5lrlrrr_ok]
  decide +kernel
def level5lrlr : BinaryTree (List W) := .node [v309, v629, v791, v1094, v1308, v1483] level5lrlrl level5lrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlr_ok : everyKey (rowOK 4 level4) level5lrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrlrl && everyKey (rowOK 4 level4) level5lrlrr) = true
  rw [level5lrlrl_ok, level5lrlrr_ok]
  decide +kernel
def level5lrl : BinaryTree (List W) := .node [v280, v629, v897, v1094, v1308, v1561] level5lrll level5lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrl_ok : everyKey (rowOK 4 level4) level5lrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrll && everyKey (rowOK 4 level4) level5lrlr) = true
  rw [level5lrll_ok, level5lrlr_ok]
  decide +kernel
def level5lrrlll : BinaryTree (List W) := (.node [v365, v897, v1094, v1271, v1308, v1483] (.node [v365, v480, v897, v1094, v1308, v1483] (.node [v360, v629, v897, v1094, v1308, v1483] (.node [v358, v629, v897, v1094, v1308, v1483] (.node [v357, v629, v897, v1094, v1308, v1483] (.node [v356, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v359, v629, v897, v1094, v1308, v1483] .nil .nil)) (.node [v363, v629, v897, v1094, v1308, v1483] (.node [v362, v629, v897, v1094, v1308, v1483] (.node [v361, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v364, v629, v897, v1094, v1308, v1483] .nil .nil))) (.node [v365, v629, v897, v1087, v1308, v1483] (.node [v365, v629, v824, v897, v1308, v1483] (.node [v365, v620, v897, v1094, v1308, v1483] (.node [v365, v497, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v365, v629, v888, v1094, v1308, v1483] .nil .nil)) (.node [v365, v629, v1043, v1094, v1308, v1483] (.node [v365, v629, v897, v1094, v1308, v1483] (.node [v365, v629, v897, v1094, v1214, v1590] .nil .nil) .nil) (.node [v365, v897, v1094, v1215, v1308, v1483] .nil .nil)))) (.node [v371, v897, v1094, v1308, v1483, v1578] (.node [v368, v629, v897, v1094, v1308, v1483] (.node [v367, v629, v897, v1094, v1308, v1483] (.node [v366, v629, v897, v1094, v1308, v1483] (.node [v365, v897, v1094, v1308, v1483, v1578] .nil .nil) .nil) (.node [v368, v480, v897, v1094, v1308, v1483] .nil .nil)) (.node [v370, v897, v1094, v1308, v1483, v1578] (.node [v370, v629, v897, v1094, v1308, v1483] (.node [v369, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v371, v629, v897, v1094, v1308, v1483] .nil .nil))) (.node [v375, v414, v948, v1094, v1308, v1483] (.node [v373, v629, v897, v1094, v1308, v1483] (.node [v372, v897, v1094, v1308, v1483, v1578] (.node [v372, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v374, v629, v897, v1094, v1308, v1483] .nil .nil)) (.node [v375, v417, v897, v1094, v1308, v1483] (.node [v375, v416, v897, v1094, v1308, v1483] (.node [v375, v415, v951, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v419, v480, v1010, v1094, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrlll_ok : everyKey (rowOK 4 level4) level5lrrlll = true := by decide +kernel
def level5lrrllr : BinaryTree (List W) := (.node [v375, v426, v897, v1094, v1308, v1483] (.node [v375, v422, v651, v1094, v1308, v1483] (.node [v375, v419, v629, v1094, v1294, v1483] (.node [v375, v419, v629, v1012, v1094, v1483] (.node [v375, v419, v629, v1010, v1094, v1483] (.node [v375, v419, v529, v1010, v1094, v1483] .nil .nil) .nil) (.node [v375, v419, v629, v1094, v1154, v1483] .nil .nil)) (.node [v375, v419, v1010, v1094, v1215, v1483] (.node [v375, v419, v1010, v1094, v1199, v1483] (.node [v375, v419, v629, v1094, v1295, v1483] .nil .nil) .nil) (.node [v375, v419, v1010, v1094, v1483, v1578] .nil .nil))) (.node [v375, v422, v971, v1094, v1308, v1483] (.node [v375, v422, v948, v1094, v1308, v1483] (.node [v375, v422, v922, v1094, v1308, v1483] (.node [v375, v422, v752, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v422, v951, v1094, v1308, v1483] .nil .nil)) (.node [v375, v424, v973, v1094, v1308, v1483] (.node [v375, v423, v897, v1094, v1308, v1483] (.node [v375, v422, v973, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v424, v989, v1094, v1308, v1483] .nil .nil)))) (.node [v375, v438, v629, v1094, v1308, v1483] (.node [v375, v435, v480, v1094, v1308, v1483] (.node [v375, v432, v629, v1094, v1308, v1483] (.node [v375, v431, v629, v1094, v1308, v1483] (.node [v375, v430, v629, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v434, v629, v1094, v1308, v1483] .nil .nil)) (.node [v375, v438, v497, v1094, v1308, v1483] (.node [v375, v438, v480, v1094, v1308, v1483] (.node [v375, v435, v629, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v438, v572, v1094, v1308, v1483] .nil .nil))) (.node [v375, v440, v629, v1094, v1308, v1483] (.node [v375, v438, v1094, v1308, v1483, v1578] (.node [v375, v438, v1094, v1308, v1483, v1524] (.node [v375, v438, v1094, v1215, v1308, v1483] .nil .nil) .nil) (.node [v375, v440, v497, v1094, v1308, v1483] .nil .nil)) (.node [v375, v443, v629, v1094, v1308, v1483] (.node [v375, v443, v497, v1094, v1308, v1483] (.node [v375, v443, v480, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v443, v1094, v1215, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrllr_ok : everyKey (rowOK 4 level4) level5lrrllr = true := by decide +kernel
def level5lrrll : BinaryTree (List W) := .node [v375, v419, v497, v1010, v1094, v1483] level5lrrlll level5lrrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrll_ok : everyKey (rowOK 4 level4) level5lrrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrlll && everyKey (rowOK 4 level4) level5lrrllr) = true
  rw [level5lrrlll_ok, level5lrrllr_ok]
  decide +kernel
def level5lrrlrl : BinaryTree (List W) := (.node [v375, v454, v629, v1094, v1308, v1483] (.node [v375, v447, v1094, v1308, v1483, v1578] (.node [v375, v447, v629, v1094, v1214, v1590] (.node [v375, v447, v497, v1094, v1308, v1483] (.node [v375, v447, v480, v1094, v1308, v1483] (.node [v375, v444, v629, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v447, v602, v1094, v1308, v1483] .nil .nil)) (.node [v375, v447, v1094, v1215, v1308, v1483] (.node [v375, v447, v629, v1308, v1399, v1483] (.node [v375, v447, v629, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v447, v1094, v1308, v1483, v1530] .nil .nil))) (.node [v375, v451, v1094, v1215, v1308, v1483] (.node [v375, v450, v629, v1094, v1308, v1483] (.node [v375, v449, v629, v1094, v1308, v1483] (.node [v375, v448, v629, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v451, v629, v1094, v1308, v1483] .nil .nil)) (.node [v375, v453, v629, v1094, v1308, v1483] (.node [v375, v452, v1094, v1215, v1308, v1483] (.node [v375, v452, v629, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v453, v1094, v1215, v1308, v1483] .nil .nil)))) (.node [v375, v473, v897, v1094, v1234, v1308] (.node [v375, v460, v897, v1094, v1308, v1483] (.node [v375, v458, v897, v1094, v1308, v1483] (.node [v375, v457, v897, v1094, v1308, v1483] (.node [v375, v456, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v459, v897, v1094, v1308, v1483] .nil .nil)) (.node [v375, v465, v897, v1094, v1308, v1483] (.node [v375, v464, v897, v1094, v1308, v1483] (.node [v375, v463, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v472, v897, v1094, v1308, v1483] .nil .nil))) (.node [v375, v474, v897, v1094, v1308, v1483] (.node [v375, v473, v897, v1094, v1308, v1486] (.node [v375, v473, v897, v1094, v1308, v1483] (.node [v375, v473, v897, v1094, v1302, v1483] .nil .nil) .nil) (.node [v375, v473, v897, v1094, v1483, v1571] .nil .nil)) (.node [v375, v477, v897, v1094, v1308, v1483] (.node [v375, v476, v897, v1094, v1308, v1483] (.node [v375, v475, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v478, v897, v1094, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrlrl_ok : everyKey (rowOK 4 level4) level5lrrlrl = true := by decide +kernel
def level5lrrlrr : BinaryTree (List W) := (.node [v375, v480, v897, v1094, v1252, v1483] (.node [v375, v480, v872, v1094, v1308, v1483] (.node [v375, v480, v811, v1094, v1308, v1483] (.node [v375, v480, v805, v1094, v1308, v1483] (.node [v375, v480, v791, v1027, v1308, v1483] (.node [v375, v480, v727, v1094, v1462, v1483] .nil .nil) .nil) (.node [v375, v480, v807, v1094, v1308, v1483] .nil .nil)) (.node [v375, v480, v861, v1094, v1308, v1483] (.node [v375, v480, v848, v1094, v1308, v1504] (.node [v375, v480, v824, v897, v1308, v1483] .nil .nil) .nil) (.node [v375, v480, v864, v1094, v1308, v1483] .nil .nil))) (.node [v375, v480, v897, v1034, v1308, v1483] (.node [v375, v480, v897, v954, v1094, v1308] (.node [v375, v480, v890, v1094, v1308, v1483] (.node [v375, v480, v888, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v480, v897, v1003, v1406, v1483] .nil .nil)) (.node [v375, v480, v897, v1088, v1308, v1483] (.node [v375, v480, v897, v1087, v1308, v1483] (.node [v375, v480, v897, v1056, v1308, v1562] .nil .nil) .nil) (.node [v375, v480, v897, v1094, v1214, v1590] .nil .nil)))) (.node [v375, v480, v897, v1094, v1308, v1561] (.node [v375, v480, v897, v1094, v1283, v1483] (.node [v375, v480, v897, v1094, v1276, v1483] (.node [v375, v480, v897, v1094, v1275, v1483] (.node [v375, v480, v897, v1094, v1253, v1483] .nil .nil) .nil) (.node [v375, v480, v897, v1094, v1277, v1483] .nil .nil)) (.node [v375, v480, v897, v1094, v1302, v1483] (.node [v375, v480, v897, v1094, v1297, v1483] (.node [v375, v480, v897, v1094, v1293, v1483] .nil .nil) .nil) (.node [v375, v480, v897, v1094, v1308, v1483] .nil .nil))) (.node [v375, v480, v897, v1094, v1424, v1483] (.node [v375, v480, v897, v1094, v1402, v1483] (.node [v375, v480, v897, v1094, v1330, v1483] (.node [v375, v480, v897, v1094, v1311, v1483] .nil .nil) .nil) (.node [v375, v480, v897, v1094, v1403, v1483] .nil .nil)) (.node [v375, v480, v897, v1094, v1483, v1514] (.node [v375, v480, v897, v1094, v1458, v1483] (.node [v375, v480, v897, v1094, v1426, v1483] .nil .nil) .nil) (.node [v375, v480, v897, v1094, v1483, v1571] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrlrr_ok : everyKey (rowOK 4 level4) level5lrrlrr = true := by decide +kernel
def level5lrrlr : BinaryTree (List W) := .node [v375, v479, v897, v1094, v1308, v1483] level5lrrlrl level5lrrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrlr_ok : everyKey (rowOK 4 level4) level5lrrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrlrl && everyKey (rowOK 4 level4) level5lrrlrr) = true
  rw [level5lrrlrl_ok, level5lrrlrr_ok]
  decide +kernel
def level5lrrl : BinaryTree (List W) := .node [v375, v443, v1094, v1308, v1483, v1578] level5lrrll level5lrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrl_ok : everyKey (rowOK 4 level4) level5lrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrll && everyKey (rowOK 4 level4) level5lrrlr) = true
  rw [level5lrrll_ok, level5lrrlr_ok]
  decide +kernel
def level5lrrrll : BinaryTree (List W) := (.node [v375, v487, v897, v1094, v1308, v1483] (.node [v375, v480, v1094, v1308, v1446, v1483] (.node [v375, v480, v937, v1094, v1308, v1483] (.node [v375, v480, v897, v1308, v1399, v1483] (.node [v375, v480, v897, v1178, v1308, v1483] (.node [v375, v480, v897, v1096, v1308, v1483] .nil .nil) .nil) (.node [v375, v480, v899, v1094, v1308, v1483] .nil .nil)) (.node [v375, v480, v1026, v1094, v1308, v1483] (.node [v375, v480, v971, v1094, v1308, v1483] (.node [v375, v480, v947, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v480, v1043, v1094, v1308, v1483] .nil .nil))) (.node [v375, v482, v897, v1094, v1308, v1483] (.node [v375, v480, v1094, v1308, v1483, v1507] (.node [v375, v480, v1094, v1308, v1453, v1483] (.node [v375, v480, v1094, v1308, v1448, v1483] .nil .nil) .nil) (.node [v375, v481, v897, v1094, v1308, v1483] .nil .nil)) (.node [v375, v485, v897, v1094, v1308, v1483] (.node [v375, v484, v897, v1094, v1308, v1483] (.node [v375, v483, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v486, v897, v1094, v1308, v1483] .nil .nil)))) (.node [v375, v497, v727, v1094, v1462, v1483] (.node [v375, v492, v897, v1094, v1308, v1483] (.node [v375, v490, v897, v1094, v1308, v1483] (.node [v375, v489, v897, v1094, v1308, v1483] (.node [v375, v488, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v491, v897, v1094, v1308, v1483] .nil .nil)) (.node [v375, v495, v897, v1094, v1308, v1483] (.node [v375, v494, v897, v1094, v1308, v1483] (.node [v375, v493, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v496, v897, v1094, v1308, v1483] .nil .nil))) (.node [v375, v497, v815, v897, v1094, v1308] (.node [v375, v497, v807, v1094, v1308, v1483] (.node [v375, v497, v805, v1094, v1308, v1483] (.node [v375, v497, v791, v1027, v1308, v1483] .nil .nil) .nil) (.node [v375, v497, v812, v1094, v1308, v1483] .nil .nil)) (.node [v375, v497, v861, v1094, v1308, v1483] (.node [v375, v497, v848, v1094, v1308, v1504] (.node [v375, v497, v824, v897, v1308, v1483] .nil .nil) .nil) (.node [v375, v497, v864, v1094, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrll_ok : everyKey (rowOK 4 level4) level5lrrrll = true := by decide +kernel
def level5lrrrlr : BinaryTree (List W) := (.node [v375, v497, v897, v1094, v1308, v1410] (.node [v375, v497, v897, v1094, v1215, v1308] (.node [v375, v497, v897, v1003, v1406, v1483] (.node [v375, v497, v897, v907, v1094, v1308] (.node [v375, v497, v888, v1094, v1308, v1483] (.node [v375, v497, v880, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v497, v897, v954, v1094, v1308] .nil .nil)) (.node [v375, v497, v897, v1087, v1308, v1483] (.node [v375, v497, v897, v1056, v1308, v1562] (.node [v375, v497, v897, v1035, v1308, v1483] .nil .nil) .nil) (.node [v375, v497, v897, v1094, v1214, v1590] .nil .nil))) (.node [v375, v497, v897, v1094, v1308, v1358] (.node [v375, v497, v897, v1094, v1305, v1483] (.node [v375, v497, v897, v1094, v1280, v1308] (.node [v375, v497, v897, v1094, v1234, v1308] .nil .nil) .nil) (.node [v375, v497, v897, v1094, v1308, v1327] .nil .nil)) (.node [v375, v497, v897, v1094, v1308, v1408] (.node [v375, v497, v897, v1094, v1308, v1360] (.node [v375, v497, v897, v1094, v1308, v1359] .nil .nil) .nil) (.node [v375, v497, v897, v1094, v1308, v1409] .nil .nil)))) (.node [v375, v497, v897, v1094, v1308, v1521] (.node [v375, v497, v897, v1094, v1308, v1486] (.node [v375, v497, v897, v1094, v1308, v1475] (.node [v375, v497, v897, v1094, v1308, v1443] (.node [v375, v497, v897, v1094, v1308, v1442] .nil .nil) .nil) (.node [v375, v497, v897, v1094, v1308, v1483] .nil .nil)) (.node [v375, v497, v897, v1094, v1308, v1510] (.node [v375, v497, v897, v1094, v1308, v1497] (.node [v375, v497, v897, v1094, v1308, v1496] .nil .nil) .nil) (.node [v375, v497, v897, v1094, v1308, v1512] .nil .nil))) (.node [v375, v497, v897, v1094, v1308, v1560] (.node [v375, v497, v897, v1094, v1308, v1535] (.node [v375, v497, v897, v1094, v1308, v1529] (.node [v375, v497, v897, v1094, v1308, v1527] .nil .nil) .nil) (.node [v375, v497, v897, v1094, v1308, v1536] .nil .nil)) (.node [v375, v497, v897, v1094, v1457, v1483] (.node [v375, v497, v897, v1094, v1401, v1483] (.node [v375, v497, v897, v1094, v1308, v1561] .nil .nil) .nil) (.node [v375, v497, v897, v1101, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrlr_ok : everyKey (rowOK 4 level4) level5lrrrlr = true := by decide +kernel
def level5lrrrl : BinaryTree (List W) := .node [v375, v497, v872, v1094, v1308, v1483] level5lrrrll level5lrrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrl_ok : everyKey (rowOK 4 level4) level5lrrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrrll && everyKey (rowOK 4 level4) level5lrrrlr) = true
  rw [level5lrrrll_ok, level5lrrrlr_ok]
  decide +kernel
def level5lrrrrl : BinaryTree (List W) := (.node [v375, v506, v897, v1094, v1308, v1483] (.node [v375, v497, v1094, v1308, v1453, v1483] (.node [v375, v497, v971, v1094, v1308, v1483] (.node [v375, v497, v937, v1094, v1308, v1483] (.node [v375, v497, v903, v1094, v1308, v1483] (.node [v375, v497, v897, v1308, v1399, v1483] .nil .nil) .nil) (.node [v375, v497, v946, v1094, v1308, v1483] .nil .nil)) (.node [v375, v497, v1094, v1308, v1446, v1483] (.node [v375, v497, v1043, v1094, v1308, v1483] (.node [v375, v497, v1026, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v497, v1094, v1308, v1448, v1483] .nil .nil))) (.node [v375, v501, v897, v1094, v1308, v1483] (.node [v375, v499, v897, v1094, v1308, v1483] (.node [v375, v498, v897, v1094, v1308, v1483] (.node [v375, v497, v1094, v1308, v1483, v1507] .nil .nil) .nil) (.node [v375, v500, v897, v1094, v1308, v1483] .nil .nil)) (.node [v375, v504, v897, v1094, v1308, v1483] (.node [v375, v503, v897, v1094, v1308, v1483] (.node [v375, v502, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v505, v897, v1094, v1308, v1483] .nil .nil)))) (.node [v375, v513, v897, v1094, v1320, v1483] (.node [v375, v513, v629, v694, v897, v1094] (.node [v375, v510, v897, v1094, v1483, v1578] (.node [v375, v508, v897, v1094, v1308, v1483] (.node [v375, v507, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v511, v897, v1094, v1483, v1578] .nil .nil)) (.node [v375, v513, v897, v1094, v1234, v1308] (.node [v375, v513, v629, v897, v1308, v1399] (.node [v375, v513, v629, v897, v1008, v1094] .nil .nil) .nil) (.node [v375, v513, v897, v1094, v1308, v1473] .nil .nil))) (.node [v375, v520, v629, v897, v1094, v1483] (.node [v375, v517, v897, v1094, v1483, v1578] (.node [v375, v516, v897, v1094, v1483, v1578] (.node [v375, v513, v897, v1094, v1483, v1571] .nil .nil) .nil) (.node [v375, v519, v629, v897, v1094, v1483] .nil .nil)) (.node [v375, v523, v897, v1094, v1308, v1483] (.node [v375, v522, v897, v1094, v1308, v1483] (.node [v375, v521, v897, v1094, v1215, v1308] .nil .nil) .nil) (.node [v375, v524, v897, v1094, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrrl_ok : everyKey (rowOK 4 level4) level5lrrrrl = true := by decide +kernel
def level5lrrrrr : BinaryTree (List W) := (.node [v375, v538, v897, v1094, v1308, v1483] (.node [v375, v535, v864, v1094, v1308, v1483] (.node [v375, v530, v897, v1094, v1308, v1483] (.node [v375, v528, v897, v1094, v1308, v1483] (.node [v375, v527, v897, v1094, v1308, v1483] (.node [v375, v526, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v529, v897, v1094, v1308, v1483] .nil .nil)) (.node [v375, v533, v897, v1094, v1308, v1483] (.node [v375, v532, v897, v1094, v1308, v1483] (.node [v375, v531, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v534, v897, v1094, v1308, v1483] .nil .nil))) (.node [v375, v536, v897, v1003, v1406, v1483] (.node [v375, v536, v861, v1094, v1308, v1483] (.node [v375, v535, v937, v1094, v1308, v1483] (.node [v375, v535, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v536, v897, v954, v1094, v1308] .nil .nil)) (.node [v375, v536, v1094, v1308, v1453, v1483] (.node [v375, v536, v897, v1094, v1308, v1561] (.node [v375, v536, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v537, v897, v1094, v1308, v1483] .nil .nil)))) (.node [v375, v550, v897, v1094, v1308, v1483] (.node [v375, v542, v897, v1094, v1308, v1483] (.node [v375, v540, v897, v1094, v1308, v1483] (.node [v375, v539, v897, v1094, v1308, v1483] (.node [v375, v539, v848, v1094, v1308, v1504] .nil .nil) .nil) (.node [v375, v541, v897, v1094, v1308, v1483] .nil .nil)) (.node [v375, v547, v897, v1094, v1308, v1483] (.node [v375, v546, v897, v1094, v1308, v1483] (.node [v375, v543, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v549, v897, v1094, v1215, v1308] .nil .nil))) (.node [v375, v555, v897, v1094, v1308, v1483] (.node [v375, v553, v897, v1094, v1308, v1483] (.node [v375, v552, v897, v1094, v1308, v1483] (.node [v375, v551, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v554, v897, v1094, v1308, v1483] .nil .nil)) (.node [v375, v558, v897, v1094, v1308, v1483] (.node [v375, v557, v897, v1094, v1308, v1483] (.node [v375, v556, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v559, v897, v1094, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrrr_ok : everyKey (rowOK 4 level4) level5lrrrrr = true := by decide +kernel
def level5lrrrr : BinaryTree (List W) := .node [v375, v525, v897, v1094, v1308, v1483] level5lrrrrl level5lrrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrrr_ok : everyKey (rowOK 4 level4) level5lrrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrrrl && everyKey (rowOK 4 level4) level5lrrrrr) = true
  rw [level5lrrrrl_ok, level5lrrrrr_ok]
  decide +kernel
def level5lrrr : BinaryTree (List W) := .node [v375, v497, v897, v1182, v1308, v1483] level5lrrrl level5lrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrr_ok : everyKey (rowOK 4 level4) level5lrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrrl && everyKey (rowOK 4 level4) level5lrrrr) = true
  rw [level5lrrrl_ok, level5lrrrr_ok]
  decide +kernel
def level5lrr : BinaryTree (List W) := .node [v375, v480, v897, v1094, v1483, v1578] level5lrrl level5lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrr_ok : everyKey (rowOK 4 level4) level5lrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrl && everyKey (rowOK 4 level4) level5lrrr) = true
  rw [level5lrrl_ok, level5lrrr_ok]
  decide +kernel
def level5lr : BinaryTree (List W) := .node [v356, v480, v897, v1094, v1308, v1483] level5lrl level5lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lr_ok : everyKey (rowOK 4 level4) level5lr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrl && everyKey (rowOK 4 level4) level5lrr) = true
  rw [level5lrl_ok, level5lrr_ok]
  decide +kernel
def level5l : BinaryTree (List W) := .node [v237, v629, v1094, v1308, v1448, v1483] level5ll level5lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5l_ok : everyKey (rowOK 4 level4) level5l = true := by
  change (_ && everyKey (rowOK 4 level4) level5ll && everyKey (rowOK 4 level4) level5lr) = true
  rw [level5ll_ok, level5lr_ok]
  decide +kernel
def level5rlllll : BinaryTree (List W) := (.node [v375, v580, v897, v1094, v1308, v1483] (.node [v375, v572, v1094, v1308, v1448, v1483] (.node [v375, v568, v897, v1094, v1308, v1483] (.node [v375, v565, v897, v1094, v1308, v1483] (.node [v375, v564, v897, v1094, v1308, v1483] (.node [v375, v563, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v567, v897, v1094, v1308, v1483] (.node [v375, v566, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v375, v571, v897, v1094, v1308, v1483] (.node [v375, v570, v897, v1094, v1308, v1483] (.node [v375, v569, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v572, v897, v1094, v1308, v1483] .nil .nil))) (.node [v375, v575, v1026, v1094, v1308, v1483] (.node [v375, v575, v872, v1094, v1308, v1483] (.node [v375, v574, v897, v1094, v1308, v1483] (.node [v375, v573, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v575, v897, v1094, v1308, v1483] .nil .nil)) (.node [v375, v578, v897, v1094, v1308, v1483] (.node [v375, v577, v897, v1094, v1308, v1483] (.node [v375, v576, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v579, v897, v1094, v1308, v1483] .nil .nil)))) (.node [v375, v589, v897, v1094, v1308, v1483] (.node [v375, v585, v897, v1094, v1308, v1483] (.node [v375, v583, v897, v1094, v1308, v1483] (.node [v375, v582, v897, v1094, v1308, v1483] (.node [v375, v581, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v584, v897, v1094, v1308, v1483] .nil .nil)) (.node [v375, v588, v727, v1094, v1462, v1483] (.node [v375, v587, v897, v1094, v1308, v1483] (.node [v375, v586, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v588, v897, v1094, v1308, v1483] .nil .nil))) (.node [v375, v594, v897, v1094, v1308, v1483] (.node [v375, v592, v897, v1094, v1308, v1483] (.node [v375, v591, v897, v1094, v1308, v1483] (.node [v375, v590, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v593, v897, v1094, v1308, v1483] .nil .nil)) (.node [v375, v596, v897, v1094, v1308, v1561] (.node [v375, v596, v897, v1094, v1308, v1483] (.node [v375, v595, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v597, v897, v1056, v1308, v1562] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlllll_ok : everyKey (rowOK 4 level4) level5rlllll = true := by decide +kernel
def level5rllllr : BinaryTree (List W) := (.node [v375, v613, v897, v1094, v1308, v1483] (.node [v375, v603, v971, v1094, v1308, v1483] (.node [v375, v602, v897, v1094, v1308, v1483] (.node [v375, v600, v897, v1094, v1308, v1483] (.node [v375, v599, v897, v1094, v1308, v1483] (.node [v375, v598, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v602, v897, v1094, v1214, v1590] .nil .nil)) (.node [v375, v603, v722, v1094, v1308, v1483] (.node [v375, v602, v1094, v1308, v1446, v1483] (.node [v375, v602, v897, v1308, v1399, v1483] .nil .nil) .nil) (.node [v375, v603, v897, v1094, v1308, v1483] .nil .nil))) (.node [v375, v607, v897, v1094, v1308, v1483] (.node [v375, v605, v897, v1094, v1308, v1483] (.node [v375, v604, v897, v1094, v1308, v1483] (.node [v375, v603, v973, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v606, v897, v1094, v1308, v1483] .nil .nil)) (.node [v375, v611, v897, v1094, v1308, v1483] (.node [v375, v610, v897, v1094, v1308, v1483] (.node [v375, v608, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v612, v897, v1094, v1308, v1483] .nil .nil)))) (.node [v375, v620, v897, v1094, v1214, v1590] (.node [v375, v618, v897, v1094, v1308, v1483] (.node [v375, v616, v897, v1094, v1308, v1483] (.node [v375, v615, v897, v1094, v1308, v1483] (.node [v375, v614, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v617, v897, v1094, v1308, v1483] .nil .nil)) (.node [v375, v620, v888, v1094, v1308, v1483] (.node [v375, v620, v824, v897, v1308, v1483] (.node [v375, v619, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v620, v897, v1087, v1308, v1483] .nil .nil))) (.node [v375, v623, v897, v1094, v1308, v1483] (.node [v375, v621, v897, v1094, v1308, v1483] (.node [v375, v620, v1043, v1094, v1308, v1483] (.node [v375, v620, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v622, v897, v1094, v1308, v1483] .nil .nil)) (.node [v375, v626, v897, v1094, v1308, v1483] (.node [v375, v625, v897, v1094, v1308, v1483] (.node [v375, v624, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v627, v897, v1094, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllllr_ok : everyKey (rowOK 4 level4) level5rllllr = true := by decide +kernel
def level5rllll : BinaryTree (List W) := .node [v375, v597, v897, v1094, v1308, v1483] level5rlllll level5rllllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllll_ok : everyKey (rowOK 4 level4) level5rllll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlllll && everyKey (rowOK 4 level4) level5rllllr) = true
  rw [level5rlllll_ok, level5rllllr_ok]
  decide +kernel
def level5rlllrl : BinaryTree (List W) := (.node [v375, v629, v791, v1029, v1308, v1483] (.node [v375, v629, v737, v897, v1427, v1483] (.node [v375, v629, v694, v897, v1094, v1590] (.node [v375, v629, v694, v897, v1094, v1308] (.node [v375, v629, v694, v897, v1094, v1214] (.node [v375, v629, v694, v897, v1094] .nil .nil) .nil) (.node [v375, v629, v694, v897, v1094, v1483] .nil .nil)) (.node [v375, v629, v727, v1094, v1462, v1483] (.node [v375, v629, v727, v1094, v1460, v1483] (.node [v375, v629, v727, v1094, v1154, v1483] .nil .nil) .nil) (.node [v375, v629, v737, v784, v897, v1483] .nil .nil))) (.node [v375, v629, v784, v897, v1308, v1483] (.node [v375, v629, v784, v897, v1003, v1483] (.node [v375, v629, v777, v1094, v1308, v1483] (.node [v375, v629, v752, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v784, v897, v1094, v1483] .nil .nil)) (.node [v375, v629, v791, v1027, v1308, v1483] (.node [v375, v629, v784, v897, v1483] (.node [v375, v629, v784, v897, v1406, v1483] .nil .nil) .nil) (.node [v375, v629, v791, v1028, v1308, v1483] .nil .nil)))) (.node [v375, v629, v805, v1094, v1308, v1483] (.node [v375, v629, v799, v1094, v1308, v1483] (.node [v375, v629, v791, v1308, v1436, v1483] (.node [v375, v629, v791, v1076, v1308, v1483] (.node [v375, v629, v791, v1073, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v798, v1094, v1308, v1483] .nil .nil)) (.node [v375, v629, v802, v1094, v1308, v1483] (.node [v375, v629, v801, v1094, v1308, v1483] (.node [v375, v629, v800, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v803, v1094, v1308, v1483] .nil .nil))) (.node [v375, v629, v812, v1094, v1308, v1483] (.node [v375, v629, v810, v1094, v1308, v1483] (.node [v375, v629, v808, v1094, v1308, v1483] (.node [v375, v629, v807, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v811, v1094, v1308, v1483] .nil .nil)) (.node [v375, v629, v814, v897, v1004, v1308] (.node [v375, v629, v814, v841, v897, v1308] (.node [v375, v629, v813, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v814, v897, v1087, v1308] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlllrl_ok : everyKey (rowOK 4 level4) level5rlllrl = true := by decide +kernel
def level5rlllrr : BinaryTree (List W) := (.node [v375, v629, v848, v1094, v1308, v1504] (.node [v375, v629, v828, v897, v1308, v1483] (.node [v375, v629, v824, v897, v1308, v1483] (.node [v375, v629, v824, v888, v1308, v1483] (.node [v375, v629, v823, v897, v1308, v1483] (.node [v375, v629, v814, v897, v1308, v1561] .nil .nil) .nil) (.node [v375, v629, v824, v897, v1214, v1590] .nil .nil)) (.node [v375, v629, v826, v897, v1308, v1483] (.node [v375, v629, v825, v897, v1308, v1483] (.node [v375, v629, v824, v1043, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v827, v897, v1308, v1483] .nil .nil))) (.node [v375, v629, v841, v897, v1308, v1562] (.node [v375, v629, v841, v897, v1308] (.node [v375, v629, v841, v897, v1094, v1308] (.node [v375, v629, v841, v897, v1056, v1308] .nil .nil) .nil) (.node [v375, v629, v841, v897, v1308, v1483] .nil .nil)) (.node [v375, v629, v848, v1094, v1308, v1502] (.node [v375, v629, v848, v1094, v1308, v1499] (.node [v375, v629, v848, v1022, v1094, v1308] .nil .nil) .nil) (.node [v375, v629, v848, v1094, v1308, v1503] .nil .nil)))) (.node [v375, v629, v866, v1094, v1308, v1483] (.node [v375, v629, v861, v1094, v1308, v1561] (.node [v375, v629, v861, v1003, v1406, v1483] (.node [v375, v629, v861, v954, v1094, v1308] (.node [v375, v629, v860, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v861, v1094, v1308, v1483] .nil .nil)) (.node [v375, v629, v864, v1094, v1308, v1483] (.node [v375, v629, v863, v1094, v1308, v1483] (.node [v375, v629, v862, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v865, v1094, v1308, v1483] .nil .nil))) (.node [v375, v629, v873, v1094, v1308, v1483] (.node [v375, v629, v871, v1094, v1308, v1483] (.node [v375, v629, v869, v1094, v1308, v1483] (.node [v375, v629, v867, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v872, v1094, v1308, v1483] .nil .nil)) (.node [v375, v629, v876, v1094, v1308, v1483] (.node [v375, v629, v875, v1094, v1308, v1483] (.node [v375, v629, v874, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v877, v1094, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlllrr_ok : everyKey (rowOK 4 level4) level5rlllrr = true := by decide +kernel
def level5rlllr : BinaryTree (List W) := .node [v375, v629, v814, v897, v1308, v1500] level5rlllrl level5rlllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlllr_ok : everyKey (rowOK 4 level4) level5rlllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlllrl && everyKey (rowOK 4 level4) level5rlllrr) = true
  rw [level5rlllrl_ok, level5rlllrr_ok]
  decide +kernel
def level5rlll : BinaryTree (List W) := .node [v375, v628, v897, v1094, v1308, v1483] level5rllll level5rlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlll_ok : everyKey (rowOK 4 level4) level5rlll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rllll && everyKey (rowOK 4 level4) level5rlllr) = true
  rw [level5rllll_ok, level5rlllr_ok]
  decide +kernel
def level5rllrll : BinaryTree (List W) := (.node [v375, v629, v896, v1094, v1308, v1483] (.node [v375, v629, v888, v1087, v1308, v1483] (.node [v375, v629, v883, v1094, v1308, v1483] (.node [v375, v629, v881, v1094, v1308, v1483] (.node [v375, v629, v880, v1094, v1308, v1483] (.node [v375, v629, v879, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v882, v1094, v1308, v1483] .nil .nil)) (.node [v375, v629, v886, v1094, v1308, v1483] (.node [v375, v629, v885, v1094, v1308, v1483] (.node [v375, v629, v884, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v887, v1094, v1308, v1483] .nil .nil))) (.node [v375, v629, v891, v1094, v1308, v1483] (.node [v375, v629, v889, v1094, v1308, v1483] (.node [v375, v629, v888, v1094, v1308, v1483] (.node [v375, v629, v888, v1094, v1214, v1590] .nil .nil) .nil) (.node [v375, v629, v890, v1094, v1308, v1483] .nil .nil)) (.node [v375, v629, v894, v1094, v1308, v1483] (.node [v375, v629, v893, v1094, v1308, v1483] (.node [v375, v629, v892, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v895, v1094, v1308, v1483] .nil .nil)))) (.node [v375, v629, v897, v1022, v1094, v1308] (.node [v375, v629, v897, v957, v1094, v1308] (.node [v375, v629, v897, v955, v1094, v1308] (.node [v375, v629, v897, v954, v1094, v1308] (.node [v375, v629, v897, v954, v1003, v1406] .nil .nil) .nil) (.node [v375, v629, v897, v956, v1094, v1308] .nil .nil)) (.node [v375, v629, v897, v1003, v1406, v1483] (.node [v375, v629, v897, v1003, v1405, v1483] (.node [v375, v629, v897, v958, v1094, v1308] .nil .nil) .nil) (.node [v375, v629, v897, v1003, v1406, v1561] .nil .nil))) (.node [v375, v629, v897, v1056, v1308, v1561] (.node [v375, v629, v897, v1035, v1308, v1483] (.node [v375, v629, v897, v1034, v1308, v1483] (.node [v375, v629, v897, v1033, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v897, v1036, v1308, v1483] .nil .nil)) (.node [v375, v629, v897, v1081, v1308, v1483] (.node [v375, v629, v897, v1080, v1308, v1483] (.node [v375, v629, v897, v1056, v1308, v1562] .nil .nil) .nil) (.node [v375, v629, v897, v1082, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrll_ok : everyKey (rowOK 4 level4) level5rllrll = true := by decide +kernel
def level5rllrlr : BinaryTree (List W) := (.node [v375, v629, v897, v1094, v1306, v1483] (.node [v375, v629, v897, v1090, v1308, v1483] (.node [v375, v629, v897, v1087, v1308, v1483] (.node [v375, v629, v897, v1086, v1308, v1483] (.node [v375, v629, v897, v1085, v1308, v1483] (.node [v375, v629, v897, v1084, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v897, v1087, v1214, v1590] .nil .nil)) (.node [v375, v629, v897, v1088, v1308, v1483] (.node [v375, v629, v897, v1087, v1308, v1562] (.node [v375, v629, v897, v1087, v1308, v1561] .nil .nil) .nil) (.node [v375, v629, v897, v1089, v1308, v1483] .nil .nil))) (.node [v375, v629, v897, v1094, v1214, v1590] (.node [v375, v629, v897, v1093, v1308, v1483] (.node [v375, v629, v897, v1092, v1308, v1483] (.node [v375, v629, v897, v1091, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v897, v1094, v1154, v1483] .nil .nil)) (.node [v375, v629, v897, v1094, v1304, v1483] (.node [v375, v629, v897, v1094, v1296, v1590] (.node [v375, v629, v897, v1094, v1280, v1308] .nil .nil) .nil) (.node [v375, v629, v897, v1094, v1305, v1483] .nil .nil)))) (.node [v375, v629, v897, v1094, v1308, v1483] (.node [v375, v629, v897, v1094, v1308, v1478] (.node [v375, v629, v897, v1094, v1308, v1476] (.node [v375, v629, v897, v1094, v1308, v1381] (.node [v375, v629, v897, v1094, v1307, v1483] .nil .nil) .nil) (.node [v375, v629, v897, v1094, v1308, v1477] .nil .nil)) (.node [v375, v629, v897, v1094, v1308, v1481] (.node [v375, v629, v897, v1094, v1308, v1480] (.node [v375, v629, v897, v1094, v1308, v1479] .nil .nil) .nil) (.node [v375, v629, v897, v1094, v1308, v1482] .nil .nil))) (.node [v375, v629, v897, v1094, v1308, v1516] (.node [v375, v629, v897, v1094, v1308, v1501] (.node [v375, v629, v897, v1094, v1308, v1490] (.node [v375, v629, v897, v1094, v1308, v1489] .nil .nil) .nil) (.node [v375, v629, v897, v1094, v1308, v1511] .nil .nil)) (.node [v375, v629, v897, v1094, v1308, v1539] (.node [v375, v629, v897, v1094, v1308, v1528] (.node [v375, v629, v897, v1094, v1308, v1518] .nil .nil) .nil) (.node [v375, v629, v897, v1094, v1308, v1558] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrlr_ok : everyKey (rowOK 4 level4) level5rllrlr = true := by decide +kernel
def level5rllrl : BinaryTree (List W) := .node [v375, v629, v897, v1083, v1308, v1483] level5rllrll level5rllrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrl_ok : everyKey (rowOK 4 level4) level5rllrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rllrll && everyKey (rowOK 4 level4) level5rllrlr) = true
  rw [level5rllrll_ok, level5rllrlr_ok]
  decide +kernel
def level5rllrrl : BinaryTree (List W) := (.node [v375, v629, v897, v1190, v1308, v1483] (.node [v375, v629, v897, v1101, v1308, v1483] (.node [v375, v629, v897, v1094, v1483, v1514] (.node [v375, v629, v897, v1094, v1412, v1483] (.node [v375, v629, v897, v1094, v1401, v1483] (.node [v375, v629, v897, v1094, v1345, v1483] .nil .nil) .nil) (.node [v375, v629, v897, v1094, v1457, v1483] .nil .nil)) (.node [v375, v629, v897, v1097, v1308, v1483] (.node [v375, v629, v897, v1096, v1308, v1483] (.node [v375, v629, v897, v1095, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v897, v1098, v1308, v1483] .nil .nil))) (.node [v375, v629, v897, v1114, v1308, v1483] (.node [v375, v629, v897, v1111, v1308, v1483] (.node [v375, v629, v897, v1108, v1308, v1483] (.node [v375, v629, v897, v1104, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v897, v1113, v1308, v1483] .nil .nil)) (.node [v375, v629, v897, v1178, v1308, v1483] (.node [v375, v629, v897, v1163, v1308, v1483] (.node [v375, v629, v897, v1119, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v897, v1182, v1308, v1483] .nil .nil)))) (.node [v375, v629, v897, v1308, v1399, v1483] (.node [v375, v629, v897, v1308, v1384, v1483] (.node [v375, v629, v897, v1308, v1360, v1562] (.node [v375, v629, v897, v1296, v1406, v1483] (.node [v375, v629, v897, v1214, v1399, v1590] .nil .nil) .nil) (.node [v375, v629, v897, v1308, v1362, v1483] .nil .nil)) (.node [v375, v629, v897, v1308, v1389, v1483] (.node [v375, v629, v897, v1308, v1387, v1483] (.node [v375, v629, v897, v1308, v1386, v1483] .nil .nil) .nil) (.node [v375, v629, v897, v1308, v1396, v1483] .nil .nil))) (.node [v375, v629, v897, v1308, v1436, v1483] (.node [v375, v629, v897, v1308, v1406, v1561] (.node [v375, v629, v897, v1308, v1405, v1562] (.node [v375, v629, v897, v1308, v1399, v1590] .nil .nil) .nil) (.node [v375, v629, v897, v1308, v1420, v1483] .nil .nil)) (.node [v375, v629, v900, v1094, v1308, v1483] (.node [v375, v629, v899, v1094, v1308, v1483] (.node [v375, v629, v898, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v902, v1094, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrrl_ok : everyKey (rowOK 4 level4) level5rllrrl = true := by decide +kernel
def level5rllrrr : BinaryTree (List W) := (.node [v375, v629, v961, v1094, v1308, v1483] (.node [v375, v629, v923, v1094, v1308, v1483] (.node [v375, v629, v916, v1094, v1308, v1483] (.node [v375, v629, v912, v1094, v1308, v1483] (.node [v375, v629, v910, v1094, v1308, v1483] (.node [v375, v629, v908, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v915, v1094, v1308, v1483] .nil .nil)) (.node [v375, v629, v919, v1094, v1308, v1483] (.node [v375, v629, v918, v1094, v1308, v1483] (.node [v375, v629, v917, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v921, v1094, v1308, v1483] .nil .nil))) (.node [v375, v629, v937, v1094, v1308, v1483] (.node [v375, v629, v929, v1094, v1308, v1483] (.node [v375, v629, v927, v1094, v1308, v1483] (.node [v375, v629, v924, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v935, v1094, v1308, v1483] .nil .nil)) (.node [v375, v629, v947, v1094, v1308, v1483] (.node [v375, v629, v946, v1094, v1308, v1483] (.node [v375, v629, v945, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v954, v1094, v1308, v1453] .nil .nil)))) (.node [v375, v629, v1021, v1094, v1308, v1483] (.node [v375, v629, v1010, v1094, v1332, v1483] (.node [v375, v629, v1003, v1406, v1453, v1483] (.node [v375, v629, v980, v1094, v1308, v1483] (.node [v375, v629, v971, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v1010, v1094, v1154, v1483] .nil .nil)) (.node [v375, v629, v1019, v1094, v1308, v1559] (.node [v375, v629, v1019, v1094, v1308, v1538] (.node [v375, v629, v1019, v1022, v1094, v1308] .nil .nil) .nil) (.node [v375, v629, v1020, v1094, v1308, v1483] .nil .nil))) (.node [v375, v629, v1026, v1094, v1308, v1483] (.node [v375, v629, v1022, v1094, v1308, v1504] (.node [v375, v629, v1022, v1094, v1308, v1483] (.node [v375, v629, v1022, v1094, v1308] .nil .nil) .nil) (.node [v375, v629, v1025, v1094, v1308, v1483] .nil .nil)) (.node [v375, v629, v1039, v1094, v1308, v1483] (.node [v375, v629, v1038, v1094, v1308, v1483] (.node [v375, v629, v1027, v1308, v1436, v1483] .nil .nil) .nil) (.node [v375, v629, v1041, v1094, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrrr_ok : everyKey (rowOK 4 level4) level5rllrrr = true := by decide +kernel
def level5rllrr : BinaryTree (List W) := .node [v375, v629, v903, v1094, v1308, v1483] level5rllrrl level5rllrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrr_ok : everyKey (rowOK 4 level4) level5rllrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rllrrl && everyKey (rowOK 4 level4) level5rllrrr) = true
  rw [level5rllrrl_ok, level5rllrrr_ok]
  decide +kernel
def level5rllr : BinaryTree (List W) := .node [v375, v629, v897, v1094, v1308, v1561] level5rllrl level5rllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllr_ok : everyKey (rowOK 4 level4) level5rllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rllrl && everyKey (rowOK 4 level4) level5rllrr) = true
  rw [level5rllrl_ok, level5rllrr_ok]
  decide +kernel
def level5rll : BinaryTree (List W) := .node [v375, v629, v878, v1094, v1308, v1483] level5rlll level5rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rll_ok : everyKey (rowOK 4 level4) level5rll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlll && everyKey (rowOK 4 level4) level5rllr) = true
  rw [level5rlll_ok, level5rllr_ok]
  decide +kernel
def level5rlrlll : BinaryTree (List W) := (.node [v375, v629, v1094, v1308, v1439, v1483] (.node [v375, v629, v1094, v1154, v1462, v1483] (.node [v375, v629, v1048, v1094, v1308, v1483] (.node [v375, v629, v1045, v1094, v1308, v1483] (.node [v375, v629, v1043, v1094, v1308, v1483] (.node [v375, v629, v1043, v1094, v1214, v1590] .nil .nil) .nil) (.node [v375, v629, v1047, v1094, v1308, v1483] (.node [v375, v629, v1046, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v375, v629, v1064, v1308, v1483, v1554] (.node [v375, v629, v1053, v1308, v1483, v1554] (.node [v375, v629, v1049, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v1094, v1154, v1308, v1483] .nil .nil))) (.node [v375, v629, v1094, v1289, v1462, v1483] (.node [v375, v629, v1094, v1237, v1462, v1483] (.node [v375, v629, v1094, v1214, v1446, v1590] (.node [v375, v629, v1094, v1154, v1483] .nil .nil) .nil) (.node [v375, v629, v1094, v1246, v1462, v1483] .nil .nil)) (.node [v375, v629, v1094, v1308, v1437, v1483] (.node [v375, v629, v1094, v1308, v1436, v1483] (.node [v375, v629, v1094, v1308, v1328, v1483] .nil .nil) .nil) (.node [v375, v629, v1094, v1308, v1438, v1483] .nil .nil)))) (.node [v375, v629, v1094, v1308, v1453, v1483] (.node [v375, v629, v1094, v1308, v1446, v1483] (.node [v375, v629, v1094, v1308, v1443, v1504] (.node [v375, v629, v1094, v1308, v1441, v1483] (.node [v375, v629, v1094, v1308, v1440, v1483] .nil .nil) .nil) (.node [v375, v629, v1094, v1308, v1444, v1483] .nil .nil)) (.node [v375, v629, v1094, v1308, v1449, v1483] (.node [v375, v629, v1094, v1308, v1448, v1483] (.node [v375, v629, v1094, v1308, v1447, v1483] .nil .nil) .nil) (.node [v375, v629, v1094, v1308, v1450, v1483] .nil .nil))) (.node [v375, v629, v1094, v1308, v1461, v1483] (.node [v375, v629, v1094, v1308, v1455, v1483] (.node [v375, v629, v1094, v1308, v1454, v1483] (.node [v375, v629, v1094, v1308, v1453, v1561] .nil .nil) .nil) (.node [v375, v629, v1094, v1308, v1456, v1483] .nil .nil)) (.node [v375, v629, v1094, v1308, v1483, v1508] (.node [v375, v629, v1094, v1308, v1483, v1507] (.node [v375, v629, v1094, v1308, v1469, v1483] .nil .nil) .nil) (.node [v375, v629, v1094, v1308, v1483, v1526] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrlll_ok : everyKey (rowOK 4 level4) level5rlrlll = true := by decide +kernel
def level5rlrllr : BinaryTree (List W) := (.node [v375, v644, v897, v1094, v1308, v1483] (.node [v375, v634, v897, v1094, v1308, v1483] (.node [v375, v629, v1308, v1436, v1483, v1554] (.node [v375, v629, v1308, v1399, v1446, v1483] (.node [v375, v629, v1094, v1308, v1483, v1553] (.node [v375, v629, v1094, v1308, v1483, v1552] .nil .nil) .nil) (.node [v375, v629, v1308, v1436, v1483] .nil .nil)) (.node [v375, v632, v897, v1094, v1308, v1483] (.node [v375, v631, v897, v1094, v1308, v1483] (.node [v375, v630, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v633, v897, v1094, v1308, v1483] .nil .nil))) (.node [v375, v639, v897, v1094, v1308, v1483] (.node [v375, v637, v897, v1094, v1308, v1483] (.node [v375, v636, v897, v1094, v1308, v1483] (.node [v375, v635, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v638, v897, v1094, v1308, v1483] .nil .nil)) (.node [v375, v642, v897, v1094, v1308, v1483] (.node [v375, v641, v897, v1094, v1308, v1483] (.node [v375, v640, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v643, v897, v1094, v1308, v1483] .nil .nil)))) (.node [v375, v663, v897, v1094, v1308, v1483] (.node [v375, v657, v897, v1094, v1308, v1483] (.node [v375, v654, v897, v1094, v1308, v1483] (.node [v375, v653, v897, v1094, v1308, v1483] (.node [v375, v650, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v656, v897, v1094, v1308, v1483] .nil .nil)) (.node [v375, v661, v897, v1094, v1308, v1483] (.node [v375, v660, v897, v1094, v1308, v1483] (.node [v375, v658, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v662, v897, v1094, v1308, v1483] .nil .nil))) (.node [v375, v677, v897, v1094, v1308, v1483] (.node [v375, v675, v897, v1094, v1308, v1483] (.node [v375, v673, v897, v1094, v1308, v1483] (.node [v375, v672, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v676, v897, v1094, v1308, v1483] .nil .nil)) (.node [v375, v680, v897, v1094, v1308, v1483] (.node [v375, v679, v897, v1094, v1308, v1483] (.node [v375, v678, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v681, v897, v1094, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrllr_ok : everyKey (rowOK 4 level4) level5rlrllr = true := by decide +kernel
def level5rlrll : BinaryTree (List W) := .node [v375, v629, v1094, v1308, v1483, v1551] level5rlrlll level5rlrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrll_ok : everyKey (rowOK 4 level4) level5rlrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrlll && everyKey (rowOK 4 level4) level5rlrllr) = true
  rw [level5rlrlll_ok, level5rlrllr_ok]
  decide +kernel
def level5rlrlrl : BinaryTree (List W) := (.node [v375, v722, v752, v1094, v1308, v1483] (.node [v375, v690, v897, v1094, v1308, v1483] (.node [v375, v685, v937, v1094, v1308, v1483] (.node [v375, v685, v864, v1094, v1308, v1483] (.node [v375, v684, v897, v1094, v1308, v1483] (.node [v375, v683, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v685, v897, v1094, v1308, v1483] .nil .nil)) (.node [v375, v688, v897, v1094, v1308, v1483] (.node [v375, v687, v897, v1094, v1308, v1483] (.node [v375, v686, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v689, v897, v1094, v1308, v1483] .nil .nil))) (.node [v375, v698, v897, v1094, v1308, v1483] (.node [v375, v693, v897, v1094, v1308, v1483] (.node [v375, v692, v897, v1094, v1308, v1483] (.node [v375, v691, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v696, v897, v1094, v1308, v1483] .nil .nil)) (.node [v375, v720, v1094, v1308, v1445, v1483] (.node [v375, v700, v897, v1094, v1308, v1483] (.node [v375, v699, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v721, v897, v1094, v1308, v1483] .nil .nil)))) (.node [v375, v727, v1094, v1215, v1462, v1483] (.node [v375, v722, v1094, v1308, v1451, v1483] (.node [v375, v722, v1040, v1094, v1308, v1483] (.node [v375, v722, v971, v1094, v1308, v1483] (.node [v375, v722, v920, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v722, v1094, v1308, v1445, v1483] .nil .nil)) (.node [v375, v725, v897, v1094, v1308, v1483] (.node [v375, v724, v897, v1094, v1308, v1483] (.node [v375, v723, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v727, v968, v1094, v1462, v1483] .nil .nil))) (.node [v375, v736, v897, v1094, v1308, v1483] (.node [v375, v735, v897, v1094, v1308, v1483] (.node [v375, v734, v897, v1094, v1308, v1483] (.node [v375, v727, v1094, v1462, v1483, v1578] .nil .nil) .nil) (.node [v375, v736, v897, v954, v1094, v1308] .nil .nil)) (.node [v375, v740, v897, v1094, v1308, v1483] (.node [v375, v739, v897, v1094, v1308, v1483] (.node [v375, v737, v897, v1094, v1483, v1571] .nil .nil) .nil) (.node [v375, v741, v897, v1094, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrlrl_ok : everyKey (rowOK 4 level4) level5rlrlrl = true := by decide +kernel
def level5rlrlrr : BinaryTree (List W) := (.node [v375, v824, v897, v1308, v1483, v1578] (.node [v375, v798, v1094, v1308, v1483, v1578] (.node [v375, v752, v897, v1094, v1308, v1483] (.node [v375, v747, v897, v1094, v1308, v1483] (.node [v375, v746, v897, v1094, v1308, v1483] (.node [v375, v743, v897, v1094, v1483, v1578] .nil .nil) .nil) (.node [v375, v749, v897, v1094, v1483, v1578] .nil .nil)) (.node [v375, v791, v1027, v1215, v1308, v1483] (.node [v375, v752, v1094, v1308, v1483] (.node [v375, v752, v973, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v791, v1027, v1308, v1483, v1578] .nil .nil))) (.node [v375, v807, v1094, v1308, v1483, v1578] (.node [v375, v805, v1094, v1308, v1483, v1578] (.node [v375, v805, v1094, v1215, v1308, v1483] (.node [v375, v801, v1094, v1215, v1308, v1483] .nil .nil) .nil) (.node [v375, v807, v1094, v1215, v1308, v1483] .nil .nil)) (.node [v375, v824, v897, v1215, v1308, v1483] (.node [v375, v823, v897, v1308, v1483, v1578] (.node [v375, v822, v897, v996, v1308, v1483] .nil .nil) .nil) (.node [v375, v824, v897, v1271, v1308, v1483] .nil .nil)))) (.node [v375, v861, v1094, v1215, v1308, v1483] (.node [v375, v848, v1094, v1230, v1308, v1504] (.node [v375, v848, v897, v1094, v1308, v1473] (.node [v375, v827, v897, v1308, v1483, v1578] (.node [v375, v826, v897, v1308, v1483, v1578] .nil .nil) .nil) (.node [v375, v848, v1094, v1215, v1308, v1504] .nil .nil)) (.node [v375, v858, v1094, v1308, v1483, v1586] (.node [v375, v858, v973, v1094, v1308, v1483] (.node [v375, v848, v1094, v1308, v1504, v1578] .nil .nil) .nil) (.node [v375, v861, v1094, v1187, v1308, v1483] .nil .nil))) (.node [v375, v872, v1094, v1260, v1308, v1483] (.node [v375, v864, v1094, v1308, v1483, v1578] (.node [v375, v864, v1094, v1215, v1308, v1483] (.node [v375, v861, v1094, v1308, v1483, v1578] .nil .nil) .nil) (.node [v375, v872, v1094, v1215, v1308, v1483] .nil .nil)) (.node [v375, v888, v1094, v1271, v1308, v1483] (.node [v375, v888, v1094, v1215, v1308, v1483] (.node [v375, v872, v1094, v1308, v1483, v1578] .nil .nil) .nil) (.node [v375, v888, v1094, v1308, v1483, v1578] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrlrr_ok : everyKey (rowOK 4 level4) level5rlrlrr = true := by decide +kernel
def level5rlrlr : BinaryTree (List W) := .node [v375, v742, v897, v1094, v1483, v1578] level5rlrlrl level5rlrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrlr_ok : everyKey (rowOK 4 level4) level5rlrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrlrl && everyKey (rowOK 4 level4) level5rlrlrr) = true
  rw [level5rlrlrl_ok, level5rlrlrr_ok]
  decide +kernel
def level5rlrl : BinaryTree (List W) := .node [v375, v682, v897, v1094, v1308, v1483] level5rlrll level5rlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrl_ok : everyKey (rowOK 4 level4) level5rlrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrll && everyKey (rowOK 4 level4) level5rlrlr) = true
  rw [level5rlrll_ok, level5rlrlr_ok]
  decide +kernel
def level5rlrrll : BinaryTree (List W) := (.node [v375, v897, v970, v1094, v1308, v1483] (.node [v375, v897, v954, v1094, v1187, v1308] (.node [v375, v897, v942, v1094, v1215, v1308] (.node [v375, v897, v931, v1094, v1308, v1483] (.node [v375, v895, v1094, v1308, v1483, v1578] (.node [v375, v894, v1094, v1308, v1483, v1578] .nil .nil) .nil) (.node [v375, v897, v939, v1094, v1308, v1483] .nil .nil)) (.node [v375, v897, v952, v1094, v1308, v1483] (.node [v375, v897, v944, v1094, v1308, v1483] (.node [v375, v897, v943, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v897, v953, v1094, v1215, v1308] .nil .nil))) (.node [v375, v897, v963, v1094, v1308, v1483] (.node [v375, v897, v959, v1094, v1308, v1483] (.node [v375, v897, v954, v1094, v1308, v1578] (.node [v375, v897, v954, v1094, v1215, v1308] .nil .nil) .nil) (.node [v375, v897, v960, v1094, v1308, v1483] .nil .nil)) (.node [v375, v897, v968, v1094, v1308, v1483] (.node [v375, v897, v966, v1094, v1308, v1483] (.node [v375, v897, v964, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v897, v969, v1094, v1308, v1483] .nil .nil)))) (.node [v375, v897, v991, v1094, v1308, v1483] (.node [v375, v897, v981, v1094, v1308, v1483] (.node [v375, v897, v977, v1094, v1308, v1483] (.node [v375, v897, v976, v1094, v1308, v1483] (.node [v375, v897, v974, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v897, v979, v1094, v1308, v1483] .nil .nil)) (.node [v375, v897, v987, v1308, v1397, v1483] (.node [v375, v897, v983, v1094, v1308, v1483] (.node [v375, v897, v982, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v897, v988, v1094, v1308, v1483] .nil .nil))) (.node [v375, v897, v998, v1094, v1308, v1483] (.node [v375, v897, v996, v1308, v1397, v1483] (.node [v375, v897, v996, v1308, v1385, v1483] (.node [v375, v897, v996, v1119, v1308, v1483] .nil .nil) .nil) (.node [v375, v897, v997, v1094, v1308, v1483] .nil .nil)) (.node [v375, v897, v1003, v1406, v1483, v1578] (.node [v375, v897, v1003, v1215, v1406, v1483] (.node [v375, v897, v1003, v1187, v1406, v1483] .nil .nil) .nil) (.node [v375, v897, v1009, v1094, v1483, v1578] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrll_ok : everyKey (rowOK 4 level4) level5rlrrll = true := by decide +kernel
def level5rlrrlr : BinaryTree (List W) := (.node [v375, v897, v1094, v1159, v1308, v1483] (.node [v375, v897, v1085, v1308, v1483, v1578] (.node [v375, v897, v1056, v1215, v1308, v1562] (.node [v375, v897, v1016, v1094, v1483, v1578] (.node [v375, v897, v1015, v1094, v1483, v1578] (.node [v375, v897, v1014, v1094, v1483, v1578] .nil .nil) .nil) (.node [v375, v897, v1056, v1094, v1308, v1473] .nil .nil)) (.node [v375, v897, v1077, v1194, v1308, v1483] (.node [v375, v897, v1056, v1308, v1562, v1578] (.node [v375, v897, v1056, v1262, v1308, v1562] .nil .nil) .nil) (.node [v375, v897, v1077, v1308, v1483, v1594] .nil .nil))) (.node [v375, v897, v1093, v1308, v1483, v1578] (.node [v375, v897, v1087, v1271, v1308, v1483] (.node [v375, v897, v1087, v1215, v1308, v1483] (.node [v375, v897, v1086, v1308, v1483, v1578] .nil .nil) .nil) (.node [v375, v897, v1087, v1308, v1483, v1578] .nil .nil)) (.node [v375, v897, v1094, v1156, v1308, v1483] (.node [v375, v897, v1094, v1155, v1308, v1483] (.node [v375, v897, v1094, v1119, v1308, v1483] .nil .nil) .nil) (.node [v375, v897, v1094, v1158, v1215, v1308] .nil .nil)))) (.node [v375, v897, v1094, v1185, v1308, v1483] (.node [v375, v897, v1094, v1168, v1308, v1483] (.node [v375, v897, v1094, v1165, v1308, v1483] (.node [v375, v897, v1094, v1164, v1308, v1483] (.node [v375, v897, v1094, v1160, v1215, v1308] .nil .nil) .nil) (.node [v375, v897, v1094, v1166, v1308, v1483] .nil .nil)) (.node [v375, v897, v1094, v1175, v1308, v1483] (.node [v375, v897, v1094, v1171, v1308, v1483] (.node [v375, v897, v1094, v1169, v1308, v1483] .nil .nil) .nil) (.node [v375, v897, v1094, v1176, v1308, v1483] .nil .nil))) (.node [v375, v897, v1094, v1195, v1308, v1483] (.node [v375, v897, v1094, v1188, v1308, v1483] (.node [v375, v897, v1094, v1187, v1308, v1561] (.node [v375, v897, v1094, v1187, v1308, v1483] .nil .nil) .nil) (.node [v375, v897, v1094, v1189, v1308, v1483] .nil .nil)) (.node [v375, v897, v1094, v1199, v1308, v1483] (.node [v375, v897, v1094, v1198, v1308, v1483] (.node [v375, v897, v1094, v1196, v1308, v1483] .nil .nil) .nil) (.node [v375, v897, v1094, v1200, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrlr_ok : everyKey (rowOK 4 level4) level5rlrrlr = true := by decide +kernel
def level5rlrrl : BinaryTree (List W) := .node [v375, v897, v1010, v1094, v1483, v1571] level5rlrrll level5rlrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrl_ok : everyKey (rowOK 4 level4) level5rlrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrrll && everyKey (rowOK 4 level4) level5rlrrlr) = true
  rw [level5rlrrll_ok, level5rlrrlr_ok]
  decide +kernel
def level5rlrrrl : BinaryTree (List W) := (.node [v375, v897, v1094, v1215, v1308, v1561] (.node [v375, v897, v1094, v1214, v1530, v1590] (.node [v375, v897, v1094, v1213, v1320, v1483] (.node [v375, v897, v1094, v1211, v1308, v1483] (.node [v375, v897, v1094, v1210, v1308, v1483] (.node [v375, v897, v1094, v1202, v1308, v1483] .nil .nil) .nil) (.node [v375, v897, v1094, v1212, v1308, v1483] .nil .nil)) (.node [v375, v897, v1094, v1214, v1320, v1483] (.node [v375, v897, v1094, v1214, v1271, v1590] (.node [v375, v897, v1094, v1214, v1215, v1590] .nil .nil) .nil) (.node [v375, v897, v1094, v1214, v1483, v1571] .nil .nil))) (.node [v375, v897, v1094, v1215, v1308, v1483] (.node [v375, v897, v1094, v1215, v1308, v1465] (.node [v375, v897, v1094, v1215, v1280, v1308] (.node [v375, v897, v1094, v1214, v1578, v1590] .nil .nil) .nil) (.node [v375, v897, v1094, v1215, v1308, v1473] .nil .nil)) (.node [v375, v897, v1094, v1215, v1308, v1519] (.node [v375, v897, v1094, v1215, v1308, v1517] (.node [v375, v897, v1094, v1215, v1308, v1492] .nil .nil) .nil) (.node [v375, v897, v1094, v1215, v1308, v1520] .nil .nil)))) (.node [v375, v897, v1094, v1225, v1308, v1483] (.node [v375, v897, v1094, v1220, v1308, v1483] (.node [v375, v897, v1094, v1218, v1308, v1483] (.node [v375, v897, v1094, v1217, v1308, v1483] (.node [v375, v897, v1094, v1216, v1308, v1483] .nil .nil) .nil) (.node [v375, v897, v1094, v1219, v1308, v1483] .nil .nil)) (.node [v375, v897, v1094, v1223, v1308, v1483] (.node [v375, v897, v1094, v1222, v1308, v1483] (.node [v375, v897, v1094, v1221, v1308, v1483] .nil .nil) .nil) (.node [v375, v897, v1094, v1224, v1308, v1483] .nil .nil))) (.node [v375, v897, v1094, v1230, v1308, v1483] (.node [v375, v897, v1094, v1228, v1308, v1483] (.node [v375, v897, v1094, v1227, v1308, v1483] (.node [v375, v897, v1094, v1226, v1308, v1483] .nil .nil) .nil) (.node [v375, v897, v1094, v1229, v1308, v1483] .nil .nil)) (.node [v375, v897, v1094, v1233, v1308, v1483] (.node [v375, v897, v1094, v1232, v1308, v1483] (.node [v375, v897, v1094, v1231, v1308, v1483] .nil .nil) .nil) (.node [v375, v897, v1094, v1234, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrrl_ok : everyKey (rowOK 4 level4) level5rlrrrl = true := by decide +kernel
def level5rlrrrr : BinaryTree (List W) := (.node [v375, v897, v1094, v1263, v1308, v1483] (.node [v375, v897, v1094, v1254, v1308, v1483] (.node [v375, v897, v1094, v1248, v1308, v1483] (.node [v375, v897, v1094, v1240, v1308, v1483] (.node [v375, v897, v1094, v1239, v1308, v1483] (.node [v375, v897, v1094, v1238, v1308, v1483] .nil .nil) .nil) (.node [v375, v897, v1094, v1241, v1308, v1483] .nil .nil)) (.node [v375, v897, v1094, v1252, v1320, v1483] (.node [v375, v897, v1094, v1251, v1308, v1483] (.node [v375, v897, v1094, v1250, v1308, v1483] .nil .nil) .nil) (.node [v375, v897, v1094, v1252, v1483, v1514] .nil .nil))) (.node [v375, v897, v1094, v1259, v1308, v1483] (.node [v375, v897, v1094, v1257, v1308, v1483] (.node [v375, v897, v1094, v1256, v1308, v1483] (.node [v375, v897, v1094, v1255, v1308, v1483] .nil .nil) .nil) (.node [v375, v897, v1094, v1258, v1308, v1483] .nil .nil)) (.node [v375, v897, v1094, v1261, v1308, v1561] (.node [v375, v897, v1094, v1261, v1308, v1483] (.node [v375, v897, v1094, v1260, v1308, v1483] .nil .nil) .nil) (.node [v375, v897, v1094, v1262, v1308, v1483] .nil .nil)))) (.node [v375, v897, v1094, v1279, v1483, v1578] (.node [v375, v897, v1094, v1271, v1308, v1483] (.node [v375, v897, v1094, v1268, v1308, v1483] (.node [v375, v897, v1094, v1267, v1308, v1483] (.node [v375, v897, v1094, v1266, v1308, v1483] .nil .nil) .nil) (.node [v375, v897, v1094, v1270, v1308, v1483] .nil .nil)) (.node [v375, v897, v1094, v1274, v1308, v1483] (.node [v375, v897, v1094, v1273, v1308, v1483] (.node [v375, v897, v1094, v1272, v1308, v1483] .nil .nil) .nil) (.node [v375, v897, v1094, v1278, v1483, v1578] .nil .nil))) (.node [v375, v897, v1094, v1284, v1308, v1483] (.node [v375, v897, v1094, v1280, v1308, v1536] (.node [v375, v897, v1094, v1280, v1308, v1483] (.node [v375, v897, v1094, v1280, v1308] .nil .nil) .nil) (.node [v375, v897, v1094, v1281, v1308, v1483] .nil .nil)) (.node [v375, v897, v1094, v1291, v1308, v1483] (.node [v375, v897, v1094, v1286, v1308, v1483] (.node [v375, v897, v1094, v1285, v1308, v1483] .nil .nil) .nil) (.node [v375, v897, v1094, v1292, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrrr_ok : everyKey (rowOK 4 level4) level5rlrrrr = true := by decide +kernel
def level5rlrrr : BinaryTree (List W) := .node [v375, v897, v1094, v1234, v1308, v1590] level5rlrrrl level5rlrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrrr_ok : everyKey (rowOK 4 level4) level5rlrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrrrl && everyKey (rowOK 4 level4) level5rlrrrr) = true
  rw [level5rlrrrl_ok, level5rlrrrr_ok]
  decide +kernel
def level5rlrr : BinaryTree (List W) := .node [v375, v897, v1094, v1201, v1308, v1483] level5rlrrl level5rlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrr_ok : everyKey (rowOK 4 level4) level5rlrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrrl && everyKey (rowOK 4 level4) level5rlrrr) = true
  rw [level5rlrrl_ok, level5rlrrr_ok]
  decide +kernel
def level5rlr : BinaryTree (List W) := .node [v375, v892, v1094, v1308, v1483, v1578] level5rlrl level5rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlr_ok : everyKey (rowOK 4 level4) level5rlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrl && everyKey (rowOK 4 level4) level5rlrr) = true
  rw [level5rlrl_ok, level5rlrr_ok]
  decide +kernel
def level5rl : BinaryTree (List W) := .node [v375, v629, v1043, v1087, v1308, v1483] level5rll level5rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rl_ok : everyKey (rowOK 4 level4) level5rl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rll && everyKey (rowOK 4 level4) level5rlr) = true
  rw [level5rll_ok, level5rlr_ok]
  decide +kernel
def level5rrllll : BinaryTree (List W) := (.node [v375, v897, v1094, v1308, v1482, v1578] (.node [v375, v897, v1094, v1308, v1326, v1483] (.node [v375, v897, v1094, v1308, v1319, v1483] (.node [v375, v897, v1094, v1301, v1308, v1483] (.node [v375, v897, v1094, v1300, v1308, v1483] (.node [v375, v897, v1094, v1299, v1308, v1483] .nil .nil) .nil) (.node [v375, v897, v1094, v1308, v1317, v1483] (.node [v375, v897, v1094, v1308, v1314, v1483] .nil .nil) .nil)) (.node [v375, v897, v1094, v1308, v1322, v1483] (.node [v375, v897, v1094, v1308, v1321, v1483] (.node [v375, v897, v1094, v1308, v1320, v1483] .nil .nil) .nil) (.node [v375, v897, v1094, v1308, v1323, v1483] .nil .nil))) (.node [v375, v897, v1094, v1308, v1473, v1590] (.node [v375, v897, v1094, v1308, v1473, v1483] (.node [v375, v897, v1094, v1308, v1464, v1483] (.node [v375, v897, v1094, v1308, v1459, v1483] .nil .nil) .nil) (.node [v375, v897, v1094, v1308, v1473, v1536] .nil .nil)) (.node [v375, v897, v1094, v1308, v1479, v1578] (.node [v375, v897, v1094, v1308, v1474, v1483] (.node [v375, v897, v1094, v1308, v1473, v1595] .nil .nil) .nil) (.node [v375, v897, v1094, v1308, v1480, v1578] .nil .nil)))) (.node [v375, v897, v1094, v1308, v1483, v1525] (.node [v375, v897, v1094, v1308, v1483, v1509] (.node [v375, v897, v1094, v1308, v1483, v1505] (.node [v375, v897, v1094, v1308, v1483, v1495] (.node [v375, v897, v1094, v1308, v1483, v1494] .nil .nil) .nil) (.node [v375, v897, v1094, v1308, v1483, v1506] .nil .nil)) (.node [v375, v897, v1094, v1308, v1483, v1522] (.node [v375, v897, v1094, v1308, v1483, v1515] (.node [v375, v897, v1094, v1308, v1483, v1514] .nil .nil) .nil) (.node [v375, v897, v1094, v1308, v1483, v1524] .nil .nil))) (.node [v375, v897, v1094, v1308, v1483, v1534] (.node [v375, v897, v1094, v1308, v1483, v1532] (.node [v375, v897, v1094, v1308, v1483, v1531] (.node [v375, v897, v1094, v1308, v1483, v1530] .nil .nil) .nil) (.node [v375, v897, v1094, v1308, v1483, v1533] .nil .nil)) (.node [v375, v897, v1094, v1308, v1483, v1548] (.node [v375, v897, v1094, v1308, v1483, v1547] (.node [v375, v897, v1094, v1308, v1483, v1541] .nil .nil) .nil) (.node [v375, v897, v1094, v1308, v1483, v1549] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrllll_ok : everyKey (rowOK 4 level4) level5rrllll = true := by decide +kernel
def level5rrlllr : BinaryTree (List W) := (.node [v375, v897, v1094, v1308, v1561, v1578] (.node [v375, v897, v1094, v1308, v1483, v1572] (.node [v375, v897, v1094, v1308, v1483, v1566] (.node [v375, v897, v1094, v1308, v1483, v1564] (.node [v375, v897, v1094, v1308, v1483, v1557] (.node [v375, v897, v1094, v1308, v1483, v1556] .nil .nil) .nil) (.node [v375, v897, v1094, v1308, v1483, v1565] .nil .nil)) (.node [v375, v897, v1094, v1308, v1483, v1570] (.node [v375, v897, v1094, v1308, v1483, v1568] (.node [v375, v897, v1094, v1308, v1483, v1567] .nil .nil) .nil) (.node [v375, v897, v1094, v1308, v1483, v1571] .nil .nil))) (.node [v375, v897, v1094, v1308, v1483, v1577] (.node [v375, v897, v1094, v1308, v1483, v1575] (.node [v375, v897, v1094, v1308, v1483, v1574] (.node [v375, v897, v1094, v1308, v1483, v1573] .nil .nil) .nil) (.node [v375, v897, v1094, v1308, v1483, v1576] .nil .nil)) (.node [v375, v897, v1094, v1308, v1483, v1580] (.node [v375, v897, v1094, v1308, v1483, v1579] (.node [v375, v897, v1094, v1308, v1483, v1578] .nil .nil) .nil) (.node [v375, v897, v1094, v1308, v1483, v1581] .nil .nil)))) (.node [v375, v897, v1094, v1483, v1514] (.node [v375, v897, v1094, v1346, v1483, v1578] (.node [v375, v897, v1094, v1318, v1483, v1578] (.node [v375, v897, v1094, v1316, v1483, v1578] (.node [v375, v897, v1094, v1315, v1483, v1578] .nil .nil) .nil) (.node [v375, v897, v1094, v1320, v1483, v1578] .nil .nil)) (.node [v375, v897, v1094, v1460, v1483, v1578] (.node [v375, v897, v1094, v1406, v1483, v1571] (.node [v375, v897, v1094, v1405, v1483, v1578] .nil .nil) .nil) (.node [v375, v897, v1094, v1462, v1483, v1571] .nil .nil))) (.node [v375, v897, v1215, v1308, v1386, v1483] (.node [v375, v897, v1119, v1194, v1308, v1483] (.node [v375, v897, v1111, v1215, v1308, v1483] (.node [v375, v897, v1094, v1483, v1514, v1578] .nil .nil) .nil) (.node [v375, v897, v1119, v1308, v1483] .nil .nil)) (.node [v375, v897, v1308, v1399, v1483, v1530] (.node [v375, v897, v1215, v1308, v1399, v1483] (.node [v375, v897, v1215, v1308, v1396, v1483] .nil .nil) .nil) (.node [v375, v897, v1308, v1399, v1483, v1578] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlllr_ok : everyKey (rowOK 4 level4) level5rrlllr = true := by decide +kernel
def level5rrlll : BinaryTree (List W) := .node [v375, v897, v1094, v1308, v1483, v1550] level5rrllll level5rrlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlll_ok : everyKey (rowOK 4 level4) level5rrlll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrllll && everyKey (rowOK 4 level4) level5rrlllr) = true
  rw [level5rrllll_ok, level5rrlllr_ok]
  decide +kernel
def level5rrllrl : BinaryTree (List W) := (.node [v375, v1094, v1215, v1308, v1453, v1483] (.node [v375, v1043, v1094, v1215, v1308, v1483] (.node [v375, v980, v1094, v1215, v1308, v1483] (.node [v375, v971, v1094, v1215, v1308, v1483] (.node [v375, v937, v1094, v1308, v1483, v1578] (.node [v375, v937, v1094, v1215, v1308, v1483] .nil .nil) .nil) (.node [v375, v971, v1094, v1308, v1483, v1578] .nil .nil)) (.node [v375, v1026, v1094, v1308, v1483, v1578] (.node [v375, v1026, v1094, v1260, v1308, v1483] (.node [v375, v1026, v1094, v1215, v1308, v1483] .nil .nil) .nil) (.node [v375, v1041, v1094, v1308, v1483, v1578] .nil .nil))) (.node [v375, v1094, v1187, v1308, v1453, v1483] (.node [v375, v1046, v1094, v1308, v1483, v1578] (.node [v375, v1043, v1094, v1308, v1483, v1578] (.node [v375, v1043, v1094, v1271, v1308, v1483] .nil .nil) .nil) (.node [v375, v1048, v1094, v1308, v1483, v1578] .nil .nil)) (.node [v375, v1094, v1215, v1308, v1446, v1483] (.node [v375, v1094, v1215, v1308, v1444, v1483] (.node [v375, v1094, v1215, v1308, v1439, v1483] .nil .nil) .nil) (.node [v375, v1094, v1215, v1308, v1448, v1483] .nil .nil)))) (.node [v377, v629, v897, v1094, v1308, v1483] (.node [v375, v1094, v1308, v1448, v1483, v1578] (.node [v375, v1094, v1308, v1446, v1483, v1578] (.node [v375, v1094, v1308, v1446, v1483, v1530] (.node [v375, v1094, v1215, v1308, v1483, v1507] .nil .nil) .nil) (.node [v375, v1094, v1308, v1448, v1483, v1524] .nil .nil)) (.node [v375, v1094, v1308, v1483, v1553, v1578] (.node [v375, v1094, v1308, v1483, v1507, v1578] (.node [v375, v1094, v1308, v1453, v1483, v1578] .nil .nil) .nil) (.node [v376, v629, v897, v1094, v1308, v1483] .nil .nil))) (.node [v380, v629, v897, v1094, v1308, v1483] (.node [v379, v629, v897, v1094, v1308, v1483] (.node [v378, v629, v897, v1094, v1308, v1483] (.node [v378, v480, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v380, v497, v897, v1094, v1308, v1483] .nil .nil)) (.node [v384, v629, v897, v1094, v1308, v1483] (.node [v383, v629, v897, v1094, v1308, v1483] (.node [v381, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v385, v629, v897, v1094, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrllrl_ok : everyKey (rowOK 4 level4) level5rrllrl = true := by decide +kernel
def level5rrllrr : BinaryTree (List W) := (.node [v402, v629, v937, v1094, v1308, v1483] (.node [v395, v629, v897, v1094, v1308, v1483] (.node [v390, v497, v897, v1094, v1308, v1483] (.node [v389, v480, v897, v1094, v1308, v1483] (.node [v388, v629, v897, v1094, v1308, v1483] (.node [v387, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v389, v629, v897, v1094, v1308, v1483] .nil .nil)) (.node [v393, v629, v897, v1094, v1308, v1483] (.node [v392, v629, v897, v1094, v1308, v1483] (.node [v390, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v394, v629, v897, v1094, v1308, v1483] .nil .nil))) (.node [v402, v480, v897, v1094, v1308, v1483] (.node [v399, v629, v897, v1094, v1308, v1483] (.node [v398, v629, v897, v1094, v1308, v1483] (.node [v397, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v401, v629, v897, v1094, v1308, v1483] .nil .nil)) (.node [v402, v629, v864, v1094, v1308, v1483] (.node [v402, v535, v897, v1094, v1308, v1483] (.node [v402, v497, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v402, v629, v897, v1094, v1308, v1483] .nil .nil)))) (.node [v410, v629, v897, v1094, v1308, v1483] (.node [v405, v711, v897, v1094, v1308, v1483] (.node [v402, v897, v1094, v1308, v1483, v1578] (.node [v402, v897, v1094, v1215, v1308, v1483] (.node [v402, v685, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v405, v708, v897, v1094, v1308, v1483] .nil .nil)) (.node [v408, v629, v897, v1094, v1308, v1483] (.node [v408, v480, v897, v1094, v1308, v1483] (.node [v407, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v409, v629, v897, v1094, v1308, v1483] .nil .nil))) (.node [v413, v497, v897, v1094, v1308, v1483] (.node [v412, v629, v897, v1094, v1308, v1483] (.node [v411, v629, v897, v1094, v1308, v1483] (.node [v411, v497, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v413, v480, v897, v1094, v1308, v1483] .nil .nil)) (.node [v413, v897, v1094, v1308, v1483, v1578] (.node [v413, v897, v1094, v1215, v1308, v1483] (.node [v413, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v419, v629, v758, v1010, v1094, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrllrr_ok : everyKey (rowOK 4 level4) level5rrllrr = true := by decide +kernel
def level5rrllr : BinaryTree (List W) := .node [v386, v629, v897, v1094, v1308, v1483] level5rrllrl level5rrllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrllr_ok : everyKey (rowOK 4 level4) level5rrllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrllrl && everyKey (rowOK 4 level4) level5rrllrr) = true
  rw [level5rrllrl_ok, level5rrllrr_ok]
  decide +kernel
def level5rrll : BinaryTree (List W) := .node [v375, v908, v1094, v1215, v1308, v1483] level5rrlll level5rrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrll_ok : everyKey (rowOK 4 level4) level5rrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrlll && everyKey (rowOK 4 level4) level5rrllr) = true
  rw [level5rrlll_ok, level5rrllr_ok]
  decide +kernel
def level5rrlrll : BinaryTree (List W) := (.node [v440, v497, v1094, v1308, v1483] (.node [v435, v629, v897, v1094, v1308, v1483] (.node [v435, v480, v629, v1094, v1308, v1483] (.node [v427, v629, v897, v1094, v1308, v1483] (.node [v422, v786, v973, v1094, v1308, v1483] (.node [v422, v758, v973, v1094, v1308, v1483] .nil .nil) .nil) (.node [v428, v629, v758, v1094, v1308, v1483] .nil .nil)) (.node [v435, v480, v1094, v1308, v1483] (.node [v435, v480, v897, v1094, v1308, v1483] (.node [v435, v480, v668, v1094, v1308, v1483] .nil .nil) .nil) (.node [v435, v629, v668, v1094, v1308, v1483] .nil .nil))) (.node [v438, v629, v1094, v1308, v1349, v1483] (.node [v438, v629, v758, v1094, v1308, v1483] (.node [v438, v629, v708, v1094, v1308, v1483] (.node [v435, v629, v1094, v1308, v1483] .nil .nil) .nil) (.node [v438, v629, v1060, v1094, v1308, v1483] .nil .nil)) (.node [v440, v497, v670, v1094, v1308, v1483] (.node [v440, v497, v629, v1094, v1308, v1483] (.node [v438, v629, v1094, v1308, v1432, v1483] .nil .nil) .nil) (.node [v440, v497, v897, v1094, v1308, v1483] .nil .nil)))) (.node [v459, v758, v897, v1094, v1308, v1483] (.node [v443, v629, v1094, v1205, v1308, v1483] (.node [v440, v629, v1094, v1308, v1483] (.node [v440, v629, v897, v1094, v1308, v1483] (.node [v440, v629, v670, v1094, v1308, v1483] .nil .nil) .nil) (.node [v443, v629, v758, v1094, v1308, v1483] .nil .nil)) (.node [v447, v629, v758, v1094, v1308, v1483] (.node [v443, v629, v1094, v1308, v1483, v1544] (.node [v443, v629, v1094, v1242, v1308, v1483] .nil .nil) .nil) (.node [v447, v629, v1094, v1308, v1417, v1483] .nil .nil))) (.node [v470, v629, v897, v1094, v1308, v1483] (.node [v468, v629, v897, v1094, v1308, v1483] (.node [v468, v480, v897, v1094, v1308, v1483] (.node [v466, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v470, v497, v897, v1094, v1308, v1483] .nil .nil)) (.node [v473, v670, v897, v1094, v1308, v1483] (.node [v473, v668, v897, v1094, v1308, v1483] (.node [v473, v667, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v473, v758, v897, v1094, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrll_ok : everyKey (rowOK 4 level4) level5rrlrll = true := by decide +kernel
def level5rrlrlr : BinaryTree (List W) := (.node [v480, v897, v1094, v1143, v1308, v1483] (.node [v480, v758, v897, v1094, v1308, v1483] (.node [v480, v668, v897, v1094, v1483, v1578] (.node [v480, v668, v897, v1094, v1252, v1483] (.node [v480, v667, v897, v1094, v1308, v1483] (.node [v480, v665, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v480, v668, v897, v1094, v1308, v1483] .nil .nil)) (.node [v480, v714, v897, v1094, v1308, v1483] (.node [v480, v701, v897, v1094, v1308, v1483] (.node [v480, v670, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v480, v758, v897, v1094, v1252, v1483] .nil .nil))) (.node [v480, v846, v897, v1094, v1308, v1483] (.node [v480, v786, v897, v1094, v1308, v1483] (.node [v480, v780, v897, v1094, v1308, v1483] (.node [v480, v758, v897, v1094, v1483, v1578] .nil .nil) .nil) (.node [v480, v840, v897, v1094, v1308, v1483] .nil .nil)) (.node [v480, v897, v1094, v1134, v1308, v1483] (.node [v480, v897, v1094, v1131, v1308, v1483] (.node [v480, v897, v938, v1094, v1308, v1483] .nil .nil) .nil) (.node [v480, v897, v1094, v1141, v1308, v1483] .nil .nil)))) (.node [v497, v667, v897, v1094, v1308, v1483] (.node [v480, v897, v1094, v1308, v1373, v1483] (.node [v480, v897, v1094, v1308, v1365, v1483] (.node [v480, v897, v1094, v1308, v1353, v1483] (.node [v480, v897, v1094, v1308, v1341, v1483] .nil .nil) .nil) (.node [v480, v897, v1094, v1308, v1366, v1483] .nil .nil)) (.node [v497, v545, v897, v1094, v1308, v1483] (.node [v488, v758, v897, v1094, v1308, v1483] (.node [v480, v897, v1094, v1308, v1417, v1483] .nil .nil) .nil) (.node [v497, v664, v897, v1094, v1308, v1483] .nil .nil))) (.node [v497, v701, v897, v1094, v1308, v1483] (.node [v497, v670, v897, v1094, v1308, v1483] (.node [v497, v670, v897, v1094, v1215, v1308] (.node [v497, v668, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v497, v670, v897, v1094, v1308, v1536] .nil .nil)) (.node [v497, v758, v897, v1094, v1308, v1483] (.node [v497, v758, v897, v1094, v1215, v1308] (.node [v497, v712, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v497, v758, v897, v1094, v1308, v1536] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrlr_ok : everyKey (rowOK 4 level4) level5rrlrlr = true := by decide +kernel
def level5rrlrl : BinaryTree (List W) := .node [v480, v544, v897, v1094, v1308, v1483] level5rrlrll level5rrlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrl_ok : everyKey (rowOK 4 level4) level5rrlrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrlrll && everyKey (rowOK 4 level4) level5rrlrlr) = true
  rw [level5rrlrll_ok, level5rrlrlr_ok]
  decide +kernel
def level5rrlrrl : BinaryTree (List W) := (.node [v529, v897, v1094, v1134, v1308, v1483] (.node [v497, v897, v1094, v1308, v1353, v1483] (.node [v497, v897, v1094, v1131, v1308, v1483] (.node [v497, v845, v897, v1094, v1308, v1483] (.node [v497, v840, v897, v1094, v1308, v1483] (.node [v497, v786, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v497, v897, v940, v1094, v1308, v1483] .nil .nil)) (.node [v497, v897, v1094, v1143, v1308, v1483] (.node [v497, v897, v1094, v1141, v1308, v1483] (.node [v497, v897, v1094, v1134, v1308, v1483] .nil .nil) .nil) (.node [v497, v897, v1094, v1308, v1341, v1483] .nil .nil))) (.node [v506, v671, v897, v1094, v1308, v1483] (.node [v497, v897, v1094, v1308, v1373, v1483] (.node [v497, v897, v1094, v1308, v1366, v1483] (.node [v497, v897, v1094, v1308, v1365, v1483] .nil .nil) .nil) (.node [v497, v897, v1094, v1308, v1417, v1483] .nil .nil)) (.node [v511, v629, v897, v1094, v1242, v1483] (.node [v507, v758, v897, v1094, v1308, v1483] (.node [v506, v758, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v529, v758, v897, v1094, v1308, v1483] .nil .nil)))) (.node [v554, v758, v897, v1094, v1308, v1483] (.node [v539, v897, v1094, v1308, v1353, v1483] (.node [v536, v897, v1094, v1131, v1308, v1483] (.node [v536, v758, v897, v1094, v1308, v1483] (.node [v535, v758, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v539, v758, v897, v1094, v1308, v1483] .nil .nil)) (.node [v549, v629, v897, v1094, v1308, v1544] (.node [v545, v629, v897, v1094, v1308, v1483] (.node [v544, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v554, v708, v897, v1094, v1308, v1483] .nil .nil))) (.node [v572, v758, v897, v1094, v1308, v1483] (.node [v572, v668, v897, v1094, v1308, v1483] (.node [v558, v758, v897, v1094, v1308, v1483] (.node [v558, v708, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v572, v708, v897, v1094, v1308, v1483] .nil .nil)) (.node [v575, v758, v897, v1094, v1308, v1483] (.node [v575, v708, v897, v1094, v1308, v1483] (.node [v575, v670, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v584, v704, v897, v1094, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrrl_ok : everyKey (rowOK 4 level4) level5rrlrrl = true := by decide +kernel
def level5rrlrrr : BinaryTree (List W) := (.node [v629, v668, v897, v1094, v1308, v1483] (.node [v603, v897, v1094, v1308, v1366, v1483] (.node [v597, v707, v897, v1094, v1308, v1483] (.node [v592, v706, v897, v1094, v1308, v1483] (.node [v588, v758, v897, v1094, v1308, v1483] (.node [v588, v705, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v592, v758, v897, v1094, v1308, v1483] .nil .nil)) (.node [v602, v897, v1094, v1308, v1417, v1483] (.node [v602, v758, v897, v1094, v1308, v1483] (.node [v597, v758, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v603, v758, v897, v1094, v1308, v1483] .nil .nil))) (.node [v620, v897, v1094, v1308, v1373, v1483] (.node [v617, v758, v897, v1094, v1308, v1483] (.node [v613, v758, v897, v1094, v1308, v1483] (.node [v609, v708, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v620, v758, v897, v1094, v1308, v1483] .nil .nil)) (.node [v629, v665, v897, v1094, v1308, v1483] (.node [v629, v664, v897, v1094, v1308, v1483] (.node [v629, v645, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v629, v667, v897, v1094, v1308, v1483] .nil .nil)))) (.node [v629, v706, v897, v1094, v1308, v1483] (.node [v629, v701, v971, v1094, v1308, v1483] (.node [v629, v701, v807, v1094, v1308, v1483] (.node [v629, v671, v897, v1094, v1308, v1483] (.node [v629, v670, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v629, v701, v897, v1094, v1308, v1483] .nil .nil)) (.node [v629, v704, v897, v1094, v1308, v1483] (.node [v629, v703, v897, v1094, v1308, v1483] (.node [v629, v702, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v629, v705, v897, v1094, v1308, v1483] .nil .nil))) (.node [v629, v714, v897, v1094, v1308, v1483] (.node [v629, v712, v897, v1094, v1308, v1483] (.node [v629, v708, v872, v1094, v1308, v1483] (.node [v629, v707, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v629, v713, v897, v1094, v1346, v1483] .nil .nil)) (.node [v629, v718, v807, v1094, v1308, v1483] (.node [v629, v717, v897, v1031, v1308, v1483] (.node [v629, v717, v805, v1094, v1308, v1483] .nil .nil) .nil) (.node [v629, v718, v897, v1094, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrrr_ok : everyKey (rowOK 4 level4) level5rrlrrr = true := by decide +kernel
def level5rrlrr : BinaryTree (List W) := .node [v584, v758, v897, v1094, v1308, v1483] level5rrlrrl level5rrlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrr_ok : everyKey (rowOK 4 level4) level5rrlrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrlrrl && everyKey (rowOK 4 level4) level5rrlrrr) = true
  rw [level5rrlrrl_ok, level5rrlrrr_ok]
  decide +kernel
def level5rrlr : BinaryTree (List W) := .node [v497, v783, v897, v1094, v1308, v1483] level5rrlrl level5rrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlr_ok : everyKey (rowOK 4 level4) level5rrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrlrl && everyKey (rowOK 4 level4) level5rrlrr) = true
  rw [level5rrlrl_ok, level5rrlrr_ok]
  decide +kernel
def level5rrl : BinaryTree (List W) := .node [v419, v629, v1010, v1094, v1134, v1483] level5rrll level5rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrl_ok : everyKey (rowOK 4 level4) level5rrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrll && everyKey (rowOK 4 level4) level5rrlr) = true
  rw [level5rrll_ok, level5rrlr_ok]
  decide +kernel
def level5rrrlll : BinaryTree (List W) := (.node [v629, v758, v864, v1094, v1308, v1483] (.node [v629, v757, v897, v1094, v1308, v1483] (.node [v629, v755, v872, v1094, v1308, v1483] (.node [v629, v754, v861, v1094, v1308, v1483] (.node [v629, v753, v897, v1094, v1308, v1483] (.node [v629, v727, v1094, v1341, v1462, v1483] .nil .nil) .nil) (.node [v629, v754, v897, v1094, v1308, v1483] .nil .nil)) (.node [v629, v756, v897, v1094, v1308, v1483] (.node [v629, v756, v864, v1094, v1308, v1483] (.node [v629, v755, v897, v1094, v1308, v1488] .nil .nil) .nil) (.node [v629, v757, v888, v1094, v1308, v1483] .nil .nil))) (.node [v629, v758, v805, v1094, v1308, v1483] (.node [v629, v758, v796, v1094, v1308, v1483] (.node [v629, v758, v791, v1027, v1308, v1483] (.node [v629, v758, v777, v1094, v1308, v1483] .nil .nil) .nil) (.node [v629, v758, v797, v1094, v1308, v1483] .nil .nil)) (.node [v629, v758, v848, v1094, v1308, v1504] (.node [v629, v758, v824, v897, v1308, v1483] (.node [v629, v758, v807, v1094, v1308, v1483] .nil .nil) .nil) (.node [v629, v758, v861, v1094, v1308, v1483] .nil .nil)))) (.node [v629, v758, v897, v1094, v1304, v1483] (.node [v629, v758, v897, v1033, v1308, v1483] (.node [v629, v758, v897, v954, v1094, v1308] (.node [v629, v758, v888, v1094, v1308, v1483] (.node [v629, v758, v872, v1094, v1308, v1483] .nil .nil) .nil) (.node [v629, v758, v897, v1003, v1406, v1483] .nil .nil)) (.node [v629, v758, v897, v1087, v1308, v1483] (.node [v629, v758, v897, v1056, v1308, v1562] (.node [v629, v758, v897, v1036, v1308, v1483] .nil .nil) .nil) (.node [v629, v758, v897, v1094, v1214, v1590] .nil .nil))) (.node [v629, v758, v897, v1308, v1389, v1483] (.node [v629, v758, v897, v1094, v1345, v1483] (.node [v629, v758, v897, v1094, v1308, v1561] (.node [v629, v758, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v629, v758, v897, v1098, v1308, v1483] .nil .nil)) (.node [v629, v758, v962, v1094, v1308, v1483] (.node [v629, v758, v937, v1094, v1308, v1483] (.node [v629, v758, v897, v1308, v1399, v1483] .nil .nil) .nil) (.node [v629, v758, v971, v1094, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrlll_ok : everyKey (rowOK 4 level4) level5rrrlll = true := by decide +kernel
def level5rrrllr : BinaryTree (List W) := (.node [v629, v775, v897, v1094, v1308, v1483] (.node [v629, v760, v897, v1094, v1308, v1483] (.node [v629, v758, v1094, v1308, v1448, v1483] (.node [v629, v758, v1043, v1094, v1308, v1483] (.node [v629, v758, v1037, v1094, v1308, v1483] (.node [v629, v758, v1026, v1094, v1308, v1483] .nil .nil) .nil) (.node [v629, v758, v1094, v1308, v1446, v1483] .nil .nil)) (.node [v629, v758, v1094, v1308, v1483, v1507] (.node [v629, v758, v1094, v1308, v1471, v1483] (.node [v629, v758, v1094, v1308, v1453, v1483] .nil .nil) .nil) (.node [v629, v759, v897, v1094, v1308, v1483] .nil .nil))) (.node [v629, v765, v897, v1094, v1308, v1483] (.node [v629, v763, v897, v1094, v1308, v1483] (.node [v629, v762, v897, v1094, v1308, v1483] (.node [v629, v761, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v629, v764, v897, v1094, v1308, v1483] .nil .nil)) (.node [v629, v774, v897, v1094, v1308, v1483] (.node [v629, v773, v897, v1094, v1308, v1483] (.node [v629, v766, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v629, v774, v937, v1094, v1308, v1483] .nil .nil)))) (.node [v629, v785, v897, v1094, v1308, v1483] (.node [v629, v778, v897, v1094, v1308, v1483] (.node [v629, v777, v934, v1094, v1308, v1483] (.node [v629, v777, v897, v1094, v1308, v1483] (.node [v629, v776, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v629, v777, v1094, v1308, v1483] .nil .nil)) (.node [v629, v782, v897, v1094, v1308, v1483] (.node [v629, v781, v897, v1094, v1308, v1483] (.node [v629, v780, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v629, v783, v897, v1094, v1308, v1483] .nil .nil))) (.node [v629, v791, v1027, v1143, v1308, v1483] (.node [v629, v787, v897, v1094, v1308, v1483] (.node [v629, v786, v897, v1094, v1308, v1483] (.node [v629, v785, v971, v1094, v1308, v1483] .nil .nil) .nil) (.node [v629, v788, v897, v1094, v1308, v1483] .nil .nil)) (.node [v629, v803, v840, v1094, v1308, v1483] (.node [v629, v803, v814, v1094, v1308, v1483] (.node [v629, v795, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v629, v803, v897, v1094, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrllr_ok : everyKey (rowOK 4 level4) level5rrrllr = true := by decide +kernel
def level5rrrll : BinaryTree (List W) := .node [v629, v758, v1011, v1094, v1308, v1483] level5rrrlll level5rrrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrll_ok : everyKey (rowOK 4 level4) level5rrrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrlll && everyKey (rowOK 4 level4) level5rrrllr) = true
  rw [level5rrrlll_ok, level5rrrllr_ok]
  decide +kernel
def level5rrrlrl : BinaryTree (List W) := (.node [v629, v872, v1094, v1308, v1349, v1483] (.node [v629, v836, v897, v1094, v1308, v1483] (.node [v629, v819, v897, v1060, v1308, v1483] (.node [v629, v805, v1094, v1308, v1483, v1544] (.node [v629, v805, v1094, v1242, v1308, v1483] (.node [v629, v805, v1094, v1205, v1308, v1483] .nil .nil) .nil) (.node [v629, v815, v897, v1094, v1308, v1544] .nil .nil)) (.node [v629, v832, v897, v1094, v1308, v1483] (.node [v629, v830, v897, v1094, v1308, v1483] (.node [v629, v824, v897, v1308, v1373, v1483] .nil .nil) .nil) (.node [v629, v835, v897, v1094, v1308, v1483] .nil .nil))) (.node [v629, v846, v897, v1094, v1308, v1483] (.node [v629, v844, v897, v1094, v1308, v1483] (.node [v629, v840, v897, v1094, v1308, v1483] (.node [v629, v838, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v629, v845, v897, v1094, v1308, v1483] .nil .nil)) (.node [v629, v861, v1094, v1131, v1308, v1483] (.node [v629, v848, v1094, v1308, v1353, v1504] (.node [v629, v847, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v629, v872, v1060, v1094, v1308, v1483] .nil .nil)))) (.node [v629, v897, v1007, v1205, v1308, v1483] (.node [v629, v897, v940, v1094, v1308, v1483] (.node [v629, v897, v905, v1094, v1308, v1483] (.node [v629, v888, v1094, v1308, v1373, v1483] (.node [v629, v872, v1094, v1308, v1432, v1483] .nil .nil) .nil) (.node [v629, v897, v938, v1094, v1308, v1483] .nil .nil)) (.node [v629, v897, v1003, v1131, v1406, v1483] (.node [v629, v897, v978, v1094, v1308, v1483] (.node [v629, v897, v954, v1094, v1131, v1308] .nil .nil) .nil) (.node [v629, v897, v1003, v1365, v1406, v1483] .nil .nil))) (.node [v629, v897, v1060, v1163, v1308, v1483] (.node [v629, v897, v1031, v1205, v1308, v1483] (.node [v629, v897, v1015, v1094, v1432, v1483] (.node [v629, v897, v1013, v1094, v1432, v1483] .nil .nil) .nil) (.node [v629, v897, v1051, v1094, v1308, v1483] .nil .nil)) (.node [v629, v897, v1061, v1094, v1308, v1483] (.node [v629, v897, v1060, v1308, v1390, v1483] (.node [v629, v897, v1060, v1308, v1388, v1483] .nil .nil) .nil) (.node [v629, v897, v1062, v1094, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrlrl_ok : everyKey (rowOK 4 level4) level5rrrlrl = true := by decide +kernel
def level5rrrlrr : BinaryTree (List W) := (.node [v629, v897, v1094, v1141, v1308, v1483] (.node [v629, v897, v1094, v1130, v1308, v1483] (.node [v629, v897, v1094, v1122, v1308, v1483] (.node [v629, v897, v1094, v1120, v1308, v1483] (.node [v629, v897, v1094, v1117, v1308, v1483] (.node [v629, v897, v1094, v1102, v1308, v1483] .nil .nil) .nil) (.node [v629, v897, v1094, v1121, v1308, v1483] .nil .nil)) (.node [v629, v897, v1094, v1126, v1308, v1483] (.node [v629, v897, v1094, v1125, v1308, v1483] (.node [v629, v897, v1094, v1124, v1308, v1483] .nil .nil) .nil) (.node [v629, v897, v1094, v1129, v1308, v1483] .nil .nil))) (.node [v629, v897, v1094, v1134, v1308, v1483] (.node [v629, v897, v1094, v1132, v1308, v1483] (.node [v629, v897, v1094, v1131, v1308, v1561] (.node [v629, v897, v1094, v1131, v1308, v1483] .nil .nil) .nil) (.node [v629, v897, v1094, v1133, v1308, v1483] .nil .nil)) (.node [v629, v897, v1094, v1139, v1308, v1483] (.node [v629, v897, v1094, v1137, v1308, v1544] (.node [v629, v897, v1094, v1135, v1308, v1483] .nil .nil) .nil) (.node [v629, v897, v1094, v1140, v1308, v1483] .nil .nil)))) (.node [v629, v897, v1094, v1151, v1308, v1483] (.node [v629, v897, v1094, v1146, v1308, v1483] (.node [v629, v897, v1094, v1144, v1308, v1483] (.node [v629, v897, v1094, v1143, v1308, v1483] (.node [v629, v897, v1094, v1142, v1308, v1483] .nil .nil) .nil) (.node [v629, v897, v1094, v1145, v1308, v1483] .nil .nil)) (.node [v629, v897, v1094, v1149, v1308, v1483] (.node [v629, v897, v1094, v1148, v1308, v1483] (.node [v629, v897, v1094, v1147, v1308, v1483] .nil .nil) .nil) (.node [v629, v897, v1094, v1150, v1308, v1483] .nil .nil))) (.node [v629, v897, v1094, v1204, v1308, v1483] (.node [v629, v897, v1094, v1174, v1308, v1483] (.node [v629, v897, v1094, v1163, v1308, v1483] (.node [v629, v897, v1094, v1152, v1308, v1483] .nil .nil) .nil) (.node [v629, v897, v1094, v1203, v1308, v1483] .nil .nil)) (.node [v629, v897, v1094, v1242, v1346, v1483] (.node [v629, v897, v1094, v1214, v1417, v1590] (.node [v629, v897, v1094, v1214, v1373, v1590] .nil .nil) .nil) (.node [v629, v897, v1094, v1242, v1400, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrlrr_ok : everyKey (rowOK 4 level4) level5rrrlrr = true := by decide +kernel
def level5rrrlr : BinaryTree (List W) := .node [v629, v897, v1087, v1308, v1373, v1483] level5rrrlrl level5rrrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrlr_ok : everyKey (rowOK 4 level4) level5rrrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrlrl && everyKey (rowOK 4 level4) level5rrrlrr) = true
  rw [level5rrrlrl_ok, level5rrrlrr_ok]
  decide +kernel
def level5rrrl : BinaryTree (List W) := .node [v629, v803, v1094, v1308, v1483] level5rrrll level5rrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrl_ok : everyKey (rowOK 4 level4) level5rrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrll && everyKey (rowOK 4 level4) level5rrrlr) = true
  rw [level5rrrll_ok, level5rrrlr_ok]
  decide +kernel
def level5rrrrll : BinaryTree (List W) := (.node [v629, v897, v1094, v1308, v1349, v1488] (.node [v629, v897, v1094, v1308, v1336, v1483] (.node [v629, v897, v1094, v1282, v1432, v1483] (.node [v629, v897, v1094, v1244, v1308, v1483] (.node [v629, v897, v1094, v1243, v1308, v1483] (.node [v629, v897, v1094, v1242, v1412, v1483] .nil .nil) .nil) (.node [v629, v897, v1094, v1245, v1308, v1483] .nil .nil)) (.node [v629, v897, v1094, v1308, v1334, v1483] (.node [v629, v897, v1094, v1308, v1333, v1483] (.node [v629, v897, v1094, v1288, v1308, v1483] .nil .nil) .nil) (.node [v629, v897, v1094, v1308, v1335, v1483] .nil .nil))) (.node [v629, v897, v1094, v1308, v1341, v1483] (.node [v629, v897, v1094, v1308, v1339, v1483] (.node [v629, v897, v1094, v1308, v1338, v1483] (.node [v629, v897, v1094, v1308, v1337, v1483] .nil .nil) .nil) (.node [v629, v897, v1094, v1308, v1340, v1483] .nil .nil)) (.node [v629, v897, v1094, v1308, v1348, v1483] (.node [v629, v897, v1094, v1308, v1343, v1483] (.node [v629, v897, v1094, v1308, v1342, v1483] .nil .nil) .nil) (.node [v629, v897, v1094, v1308, v1349, v1381] .nil .nil)))) (.node [v629, v897, v1094, v1308, v1366, v1483] (.node [v629, v897, v1094, v1308, v1353, v1483] (.node [v629, v897, v1094, v1308, v1351, v1483] (.node [v629, v897, v1094, v1308, v1350, v1483] (.node [v629, v897, v1094, v1308, v1349, v1513] .nil .nil) .nil) (.node [v629, v897, v1094, v1308, v1352, v1483] .nil .nil)) (.node [v629, v897, v1094, v1308, v1364, v1483] (.node [v629, v897, v1094, v1308, v1363, v1483] (.node [v629, v897, v1094, v1308, v1357, v1483] .nil .nil) .nil) (.node [v629, v897, v1094, v1308, v1365, v1483] .nil .nil))) (.node [v629, v897, v1094, v1308, v1374, v1483] (.node [v629, v897, v1094, v1308, v1371, v1483] (.node [v629, v897, v1094, v1308, v1369, v1483] (.node [v629, v897, v1094, v1308, v1367, v1483] .nil .nil) .nil) (.node [v629, v897, v1094, v1308, v1373, v1483] .nil .nil)) (.node [v629, v897, v1094, v1308, v1377, v1483] (.node [v629, v897, v1094, v1308, v1376, v1483] (.node [v629, v897, v1094, v1308, v1375, v1483] .nil .nil) .nil) (.node [v629, v897, v1094, v1308, v1378, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrll_ok : everyKey (rowOK 4 level4) level5rrrrll = true := by decide +kernel
def level5rrrrlr : BinaryTree (List W) := (.node [v629, v897, v1094, v1308, v1483, v1542] (.node [v629, v897, v1094, v1308, v1412, v1483] (.node [v629, v897, v1094, v1308, v1383, v1483] (.node [v629, v897, v1094, v1308, v1381, v1544] (.node [v629, v897, v1094, v1308, v1381, v1483] (.node [v629, v897, v1094, v1308, v1381] .nil .nil) .nil) (.node [v629, v897, v1094, v1308, v1382, v1483] .nil .nil)) (.node [v629, v897, v1094, v1308, v1409, v1544] (.node [v629, v897, v1094, v1308, v1395, v1483] (.node [v629, v897, v1094, v1308, v1393, v1483] .nil .nil) .nil) (.node [v629, v897, v1094, v1308, v1411, v1483] .nil .nil))) (.node [v629, v897, v1094, v1308, v1428, v1483] (.node [v629, v897, v1094, v1308, v1417, v1483] (.node [v629, v897, v1094, v1308, v1415, v1483] (.node [v629, v897, v1094, v1308, v1413, v1483] .nil .nil) .nil) (.node [v629, v897, v1094, v1308, v1419, v1483] .nil .nil)) (.node [v629, v897, v1094, v1308, v1435, v1483] (.node [v629, v897, v1094, v1308, v1434, v1483] (.node [v629, v897, v1094, v1308, v1430, v1483] .nil .nil) .nil) (.node [v629, v897, v1094, v1308, v1483, v1493] .nil .nil)))) (.node [v629, v1094, v1131, v1308, v1453, v1483] (.node [v629, v897, v1308, v1399, v1417, v1483] (.node [v629, v897, v1163, v1205, v1308, v1483] (.node [v629, v897, v1094, v1412, v1483] (.node [v629, v897, v1094, v1412, v1432, v1483] .nil .nil) .nil) (.node [v629, v897, v1163, v1308, v1483] .nil .nil)) (.node [v629, v1043, v1094, v1152, v1308, v1483] (.node [v629, v1026, v1094, v1141, v1308, v1483] (.node [v629, v1019, v1094, v1139, v1308, v1483] .nil .nil) .nil) (.node [v629, v1043, v1094, v1308, v1373, v1483] .nil .nil))) (.node [v629, v1094, v1308, v1365, v1483, v1508] (.node [v629, v1094, v1308, v1341, v1448, v1483] (.node [v629, v1094, v1308, v1339, v1453, v1483] (.node [v629, v1094, v1308, v1336, v1446, v1483] .nil .nil) .nil) (.node [v629, v1094, v1308, v1343, v1462, v1483] .nil .nil)) (.node [v629, v1094, v1308, v1417, v1446, v1483] (.node [v629, v1094, v1308, v1383, v1483, v1554] (.node [v629, v1094, v1308, v1366, v1483, v1507] .nil .nil) .nil) (.node [v638, v758, v897, v1094, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrlr_ok : everyKey (rowOK 4 level4) level5rrrrlr = true := by decide +kernel
def level5rrrrl : BinaryTree (List W) := .node [v629, v897, v1094, v1308, v1379, v1483] level5rrrrll level5rrrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrl_ok : everyKey (rowOK 4 level4) level5rrrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrrll && everyKey (rowOK 4 level4) level5rrrrlr) = true
  rw [level5rrrrll_ok, level5rrrrlr_ok]
  decide +kernel
def level5rrrrrl : BinaryTree (List W) := (.node [v758, v897, v1094, v1199, v1308, v1483] (.node [v698, v758, v897, v1094, v1308, v1483] (.node [v670, v897, v1094, v1308, v1483, v1571] (.node [v668, v897, v1094, v1308, v1483, v1578] (.node [v668, v897, v1094, v1234, v1308, v1483] (.node [v668, v897, v1094, v1215, v1308, v1483] .nil .nil) .nil) (.node [v670, v897, v1094, v1215, v1308, v1483] .nil .nil)) (.node [v685, v758, v897, v1094, v1308, v1483] (.node [v682, v758, v897, v1094, v1308, v1483] (.node [v670, v897, v1094, v1308, v1483, v1578] .nil .nil) .nil) (.node [v690, v758, v897, v1094, v1308, v1483] .nil .nil))) (.node [v758, v897, v966, v1094, v1308, v1483] (.node [v703, v897, v1094, v1215, v1308, v1483] (.node [v701, v897, v1094, v1308, v1483, v1578] (.node [v701, v897, v1094, v1215, v1308, v1483] .nil .nil) .nil) (.node [v741, v758, v897, v1094, v1308, v1483] .nil .nil)) (.node [v758, v897, v1015, v1094, v1483, v1578] (.node [v758, v897, v976, v1094, v1308, v1483] (.node [v758, v897, v968, v1094, v1308, v1483] .nil .nil) .nil) (.node [v758, v897, v1094, v1187, v1308, v1483] .nil .nil)))) (.node [v758, v897, v1094, v1308, v1320, v1483] (.node [v758, v897, v1094, v1234, v1308, v1483] (.node [v758, v897, v1094, v1225, v1308, v1483] (.node [v758, v897, v1094, v1215, v1308, v1483] (.node [v758, v897, v1094, v1200, v1308, v1483] .nil .nil) .nil) (.node [v758, v897, v1094, v1230, v1308, v1483] .nil .nil)) (.node [v758, v897, v1094, v1262, v1308, v1483] (.node [v758, v897, v1094, v1260, v1308, v1483] (.node [v758, v897, v1094, v1251, v1308, v1483] .nil .nil) .nil) (.node [v758, v897, v1094, v1271, v1308, v1483] .nil .nil))) (.node [v758, v897, v1094, v1308, v1483, v1578] (.node [v758, v897, v1094, v1308, v1483, v1530] (.node [v758, v897, v1094, v1308, v1483, v1524] (.node [v758, v897, v1094, v1308, v1473, v1483] .nil .nil) .nil) (.node [v758, v897, v1094, v1308, v1483, v1571] .nil .nil)) (.node [v786, v897, v1094, v1308, v1483, v1578] (.node [v786, v897, v1094, v1215, v1308, v1483] (.node [v758, v897, v1094, v1346, v1483, v1578] .nil .nil) .nil) (.node [v835, v897, v1094, v1215, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrrl_ok : everyKey (rowOK 4 level4) level5rrrrrl = true := by decide +kernel
def level5rrrrrr : BinaryTree (List W) := (.node [v897, v1094, v1215, v1308, v1366, v1483] (.node [v897, v1094, v1141, v1308, v1483, v1578] (.node [v897, v1094, v1131, v1308, v1483, v1578] (.node [v897, v1094, v1131, v1187, v1308, v1483] (.node [v897, v1094, v1124, v1215, v1308, v1483] (.node [v840, v897, v1094, v1308, v1483, v1578] .nil .nil) .nil) (.node [v897, v1094, v1131, v1215, v1308, v1483] .nil .nil)) (.node [v897, v1094, v1134, v1308, v1483, v1578] (.node [v897, v1094, v1134, v1215, v1308, v1483] (.node [v897, v1094, v1134, v1199, v1308, v1483] .nil .nil) .nil) (.node [v897, v1094, v1141, v1215, v1308, v1483] .nil .nil))) (.node [v897, v1094, v1215, v1244, v1308, v1483] (.node [v897, v1094, v1148, v1308, v1483, v1578] (.node [v897, v1094, v1143, v1308, v1483, v1578] (.node [v897, v1094, v1143, v1215, v1308, v1483] .nil .nil) .nil) (.node [v897, v1094, v1204, v1308, v1483, v1578] .nil .nil)) (.node [v897, v1094, v1215, v1308, v1353, v1483] (.node [v897, v1094, v1215, v1308, v1341, v1483] (.node [v897, v1094, v1215, v1308, v1334, v1483] .nil .nil) .nil) (.node [v897, v1094, v1215, v1308, v1365, v1483] .nil .nil)))) (.node [v897, v1094, v1308, v1365, v1483, v1578] (.node [v897, v1094, v1244, v1308, v1320, v1483] (.node [v897, v1094, v1215, v1308, v1417, v1483] (.node [v897, v1094, v1215, v1308, v1415, v1483] (.node [v897, v1094, v1215, v1308, v1373, v1483] .nil .nil) .nil) (.node [v897, v1094, v1230, v1308, v1353, v1483] .nil .nil)) (.node [v897, v1094, v1308, v1341, v1483, v1578] (.node [v897, v1094, v1271, v1308, v1373, v1483] (.node [v897, v1094, v1251, v1308, v1366, v1483] .nil .nil) .nil) (.node [v897, v1094, v1308, v1353, v1483, v1578] .nil .nil))) (.node [v897, v1094, v1308, v1379, v1483, v1578] (.node [v897, v1094, v1308, v1373, v1483, v1578] (.node [v897, v1094, v1308, v1371, v1483, v1578] (.node [v897, v1094, v1308, v1366, v1483, v1578] .nil .nil) .nil) (.node [v897, v1094, v1308, v1378, v1483, v1578] .nil .nil)) (.node [v897, v1094, v1308, v1473, v1483, v1542] (.node [v897, v1094, v1308, v1417, v1483, v1578] (.node [v897, v1094, v1308, v1417, v1483, v1530] .nil .nil) .nil) (.node [v897, v1094, v1308, v1483, v1542, v1578] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrrr_ok : everyKey (rowOK 4 level4) level5rrrrrr = true := by decide +kernel
def level5rrrrr : BinaryTree (List W) := .node [v840, v897, v1094, v1215, v1308, v1483] level5rrrrrl level5rrrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrrr_ok : everyKey (rowOK 4 level4) level5rrrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrrrl && everyKey (rowOK 4 level4) level5rrrrrr) = true
  rw [level5rrrrrl_ok, level5rrrrrr_ok]
  decide +kernel
def level5rrrr : BinaryTree (List W) := .node [v644, v758, v897, v1094, v1308, v1483] level5rrrrl level5rrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrr_ok : everyKey (rowOK 4 level4) level5rrrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrrl && everyKey (rowOK 4 level4) level5rrrrr) = true
  rw [level5rrrrl_ok, level5rrrrr_ok]
  decide +kernel
def level5rrr : BinaryTree (List W) := .node [v629, v897, v1094, v1242, v1404, v1483] level5rrrl level5rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrr_ok : everyKey (rowOK 4 level4) level5rrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrl && everyKey (rowOK 4 level4) level5rrrr) = true
  rw [level5rrrl_ok, level5rrrr_ok]
  decide +kernel
def level5rr : BinaryTree (List W) := .node [v629, v727, v758, v1094, v1462, v1483] level5rrl level5rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rr_ok : everyKey (rowOK 4 level4) level5rr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrl && everyKey (rowOK 4 level4) level5rrr) = true
  rw [level5rrl_ok, level5rrr_ok]
  decide +kernel
def level5r : BinaryTree (List W) := .node [v375, v897, v1094, v1298, v1308, v1483] level5rl level5rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5r_ok : everyKey (rowOK 4 level4) level5r = true := by
  change (_ && everyKey (rowOK 4 level4) level5rl && everyKey (rowOK 4 level4) level5rr) = true
  rw [level5rl_ok, level5rr_ok]
  decide +kernel
def level5 : BinaryTree (List W) := .node [v375, v561, v897, v1094, v1308, v1483] level5l level5r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5_ok : everyKey (rowOK 4 level4) level5 = true := by
  change (_ && everyKey (rowOK 4 level4) level5l && everyKey (rowOK 4 level4) level5r) = true
  rw [level5l_ok, level5r_ok]
  decide +kernel
theorem closed5 : Closed 5 level5 := closed_next 4 (by decide) level5 level4 closed4 level5_ok
def level6llllll : BinaryTree (List W) := (.node [v5, v375, v629, v897, v1094, v1308, v1483] (.node [v0, v629, v758, v897, v1094, v1308, v1483] (.node [v0, v375, v629, v897, v1094, v1308, v1483] (.node [v0, v375, v480, v897, v1094, v1308, v1483] (.node [v0, v237, v629, v897, v1094, v1308, v1483] .nil .nil) (.node [v0, v375, v497, v897, v1094, v1308, v1483] .nil .nil)) (.node [v0, v375, v897, v1094, v1308, v1483, v1578] (.node [v0, v375, v897, v1094, v1215, v1308, v1483] .nil .nil) .nil)) (.node [v3, v375, v480, v897, v1094, v1308, v1483] (.node [v2, v375, v629, v897, v1094, v1308, v1483] (.node [v1, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v4, v375, v629, v897, v1094, v1308, v1483] (.node [v3, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v11, v375, v629, v897, v1094, v1308, v1483] (.node [v8, v375, v629, v897, v1094, v1308, v1483] (.node [v6, v629, v758, v897, v1094, v1308, v1483] (.node [v6, v375, v629, v897, v1094, v1308, v1483] .nil .nil) (.node [v7, v375, v629, v897, v1094, v1308, v1483] .nil .nil)) (.node [v10, v375, v629, v897, v1094, v1308, v1483] (.node [v9, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v13, v375, v629, v897, v1094, v1308, v1483] (.node [v12, v375, v629, v897, v1094, v1308, v1483] (.node [v12, v375, v497, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v14, v375, v629, v897, v1094, v1308, v1483] (.node [v13, v375, v897, v1094, v1308, v1483, v1578] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llllll_ok : everyKey (rowOK 5 level5) level6llllll = true := by decide +kernel
def level6lllllr : BinaryTree (List W) := (.node [v25, v375, v629, v897, v1094, v1308, v1483] (.node [v18, v375, v897, v1094, v1308, v1483, v1578] (.node [v18, v375, v629, v897, v1094, v1308, v1483] (.node [v16, v375, v897, v1094, v1308, v1483, v1578] (.node [v16, v375, v629, v897, v1094, v1308, v1483] .nil .nil) (.node [v18, v375, v513, v897, v1094, v1308, v1483] .nil .nil)) (.node [v18, v375, v897, v1094, v1308, v1483] (.node [v18, v375, v897, v1094, v1215, v1308, v1483] .nil .nil) .nil)) (.node [v23, v237, v629, v897, v1094, v1308, v1483] (.node [v22, v375, v629, v897, v1094, v1308, v1483] (.node [v22, v237, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v24, v375, v629, v897, v1094, v1308, v1483] (.node [v23, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v31, v375, v629, v897, v1094, v1308, v1483] (.node [v28, v375, v629, v897, v1094, v1308, v1483] (.node [v27, v375, v629, v897, v1094, v1308, v1483] (.node [v26, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v30, v375, v629, v897, v1094, v1308, v1483] (.node [v29, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v33, v375, v629, v897, v1094, v1308, v1483] (.node [v33, v237, v629, v897, v1094, v1308, v1483] (.node [v32, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v34, v375, v629, v897, v1094, v1308, v1483] (.node [v34, v237, v629, v897, v1094, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllllr_ok : everyKey (rowOK 5 level5) level6lllllr = true := by decide +kernel
def level6lllll : BinaryTree (List W) := .node [v14, v375, v897, v1094, v1308, v1483, v1578] level6llllll level6lllllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllll_ok : everyKey (rowOK 5 level5) level6lllll = true := by
  change (_ && everyKey (rowOK 5 level5) level6llllll && everyKey (rowOK 5 level5) level6lllllr) = true
  rw [level6llllll_ok, level6lllllr_ok]
  decide +kernel
def level6llllrl : BinaryTree (List W) := (.node [v36, v375, v644, v897, v1094, v1308, v1483] (.node [v36, v375, v629, v897, v1019, v1094, v1308] (.node [v36, v375, v497, v897, v1094, v1308, v1483] (.node [v36, v375, v419, v629, v1094, v1308, v1483] (.node [v36, v237, v629, v897, v1094, v1308, v1483] .nil .nil) (.node [v36, v375, v480, v897, v1094, v1308, v1483] .nil .nil)) (.node [v36, v375, v629, v848, v1094, v1308, v1483] (.node [v36, v375, v592, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v36, v375, v629, v1019, v1094, v1308] (.node [v36, v375, v629, v897, v1094, v1308, v1504] (.node [v36, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v36, v375, v629, v1094, v1308, v1462, v1483] (.node [v36, v375, v629, v1019, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v45, v375, v629, v897, v1094, v1308, v1483] (.node [v37, v375, v629, v897, v1094, v1308, v1483] (.node [v36, v375, v897, v1094, v1308, v1483, v1578] (.node [v36, v375, v897, v1094, v1215, v1308, v1483] .nil .nil) (.node [v36, v629, v758, v897, v1094, v1308, v1483] .nil .nil)) (.node [v44, v375, v629, v897, v1094, v1308, v1483] (.node [v43, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v48, v375, v629, v897, v1094, v1308, v1483] (.node [v47, v375, v629, v897, v1094, v1308, v1483] (.node [v46, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v49, v375, v897, v1094, v1215, v1308, v1483] (.node [v49, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llllrl_ok : everyKey (rowOK 5 level5) level6llllrl = true := by decide +kernel
def level6llllrr : BinaryTree (List W) := (.node [v64, v190, v375, v897, v1094, v1308, v1483] (.node [v59, v375, v629, v897, v1094, v1308, v1483] (.node [v56, v375, v629, v897, v1094, v1308, v1483] (.node [v54, v375, v629, v897, v1094, v1308, v1483] (.node [v53, v375, v629, v897, v1094, v1308, v1483] .nil .nil) (.node [v55, v375, v629, v897, v1094, v1308, v1483] .nil .nil)) (.node [v58, v375, v629, v897, v1094, v1308, v1483] (.node [v57, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v63, v375, v629, v897, v1094, v1308, v1483] (.node [v62, v375, v629, v897, v1094, v1308, v1483] (.node [v60, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v64, v108, v629, v897, v1094, v1308, v1483] (.node [v64, v90, v629, v897, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v64, v375, v422, v897, v1094, v1308, v1483] (.node [v64, v237, v629, v897, v1094, v1308, v1483] (.node [v64, v190, v897, v1094, v1308, v1483] (.node [v64, v190, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v64, v303, v629, v897, v1094, v1308, v1483] (.node [v64, v266, v629, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v64, v375, v629, v897, v1094, v1308, v1483] (.node [v64, v375, v497, v897, v1094, v1308, v1483] (.node [v64, v375, v480, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v64, v375, v722, v897, v1094, v1308, v1483] (.node [v64, v375, v708, v897, v1094, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llllrr_ok : everyKey (rowOK 5 level5) level6llllrr = true := by decide +kernel
def level6llllr : BinaryTree (List W) := .node [v51, v375, v629, v897, v1094, v1308, v1483] level6llllrl level6llllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llllr_ok : everyKey (rowOK 5 level5) level6llllr = true := by
  change (_ && everyKey (rowOK 5 level5) level6llllrl && everyKey (rowOK 5 level5) level6llllrr) = true
  rw [level6llllrl_ok, level6llllrr_ok]
  decide +kernel
def level6llll : BinaryTree (List W) := .node [v35, v375, v629, v897, v1094, v1308, v1483] level6lllll level6llllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llll_ok : everyKey (rowOK 5 level5) level6llll = true := by
  change (_ && everyKey (rowOK 5 level5) level6lllll && everyKey (rowOK 5 level5) level6llllr) = true
  rw [level6lllll_ok, level6llllr_ok]
  decide +kernel
def level6lllrll : BinaryTree (List W) := (.node [v78, v375, v629, v897, v1094, v1308, v1483] (.node [v72, v375, v629, v897, v1094, v1308, v1483] (.node [v64, v629, v897, v1094, v1242, v1308, v1483] (.node [v64, v629, v758, v897, v1094, v1308, v1483] (.node [v64, v375, v897, v1094, v1308, v1483, v1578] .nil .nil) (.node [v64, v629, v897, v1094, v1205, v1308, v1483] .nil .nil)) (.node [v71, v375, v629, v897, v1094, v1308, v1483] (.node [v64, v629, v897, v1094, v1308, v1483, v1544] .nil .nil) .nil)) (.node [v75, v375, v629, v897, v1094, v1308, v1483] (.node [v74, v375, v629, v897, v1094, v1308, v1483] (.node [v73, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v77, v375, v629, v897, v1094, v1308, v1483] (.node [v76, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v80, v375, v629, v897, v1094, v1308, v1536] (.node [v80, v375, v497, v897, v1094, v1308, v1483] (.node [v80, v237, v629, v897, v1094, v1308, v1483] (.node [v79, v375, v629, v897, v1094, v1308, v1483] .nil .nil) (.node [v80, v375, v480, v897, v1094, v1308, v1483] .nil .nil)) (.node [v80, v375, v629, v897, v1094, v1308, v1483] (.node [v80, v375, v629, v897, v1094, v1215, v1308] .nil .nil) .nil)) (.node [v80, v375, v897, v1094, v1308, v1483, v1578] (.node [v80, v375, v897, v1094, v1215, v1308, v1483] (.node [v80, v375, v897, v1094, v1215, v1308] .nil .nil) .nil) (.node [v81, v375, v629, v897, v1094, v1308, v1483] (.node [v80, v629, v758, v897, v1094, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllrll_ok : everyKey (rowOK 5 level5) level6lllrll = true := by decide +kernel
def level6lllrlr : BinaryTree (List W) := (.node [v86, v375, v629, v897, v1094, v1308, v1483] (.node [v82, v375, v897, v1094, v1308, v1483, v1578] (.node [v82, v375, v629, v897, v1094, v1308, v1483] (.node [v82, v375, v497, v897, v1094, v1308, v1483] (.node [v82, v375, v480, v897, v1094, v1308, v1483] .nil .nil) (.node [v82, v375, v629, v897, v1094, v1252, v1483] .nil .nil)) (.node [v82, v375, v897, v1094, v1215, v1308, v1483] (.node [v82, v375, v629, v897, v1094, v1483, v1578] .nil .nil) .nil)) (.node [v83, v375, v629, v897, v1094, v1308, v1483] (.node [v82, v629, v758, v897, v1094, v1308, v1483] (.node [v82, v375, v897, v1094, v1483, v1578] .nil .nil) .nil) (.node [v85, v375, v629, v897, v1094, v1308, v1483] (.node [v84, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v88, v375, v480, v897, v1094, v1308, v1483] (.node [v88, v108, v629, v897, v1094, v1308, v1483] (.node [v88, v90, v629, v897, v1094, v1308, v1483] (.node [v87, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v88, v266, v629, v897, v1094, v1308, v1483] (.node [v88, v237, v629, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v88, v375, v629, v897, v1094, v1308, v1483] (.node [v88, v375, v629, v897, v1060, v1308, v1483] (.node [v88, v375, v497, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v88, v375, v897, v1094, v1215, v1308, v1483] (.node [v88, v375, v629, v897, v1205, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllrlr_ok : everyKey (rowOK 5 level5) level6lllrlr = true := by decide +kernel
def level6lllrl : BinaryTree (List W) := .node [v82, v237, v629, v897, v1094, v1308, v1483] level6lllrll level6lllrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllrl_ok : everyKey (rowOK 5 level5) level6lllrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6lllrll && everyKey (rowOK 5 level5) level6lllrlr) = true
  rw [level6lllrll_ok, level6lllrlr_ok]
  decide +kernel
def level6lllrrl : BinaryTree (List W) := (.node [v90, v375, v629, v897, v1094, v1308, v1349] (.node [v90, v225, v629, v897, v1094, v1308, v1483] (.node [v88, v629, v897, v1094, v1308, v1483, v1544] (.node [v88, v629, v897, v1094, v1205, v1308, v1483] (.node [v88, v629, v758, v897, v1094, v1308, v1483] .nil .nil) (.node [v88, v629, v897, v1094, v1242, v1308, v1483] .nil .nil)) (.node [v89, v375, v629, v897, v1094, v1308, v1483] (.node [v88, v629, v897, v1205, v1308, v1483] .nil .nil) .nil)) (.node [v90, v375, v480, v897, v1094, v1308, v1483] (.node [v90, v264, v629, v897, v1094, v1308, v1483] (.node [v90, v237, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v90, v375, v558, v897, v1094, v1308, v1483] (.node [v90, v375, v497, v897, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v90, v629, v708, v897, v1094, v1308, v1483] (.node [v90, v375, v682, v897, v1094, v1308, v1483] (.node [v90, v375, v629, v897, v1094, v1308, v1544] (.node [v90, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v90, v375, v897, v1094, v1308, v1483, v1578] (.node [v90, v375, v897, v1094, v1215, v1308, v1483] .nil .nil) .nil)) (.node [v90, v629, v897, v1094, v1308, v1349] (.node [v90, v629, v897, v1060, v1094, v1308, v1483] (.node [v90, v629, v758, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v90, v629, v897, v1094, v1308, v1432, v1483] (.node [v90, v629, v897, v1094, v1308, v1349, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllrrl_ok : everyKey (rowOK 5 level5) level6lllrrl = true := by decide +kernel
def level6lllrrr : BinaryTree (List W) := (.node [v102, v375, v629, v848, v1094, v1308, v1483] (.node [v102, v375, v419, v629, v1094, v1308, v1483] (.node [v101, v375, v629, v897, v1094, v1308, v1483] (.node [v99, v629, v814, v897, v1094, v1308, v1483] (.node [v99, v375, v629, v897, v1094, v1308, v1483] .nil .nil) (.node [v99, v629, v897, v1094, v1308, v1483] .nil .nil)) (.node [v102, v237, v629, v897, v1094, v1308, v1483] (.node [v102, v159, v375, v629, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v102, v375, v497, v897, v1094, v1308, v1483] (.node [v102, v375, v480, v897, v1094, v1308, v1483] (.node [v102, v375, v422, v629, v1094, v1308, v1483] .nil .nil) .nil) (.node [v102, v375, v629, v791, v1094, v1308, v1483] (.node [v102, v375, v629, v758, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v102, v375, v897, v1094, v1215, v1308, v1483] (.node [v102, v375, v629, v1019, v1094, v1308, v1483] (.node [v102, v375, v629, v934, v1094, v1308, v1483] (.node [v102, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v102, v375, v629, v1094, v1308, v1483, v1554] (.node [v102, v375, v629, v1094, v1308, v1462, v1483] .nil .nil) .nil)) (.node [v102, v629, v758, v1094, v1308, v1483] (.node [v102, v629, v758, v897, v1094, v1308, v1483] (.node [v102, v375, v897, v1094, v1308, v1483, v1578] .nil .nil) .nil) (.node [v106, v375, v629, v897, v1094, v1308, v1483] (.node [v105, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllrrr_ok : everyKey (rowOK 5 level5) level6lllrrr = true := by decide +kernel
def level6lllrr : BinaryTree (List W) := .node [v91, v375, v629, v897, v1094, v1308, v1483] level6lllrrl level6lllrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllrr_ok : everyKey (rowOK 5 level5) level6lllrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lllrrl && everyKey (rowOK 5 level5) level6lllrrr) = true
  rw [level6lllrrl_ok, level6lllrrr_ok]
  decide +kernel
def level6lllr : BinaryTree (List W) := .node [v88, v375, v897, v1094, v1308, v1483, v1578] level6lllrl level6lllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllr_ok : everyKey (rowOK 5 level5) level6lllr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lllrl && everyKey (rowOK 5 level5) level6lllrr) = true
  rw [level6lllrl_ok, level6lllrr_ok]
  decide +kernel
def level6lll : BinaryTree (List W) := .node [v64, v375, v897, v1094, v1215, v1308, v1483] level6llll level6lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lll_ok : everyKey (rowOK 5 level5) level6lll = true := by
  change (_ && everyKey (rowOK 5 level5) level6llll && everyKey (rowOK 5 level5) level6lllr) = true
  rw [level6llll_ok, level6lllr_ok]
  decide +kernel
def level6llrlll : BinaryTree (List W) := (.node [v108, v629, v708, v897, v1094, v1308, v1483] (.node [v108, v375, v629, v897, v1094, v1242, v1483] (.node [v108, v375, v480, v897, v1094, v1308, v1483] (.node [v108, v237, v629, v897, v1094, v1308, v1483] (.node [v108, v225, v629, v897, v1094, v1308, v1483] .nil .nil) (.node [v108, v264, v629, v897, v1094, v1308, v1483] .nil .nil)) (.node [v108, v375, v554, v897, v1094, v1308, v1483] (.node [v108, v375, v497, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v108, v375, v698, v897, v1094, v1308, v1483] (.node [v108, v375, v629, v897, v1094, v1432, v1483] (.node [v108, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v108, v375, v897, v1094, v1308, v1483, v1578] (.node [v108, v375, v897, v1094, v1215, v1308, v1483] .nil .nil) .nil))) (.node [v110, v375, v629, v897, v1094, v1308, v1483] (.node [v108, v629, v897, v1094, v1308, v1432, v1483] (.node [v108, v629, v897, v1060, v1094, v1308, v1483] (.node [v108, v629, v758, v897, v1094, v1308, v1483] .nil .nil) (.node [v108, v629, v897, v1094, v1308, v1349, v1483] .nil .nil)) (.node [v109, v375, v629, v897, v1094, v1308, v1483] (.node [v108, v629, v897, v1094, v1432, v1483] .nil .nil) .nil)) (.node [v113, v375, v629, v897, v1094, v1308, v1483] (.node [v113, v375, v497, v897, v1094, v1308, v1483] (.node [v111, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v113, v497, v897, v1094, v1308, v1483] (.node [v113, v497, v629, v897, v1094, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrlll_ok : everyKey (rowOK 5 level5) level6llrlll = true := by decide +kernel
def level6llrllr : BinaryTree (List W) := (.node [v132, v237, v629, v897, v1094, v1308, v1483] (.node [v125, v629, v897, v1094, v1308, v1406, v1483] (.node [v118, v480, v897, v1094, v1308, v1483] (.node [v118, v375, v629, v897, v1094, v1308, v1483] (.node [v118, v375, v480, v897, v1094, v1308, v1483] .nil .nil) (.node [v118, v480, v629, v897, v1094, v1308, v1483] .nil .nil)) (.node [v125, v375, v629, v897, v1094, v1308, v1483] (.node [v118, v629, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v130, v375, v629, v897, v1094, v1308, v1483] (.node [v129, v375, v629, v897, v1094, v1308, v1483] (.node [v125, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v132, v187, v375, v629, v897, v1308, v1483] (.node [v131, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v132, v375, v629, v814, v897, v1308] (.node [v132, v375, v497, v897, v1094, v1308, v1483] (.node [v132, v375, v480, v897, v1094, v1308, v1483] (.node [v132, v283, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v132, v375, v629, v814, v897, v1094, v1308] (.node [v132, v375, v535, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v132, v375, v629, v897, v1056, v1308, v1483] (.node [v132, v375, v629, v864, v1094, v1308, v1483] (.node [v132, v375, v629, v814, v897, v1308, v1483] .nil .nil) .nil) (.node [v132, v375, v629, v897, v1094, v1308, v1562] (.node [v132, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrllr_ok : everyKey (rowOK 5 level5) level6llrllr = true := by decide +kernel
def level6llrll : BinaryTree (List W) := .node [v113, v629, v897, v1094, v1308, v1483] level6llrlll level6llrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrll_ok : everyKey (rowOK 5 level5) level6llrll = true := by
  change (_ && everyKey (rowOK 5 level5) level6llrlll && everyKey (rowOK 5 level5) level6llrllr) = true
  rw [level6llrlll_ok, level6llrllr_ok]
  decide +kernel
def level6llrlrl : BinaryTree (List W) := (.node [v137, v375, v497, v897, v1094, v1308, v1483] (.node [v133, v375, v629, v897, v1094, v1308, v1483] (.node [v132, v375, v897, v1094, v1308, v1483, v1578] (.node [v132, v375, v685, v897, v1094, v1308, v1483] (.node [v132, v375, v629, v937, v1094, v1308, v1483] .nil .nil) (.node [v132, v375, v897, v1094, v1215, v1308, v1483] .nil .nil)) (.node [v132, v629, v758, v897, v1094, v1308, v1483] (.node [v132, v402, v629, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v136, v375, v629, v897, v1094, v1308, v1483] (.node [v135, v375, v629, v897, v1094, v1308, v1483] (.node [v134, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v137, v375, v480, v897, v1094, v1308, v1483] (.node [v137, v237, v629, v897, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v137, v375, v629, v897, v1094, v1308, v1590] (.node [v137, v375, v513, v629, v897, v1094, v1483] (.node [v137, v375, v513, v629, v897, v1094] (.node [v137, v375, v506, v897, v1094, v1308, v1483] .nil .nil) (.node [v137, v375, v513, v629, v897, v1094, v1308] .nil .nil)) (.node [v137, v375, v629, v897, v1094, v1308, v1483] (.node [v137, v375, v629, v897, v1094, v1214, v1483] .nil .nil) .nil)) (.node [v137, v375, v897, v1094, v1308, v1483, v1578] (.node [v137, v375, v897, v1094, v1215, v1308, v1483] (.node [v137, v375, v690, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v138, v375, v629, v897, v1094, v1308, v1483] (.node [v137, v629, v758, v897, v1094, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrlrl_ok : everyKey (rowOK 5 level5) level6llrlrl = true := by decide +kernel
def level6llrlrr : BinaryTree (List W) := (.node [v156, v375, v497, v897, v1094, v1308, v1483] (.node [v151, v375, v629, v897, v1094, v1308, v1483] (.node [v143, v375, v629, v897, v1094, v1308, v1483] (.node [v141, v375, v629, v897, v1094, v1308, v1483] (.node [v140, v375, v629, v897, v1094, v1308, v1483] .nil .nil) (.node [v141, v375, v897, v1094, v1308, v1483, v1578] .nil .nil)) (.node [v147, v375, v897, v1094, v1215, v1308, v1483] (.node [v147, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v153, v375, v629, v897, v1094, v1308, v1483] (.node [v153, v375, v480, v897, v1094, v1308, v1483] (.node [v152, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v155, v375, v629, v897, v1094, v1308, v1483] (.node [v154, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v159, v237, v629, v1094, v1308, v1483] (.node [v158, v375, v629, v897, v1094, v1308, v1483] (.node [v157, v375, v629, v897, v1094, v1308, v1483] (.node [v156, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v159, v237, v629, v897, v1094, v1308, v1483] (.node [v159, v237, v375, v629, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v159, v375, v480, v897, v1094, v1308, v1483] (.node [v159, v375, v422, v897, v1094, v1308, v1483] (.node [v159, v296, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v159, v375, v629, v722, v1094, v1308, v1483] (.node [v159, v375, v497, v897, v1094, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrlrr_ok : everyKey (rowOK 5 level5) level6llrlrr = true := by decide +kernel
def level6llrlr : BinaryTree (List W) := .node [v139, v375, v629, v897, v1094, v1308, v1483] level6llrlrl level6llrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrlr_ok : everyKey (rowOK 5 level5) level6llrlr = true := by
  change (_ && everyKey (rowOK 5 level5) level6llrlrl && everyKey (rowOK 5 level5) level6llrlrr) = true
  rw [level6llrlrl_ok, level6llrlrr_ok]
  decide +kernel
def level6llrl : BinaryTree (List W) := .node [v132, v375, v629, v897, v1308, v1406, v1483] level6llrll level6llrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrl_ok : everyKey (rowOK 5 level5) level6llrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6llrll && everyKey (rowOK 5 level5) level6llrlr) = true
  rw [level6llrll_ok, level6llrlr_ok]
  decide +kernel
def level6llrrll : BinaryTree (List W) := (.node [v167, v375, v629, v897, v1094, v1308, v1483] (.node [v159, v629, v758, v897, v1094, v1308, v1483] (.node [v159, v375, v897, v1094, v1215, v1308, v1483] (.node [v159, v375, v722, v897, v1094, v1308, v1483] (.node [v159, v375, v629, v973, v1094, v1308, v1483] .nil .nil) (.node [v159, v375, v722, v1094, v1308, v1483] .nil .nil)) (.node [v159, v413, v629, v897, v1094, v1308, v1483] (.node [v159, v375, v897, v1094, v1308, v1483, v1578] .nil .nil) .nil)) (.node [v166, v375, v629, v708, v1094, v1308, v1483] (.node [v161, v375, v629, v897, v1094, v1308, v1483] (.node [v160, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v166, v375, v629, v1094, v1308, v1483] (.node [v166, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v173, v375, v629, v897, v1094, v1308, v1483] (.node [v170, v629, v758, v897, v1094, v1308, v1483] (.node [v168, v629, v758, v897, v1094, v1308, v1483] (.node [v168, v375, v629, v897, v1094, v1308, v1483] .nil .nil) (.node [v170, v375, v629, v897, v1094, v1308, v1483] .nil .nil)) (.node [v171, v629, v758, v897, v1094, v1308, v1483] (.node [v171, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v175, v375, v480, v897, v1094, v1308, v1483] (.node [v175, v237, v629, v897, v1094, v1308, v1483] (.node [v174, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v175, v375, v629, v791, v1094, v1308, v1483] (.node [v175, v375, v497, v897, v1094, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrrll_ok : everyKey (rowOK 5 level5) level6llrrll = true := by decide +kernel
def level6llrrlr : BinaryTree (List W) := (.node [v181, v375, v629, v897, v1094, v1308, v1483] (.node [v175, v629, v758, v897, v1094, v1308, v1483] (.node [v175, v375, v629, v1308, v1483, v1554] (.node [v175, v375, v629, v897, v1308, v1483, v1554] (.node [v175, v375, v629, v897, v1094, v1308, v1483] .nil .nil) (.node [v175, v375, v629, v1094, v1308, v1483, v1554] .nil .nil)) (.node [v175, v375, v897, v1094, v1308, v1483, v1578] (.node [v175, v375, v897, v1094, v1215, v1308, v1483] .nil .nil) .nil)) (.node [v179, v375, v629, v897, v1094, v1308, v1483] (.node [v178, v375, v629, v897, v1094, v1308, v1483] (.node [v176, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v181, v375, v497, v897, v1094, v1308, v1483] (.node [v180, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v185, v375, v497, v897, v1094, v1308, v1483] (.node [v183, v375, v480, v897, v1094, v1308, v1483] (.node [v182, v375, v629, v897, v1094, v1308, v1483] (.node [v182, v375, v480, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v184, v375, v629, v897, v1094, v1308, v1483] (.node [v183, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v187, v237, v629, v897, v1094, v1308, v1483] (.node [v186, v375, v629, v897, v1094, v1308, v1483] (.node [v185, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v187, v375, v497, v897, v1094, v1308, v1483] (.node [v187, v375, v480, v897, v1094, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrrlr_ok : everyKey (rowOK 5 level5) level6llrrlr = true := by decide +kernel
def level6llrrl : BinaryTree (List W) := .node [v175, v375, v629, v897, v1027, v1308, v1483] level6llrrll level6llrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrrl_ok : everyKey (rowOK 5 level5) level6llrrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6llrrll && everyKey (rowOK 5 level5) level6llrrlr) = true
  rw [level6llrrll_ok, level6llrrlr_ok]
  decide +kernel
def level6llrrrl : BinaryTree (List W) := (.node [v190, v303, v375, v897, v1094, v1308, v1483] (.node [v187, v375, v897, v1094, v1215, v1308, v1483] (.node [v187, v375, v629, v897, v1094, v1308, v1483] (.node [v187, v375, v629, v737, v897, v1483] (.node [v187, v375, v629, v737, v897, v1308, v1483] .nil .nil) (.node [v187, v375, v629, v897, v1003, v1308, v1483] .nil .nil)) (.node [v187, v375, v629, v897, v1308, v1483, v1562] (.node [v187, v375, v629, v897, v1094, v1406, v1483] .nil .nil) .nil)) (.node [v188, v375, v629, v897, v1094, v1308, v1483] (.node [v187, v629, v758, v897, v1094, v1308, v1483] (.node [v187, v375, v897, v1094, v1308, v1483, v1578] .nil .nil) .nil) (.node [v190, v237, v629, v897, v1094, v1308, v1483] (.node [v189, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v190, v629, v708, v897, v1094, v1308, v1483] (.node [v190, v375, v629, v897, v1094, v1308, v1483] (.node [v190, v375, v497, v897, v1094, v1308, v1483] (.node [v190, v375, v480, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v190, v375, v897, v1094, v1308, v1483, v1578] (.node [v190, v375, v897, v1094, v1215, v1308, v1483] .nil .nil) .nil)) (.node [v193, v237, v629, v897, v1094, v1308, v1483] (.node [v193, v231, v375, v897, v1094, v1308, v1483] (.node [v190, v629, v758, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v193, v375, v422, v897, v1094, v1308, v1483] (.node [v193, v298, v629, v897, v1094, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrrrl_ok : everyKey (rowOK 5 level5) level6llrrrl = true := by decide +kernel
def level6llrrrr : BinaryTree (List W) := (.node [v193, v629, v758, v897, v1094, v1308, v1483] (.node [v193, v375, v722, v897, v1094, v1308, v1483] (.node [v193, v375, v629, v897, v1094, v1308, v1483] (.node [v193, v375, v629, v807, v1094, v1308, v1483] (.node [v193, v375, v497, v897, v1094, v1308, v1483] .nil .nil) (.node [v193, v375, v629, v897, v996, v1308, v1483] .nil .nil)) (.node [v193, v375, v629, v971, v1094, v1308, v1483] (.node [v193, v375, v629, v897, v1194, v1308, v1483] .nil .nil) .nil)) (.node [v193, v375, v897, v1094, v1308, v1483, v1578] (.node [v193, v375, v897, v1094, v1215, v1308, v1483] (.node [v193, v375, v897, v1094, v1194, v1308, v1483] .nil .nil) .nil) (.node [v193, v629, v701, v897, v1094, v1308, v1483] (.node [v193, v375, v897, v1194, v1308, v1483] .nil .nil) .nil))) (.node [v198, v375, v629, v897, v1094, v1308, v1483] (.node [v196, v237, v629, v897, v1094, v1308, v1483] (.node [v195, v375, v629, v897, v1094, v1308, v1483] (.node [v194, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v197, v375, v629, v897, v1094, v1308, v1483] (.node [v196, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v202, v375, v629, v897, v1094, v1308, v1483] (.node [v201, v375, v629, v897, v1094, v1308, v1483] (.node [v200, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v204, v375, v629, v897, v1094, v1308, v1483] (.node [v203, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrrrr_ok : everyKey (rowOK 5 level5) level6llrrrr = true := by decide +kernel
def level6llrrr : BinaryTree (List W) := .node [v193, v375, v480, v897, v1094, v1308, v1483] level6llrrrl level6llrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrrr_ok : everyKey (rowOK 5 level5) level6llrrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6llrrrl && everyKey (rowOK 5 level5) level6llrrrr) = true
  rw [level6llrrrl_ok, level6llrrrr_ok]
  decide +kernel
def level6llrr : BinaryTree (List W) := .node [v187, v375, v629, v737, v897, v1094, v1483] level6llrrl level6llrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrr_ok : everyKey (rowOK 5 level5) level6llrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6llrrl && everyKey (rowOK 5 level5) level6llrrr) = true
  rw [level6llrrl_ok, level6llrrr_ok]
  decide +kernel
def level6llr : BinaryTree (List W) := .node [v159, v375, v629, v897, v1094, v1308, v1483] level6llrl level6llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llr_ok : everyKey (rowOK 5 level5) level6llr = true := by
  change (_ && everyKey (rowOK 5 level5) level6llrl && everyKey (rowOK 5 level5) level6llrr) = true
  rw [level6llrl_ok, level6llrr_ok]
  decide +kernel
def level6ll : BinaryTree (List W) := .node [v107, v375, v629, v897, v1094, v1308, v1483] level6lll level6llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6ll_ok : everyKey (rowOK 5 level5) level6ll = true := by
  change (_ && everyKey (rowOK 5 level5) level6lll && everyKey (rowOK 5 level5) level6llr) = true
  rw [level6lll_ok, level6llr_ok]
  decide +kernel
def level6lrllll : BinaryTree (List W) := (.node [v220, v375, v497, v897, v1094, v1308, v1483] (.node [v216, v375, v480, v897, v1094, v1308, v1483] (.node [v210, v375, v629, v897, v1214, v1308, v1483] (.node [v208, v375, v629, v897, v1094, v1308, v1483] (.node [v207, v375, v897, v1094, v1215, v1308, v1483] .nil .nil) (.node [v210, v375, v629, v897, v1094, v1308, v1483] .nil .nil)) (.node [v215, v375, v629, v897, v1094, v1308, v1483] (.node [v210, v375, v629, v897, v1308, v1483] .nil .nil) .nil)) (.node [v218, v375, v480, v897, v1094, v1308, v1483] (.node [v217, v375, v629, v897, v1094, v1308, v1483] (.node [v216, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v219, v375, v629, v897, v1094, v1308, v1483] (.node [v218, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v223, v375, v629, v897, v1094, v1308, v1483] (.node [v222, v237, v629, v897, v1094, v1308, v1483] (.node [v221, v375, v497, v897, v1094, v1308, v1483] (.node [v220, v375, v629, v897, v1094, v1308, v1483] .nil .nil) (.node [v221, v375, v629, v897, v1094, v1308, v1483] .nil .nil)) (.node [v223, v237, v629, v897, v1094, v1308, v1483] (.node [v222, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v225, v266, v629, v897, v1094, v1308, v1483] (.node [v225, v237, v629, v897, v1094, v1308, v1483] (.node [v224, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v225, v375, v497, v897, v1094, v1308, v1483] (.node [v225, v375, v480, v897, v1094, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrllll_ok : everyKey (rowOK 5 level5) level6lrllll = true := by decide +kernel
def level6lrlllr : BinaryTree (List W) := (.node [v227, v375, v629, v897, v1094, v1308, v1483] (.node [v225, v629, v897, v1094, v1242, v1308, v1483] (.node [v225, v375, v897, v1094, v1308, v1483, v1578] (.node [v225, v375, v629, v897, v1094, v1432, v1483] (.node [v225, v375, v629, v897, v1094, v1308, v1483] .nil .nil) (.node [v225, v375, v897, v1094, v1215, v1308, v1483] .nil .nil)) (.node [v225, v629, v897, v1094, v1205, v1308, v1483] (.node [v225, v629, v758, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v226, v237, v629, v897, v1094, v1308, v1483] (.node [v225, v629, v897, v1094, v1308, v1483, v1544] (.node [v225, v629, v897, v1094, v1242, v1483] .nil .nil) .nil) (.node [v227, v237, v629, v897, v1094, v1308, v1483] (.node [v226, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v231, v375, v629, v897, v996, v1308, v1483] (.node [v231, v237, v629, v897, v1094, v1308, v1483] (.node [v230, v375, v629, v897, v1094, v1308, v1483] (.node [v228, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v231, v375, v497, v897, v1094, v1308, v1483] (.node [v231, v375, v480, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v231, v375, v897, v996, v1094, v1308, v1483] (.node [v231, v375, v629, v897, v1194, v1308, v1483] (.node [v231, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v231, v375, v897, v1094, v1215, v1308, v1483] (.node [v231, v375, v897, v996, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlllr_ok : everyKey (rowOK 5 level5) level6lrlllr = true := by decide +kernel
def level6lrlll : BinaryTree (List W) := .node [v225, v375, v629, v897, v1094, v1242, v1483] level6lrllll level6lrlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlll_ok : everyKey (rowOK 5 level5) level6lrlll = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrllll && everyKey (rowOK 5 level5) level6lrlllr) = true
  rw [level6lrllll_ok, level6lrlllr_ok]
  decide +kernel
def level6lrllrl : BinaryTree (List W) := (.node [v237, v375, v629, v897, v1094, v1308, v1483] (.node [v237, v375, v422, v629, v1094, v1308, v1483] (.node [v237, v266, v629, v897, v1094, v1308, v1483] (.node [v237, v237, v629, v897, v1094, v1308, v1483] (.node [v231, v629, v758, v897, v1094, v1308, v1483] .nil .nil) (.node [v237, v264, v629, v897, v1094, v1308, v1483] .nil .nil)) (.node [v237, v375, v419, v629, v1094, v1308, v1483] (.node [v237, v303, v629, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v237, v375, v629, v758, v1094, v1308, v1483] (.node [v237, v375, v497, v897, v1094, v1308, v1483] (.node [v237, v375, v480, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v237, v375, v629, v848, v1094, v1308, v1483] (.node [v237, v375, v629, v791, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v237, v419, v629, v897, v1094, v1308, v1483] (.node [v237, v375, v629, v1094, v1308, v1483, v1554] (.node [v237, v375, v629, v1019, v1094, v1308, v1483] (.node [v237, v375, v629, v934, v1094, v1308, v1483] .nil .nil) (.node [v237, v375, v629, v1094, v1308, v1462, v1483] .nil .nil)) (.node [v237, v375, v897, v1094, v1308, v1483, v1578] (.node [v237, v375, v897, v1094, v1215, v1308, v1483] .nil .nil) .nil)) (.node [v237, v422, v629, v1094, v1308, v1483] (.node [v237, v422, v629, v897, v1094, v1308, v1483] (.node [v237, v419, v629, v1094, v1308, v1483] .nil .nil) .nil) (.node [v237, v480, v897, v1094, v1308, v1483] (.node [v237, v480, v629, v897, v1094, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrllrl_ok : everyKey (rowOK 5 level5) level6lrllrl = true := by decide +kernel
def level6lrllrr : BinaryTree (List W) := (.node [v237, v629, v848, v897, v1094, v1308, v1483] (.node [v237, v629, v737, v897, v1094, v1308, v1483] (.node [v237, v629, v708, v897, v1094, v1308, v1483] (.node [v237, v513, v629, v897, v1094, v1308, v1483] (.node [v237, v497, v897, v1094, v1308, v1483] .nil .nil) (.node [v237, v629, v651, v897, v1094, v1308, v1483] .nil .nil)) (.node [v237, v629, v727, v897, v1094, v1308, v1483] (.node [v237, v629, v722, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v237, v629, v791, v897, v1094, v1308, v1483] (.node [v237, v629, v758, v1094, v1308, v1483] (.node [v237, v629, v758, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v237, v629, v814, v897, v1094, v1308, v1483] (.node [v237, v629, v791, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v237, v629, v897, v1003, v1094, v1308, v1483] (.node [v237, v629, v897, v934, v1094, v1308, v1483] (.node [v237, v629, v897, v897, v1094, v1308, v1483] (.node [v237, v629, v848, v1094, v1308, v1483] .nil .nil) .nil) (.node [v237, v629, v897, v996, v1094, v1308, v1483] (.node [v237, v629, v897, v973, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v237, v629, v897, v1027, v1094, v1308, v1483] (.node [v237, v629, v897, v1019, v1094, v1308, v1483] (.node [v237, v629, v897, v1010, v1094, v1308, v1483] .nil .nil) .nil) (.node [v237, v629, v897, v1060, v1094, v1308, v1483] (.node [v237, v629, v897, v1056, v1094, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrllrr_ok : everyKey (rowOK 5 level5) level6lrllrr = true := by decide +kernel
def level6lrllr : BinaryTree (List W) := .node [v237, v497, v629, v897, v1094, v1308, v1483] level6lrllrl level6lrllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrllr_ok : everyKey (rowOK 5 level5) level6lrllr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrllrl && everyKey (rowOK 5 level5) level6lrllrr) = true
  rw [level6lrllrl_ok, level6lrllrr_ok]
  decide +kernel
def level6lrll : BinaryTree (List W) := .node [v231, v375, v897, v1094, v1308, v1483, v1578] level6lrlll level6lrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrll_ok : everyKey (rowOK 5 level5) level6lrll = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrlll && everyKey (rowOK 5 level5) level6lrllr) = true
  rw [level6lrlll_ok, level6lrllr_ok]
  decide +kernel
def level6lrlrll : BinaryTree (List W) := (.node [v237, v629, v897, v1094, v1308, v1432, v1483] (.node [v237, v629, v897, v1094, v1252, v1308, v1483] (.node [v237, v629, v897, v1094, v1214, v1308, v1483] (.node [v237, v629, v897, v1094, v1194, v1308, v1483] (.node [v237, v629, v897, v1094, v1191, v1308, v1483] .nil .nil) (.node [v237, v629, v897, v1094, v1205, v1308, v1483] .nil .nil)) (.node [v237, v629, v897, v1094, v1242, v1308, v1483] (.node [v237, v629, v897, v1094, v1215, v1308, v1483] .nil .nil) .nil)) (.node [v237, v629, v897, v1094, v1308, v1356, v1483] (.node [v237, v629, v897, v1094, v1308, v1349, v1483] (.node [v237, v629, v897, v1094, v1295, v1308, v1483] .nil .nil) .nil) (.node [v237, v629, v897, v1094, v1308, v1429, v1483] (.node [v237, v629, v897, v1094, v1308, v1406, v1483] .nil .nil) .nil))) (.node [v237, v629, v897, v1094, v1308, v1483, v1554] (.node [v237, v629, v897, v1094, v1308, v1483, v1504] (.node [v237, v629, v897, v1094, v1308, v1483] (.node [v237, v629, v897, v1094, v1308, v1462, v1483] .nil .nil) (.node [v237, v629, v897, v1094, v1308, v1483, v1502] .nil .nil)) (.node [v237, v629, v897, v1094, v1308, v1483, v1544] (.node [v237, v629, v897, v1094, v1308, v1483, v1536] .nil .nil) .nil)) (.node [v237, v629, v897, v1094, v1308, v1483, v1590] (.node [v237, v629, v897, v1094, v1308, v1483, v1578] (.node [v237, v629, v897, v1094, v1308, v1483, v1562] .nil .nil) .nil) (.node [v237, v629, v1019, v1094, v1308, v1483] (.node [v237, v629, v934, v1094, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlrll_ok : everyKey (rowOK 5 level5) level6lrlrll = true := by decide +kernel
def level6lrlrlr : BinaryTree (List W) := (.node [v264, v375, v629, v897, v1094, v1308, v1483] (.node [v252, v375, v629, v897, v1094, v1308, v1483] (.node [v249, v375, v629, v897, v1094, v1308, v1483] (.node [v237, v897, v1094, v1215, v1308, v1483] (.node [v237, v629, v1094, v1308, v1483, v1554] .nil .nil) (.node [v237, v897, v1094, v1308, v1483, v1578] .nil .nil)) (.node [v249, v629, v897, v1094, v1308, v1483] (.node [v249, v629, v897, v1010, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v264, v375, v480, v897, v1094, v1308, v1483] (.node [v264, v266, v629, v897, v1094, v1308, v1483] (.node [v263, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v264, v375, v629, v897, v1094, v1308, v1349] (.node [v264, v375, v497, v897, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v264, v629, v897, v1094, v1242, v1308, v1483] (.node [v264, v375, v897, v1094, v1308, v1483, v1578] (.node [v264, v375, v897, v1094, v1215, v1308, v1483] (.node [v264, v375, v629, v897, v1094, v1308, v1544] .nil .nil) .nil) (.node [v264, v629, v897, v1094, v1205, v1308, v1483] (.node [v264, v629, v758, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v265, v375, v629, v897, v1094, v1308, v1483] (.node [v264, v629, v897, v1094, v1308, v1544] (.node [v264, v629, v897, v1094, v1308, v1483, v1544] .nil .nil) .nil) (.node [v266, v375, v497, v897, v1094, v1308, v1483] (.node [v266, v375, v480, v897, v1094, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlrlr_ok : everyKey (rowOK 5 level5) level6lrlrlr = true := by decide +kernel
def level6lrlrl : BinaryTree (List W) := .node [v237, v629, v1094, v1308, v1462, v1483] level6lrlrll level6lrlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlrl_ok : everyKey (rowOK 5 level5) level6lrlrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrlrll && everyKey (rowOK 5 level5) level6lrlrlr) = true
  rw [level6lrlrll_ok, level6lrlrlr_ok]
  decide +kernel
def level6lrlrrl : BinaryTree (List W) := (.node [v277, v629, v897, v1027, v1094, v1308, v1483] (.node [v266, v629, v897, v1060, v1094, v1308, v1483] (.node [v266, v375, v897, v1094, v1308, v1483, v1578] (.node [v266, v375, v629, v897, v1205, v1308, v1483] (.node [v266, v375, v629, v897, v1094, v1308, v1483] .nil .nil) (.node [v266, v375, v897, v1094, v1215, v1308, v1483] .nil .nil)) (.node [v266, v629, v758, v897, v1094, v1308, v1483] (.node [v266, v629, v708, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v266, v629, v897, v1094, v1308, v1432, v1483] (.node [v266, v629, v897, v1094, v1308, v1349, v1483] (.node [v266, v629, v897, v1060, v1308, v1483] .nil .nil) .nil) (.node [v277, v375, v629, v897, v1094, v1308, v1483] (.node [v267, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v283, v629, v897, v1094, v1308, v1483] (.node [v280, v629, v897, v1003, v1094, v1308, v1483] (.node [v280, v375, v629, v897, v1094, v1308, v1483] (.node [v277, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v283, v375, v629, v897, v1094, v1308, v1483] (.node [v280, v629, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v287, v629, v897, v1094, v1308, v1483, v1504] (.node [v287, v629, v897, v1094, v1308, v1483] (.node [v287, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v293, v375, v629, v897, v1094, v1308, v1483] (.node [v292, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlrrl_ok : everyKey (rowOK 5 level5) level6lrlrrl = true := by decide +kernel
def level6lrlrrr : BinaryTree (List W) := (.node [v303, v629, v758, v897, v1094, v1308, v1483] (.node [v303, v375, v629, v897, v1094, v1308, v1483] (.node [v303, v375, v422, v897, v1094, v1308, v1483] (.node [v298, v375, v629, v897, v1094, v1308, v1483] (.node [v296, v629, v897, v1094, v1308, v1483] .nil .nil) (.node [v298, v629, v897, v1094, v1308, v1483] .nil .nil)) (.node [v303, v375, v497, v897, v1094, v1308, v1483] (.node [v303, v375, v480, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v303, v375, v897, v1094, v1215, v1308, v1483] (.node [v303, v375, v722, v897, v1094, v1308, v1483] (.node [v303, v375, v708, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v303, v629, v708, v897, v1094, v1308, v1483] (.node [v303, v375, v897, v1094, v1308, v1483, v1578] .nil .nil) .nil))) (.node [v309, v629, v897, v1094, v1308, v1483] (.node [v308, v375, v629, v897, v1094, v1308, v1483] (.node [v304, v375, v629, v897, v1094, v1308, v1483] (.node [v303, v708, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v309, v629, v897, v973, v1094, v1308, v1483] (.node [v309, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v317, v375, v629, v897, v1094, v1308, v1483] (.node [v313, v375, v629, v897, v1094, v1308, v1483] (.node [v311, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v319, v375, v629, v897, v1094, v1308, v1483] (.node [v318, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlrrr_ok : everyKey (rowOK 5 level5) level6lrlrrr = true := by decide +kernel
def level6lrlrr : BinaryTree (List W) := .node [v296, v375, v629, v897, v1094, v1308, v1483] level6lrlrrl level6lrlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlrr_ok : everyKey (rowOK 5 level5) level6lrlrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrlrrl && everyKey (rowOK 5 level5) level6lrlrrr) = true
  rw [level6lrlrrl_ok, level6lrlrrr_ok]
  decide +kernel
def level6lrlr : BinaryTree (List W) := .node [v266, v375, v629, v897, v1060, v1308, v1483] level6lrlrl level6lrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlr_ok : everyKey (rowOK 5 level5) level6lrlr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrlrl && everyKey (rowOK 5 level5) level6lrlrr) = true
  rw [level6lrlrl_ok, level6lrlrr_ok]
  decide +kernel
def level6lrl : BinaryTree (List W) := .node [v237, v629, v897, v1076, v1094, v1308, v1483] level6lrll level6lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrl_ok : everyKey (rowOK 5 level5) level6lrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrll && everyKey (rowOK 5 level5) level6lrlr) = true
  rw [level6lrll_ok, level6lrlr_ok]
  decide +kernel
def level6lrrlll : BinaryTree (List W) := (.node [v337, v375, v629, v897, v1094, v1308, v1483] (.node [v329, v375, v629, v897, v1094, v1308, v1483] (.node [v326, v375, v629, v897, v1094, v1308, v1483] (.node [v322, v375, v629, v897, v1094, v1308, v1483] (.node [v321, v375, v629, v897, v1094, v1308, v1483] .nil .nil) (.node [v322, v375, v897, v1094, v1215, v1308, v1483] .nil .nil)) (.node [v326, v629, v897, v1094, v1308, v1483] (.node [v326, v629, v897, v1019, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v332, v375, v629, v897, v1094, v1308, v1483] (.node [v329, v629, v897, v1094, v1308, v1483] (.node [v329, v629, v897, v1094, v1214, v1308, v1483] .nil .nil) .nil) (.node [v332, v629, v897, v1094, v1308, v1483, v1554] (.node [v332, v629, v897, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v346, v375, v629, v897, v1094, v1308, v1483] (.node [v343, v375, v629, v897, v1094, v1308, v1483] (.node [v341, v375, v629, v897, v1094, v1308, v1483] (.node [v340, v375, v629, v897, v1094, v1308, v1483] .nil .nil) (.node [v342, v375, v629, v897, v1094, v1308, v1483] .nil .nil)) (.node [v345, v375, v629, v897, v1094, v1308, v1483] (.node [v344, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v355, v375, v629, v897, v1094, v1308, v1483] (.node [v347, v375, v897, v1094, v1308, v1483, v1578] (.node [v347, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v355, v629, v897, v1094, v1308, v1483] (.node [v355, v629, v897, v1094, v1308, v1462, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrlll_ok : everyKey (rowOK 5 level5) level6lrrlll = true := by decide +kernel
def level6lrrllr : BinaryTree (List W) := (.node [v375, v414, v480, v897, v1094, v1308, v1483] (.node [v375, v400, v629, v897, v1094, v1308, v1483] (.node [v375, v382, v629, v897, v1094, v1308, v1483] (.node [v365, v629, v897, v1094, v1308, v1483, v1590] (.node [v365, v629, v897, v1094, v1308, v1483] .nil .nil) (.node [v375, v375, v629, v897, v1094, v1308, v1483] .nil .nil)) (.node [v375, v396, v629, v897, v1094, v1308, v1483] (.node [v375, v391, v629, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v375, v405, v629, v897, v1094, v1308, v1483] (.node [v375, v403, v629, v897, v1094, v1308, v1483] (.node [v375, v402, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v413, v629, v897, v1094, v1308, v1483] (.node [v375, v406, v629, v897, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v375, v419, v497, v897, v1094, v1308, v1483] (.node [v375, v415, v629, v897, v1094, v1308, v1483] (.node [v375, v415, v497, v897, v1094, v1308, v1483] (.node [v375, v414, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v419, v480, v897, v1094, v1308, v1483] (.node [v375, v418, v629, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v375, v419, v629, v897, v1010, v1094, v1483] (.node [v375, v419, v629, v791, v1094, v1308, v1483] (.node [v375, v419, v629, v727, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v419, v629, v897, v1094, v1462, v1483] (.node [v375, v419, v629, v897, v1094, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrllr_ok : everyKey (rowOK 5 level5) level6lrrllr = true := by decide +kernel
def level6lrrll : BinaryTree (List W) := .node [v365, v375, v629, v897, v1094, v1308, v1483] level6lrrlll level6lrrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrll_ok : everyKey (rowOK 5 level5) level6lrrll = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrrlll && everyKey (rowOK 5 level5) level6lrrllr) = true
  rw [level6lrrlll_ok, level6lrrllr_ok]
  decide +kernel
def level6lrrlrl : BinaryTree (List W) := (.node [v375, v422, v897, v973, v1094, v1308, v1483] (.node [v375, v421, v629, v897, v1094, v1308, v1483] (.node [v375, v419, v897, v1094, v1215, v1308, v1483] (.node [v375, v419, v629, v1094, v1308, v1483, v1504] (.node [v375, v419, v629, v1010, v1094, v1483] .nil .nil) (.node [v375, v419, v629, v1094, v1308, v1483, v1554] .nil .nil)) (.node [v375, v420, v629, v897, v1094, v1308, v1483] (.node [v375, v419, v897, v1094, v1308, v1483, v1578] .nil .nil) .nil)) (.node [v375, v422, v629, v722, v1094, v1308, v1483] (.node [v375, v422, v497, v897, v1094, v1308, v1483] (.node [v375, v422, v480, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v422, v629, v973, v1094, v1308, v1483] (.node [v375, v422, v629, v897, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v375, v424, v897, v1094, v1215, v1308, v1483] (.node [v375, v422, v897, v1094, v1308, v1483, v1578] (.node [v375, v422, v897, v1094, v1215, v1308, v1483] (.node [v375, v422, v897, v996, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v424, v629, v897, v1094, v1308, v1483] (.node [v375, v422, v973, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v375, v429, v629, v897, v1094, v1308, v1483] (.node [v375, v428, v629, v897, v1094, v1308, v1483] (.node [v375, v425, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v438, v629, v1094, v1242, v1308, v1483] (.node [v375, v438, v629, v897, v1094, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrlrl_ok : everyKey (rowOK 5 level5) level6lrrlrl = true := by decide +kernel
def level6lrrlrr : BinaryTree (List W) := (.node [v375, v467, v629, v897, v1094, v1308, v1483] (.node [v375, v447, v629, v1094, v1308, v1483] (.node [v375, v445, v629, v897, v1094, v1308, v1483] (.node [v375, v443, v629, v897, v1094, v1308, v1483] (.node [v375, v443, v629, v708, v1094, v1308, v1483] .nil .nil) (.node [v375, v443, v629, v1094, v1308, v1483] .nil .nil)) (.node [v375, v447, v629, v1094, v1214, v1308, v1483] (.node [v375, v447, v629, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v375, v459, v897, v1094, v1308, v1483] (.node [v375, v459, v897, v934, v1094, v1308, v1483] (.node [v375, v459, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v462, v629, v897, v1094, v1308, v1483] (.node [v375, v461, v629, v897, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v375, v473, v629, v897, v1094, v1308, v1483] (.node [v375, v473, v480, v897, v1094, v1308, v1483] (.node [v375, v471, v629, v897, v1094, v1308, v1483] (.node [v375, v469, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v473, v513, v897, v1094, v1308, v1483] (.node [v375, v473, v497, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v375, v480, v497, v897, v1094, v1308, v1483] (.node [v375, v480, v480, v897, v1094, v1308, v1483] (.node [v375, v473, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v480, v629, v897, v1094, v1252, v1483] (.node [v375, v480, v513, v897, v1094, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrlrr_ok : everyKey (rowOK 5 level5) level6lrrlrr = true := by decide +kernel
def level6lrrlr : BinaryTree (List W) := .node [v375, v438, v629, v1094, v1308, v1483] level6lrrlrl level6lrrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrlr_ok : everyKey (rowOK 5 level5) level6lrrlr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrrlrl && everyKey (rowOK 5 level5) level6lrrlrr) = true
  rw [level6lrrlrl_ok, level6lrrlrr_ok]
  decide +kernel
def level6lrrl : BinaryTree (List W) := .node [v375, v419, v629, v1010, v1094, v1308, v1483] level6lrrll level6lrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrl_ok : everyKey (rowOK 5 level5) level6lrrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrrll && everyKey (rowOK 5 level5) level6lrrlr) = true
  rw [level6lrrll_ok, level6lrrlr_ok]
  decide +kernel
def level6lrrrll : BinaryTree (List W) := (.node [v375, v480, v897, v948, v1094, v1308, v1483] (.node [v375, v480, v737, v897, v1094, v1308, v1483] (.node [v375, v480, v722, v897, v1094, v1308, v1483] (.node [v375, v480, v668, v897, v1094, v1308, v1483] (.node [v375, v480, v629, v897, v1094, v1483, v1578] .nil .nil) (.node [v375, v480, v708, v897, v1094, v1308, v1483] .nil .nil)) (.node [v375, v480, v730, v897, v1094, v1308, v1483] (.node [v375, v480, v727, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v375, v480, v814, v897, v1094, v1308, v1483] (.node [v375, v480, v791, v897, v1094, v1308, v1483] (.node [v375, v480, v758, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v480, v897, v934, v1094, v1308, v1483] (.node [v375, v480, v848, v897, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v375, v480, v897, v1027, v1094, v1308, v1483] (.node [v375, v480, v897, v1005, v1094, v1308, v1483] (.node [v375, v480, v897, v996, v1094, v1308, v1483] (.node [v375, v480, v897, v973, v1094, v1308, v1483] .nil .nil) (.node [v375, v480, v897, v1003, v1094, v1308, v1483] .nil .nil)) (.node [v375, v480, v897, v1019, v1094, v1308, v1483] (.node [v375, v480, v897, v1010, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v375, v480, v897, v1094, v1180, v1308, v1483] (.node [v375, v480, v897, v1060, v1094, v1308, v1483] (.node [v375, v480, v897, v1056, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v480, v897, v1094, v1205, v1308, v1483] (.node [v375, v480, v897, v1094, v1194, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrrll_ok : everyKey (rowOK 5 level5) level6lrrrll = true := by decide +kernel
def level6lrrrlr : BinaryTree (List W) := (.node [v375, v480, v897, v1094, v1308, v1483, v1504] (.node [v375, v480, v897, v1094, v1308, v1349, v1483] (.node [v375, v480, v897, v1094, v1252, v1308, v1483] (.node [v375, v480, v897, v1094, v1234, v1308, v1483] (.node [v375, v480, v897, v1094, v1215, v1308, v1483] .nil .nil) (.node [v375, v480, v897, v1094, v1242, v1308, v1483] .nil .nil)) (.node [v375, v480, v897, v1094, v1308, v1308, v1483] (.node [v375, v480, v897, v1094, v1252, v1483] .nil .nil) .nil)) (.node [v375, v480, v897, v1094, v1308, v1462, v1483] (.node [v375, v480, v897, v1094, v1308, v1432, v1483] (.node [v375, v480, v897, v1094, v1308, v1406, v1483] .nil .nil) .nil) (.node [v375, v480, v897, v1094, v1308, v1483, v1486] (.node [v375, v480, v897, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v375, v480, v897, v1094, v1308, v1483, v1590] (.node [v375, v480, v897, v1094, v1308, v1483, v1554] (.node [v375, v480, v897, v1094, v1308, v1483, v1544] (.node [v375, v480, v897, v1094, v1308, v1483, v1536] .nil .nil) .nil) (.node [v375, v480, v897, v1094, v1308, v1483, v1578] (.node [v375, v480, v897, v1094, v1308, v1483, v1562] .nil .nil) .nil)) (.node [v375, v497, v513, v897, v1094, v1308, v1483] (.node [v375, v497, v497, v897, v1094, v1308, v1483] (.node [v375, v480, v897, v1094, v1483, v1578] .nil .nil) .nil) (.node [v375, v497, v629, v897, v1094, v1308, v1483] (.node [v375, v497, v629, v897, v1094, v1215, v1308] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrrlr_ok : everyKey (rowOK 5 level5) level6lrrrlr = true := by decide +kernel
def level6lrrrl : BinaryTree (List W) := .node [v375, v480, v897, v1094, v1214, v1308, v1483] level6lrrrll level6lrrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrrl_ok : everyKey (rowOK 5 level5) level6lrrrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrrrll && everyKey (rowOK 5 level5) level6lrrrlr) = true
  rw [level6lrrrll_ok, level6lrrrlr_ok]
  decide +kernel
def level6lrrrrl : BinaryTree (List W) := (.node [v375, v497, v897, v973, v1094, v1308, v1483] (.node [v375, v497, v758, v897, v1094, v1308, v1483] (.node [v375, v497, v727, v897, v1094, v1308, v1483] (.node [v375, v497, v708, v897, v1094, v1308, v1483] (.node [v375, v497, v670, v897, v1094, v1308, v1483] .nil .nil) (.node [v375, v497, v722, v897, v1094, v1308, v1483] .nil .nil)) (.node [v375, v497, v737, v897, v1094, v1308, v1483] (.node [v375, v497, v729, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v375, v497, v848, v897, v1094, v1308, v1483] (.node [v375, v497, v814, v897, v1094, v1308, v1483] (.node [v375, v497, v791, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v497, v897, v951, v1094, v1308, v1483] (.node [v375, v497, v897, v934, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v375, v497, v897, v1027, v1094, v1308, v1483] (.node [v375, v497, v897, v1006, v1094, v1308, v1483] (.node [v375, v497, v897, v1003, v1094, v1308, v1483] (.node [v375, v497, v897, v996, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v497, v897, v1019, v1094, v1308, v1483] (.node [v375, v497, v897, v1010, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v375, v497, v897, v1094, v1183, v1308, v1483] (.node [v375, v497, v897, v1060, v1094, v1308, v1483] (.node [v375, v497, v897, v1056, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v497, v897, v1094, v1205, v1308, v1483] (.node [v375, v497, v897, v1094, v1194, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrrrl_ok : everyKey (rowOK 5 level5) level6lrrrrl = true := by decide +kernel
def level6lrrrrr : BinaryTree (List W) := (.node [v375, v497, v897, v1094, v1308, v1483, v1536] (.node [v375, v497, v897, v1094, v1308, v1406, v1483] (.node [v375, v497, v897, v1094, v1252, v1308, v1483] (.node [v375, v497, v897, v1094, v1215, v1308, v1483] (.node [v375, v497, v897, v1094, v1215, v1308] .nil .nil) (.node [v375, v497, v897, v1094, v1242, v1308, v1483] .nil .nil)) (.node [v375, v497, v897, v1094, v1308, v1349, v1483] (.node [v375, v497, v897, v1094, v1302, v1308, v1483] .nil .nil) .nil)) (.node [v375, v497, v897, v1094, v1308, v1483] (.node [v375, v497, v897, v1094, v1308, v1462, v1483] (.node [v375, v497, v897, v1094, v1308, v1432, v1483] .nil .nil) .nil) (.node [v375, v497, v897, v1094, v1308, v1483, v1504] (.node [v375, v497, v897, v1094, v1308, v1483, v1483] .nil .nil) .nil))) (.node [v375, v497, v897, v1094, v1308, v1483, v1590] (.node [v375, v497, v897, v1094, v1308, v1483, v1562] (.node [v375, v497, v897, v1094, v1308, v1483, v1554] (.node [v375, v497, v897, v1094, v1308, v1483, v1544] .nil .nil) .nil) (.node [v375, v497, v897, v1094, v1308, v1483, v1578] (.node [v375, v497, v897, v1094, v1308, v1483, v1571] .nil .nil) .nil)) (.node [v375, v506, v897, v1094, v1308, v1483] (.node [v375, v506, v629, v897, v1094, v1308, v1483] (.node [v375, v497, v897, v1094, v1308, v1536] .nil .nil) .nil) (.node [v375, v510, v629, v897, v1094, v1308, v1483] (.node [v375, v509, v629, v897, v1094, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrrrr_ok : everyKey (rowOK 5 level5) level6lrrrrr = true := by decide +kernel
def level6lrrrr : BinaryTree (List W) := .node [v375, v497, v897, v1094, v1214, v1308, v1483] level6lrrrrl level6lrrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrrr_ok : everyKey (rowOK 5 level5) level6lrrrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrrrrl && everyKey (rowOK 5 level5) level6lrrrrr) = true
  rw [level6lrrrrl_ok, level6lrrrrr_ok]
  decide +kernel
def level6lrrr : BinaryTree (List W) := .node [v375, v497, v629, v897, v1094, v1308, v1536] level6lrrrl level6lrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrr_ok : everyKey (rowOK 5 level5) level6lrrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrrrl && everyKey (rowOK 5 level5) level6lrrrr) = true
  rw [level6lrrrl_ok, level6lrrrr_ok]
  decide +kernel
def level6lrr : BinaryTree (List W) := .node [v375, v480, v629, v897, v1094, v1308, v1483] level6lrrl level6lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrr_ok : everyKey (rowOK 5 level5) level6lrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrrl && everyKey (rowOK 5 level5) level6lrrr) = true
  rw [level6lrrl_ok, level6lrrr_ok]
  decide +kernel
def level6lr : BinaryTree (List W) := .node [v320, v375, v629, v897, v1094, v1308, v1483] level6lrl level6lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lr_ok : everyKey (rowOK 5 level5) level6lr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrl && everyKey (rowOK 5 level5) level6lrr) = true
  rw [level6lrl_ok, level6lrr_ok]
  decide +kernel
def level6l : BinaryTree (List W) := .node [v207, v375, v629, v897, v1094, v1308, v1483] level6ll level6lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6l_ok : everyKey (rowOK 5 level5) level6l = true := by
  change (_ && everyKey (rowOK 5 level5) level6ll && everyKey (rowOK 5 level5) level6lr) = true
  rw [level6ll_ok, level6lr_ok]
  decide +kernel
def level6rlllll : BinaryTree (List W) := (.node [v375, v518, v629, v897, v1094, v1308, v1483] (.node [v375, v513, v897, v1094, v1215, v1308, v1483] (.node [v375, v513, v629, v897, v1094, v1308, v1483] (.node [v375, v513, v629, v814, v897, v1094, v1308] (.node [v375, v512, v629, v897, v1094, v1308, v1483] .nil .nil) (.node [v375, v513, v629, v897, v1094, v1214, v1308] .nil .nil)) (.node [v375, v513, v629, v897, v1094, v1483, v1590] (.node [v375, v513, v629, v897, v1094, v1308, v1562] .nil .nil) .nil)) (.node [v375, v515, v629, v897, v1094, v1308, v1483] (.node [v375, v514, v629, v897, v1094, v1308, v1483] (.node [v375, v513, v897, v1094, v1308, v1483, v1578] .nil .nil) .nil) (.node [v375, v517, v629, v897, v1094, v1308, v1483] (.node [v375, v516, v629, v897, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v375, v536, v629, v897, v1094, v1308, v1483] (.node [v375, v529, v897, v1094, v1308, v1483] (.node [v375, v529, v629, v897, v1094, v1308, v1483] (.node [v375, v521, v629, v897, v1094, v1308, v1483] .nil .nil) (.node [v375, v529, v897, v1010, v1094, v1308, v1483] .nil .nil)) (.node [v375, v535, v897, v1094, v1308, v1483] (.node [v375, v535, v629, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v375, v539, v629, v897, v1094, v1308, v1483] (.node [v375, v536, v897, v1094, v1308, v1483] (.node [v375, v536, v897, v1003, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v539, v897, v1094, v1308, v1483, v1504] (.node [v375, v539, v897, v1094, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlllll_ok : everyKey (rowOK 5 level5) level6rlllll = true := by decide +kernel
def level6rllllr : BinaryTree (List W) := (.node [v375, v575, v897, v1094, v1308, v1483, v1544] (.node [v375, v562, v629, v897, v1094, v1308, v1483] (.node [v375, v558, v629, v897, v1094, v1308, v1483] (.node [v375, v554, v629, v897, v1094, v1308, v1483] (.node [v375, v549, v629, v897, v1094, v1308, v1483] .nil .nil) (.node [v375, v554, v897, v1094, v1308, v1483] .nil .nil)) (.node [v375, v560, v629, v897, v1094, v1308, v1483] (.node [v375, v558, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v375, v572, v897, v1094, v1308, v1483] (.node [v375, v572, v897, v1094, v1242, v1308, v1483] (.node [v375, v572, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v575, v897, v1094, v1308, v1483] (.node [v375, v575, v629, v897, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v375, v588, v897, v1094, v1308, v1483] (.node [v375, v584, v897, v1094, v1308, v1483] (.node [v375, v584, v737, v897, v1094, v1308, v1483] (.node [v375, v584, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v588, v727, v897, v1094, v1308, v1483] (.node [v375, v588, v629, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v375, v597, v629, v897, v1094, v1308, v1483] (.node [v375, v592, v897, v1094, v1308, v1483] (.node [v375, v592, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v597, v897, v1094, v1308, v1483, v1562] (.node [v375, v597, v897, v1094, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllllr_ok : everyKey (rowOK 5 level5) level6rllllr = true := by decide +kernel
def level6rllll : BinaryTree (List W) := .node [v375, v548, v629, v897, v1094, v1308, v1483] level6rlllll level6rllllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllll_ok : everyKey (rowOK 5 level5) level6rllll = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlllll && everyKey (rowOK 5 level5) level6rllllr) = true
  rw [level6rlllll_ok, level6rllllr_ok]
  decide +kernel
def level6rlllrl : BinaryTree (List W) := (.node [v375, v629, v647, v897, v1094, v1308, v1483] (.node [v375, v620, v629, v897, v1094, v1308, v1483] (.node [v375, v603, v897, v1094, v1308, v1483] (.node [v375, v602, v897, v1094, v1308, v1483] (.node [v375, v602, v897, v1094, v1214, v1308, v1483] .nil .nil) (.node [v375, v603, v629, v897, v1094, v1308, v1483] .nil .nil)) (.node [v375, v609, v629, v897, v1094, v1308, v1483] (.node [v375, v603, v897, v1094, v1308, v1483, v1554] .nil .nil) .nil)) (.node [v375, v629, v629, v897, v1094, v1308, v1483] (.node [v375, v620, v897, v1094, v1308, v1483, v1590] (.node [v375, v620, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v646, v897, v1094, v1308, v1483] (.node [v375, v629, v644, v897, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v375, v629, v666, v897, v1094, v1308, v1483] (.node [v375, v629, v652, v897, v1094, v1308, v1483] (.node [v375, v629, v649, v897, v1094, v1308, v1483] (.node [v375, v629, v648, v897, v1094, v1308, v1483] .nil .nil) (.node [v375, v629, v651, v897, v1094, v1308, v1483] .nil .nil)) (.node [v375, v629, v659, v897, v1094, v1308, v1483] (.node [v375, v629, v655, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v375, v629, v670, v897, v1094, v1308, v1483] (.node [v375, v629, v669, v897, v1094, v1308, v1483] (.node [v375, v629, v668, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v685, v897, v1094, v1308, v1483] (.node [v375, v629, v682, v897, v1094, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlllrl_ok : everyKey (rowOK 5 level5) level6rlllrl = true := by decide +kernel
def level6rlllrr : BinaryTree (List W) := (.node [v375, v629, v719, v897, v1094, v1308, v1483] (.node [v375, v629, v710, v897, v1094, v1308, v1483] (.node [v375, v629, v701, v897, v1094, v1308, v1483] (.node [v375, v629, v697, v897, v1094, v1308, v1483] (.node [v375, v629, v695, v897, v1094, v1308, v1483] .nil .nil) (.node [v375, v629, v698, v897, v1094, v1308, v1483] .nil .nil)) (.node [v375, v629, v709, v897, v1094, v1308, v1483] (.node [v375, v629, v708, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v375, v629, v715, v897, v1094, v1308, v1483] (.node [v375, v629, v713, v897, v1094, v1308, v1483] (.node [v375, v629, v711, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v717, v897, v1094, v1308, v1483] (.node [v375, v629, v716, v897, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v375, v629, v727, v848, v1094, v1308, v1483] (.node [v375, v629, v722, v897, v1094, v1308, v1483] (.node [v375, v629, v722, v791, v1094, v1308, v1483] (.node [v375, v629, v720, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v726, v897, v1094, v1308, v1483] (.node [v375, v629, v722, v1094, v1308, v1483, v1554] .nil .nil) .nil)) (.node [v375, v629, v727, v897, v1094, v1462, v1483] (.node [v375, v629, v727, v897, v1094, v1308, v1483] (.node [v375, v629, v727, v897, v1010, v1094, v1483] .nil .nil) .nil) (.node [v375, v629, v727, v1094, v1308, v1462, v1483] (.node [v375, v629, v727, v1019, v1094, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlllrr_ok : everyKey (rowOK 5 level5) level6rlllrr = true := by decide +kernel
def level6rlllr : BinaryTree (List W) := .node [v375, v629, v690, v897, v1094, v1308, v1483] level6rlllrl level6rlllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlllr_ok : everyKey (rowOK 5 level5) level6rlllr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlllrl && everyKey (rowOK 5 level5) level6rlllrr) = true
  rw [level6rlllrl_ok, level6rlllrr_ok]
  decide +kernel
def level6rlll : BinaryTree (List W) := .node [v375, v602, v629, v897, v1094, v1308, v1483] level6rllll level6rlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlll_ok : everyKey (rowOK 5 level5) level6rlll = true := by
  change (_ && everyKey (rowOK 5 level5) level6rllll && everyKey (rowOK 5 level5) level6rlllr) = true
  rw [level6rllll_ok, level6rlllr_ok]
  decide +kernel
def level6rllrll : BinaryTree (List W) := (.node [v375, v629, v741, v897, v1094, v1308, v1483] (.node [v375, v629, v737, v814, v897, v1308, v1483] (.node [v375, v629, v731, v897, v1094, v1308, v1483] (.node [v375, v629, v729, v897, v1094, v1308, v1483] (.node [v375, v629, v728, v897, v1094, v1308, v1483] .nil .nil) (.node [v375, v629, v730, v897, v1094, v1308, v1483] .nil .nil)) (.node [v375, v629, v733, v897, v1094, v1308, v1483] (.node [v375, v629, v732, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v375, v629, v737, v897, v1094, v1308, v1483] (.node [v375, v629, v737, v897, v1056, v1308, v1483] (.node [v375, v629, v737, v897, v1003, v1094, v1483] .nil .nil) .nil) (.node [v375, v629, v738, v897, v1094, v1308, v1483] (.node [v375, v629, v737, v897, v1308, v1406, v1483] .nil .nil) .nil))) (.node [v375, v629, v755, v897, v1094, v1308, v1483] (.node [v375, v629, v745, v897, v1094, v1308, v1483] (.node [v375, v629, v743, v897, v1094, v1308, v1483] (.node [v375, v629, v742, v897, v1094, v1308, v1483] .nil .nil) (.node [v375, v629, v744, v897, v1094, v1308, v1483] .nil .nil)) (.node [v375, v629, v749, v897, v1094, v1308, v1483] (.node [v375, v629, v748, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v375, v629, v768, v897, v1094, v1308, v1483] (.node [v375, v629, v767, v897, v1094, v1308, v1483] (.node [v375, v629, v758, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v770, v897, v1094, v1308, v1483] (.node [v375, v629, v769, v897, v1094, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllrll_ok : everyKey (rowOK 5 level5) level6rllrll = true := by decide +kernel
def level6rllrlr : BinaryTree (List W) := (.node [v375, v629, v792, v897, v1094, v1308, v1483] (.node [v375, v629, v791, v897, v1308, v1483, v1554] (.node [v375, v629, v791, v848, v1094, v1308, v1483] (.node [v375, v629, v786, v897, v1094, v1308, v1483] (.node [v375, v629, v772, v897, v1094, v1308, v1483] .nil .nil) (.node [v375, v629, v790, v897, v1094, v1308, v1483] .nil .nil)) (.node [v375, v629, v791, v897, v1094, v1308, v1483] (.node [v375, v629, v791, v897, v1027, v1308, v1483] .nil .nil) .nil)) (.node [v375, v629, v791, v1027, v1094, v1308, v1483] (.node [v375, v629, v791, v1019, v1094, v1308, v1483] (.node [v375, v629, v791, v973, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v791, v1094, v1308, v1462, v1483] (.node [v375, v629, v791, v1027, v1308, v1483] .nil .nil) .nil))) (.node [v375, v629, v805, v1060, v1094, v1308, v1483] (.node [v375, v629, v796, v897, v1094, v1308, v1483] (.node [v375, v629, v794, v897, v1094, v1308, v1483] (.node [v375, v629, v793, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v805, v897, v1094, v1308, v1483] (.node [v375, v629, v797, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v375, v629, v807, v1094, v1308, v1483] (.node [v375, v629, v807, v897, v1094, v1308, v1483] (.node [v375, v629, v805, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v814, v897, v1056, v1094, v1308] (.node [v375, v629, v814, v897, v1003, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllrlr_ok : everyKey (rowOK 5 level5) level6rllrlr = true := by decide +kernel
def level6rllrl : BinaryTree (List W) := .node [v375, v629, v771, v897, v1094, v1308, v1483] level6rllrll level6rllrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllrl_ok : everyKey (rowOK 5 level5) level6rllrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rllrll && everyKey (rowOK 5 level5) level6rllrlr) = true
  rw [level6rllrll_ok, level6rllrlr_ok]
  decide +kernel
def level6rllrrl : BinaryTree (List W) := (.node [v375, v629, v824, v897, v1308, v1483, v1590] (.node [v375, v629, v819, v897, v1094, v1308, v1483] (.node [v375, v629, v816, v897, v1094, v1308, v1483] (.node [v375, v629, v814, v897, v1308, v1483, v1562] (.node [v375, v629, v814, v897, v1094, v1308, v1590] .nil .nil) (.node [v375, v629, v815, v897, v1094, v1308, v1483] .nil .nil)) (.node [v375, v629, v818, v897, v1094, v1308, v1483] (.node [v375, v629, v817, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v375, v629, v822, v897, v1094, v1308, v1483] (.node [v375, v629, v821, v897, v1094, v1308, v1483] (.node [v375, v629, v820, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v824, v897, v1308, v1483] (.node [v375, v629, v824, v897, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v375, v629, v848, v897, v1019, v1094, v1308] (.node [v375, v629, v837, v897, v1094, v1308, v1483] (.node [v375, v629, v834, v897, v1094, v1308, v1483] (.node [v375, v629, v833, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v840, v897, v1094, v1308, v1483] (.node [v375, v629, v839, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v375, v629, v848, v1010, v1094, v1308, v1483] (.node [v375, v629, v848, v897, v1094, v1308, v1504] (.node [v375, v629, v848, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v848, v1094, v1308, v1483, v1554] (.node [v375, v629, v848, v1094, v1308, v1483, v1504] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllrrl_ok : everyKey (rowOK 5 level5) level6rllrrl = true := by decide +kernel
def level6rllrrr : BinaryTree (List W) := (.node [v375, v629, v861, v1003, v1094, v1308, v1483] (.node [v375, v629, v855, v897, v1094, v1308, v1483] (.node [v375, v629, v852, v897, v1094, v1308, v1483] (.node [v375, v629, v850, v897, v1094, v1308, v1483] (.node [v375, v629, v849, v897, v1094, v1308, v1483] .nil .nil) (.node [v375, v629, v851, v897, v1094, v1308, v1483] .nil .nil)) (.node [v375, v629, v854, v897, v1094, v1308, v1483] (.node [v375, v629, v853, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v375, v629, v858, v897, v1094, v1308, v1483] (.node [v375, v629, v857, v897, v1094, v1308, v1483] (.node [v375, v629, v856, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v861, v897, v1094, v1308, v1483] (.node [v375, v629, v859, v897, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v375, v629, v872, v1094, v1308, v1483, v1544] (.node [v375, v629, v864, v1094, v1308, v1483] (.node [v375, v629, v864, v897, v1094, v1308, v1483] (.node [v375, v629, v861, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v872, v1094, v1308, v1483] (.node [v375, v629, v872, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v375, v629, v888, v1094, v1308, v1483, v1590] (.node [v375, v629, v888, v1094, v1308, v1483] (.node [v375, v629, v888, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v897, v901, v1094, v1308, v1483] (.node [v375, v629, v897, v897, v1094, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllrrr_ok : everyKey (rowOK 5 level5) level6rllrrr = true := by decide +kernel
def level6rllrr : BinaryTree (List W) := .node [v375, v629, v848, v1094, v1308, v1504] level6rllrrl level6rllrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllrr_ok : everyKey (rowOK 5 level5) level6rllrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rllrrl && everyKey (rowOK 5 level5) level6rllrrr) = true
  rw [level6rllrrl_ok, level6rllrrr_ok]
  decide +kernel
def level6rllr : BinaryTree (List W) := .node [v375, v629, v814, v897, v1094, v1308, v1483] level6rllrl level6rllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllr_ok : everyKey (rowOK 5 level5) level6rllr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rllrl && everyKey (rowOK 5 level5) level6rllrr) = true
  rw [level6rllrl_ok, level6rllrr_ok]
  decide +kernel
def level6rll : BinaryTree (List W) := .node [v375, v629, v727, v1094, v1462, v1483] level6rlll level6rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rll_ok : everyKey (rowOK 5 level5) level6rll = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlll && everyKey (rowOK 5 level5) level6rllr) = true
  rw [level6rlll_ok, level6rllr_ok]
  decide +kernel
def level6rlrlll : BinaryTree (List W) := (.node [v375, v629, v897, v932, v1094, v1308, v1483] (.node [v375, v629, v897, v920, v1094, v1308, v1483] (.node [v375, v629, v897, v911, v1094, v1308, v1483] (.node [v375, v629, v897, v907, v1094, v1308, v1483] (.node [v375, v629, v897, v906, v1094, v1308, v1483] .nil .nil) (.node [v375, v629, v897, v909, v1094, v1308, v1483] .nil .nil)) (.node [v375, v629, v897, v914, v1094, v1308, v1483] (.node [v375, v629, v897, v913, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v375, v629, v897, v926, v1094, v1308, v1483] (.node [v375, v629, v897, v925, v1094, v1308, v1483] (.node [v375, v629, v897, v922, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v897, v930, v1094, v1308, v1483] (.node [v375, v629, v897, v928, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v375, v629, v897, v948, v1094, v1308, v1483] (.node [v375, v629, v897, v937, v1094, v1308, v1483] (.node [v375, v629, v897, v934, v1094, v1308, v1483] (.node [v375, v629, v897, v933, v1094, v1308, v1483] .nil .nil) (.node [v375, v629, v897, v936, v1094, v1308, v1483] .nil .nil)) (.node [v375, v629, v897, v942, v1094, v1308, v1483] (.node [v375, v629, v897, v941, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v375, v629, v897, v951, v1094, v1308, v1483] (.node [v375, v629, v897, v950, v1094, v1308, v1483] (.node [v375, v629, v897, v949, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v897, v954, v1003, v1094, v1308] (.node [v375, v629, v897, v953, v1094, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrlll_ok : everyKey (rowOK 5 level5) level6rlrlll = true := by decide +kernel
def level6rlrllr : BinaryTree (List W) := (.node [v375, v629, v897, v986, v1094, v1308, v1483] (.node [v375, v629, v897, v972, v1094, v1308, v1483] (.node [v375, v629, v897, v967, v1094, v1308, v1483] (.node [v375, v629, v897, v962, v1094, v1308, v1483] (.node [v375, v629, v897, v954, v1094, v1308, v1483] .nil .nil) (.node [v375, v629, v897, v965, v1094, v1308, v1483] .nil .nil)) (.node [v375, v629, v897, v971, v1094, v1308, v1483] (.node [v375, v629, v897, v968, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v375, v629, v897, v976, v1094, v1308, v1483] (.node [v375, v629, v897, v975, v1094, v1308, v1483] (.node [v375, v629, v897, v973, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v897, v985, v1094, v1308, v1483] (.node [v375, v629, v897, v984, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v375, v629, v897, v994, v1094, v1308, v1483] (.node [v375, v629, v897, v990, v1094, v1308, v1483] (.node [v375, v629, v897, v989, v1094, v1308, v1483] (.node [v375, v629, v897, v987, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v897, v993, v1094, v1308, v1483] (.node [v375, v629, v897, v992, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v375, v629, v897, v999, v1094, v1308, v1483] (.node [v375, v629, v897, v996, v1094, v1308, v1483] (.node [v375, v629, v897, v995, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v897, v1001, v1094, v1308, v1483] (.node [v375, v629, v897, v1000, v1094, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrllr_ok : everyKey (rowOK 5 level5) level6rlrllr = true := by decide +kernel
def level6rlrll : BinaryTree (List W) := .node [v375, v629, v897, v954, v1094, v1308] level6rlrlll level6rlrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrll_ok : everyKey (rowOK 5 level5) level6rlrll = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlrlll && everyKey (rowOK 5 level5) level6rlrllr) = true
  rw [level6rlrlll_ok, level6rlrllr_ok]
  decide +kernel
def level6rlrlrl : BinaryTree (List W) := (.node [v375, v629, v897, v1010, v1094, v1308, v1483] (.node [v375, v629, v897, v1004, v1094, v1308, v1483] (.node [v375, v629, v897, v1003, v1094, v1406, v1483] (.node [v375, v629, v897, v1003, v1094, v1308, v1483] (.node [v375, v629, v897, v1003, v1056, v1308, v1483] .nil .nil) (.node [v375, v629, v897, v1003, v1094, v1308, v1561] .nil .nil)) (.node [v375, v629, v897, v1003, v1406, v1483] (.node [v375, v629, v897, v1003, v1308, v1406, v1483] .nil .nil) .nil)) (.node [v375, v629, v897, v1007, v1094, v1308, v1483] (.node [v375, v629, v897, v1006, v1094, v1308, v1483] (.node [v375, v629, v897, v1005, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v897, v1009, v1094, v1308, v1483] (.node [v375, v629, v897, v1008, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v375, v629, v897, v1016, v1094, v1308, v1483] (.node [v375, v629, v897, v1013, v1094, v1308, v1483] (.node [v375, v629, v897, v1012, v1094, v1308, v1483] (.node [v375, v629, v897, v1011, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v897, v1015, v1094, v1308, v1483] (.node [v375, v629, v897, v1014, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v375, v629, v897, v1019, v1094, v1308, v1483] (.node [v375, v629, v897, v1018, v1094, v1308, v1483] (.node [v375, v629, v897, v1017, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v897, v1024, v1094, v1308, v1483] (.node [v375, v629, v897, v1023, v1094, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrlrl_ok : everyKey (rowOK 5 level5) level6rlrlrl = true := by decide +kernel
def level6rlrlrr : BinaryTree (List W) := (.node [v375, v629, v897, v1053, v1094, v1308, v1483] (.node [v375, v629, v897, v1037, v1094, v1308, v1483] (.node [v375, v629, v897, v1030, v1094, v1308, v1483] (.node [v375, v629, v897, v1028, v1094, v1308, v1483] (.node [v375, v629, v897, v1027, v1094, v1308, v1483] .nil .nil) (.node [v375, v629, v897, v1029, v1094, v1308, v1483] .nil .nil)) (.node [v375, v629, v897, v1032, v1094, v1308, v1483] (.node [v375, v629, v897, v1031, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v375, v629, v897, v1043, v1094, v1308, v1483] (.node [v375, v629, v897, v1042, v1094, v1308, v1483] (.node [v375, v629, v897, v1040, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v897, v1052, v1094, v1308, v1483] (.node [v375, v629, v897, v1044, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v375, v629, v897, v1057, v1094, v1308, v1483] (.node [v375, v629, v897, v1056, v1094, v1308, v1562] (.node [v375, v629, v897, v1056, v1094, v1308, v1483] (.node [v375, v629, v897, v1055, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v897, v1056, v1308, v1562] (.node [v375, v629, v897, v1056, v1308, v1483, v1562] .nil .nil) .nil)) (.node [v375, v629, v897, v1060, v1094, v1308, v1483] (.node [v375, v629, v897, v1059, v1094, v1308, v1483] (.node [v375, v629, v897, v1058, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v897, v1064, v1094, v1308, v1483] (.node [v375, v629, v897, v1063, v1094, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrlrr_ok : everyKey (rowOK 5 level5) level6rlrlrr = true := by decide +kernel
def level6rlrlr : BinaryTree (List W) := .node [v375, v629, v897, v1026, v1094, v1308, v1483] level6rlrlrl level6rlrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrlr_ok : everyKey (rowOK 5 level5) level6rlrlr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlrlrl && everyKey (rowOK 5 level5) level6rlrlrr) = true
  rw [level6rlrlrl_ok, level6rlrlrr_ok]
  decide +kernel
def level6rlrl : BinaryTree (List W) := .node [v375, v629, v897, v1002, v1094, v1308, v1483] level6rlrll level6rlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrl_ok : everyKey (rowOK 5 level5) level6rlrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlrll && everyKey (rowOK 5 level5) level6rlrlr) = true
  rw [level6rlrll_ok, level6rlrlr_ok]
  decide +kernel
def level6rlrrll : BinaryTree (List W) := (.node [v375, v629, v897, v1078, v1094, v1308, v1483] (.node [v375, v629, v897, v1072, v1094, v1308, v1483] (.node [v375, v629, v897, v1069, v1094, v1308, v1483] (.node [v375, v629, v897, v1067, v1094, v1308, v1483] (.node [v375, v629, v897, v1066, v1094, v1308, v1483] .nil .nil) (.node [v375, v629, v897, v1068, v1094, v1308, v1483] .nil .nil)) (.node [v375, v629, v897, v1071, v1094, v1308, v1483] (.node [v375, v629, v897, v1070, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v375, v629, v897, v1075, v1094, v1308, v1483] (.node [v375, v629, v897, v1074, v1094, v1308, v1483] (.node [v375, v629, v897, v1073, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v897, v1077, v1094, v1308, v1483] (.node [v375, v629, v897, v1076, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v375, v629, v897, v1094, v1100, v1308, v1483] (.node [v375, v629, v897, v1087, v1308, v1483, v1590] (.node [v375, v629, v897, v1087, v1094, v1308, v1483] (.node [v375, v629, v897, v1079, v1094, v1308, v1483] .nil .nil) (.node [v375, v629, v897, v1087, v1308, v1483] .nil .nil)) (.node [v375, v629, v897, v1094, v1099, v1308, v1483] (.node [v375, v629, v897, v1094, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v375, v629, v897, v1094, v1106, v1308, v1483] (.node [v375, v629, v897, v1094, v1105, v1308, v1483] (.node [v375, v629, v897, v1094, v1103, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v897, v1094, v1109, v1308, v1483] (.node [v375, v629, v897, v1094, v1107, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrrll_ok : everyKey (rowOK 5 level5) level6rlrrll = true := by decide +kernel
def level6rlrrlr : BinaryTree (List W) := (.node [v375, v629, v897, v1094, v1160, v1308, v1483] (.node [v375, v629, v897, v1094, v1134, v1308, v1483] (.node [v375, v629, v897, v1094, v1118, v1308, v1483] (.node [v375, v629, v897, v1094, v1115, v1308, v1483] (.node [v375, v629, v897, v1094, v1112, v1308, v1483] .nil .nil) (.node [v375, v629, v897, v1094, v1116, v1308, v1483] .nil .nil)) (.node [v375, v629, v897, v1094, v1131, v1308, v1483] (.node [v375, v629, v897, v1094, v1123, v1308, v1483] .nil .nil) .nil)) (.node [v375, v629, v897, v1094, v1143, v1308, v1483] (.node [v375, v629, v897, v1094, v1141, v1308, v1483] (.node [v375, v629, v897, v1094, v1137, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v897, v1094, v1158, v1308, v1483] (.node [v375, v629, v897, v1094, v1157, v1308, v1483] .nil .nil) .nil))) (.node [v375, v629, v897, v1094, v1173, v1308, v1483] (.node [v375, v629, v897, v1094, v1167, v1308, v1483] (.node [v375, v629, v897, v1094, v1162, v1308, v1483] (.node [v375, v629, v897, v1094, v1161, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v897, v1094, v1172, v1308, v1483] (.node [v375, v629, v897, v1094, v1170, v1308, v1483] .nil .nil) .nil)) (.node [v375, v629, v897, v1094, v1180, v1308, v1483] (.node [v375, v629, v897, v1094, v1179, v1308, v1483] (.node [v375, v629, v897, v1094, v1177, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v897, v1094, v1183, v1308, v1483] (.node [v375, v629, v897, v1094, v1181, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrrlr_ok : everyKey (rowOK 5 level5) level6rlrrlr = true := by decide +kernel
def level6rlrrl : BinaryTree (List W) := .node [v375, v629, v897, v1094, v1110, v1308, v1483] level6rlrrll level6rlrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrrl_ok : everyKey (rowOK 5 level5) level6rlrrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlrrll && everyKey (rowOK 5 level5) level6rlrrlr) = true
  rw [level6rlrrll_ok, level6rlrrlr_ok]
  decide +kernel
def level6rlrrrl : BinaryTree (List W) := (.node [v375, v629, v897, v1094, v1213, v1308, v1483] (.node [v375, v629, v897, v1094, v1199, v1308, v1483] (.node [v375, v629, v897, v1094, v1193, v1308, v1483] (.node [v375, v629, v897, v1094, v1191, v1308, v1483] (.node [v375, v629, v897, v1094, v1187, v1308, v1483] .nil .nil) (.node [v375, v629, v897, v1094, v1192, v1308, v1483] .nil .nil)) (.node [v375, v629, v897, v1094, v1197, v1308, v1483] (.node [v375, v629, v897, v1094, v1194, v1308, v1483] .nil .nil) .nil)) (.node [v375, v629, v897, v1094, v1207, v1308, v1483] (.node [v375, v629, v897, v1094, v1206, v1308, v1483] (.node [v375, v629, v897, v1094, v1205, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v897, v1094, v1209, v1308, v1483] (.node [v375, v629, v897, v1094, v1208, v1308, v1483] .nil .nil) .nil))) (.node [v375, v629, v897, v1094, v1230, v1308, v1483] (.node [v375, v629, v897, v1094, v1214, v1483, v1590] (.node [v375, v629, v897, v1094, v1214, v1308, v1590] (.node [v375, v629, v897, v1094, v1214, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v897, v1094, v1215, v1308, v1483] (.node [v375, v629, v897, v1094, v1214, v1590] .nil .nil) .nil)) (.node [v375, v629, v897, v1094, v1237, v1308, v1483] (.node [v375, v629, v897, v1094, v1236, v1308, v1483] (.node [v375, v629, v897, v1094, v1234, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v897, v1094, v1246, v1308, v1483] (.node [v375, v629, v897, v1094, v1242, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrrrl_ok : everyKey (rowOK 5 level5) level6rlrrrl = true := by decide +kernel
def level6rlrrrr : BinaryTree (List W) := (.node [v375, v629, v897, v1094, v1277, v1308, v1483] (.node [v375, v629, v897, v1094, v1264, v1308, v1483] (.node [v375, v629, v897, v1094, v1253, v1308, v1483] (.node [v375, v629, v897, v1094, v1251, v1308, v1483] (.node [v375, v629, v897, v1094, v1249, v1308, v1483] .nil .nil) (.node [v375, v629, v897, v1094, v1252, v1308, v1483] .nil .nil)) (.node [v375, v629, v897, v1094, v1262, v1308, v1483] (.node [v375, v629, v897, v1094, v1260, v1308, v1483] .nil .nil) .nil)) (.node [v375, v629, v897, v1094, v1271, v1308, v1483] (.node [v375, v629, v897, v1094, v1269, v1308, v1483] (.node [v375, v629, v897, v1094, v1265, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v897, v1094, v1276, v1308, v1483] (.node [v375, v629, v897, v1094, v1275, v1308, v1483] .nil .nil) .nil))) (.node [v375, v629, v897, v1094, v1289, v1308, v1483] (.node [v375, v629, v897, v1094, v1282, v1308, v1483] (.node [v375, v629, v897, v1094, v1279, v1308, v1483] (.node [v375, v629, v897, v1094, v1278, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v897, v1094, v1287, v1308, v1483] (.node [v375, v629, v897, v1094, v1283, v1308, v1483] .nil .nil) .nil)) (.node [v375, v629, v897, v1094, v1294, v1308, v1483] (.node [v375, v629, v897, v1094, v1293, v1308, v1483] (.node [v375, v629, v897, v1094, v1290, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v897, v1094, v1296, v1308, v1483] (.node [v375, v629, v897, v1094, v1295, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrrrr_ok : everyKey (rowOK 5 level5) level6rlrrrr = true := by decide +kernel
def level6rlrrr : BinaryTree (List W) := .node [v375, v629, v897, v1094, v1247, v1308, v1483] level6rlrrrl level6rlrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrrr_ok : everyKey (rowOK 5 level5) level6rlrrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlrrrl && everyKey (rowOK 5 level5) level6rlrrrr) = true
  rw [level6rlrrrl_ok, level6rlrrrr_ok]
  decide +kernel
def level6rlrr : BinaryTree (List W) := .node [v375, v629, v897, v1094, v1186, v1308, v1483] level6rlrrl level6rlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrr_ok : everyKey (rowOK 5 level5) level6rlrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlrrl && everyKey (rowOK 5 level5) level6rlrrr) = true
  rw [level6rlrrl_ok, level6rlrrr_ok]
  decide +kernel
def level6rlr : BinaryTree (List W) := .node [v375, v629, v897, v1065, v1094, v1308, v1483] level6rlrl level6rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlr_ok : everyKey (rowOK 5 level5) level6rlr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlrl && everyKey (rowOK 5 level5) level6rlrr) = true
  rw [level6rlrl_ok, level6rlrr_ok]
  decide +kernel
def level6rl : BinaryTree (List W) := .node [v375, v629, v897, v904, v1094, v1308, v1483] level6rll level6rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rl_ok : everyKey (rowOK 5 level5) level6rl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rll && everyKey (rowOK 5 level5) level6rlr) = true
  rw [level6rll_ok, level6rlr_ok]
  decide +kernel
def level6rrllll : BinaryTree (List W) := (.node [v375, v629, v897, v1094, v1308, v1324, v1483] (.node [v375, v629, v897, v1094, v1308, v1312, v1483] (.node [v375, v629, v897, v1094, v1308, v1309, v1483] (.node [v375, v629, v897, v1094, v1303, v1308, v1483] (.node [v375, v629, v897, v1094, v1302, v1308, v1483] .nil .nil) (.node [v375, v629, v897, v1094, v1308, v1308, v1483] .nil .nil)) (.node [v375, v629, v897, v1094, v1308, v1311, v1483] (.node [v375, v629, v897, v1094, v1308, v1310, v1483] .nil .nil) .nil)) (.node [v375, v629, v897, v1094, v1308, v1316, v1483] (.node [v375, v629, v897, v1094, v1308, v1315, v1483] (.node [v375, v629, v897, v1094, v1308, v1313, v1483] .nil .nil) .nil) (.node [v375, v629, v897, v1094, v1308, v1320, v1483] (.node [v375, v629, v897, v1094, v1308, v1318, v1483] .nil .nil) .nil))) (.node [v375, v629, v897, v1094, v1308, v1346, v1483] (.node [v375, v629, v897, v1094, v1308, v1331, v1483] (.node [v375, v629, v897, v1094, v1308, v1327, v1483] (.node [v375, v629, v897, v1094, v1308, v1325, v1483] .nil .nil) (.node [v375, v629, v897, v1094, v1308, v1330, v1483] .nil .nil)) (.node [v375, v629, v897, v1094, v1308, v1341, v1483] (.node [v375, v629, v897, v1094, v1308, v1332, v1483] .nil .nil) .nil)) (.node [v375, v629, v897, v1094, v1308, v1353, v1483] (.node [v375, v629, v897, v1094, v1308, v1349, v1483] (.node [v375, v629, v897, v1094, v1308, v1347, v1483] .nil .nil) .nil) (.node [v375, v629, v897, v1094, v1308, v1355, v1483] (.node [v375, v629, v897, v1094, v1308, v1354, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrllll_ok : everyKey (rowOK 5 level5) level6rrllll = true := by decide +kernel
def level6rrlllr : BinaryTree (List W) := (.node [v375, v629, v897, v1094, v1308, v1391, v1483] (.node [v375, v629, v897, v1094, v1308, v1370, v1483] (.node [v375, v629, v897, v1094, v1308, v1365, v1483] (.node [v375, v629, v897, v1094, v1308, v1359, v1483] (.node [v375, v629, v897, v1094, v1308, v1358, v1483] .nil .nil) (.node [v375, v629, v897, v1094, v1308, v1360, v1483] .nil .nil)) (.node [v375, v629, v897, v1094, v1308, v1368, v1483] (.node [v375, v629, v897, v1094, v1308, v1366, v1483] .nil .nil) .nil)) (.node [v375, v629, v897, v1094, v1308, v1385, v1483] (.node [v375, v629, v897, v1094, v1308, v1373, v1483] (.node [v375, v629, v897, v1094, v1308, v1372, v1483] .nil .nil) .nil) (.node [v375, v629, v897, v1094, v1308, v1390, v1483] (.node [v375, v629, v897, v1094, v1308, v1388, v1483] .nil .nil) .nil))) (.node [v375, v629, v897, v1094, v1308, v1402, v1483] (.node [v375, v629, v897, v1094, v1308, v1398, v1483] (.node [v375, v629, v897, v1094, v1308, v1397, v1483] (.node [v375, v629, v897, v1094, v1308, v1392, v1483] .nil .nil) .nil) (.node [v375, v629, v897, v1094, v1308, v1400, v1483] (.node [v375, v629, v897, v1094, v1308, v1399, v1483] .nil .nil) .nil)) (.node [v375, v629, v897, v1094, v1308, v1405, v1483] (.node [v375, v629, v897, v1094, v1308, v1404, v1483] (.node [v375, v629, v897, v1094, v1308, v1403, v1483] .nil .nil) .nil) (.node [v375, v629, v897, v1094, v1308, v1407, v1483] (.node [v375, v629, v897, v1094, v1308, v1406, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlllr_ok : everyKey (rowOK 5 level5) level6rrlllr = true := by decide +kernel
def level6rrlll : BinaryTree (List W) := .node [v375, v629, v897, v1094, v1308, v1356, v1483] level6rrllll level6rrlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlll_ok : everyKey (rowOK 5 level5) level6rrlll = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrllll && everyKey (rowOK 5 level5) level6rrlllr) = true
  rw [level6rrllll_ok, level6rrlllr_ok]
  decide +kernel
def level6rrllrl : BinaryTree (List W) := (.node [v375, v629, v897, v1094, v1308, v1432, v1483] (.node [v375, v629, v897, v1094, v1308, v1424, v1483] (.node [v375, v629, v897, v1094, v1308, v1417, v1483] (.node [v375, v629, v897, v1094, v1308, v1410, v1483] (.node [v375, v629, v897, v1094, v1308, v1409, v1483] .nil .nil) (.node [v375, v629, v897, v1094, v1308, v1416, v1483] .nil .nil)) (.node [v375, v629, v897, v1094, v1308, v1423, v1483] (.node [v375, v629, v897, v1094, v1308, v1418, v1483] .nil .nil) .nil)) (.node [v375, v629, v897, v1094, v1308, v1427, v1483] (.node [v375, v629, v897, v1094, v1308, v1426, v1483] (.node [v375, v629, v897, v1094, v1308, v1425, v1483] .nil .nil) .nil) (.node [v375, v629, v897, v1094, v1308, v1431, v1483] (.node [v375, v629, v897, v1094, v1308, v1429, v1483] .nil .nil) .nil))) (.node [v375, v629, v897, v1094, v1308, v1451, v1483] (.node [v375, v629, v897, v1094, v1308, v1445, v1483] (.node [v375, v629, v897, v1094, v1308, v1442, v1483] (.node [v375, v629, v897, v1094, v1308, v1433, v1483] .nil .nil) (.node [v375, v629, v897, v1094, v1308, v1443, v1483] .nil .nil)) (.node [v375, v629, v897, v1094, v1308, v1448, v1483] (.node [v375, v629, v897, v1094, v1308, v1446, v1483] .nil .nil) .nil)) (.node [v375, v629, v897, v1094, v1308, v1458, v1483] (.node [v375, v629, v897, v1094, v1308, v1453, v1483] (.node [v375, v629, v897, v1094, v1308, v1452, v1483] .nil .nil) .nil) (.node [v375, v629, v897, v1094, v1308, v1462, v1483] (.node [v375, v629, v897, v1094, v1308, v1460, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrllrl_ok : everyKey (rowOK 5 level5) level6rrllrl = true := by decide +kernel
def level6rrllrr : BinaryTree (List W) := (.node [v375, v629, v897, v1094, v1308, v1483, v1485] (.node [v375, v629, v897, v1094, v1308, v1472, v1483] (.node [v375, v629, v897, v1094, v1308, v1468, v1483] (.node [v375, v629, v897, v1094, v1308, v1466, v1483] (.node [v375, v629, v897, v1094, v1308, v1465, v1483] .nil .nil) (.node [v375, v629, v897, v1094, v1308, v1467, v1483] .nil .nil)) (.node [v375, v629, v897, v1094, v1308, v1471, v1483] (.node [v375, v629, v897, v1094, v1308, v1470, v1483] .nil .nil) .nil)) (.node [v375, v629, v897, v1094, v1308, v1483] (.node [v375, v629, v897, v1094, v1308, v1475, v1483] (.node [v375, v629, v897, v1094, v1308, v1473, v1483] .nil .nil) .nil) (.node [v375, v629, v897, v1094, v1308, v1483, v1484] (.node [v375, v629, v897, v1094, v1308, v1483, v1483] .nil .nil) .nil))) (.node [v375, v629, v897, v1094, v1308, v1483, v1496] (.node [v375, v629, v897, v1094, v1308, v1483, v1488] (.node [v375, v629, v897, v1094, v1308, v1483, v1487] (.node [v375, v629, v897, v1094, v1308, v1483, v1486] .nil .nil) .nil) (.node [v375, v629, v897, v1094, v1308, v1483, v1492] (.node [v375, v629, v897, v1094, v1308, v1483, v1491] .nil .nil) .nil)) (.node [v375, v629, v897, v1094, v1308, v1483, v1499] (.node [v375, v629, v897, v1094, v1308, v1483, v1498] (.node [v375, v629, v897, v1094, v1308, v1483, v1497] .nil .nil) .nil) (.node [v375, v629, v897, v1094, v1308, v1483, v1502] (.node [v375, v629, v897, v1094, v1308, v1483, v1500] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrllrr_ok : everyKey (rowOK 5 level5) level6rrllrr = true := by decide +kernel
def level6rrllr : BinaryTree (List W) := .node [v375, v629, v897, v1094, v1308, v1463, v1483] level6rrllrl level6rrllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrllr_ok : everyKey (rowOK 5 level5) level6rrllr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrllrl && everyKey (rowOK 5 level5) level6rrllrr) = true
  rw [level6rrllrl_ok, level6rrllrr_ok]
  decide +kernel
def level6rrll : BinaryTree (List W) := .node [v375, v629, v897, v1094, v1308, v1408, v1483] level6rrlll level6rrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrll_ok : everyKey (rowOK 5 level5) level6rrll = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrlll && everyKey (rowOK 5 level5) level6rrllr) = true
  rw [level6rrlll_ok, level6rrllr_ok]
  decide +kernel
def level6rrlrll : BinaryTree (List W) := (.node [v375, v629, v897, v1094, v1308, v1483, v1529] (.node [v375, v629, v897, v1094, v1308, v1483, v1519] (.node [v375, v629, v897, v1094, v1308, v1483, v1512] (.node [v375, v629, v897, v1094, v1308, v1483, v1507] (.node [v375, v629, v897, v1094, v1308, v1483, v1504] .nil .nil) (.node [v375, v629, v897, v1094, v1308, v1483, v1510] .nil .nil)) (.node [v375, v629, v897, v1094, v1308, v1483, v1517] (.node [v375, v629, v897, v1094, v1308, v1483, v1513] .nil .nil) .nil)) (.node [v375, v629, v897, v1094, v1308, v1483, v1523] (.node [v375, v629, v897, v1094, v1308, v1483, v1521] (.node [v375, v629, v897, v1094, v1308, v1483, v1520] .nil .nil) .nil) (.node [v375, v629, v897, v1094, v1308, v1483, v1527] (.node [v375, v629, v897, v1094, v1308, v1483, v1524] .nil .nil) .nil))) (.node [v375, v629, v897, v1094, v1308, v1483, v1543] (.node [v375, v629, v897, v1094, v1308, v1483, v1537] (.node [v375, v629, v897, v1094, v1308, v1483, v1535] (.node [v375, v629, v897, v1094, v1308, v1483, v1530] .nil .nil) (.node [v375, v629, v897, v1094, v1308, v1483, v1536] .nil .nil)) (.node [v375, v629, v897, v1094, v1308, v1483, v1540] (.node [v375, v629, v897, v1094, v1308, v1483, v1538] .nil .nil) .nil)) (.node [v375, v629, v897, v1094, v1308, v1483, v1546] (.node [v375, v629, v897, v1094, v1308, v1483, v1545] (.node [v375, v629, v897, v1094, v1308, v1483, v1544] .nil .nil) .nil) (.node [v375, v629, v897, v1094, v1308, v1483, v1555] (.node [v375, v629, v897, v1094, v1308, v1483, v1554] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlrll_ok : everyKey (rowOK 5 level5) level6rrlrll = true := by decide +kernel
def level6rrlrlr : BinaryTree (List W) := (.node [v375, v629, v897, v1094, v1308, v1483, v1589] (.node [v375, v629, v897, v1094, v1308, v1483, v1583] (.node [v375, v629, v897, v1094, v1308, v1483, v1571] (.node [v375, v629, v897, v1094, v1308, v1483, v1561] (.node [v375, v629, v897, v1094, v1308, v1483, v1560] .nil .nil) (.node [v375, v629, v897, v1094, v1308, v1483, v1562] .nil .nil)) (.node [v375, v629, v897, v1094, v1308, v1483, v1582] (.node [v375, v629, v897, v1094, v1308, v1483, v1578] .nil .nil) .nil)) (.node [v375, v629, v897, v1094, v1308, v1483, v1586] (.node [v375, v629, v897, v1094, v1308, v1483, v1585] (.node [v375, v629, v897, v1094, v1308, v1483, v1584] .nil .nil) .nil) (.node [v375, v629, v897, v1094, v1308, v1483, v1588] (.node [v375, v629, v897, v1094, v1308, v1483, v1587] .nil .nil) .nil))) (.node [v375, v629, v897, v1094, v1308, v1483, v1595] (.node [v375, v629, v897, v1094, v1308, v1483, v1592] (.node [v375, v629, v897, v1094, v1308, v1483, v1591] (.node [v375, v629, v897, v1094, v1308, v1483, v1590] .nil .nil) .nil) (.node [v375, v629, v897, v1094, v1308, v1483, v1594] (.node [v375, v629, v897, v1094, v1308, v1483, v1593] .nil .nil) .nil)) (.node [v375, v629, v897, v1094, v1308, v1562, v1590] (.node [v375, v629, v897, v1094, v1308, v1561] (.node [v375, v629, v897, v1094, v1308, v1483, v1596] .nil .nil) .nil) (.node [v375, v629, v897, v1308, v1399, v1483] (.node [v375, v629, v897, v1214, v1308, v1399, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlrlr_ok : everyKey (rowOK 5 level5) level6rrlrlr = true := by decide +kernel
def level6rrlrl : BinaryTree (List W) := .node [v375, v629, v897, v1094, v1308, v1483, v1559] level6rrlrll level6rrlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlrl_ok : everyKey (rowOK 5 level5) level6rrlrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrlrll && everyKey (rowOK 5 level5) level6rrlrlr) = true
  rw [level6rrlrll_ok, level6rrlrlr_ok]
  decide +kernel
def level6rrlrrl : BinaryTree (List W) := (.node [v375, v629, v1043, v1094, v1308, v1483, v1590] (.node [v375, v629, v1019, v1094, v1308, v1483, v1504] (.node [v375, v629, v1003, v1094, v1308, v1453, v1483] (.node [v375, v629, v971, v1094, v1308, v1483] (.node [v375, v629, v937, v1094, v1308, v1483] .nil .nil) (.node [v375, v629, v973, v1094, v1308, v1483, v1554] .nil .nil)) (.node [v375, v629, v1010, v1094, v1308, v1462, v1483] (.node [v375, v629, v1010, v1019, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v375, v629, v1026, v1094, v1308, v1483, v1544] (.node [v375, v629, v1026, v1094, v1308, v1483] (.node [v375, v629, v1019, v1094, v1308, v1483, v1554] .nil .nil) .nil) (.node [v375, v629, v1043, v1094, v1308, v1483] (.node [v375, v629, v1027, v1094, v1308, v1483, v1554] .nil .nil) .nil))) (.node [v375, v629, v1094, v1308, v1453, v1483] (.node [v375, v629, v1094, v1242, v1308, v1448, v1483] (.node [v375, v629, v1094, v1214, v1308, v1446, v1483] (.node [v375, v629, v1060, v1094, v1308, v1483, v1507] .nil .nil) .nil) (.node [v375, v629, v1094, v1308, v1448, v1483] (.node [v375, v629, v1094, v1308, v1446, v1483] .nil .nil) .nil)) (.node [v375, v629, v1094, v1308, v1483, v1507] (.node [v375, v629, v1094, v1308, v1462, v1483, v1554] (.node [v375, v629, v1094, v1308, v1462, v1483, v1504] .nil .nil) .nil) (.node [v375, v682, v897, v1094, v1308, v1483] (.node [v375, v644, v897, v1094, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlrrl_ok : everyKey (rowOK 5 level5) level6rrlrrl = true := by decide +kernel
def level6rrlrrr : BinaryTree (List W) := (.node [v375, v731, v897, v1094, v1215, v1308, v1483] (.node [v375, v722, v897, v996, v1094, v1308, v1483] (.node [v375, v708, v897, v1094, v1308, v1483, v1578] (.node [v375, v698, v897, v1094, v1308, v1483] (.node [v375, v690, v897, v1094, v1308, v1483] .nil .nil) (.node [v375, v708, v897, v1094, v1215, v1308, v1483] .nil .nil)) (.node [v375, v722, v897, v973, v1094, v1308, v1483] (.node [v375, v720, v897, v1094, v1215, v1308, v1483] .nil .nil) .nil)) (.node [v375, v727, v897, v968, v1094, v1308, v1483] (.node [v375, v722, v897, v1094, v1308, v1483, v1578] (.node [v375, v722, v897, v1094, v1215, v1308, v1483] .nil .nil) .nil) (.node [v375, v727, v897, v1094, v1308, v1483, v1578] (.node [v375, v727, v897, v1094, v1215, v1308, v1483] .nil .nil) .nil))) (.node [v375, v758, v897, v1094, v1215, v1308, v1483] (.node [v375, v737, v897, v1094, v1308, v1483, v1578] (.node [v375, v737, v897, v1094, v1215, v1308, v1483] (.node [v375, v737, v897, v976, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v741, v897, v1094, v1308, v1483] (.node [v375, v741, v897, v934, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v375, v791, v897, v1094, v1308, v1483, v1578] (.node [v375, v791, v897, v1094, v1215, v1308, v1483] (.node [v375, v758, v897, v1094, v1308, v1483, v1578] .nil .nil) .nil) (.node [v375, v814, v897, v1094, v1308, v1483, v1578] (.node [v375, v814, v897, v1094, v1215, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlrrr_ok : everyKey (rowOK 5 level5) level6rrlrrr = true := by decide +kernel
def level6rrlrr : BinaryTree (List W) := .node [v375, v685, v897, v1094, v1308, v1483] level6rrlrrl level6rrlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlrr_ok : everyKey (rowOK 5 level5) level6rrlrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrlrrl && everyKey (rowOK 5 level5) level6rrlrrr) = true
  rw [level6rrlrrl_ok, level6rrlrrr_ok]
  decide +kernel
def level6rrlr : BinaryTree (List W) := .node [v375, v629, v897, v1308, v1406, v1483, v1562] level6rrlrl level6rrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlr_ok : everyKey (rowOK 5 level5) level6rrlr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrlrl && everyKey (rowOK 5 level5) level6rrlrr) = true
  rw [level6rrlrl_ok, level6rrlrr_ok]
  decide +kernel
def level6rrl : BinaryTree (List W) := .node [v375, v629, v897, v1094, v1308, v1483, v1503] level6rrll level6rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrl_ok : everyKey (rowOK 5 level5) level6rrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrll && everyKey (rowOK 5 level5) level6rrlr) = true
  rw [level6rrll_ok, level6rrlr_ok]
  decide +kernel
def level6rrrlll : BinaryTree (List W) := (.node [v375, v897, v996, v1094, v1215, v1308, v1483] (.node [v375, v897, v973, v1094, v1215, v1308, v1483] (.node [v375, v897, v934, v1094, v1215, v1308, v1483] (.node [v375, v848, v897, v1094, v1308, v1483, v1578] (.node [v375, v848, v897, v1094, v1215, v1308, v1483] .nil .nil) (.node [v375, v858, v897, v1094, v1308, v1483, v1578] .nil .nil)) (.node [v375, v897, v968, v1094, v1308, v1483] (.node [v375, v897, v934, v1094, v1308, v1483, v1578] .nil .nil) .nil)) (.node [v375, v897, v987, v1094, v1215, v1308, v1483] (.node [v375, v897, v976, v1094, v1308, v1483] (.node [v375, v897, v973, v1094, v1308, v1483, v1578] .nil .nil) .nil) (.node [v375, v897, v996, v1094, v1194, v1308, v1483] (.node [v375, v897, v989, v1094, v1215, v1308, v1483] .nil .nil) .nil))) (.node [v375, v897, v1010, v1094, v1308, v1483, v1578] (.node [v375, v897, v1003, v1094, v1308, v1483, v1578] (.node [v375, v897, v1003, v1094, v1187, v1308, v1483] (.node [v375, v897, v996, v1094, v1308, v1483, v1578] .nil .nil) (.node [v375, v897, v1003, v1094, v1215, v1308, v1483] .nil .nil)) (.node [v375, v897, v1010, v1094, v1215, v1308, v1483] (.node [v375, v897, v1010, v1094, v1199, v1308, v1483] .nil .nil) .nil)) (.node [v375, v897, v1027, v1094, v1215, v1308, v1483] (.node [v375, v897, v1019, v1094, v1308, v1483, v1578] (.node [v375, v897, v1019, v1094, v1215, v1308, v1483] .nil .nil) .nil) (.node [v375, v897, v1040, v1094, v1308, v1483, v1578] (.node [v375, v897, v1027, v1094, v1308, v1483, v1578] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrlll_ok : everyKey (rowOK 5 level5) level6rrrlll = true := by decide +kernel
def level6rrrllr : BinaryTree (List W) := (.node [v375, v897, v1094, v1214, v1215, v1308, v1483] (.node [v375, v897, v1094, v1194, v1308, v1483, v1578] (.node [v375, v897, v1077, v1094, v1308, v1483, v1578] (.node [v375, v897, v1060, v1094, v1215, v1308, v1483] (.node [v375, v897, v1056, v1094, v1308, v1483, v1578] .nil .nil) (.node [v375, v897, v1060, v1094, v1308, v1483, v1578] .nil .nil)) (.node [v375, v897, v1094, v1194, v1215, v1308, v1483] (.node [v375, v897, v1094, v1187, v1308, v1483] .nil .nil) .nil)) (.node [v375, v897, v1094, v1205, v1308, v1483, v1578] (.node [v375, v897, v1094, v1205, v1215, v1308, v1483] (.node [v375, v897, v1094, v1199, v1308, v1483] .nil .nil) .nil) (.node [v375, v897, v1094, v1213, v1215, v1308, v1483] (.node [v375, v897, v1094, v1207, v1215, v1308, v1483] .nil .nil) .nil))) (.node [v375, v897, v1094, v1215, v1308, v1320, v1483] (.node [v375, v897, v1094, v1215, v1215, v1308, v1483] (.node [v375, v897, v1094, v1214, v1308, v1483, v1578] (.node [v375, v897, v1094, v1214, v1308, v1483, v1530] .nil .nil) .nil) (.node [v375, v897, v1094, v1215, v1252, v1308, v1483] (.node [v375, v897, v1094, v1215, v1242, v1308, v1483] .nil .nil) .nil)) (.node [v375, v897, v1094, v1215, v1308, v1406, v1483] (.node [v375, v897, v1094, v1215, v1308, v1397, v1483] (.node [v375, v897, v1094, v1215, v1308, v1349, v1483] .nil .nil) .nil) (.node [v375, v897, v1094, v1215, v1308, v1432, v1483] (.node [v375, v897, v1094, v1215, v1308, v1416, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrllr_ok : everyKey (rowOK 5 level5) level6rrrllr = true := by decide +kernel
def level6rrrll : BinaryTree (List W) := .node [v375, v897, v1056, v1094, v1215, v1308, v1483] level6rrrlll level6rrrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrll_ok : everyKey (rowOK 5 level5) level6rrrll = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrrlll && everyKey (rowOK 5 level5) level6rrrllr) = true
  rw [level6rrrlll_ok, level6rrrllr_ok]
  decide +kernel
def level6rrrlrl : BinaryTree (List W) := (.node [v375, v897, v1094, v1234, v1308, v1483] (.node [v375, v897, v1094, v1215, v1308, v1483, v1554] (.node [v375, v897, v1094, v1215, v1308, v1483, v1504] (.node [v375, v897, v1094, v1215, v1308, v1483] (.node [v375, v897, v1094, v1215, v1308, v1462, v1483] .nil .nil) (.node [v375, v897, v1094, v1215, v1308, v1483, v1483] .nil .nil)) (.node [v375, v897, v1094, v1215, v1308, v1483, v1544] (.node [v375, v897, v1094, v1215, v1308, v1483, v1536] .nil .nil) .nil)) (.node [v375, v897, v1094, v1215, v1308, v1483, v1590] (.node [v375, v897, v1094, v1215, v1308, v1483, v1578] (.node [v375, v897, v1094, v1215, v1308, v1483, v1562] .nil .nil) .nil) (.node [v375, v897, v1094, v1230, v1308, v1483, v1504] (.node [v375, v897, v1094, v1230, v1308, v1483] .nil .nil) .nil))) (.node [v375, v897, v1094, v1260, v1308, v1483] (.node [v375, v897, v1094, v1251, v1308, v1483] (.node [v375, v897, v1094, v1242, v1308, v1483, v1578] (.node [v375, v897, v1094, v1242, v1308, v1483, v1524] .nil .nil) .nil) (.node [v375, v897, v1094, v1252, v1308, v1483, v1578] (.node [v375, v897, v1094, v1251, v1308, v1483, v1554] .nil .nil) .nil)) (.node [v375, v897, v1094, v1262, v1308, v1483, v1562] (.node [v375, v897, v1094, v1262, v1308, v1483] (.node [v375, v897, v1094, v1260, v1308, v1483, v1544] .nil .nil) .nil) (.node [v375, v897, v1094, v1271, v1308, v1483, v1590] (.node [v375, v897, v1094, v1271, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrlrl_ok : everyKey (rowOK 5 level5) level6rrrlrl = true := by decide +kernel
def level6rrrlrr : BinaryTree (List W) := (.node [v375, v897, v1094, v1308, v1483, v1544, v1578] (.node [v375, v897, v1094, v1308, v1473, v1483] (.node [v375, v897, v1094, v1308, v1406, v1483, v1578] (.node [v375, v897, v1094, v1308, v1349, v1483, v1578] (.node [v375, v897, v1094, v1308, v1320, v1483] .nil .nil) (.node [v375, v897, v1094, v1308, v1370, v1483, v1578] .nil .nil)) (.node [v375, v897, v1094, v1308, v1462, v1483, v1578] (.node [v375, v897, v1094, v1308, v1432, v1483, v1578] .nil .nil) .nil)) (.node [v375, v897, v1094, v1308, v1483, v1524] (.node [v375, v897, v1094, v1308, v1483, v1504, v1578] (.node [v375, v897, v1094, v1308, v1473, v1483, v1578] .nil .nil) .nil) (.node [v375, v897, v1094, v1308, v1483, v1536, v1578] (.node [v375, v897, v1094, v1308, v1483, v1530] .nil .nil) .nil))) (.node [v375, v897, v1094, v1308, v1483, v1578, v1586] (.node [v375, v897, v1094, v1308, v1483, v1571] (.node [v375, v897, v1094, v1308, v1483, v1562, v1578] (.node [v375, v897, v1094, v1308, v1483, v1554, v1578] .nil .nil) .nil) (.node [v375, v897, v1094, v1308, v1483, v1578, v1578] (.node [v375, v897, v1094, v1308, v1483, v1578] .nil .nil) .nil)) (.node [v375, v897, v1094, v1308, v1483, v1578, v1594] (.node [v375, v897, v1094, v1308, v1483, v1578, v1590] (.node [v375, v897, v1094, v1308, v1483, v1578, v1587] .nil .nil) .nil) (.node [v402, v629, v897, v1094, v1308, v1483] (.node [v375, v897, v1094, v1308, v1483, v1578, v1595] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrlrr_ok : everyKey (rowOK 5 level5) level6rrrlrr = true := by decide +kernel
def level6rrrlr : BinaryTree (List W) := .node [v375, v897, v1094, v1308, v1308, v1483, v1578] level6rrrlrl level6rrrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrlr_ok : everyKey (rowOK 5 level5) level6rrrlr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrrlrl && everyKey (rowOK 5 level5) level6rrrlrr) = true
  rw [level6rrrlrl_ok, level6rrrlrr_ok]
  decide +kernel
def level6rrrl : BinaryTree (List W) := .node [v375, v897, v1094, v1215, v1308, v1445, v1483] level6rrrll level6rrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrl_ok : everyKey (rowOK 5 level5) level6rrrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrrll && everyKey (rowOK 5 level5) level6rrrlr) = true
  rw [level6rrrll_ok, level6rrrlr_ok]
  decide +kernel
def level6rrrrll : BinaryTree (List W) := (.node [v629, v668, v897, v1094, v1308, v1483] (.node [v480, v758, v897, v1094, v1308, v1483] (.node [v480, v629, v668, v897, v1094, v1308, v1483] (.node [v419, v629, v758, v897, v1094, v1308, v1483] (.node [v413, v629, v897, v1094, v1308, v1483] .nil .nil) (.node [v422, v629, v758, v897, v1094, v1308, v1483] .nil .nil)) (.node [v480, v668, v897, v1094, v1308, v1483] (.node [v480, v629, v758, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v497, v670, v897, v1094, v1308, v1483] (.node [v497, v629, v758, v897, v1094, v1308, v1483] (.node [v497, v629, v670, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v513, v629, v758, v897, v1094, v1308, v1483] (.node [v497, v758, v897, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v629, v711, v758, v897, v1094, v1308, v1483] (.node [v629, v708, v897, v1094, v1205, v1308, v1483] (.node [v629, v701, v897, v1094, v1308, v1483] (.node [v629, v670, v897, v1094, v1308, v1483] .nil .nil) (.node [v629, v708, v758, v897, v1094, v1308, v1483] .nil .nil)) (.node [v629, v708, v897, v1094, v1308, v1483, v1544] (.node [v629, v708, v897, v1094, v1242, v1308, v1483] .nil .nil) .nil)) (.node [v629, v722, v758, v897, v1094, v1308, v1483] (.node [v629, v717, v758, v897, v1094, v1308, v1483] (.node [v629, v713, v758, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v629, v737, v758, v897, v1094, v1308, v1483] (.node [v629, v727, v758, v897, v1094, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrrll_ok : everyKey (rowOK 5 level5) level6rrrrll = true := by decide +kernel
def level6rrrrlr : BinaryTree (List W) := (.node [v629, v758, v897, v1019, v1094, v1308, v1483] (.node [v629, v758, v897, v967, v1094, v1308, v1483] (.node [v629, v758, v848, v897, v1094, v1308, v1483] (.node [v629, v758, v791, v897, v1094, v1308, v1483] (.node [v629, v758, v758, v897, v1094, v1308, v1483] .nil .nil) (.node [v629, v758, v814, v897, v1094, v1308, v1483] .nil .nil)) (.node [v629, v758, v897, v934, v1094, v1308, v1483] (.node [v629, v758, v897, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v629, v758, v897, v1003, v1094, v1308, v1483] (.node [v629, v758, v897, v996, v1094, v1308, v1483] (.node [v629, v758, v897, v973, v1094, v1308, v1483] .nil .nil) .nil) (.node [v629, v758, v897, v1015, v1094, v1308, v1483] (.node [v629, v758, v897, v1010, v1094, v1308, v1483] .nil .nil) .nil))) (.node [v629, v758, v897, v1094, v1194, v1308, v1483] (.node [v629, v758, v897, v1056, v1094, v1308, v1483] (.node [v629, v758, v897, v1031, v1094, v1308, v1483] (.node [v629, v758, v897, v1027, v1094, v1308, v1483] .nil .nil) .nil) (.node [v629, v758, v897, v1094, v1137, v1308, v1483] (.node [v629, v758, v897, v1060, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v629, v758, v897, v1094, v1215, v1308, v1483] (.node [v629, v758, v897, v1094, v1214, v1308, v1483] (.node [v629, v758, v897, v1094, v1205, v1308, v1483] .nil .nil) .nil) (.node [v629, v758, v897, v1094, v1252, v1308, v1483] (.node [v629, v758, v897, v1094, v1242, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrrlr_ok : everyKey (rowOK 5 level5) level6rrrrlr = true := by decide +kernel
def level6rrrrl : BinaryTree (List W) := .node [v629, v755, v758, v897, v1094, v1308, v1483] level6rrrrll level6rrrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrrl_ok : everyKey (rowOK 5 level5) level6rrrrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrrrll && everyKey (rowOK 5 level5) level6rrrrlr) = true
  rw [level6rrrrll_ok, level6rrrrlr_ok]
  decide +kernel
def level6rrrrrl : BinaryTree (List W) := (.node [v629, v758, v897, v1094, v1308, v1483, v1578] (.node [v629, v758, v897, v1094, v1308, v1483, v1488] (.node [v629, v758, v897, v1094, v1308, v1432, v1483] (.node [v629, v758, v897, v1094, v1308, v1390, v1483] (.node [v629, v758, v897, v1094, v1308, v1349, v1483] .nil .nil) (.node [v629, v758, v897, v1094, v1308, v1406, v1483] .nil .nil)) (.node [v629, v758, v897, v1094, v1308, v1483] (.node [v629, v758, v897, v1094, v1308, v1462, v1483] .nil .nil) .nil)) (.node [v629, v758, v897, v1094, v1308, v1483, v1544] (.node [v629, v758, v897, v1094, v1308, v1483, v1536] (.node [v629, v758, v897, v1094, v1308, v1483, v1504] .nil .nil) .nil) (.node [v629, v758, v897, v1094, v1308, v1483, v1562] (.node [v629, v758, v897, v1094, v1308, v1483, v1554] .nil .nil) .nil))) (.node [v629, v897, v1003, v1094, v1131, v1308, v1483] (.node [v629, v786, v897, v1094, v1308, v1483] (.node [v629, v786, v897, v973, v1094, v1308, v1483] (.node [v629, v758, v897, v1094, v1308, v1483, v1590] .nil .nil) .nil) (.node [v629, v840, v897, v1094, v1308, v1483] (.node [v629, v814, v840, v897, v1094, v1308, v1483] .nil .nil) .nil)) (.node [v629, v897, v1027, v1094, v1143, v1308, v1483] (.node [v629, v897, v1019, v1094, v1141, v1308, v1483] (.node [v629, v897, v1010, v1094, v1134, v1308, v1483] .nil .nil) .nil) (.node [v629, v897, v1060, v1094, v1242, v1308, v1483] (.node [v629, v897, v1060, v1094, v1205, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrrrl_ok : everyKey (rowOK 5 level5) level6rrrrrl = true := by decide +kernel
def level6rrrrrr : BinaryTree (List W) := (.node [v629, v897, v1094, v1308, v1353, v1483] (.node [v629, v897, v1094, v1214, v1308, v1417, v1483] (.node [v629, v897, v1094, v1143, v1308, v1483] (.node [v629, v897, v1094, v1134, v1308, v1483] (.node [v629, v897, v1094, v1131, v1308, v1483] .nil .nil) (.node [v629, v897, v1094, v1141, v1308, v1483] .nil .nil)) (.node [v629, v897, v1094, v1205, v1308, v1432, v1483] (.node [v629, v897, v1094, v1205, v1308, v1349, v1483] .nil .nil) .nil)) (.node [v629, v897, v1094, v1308, v1341, v1462, v1483] (.node [v629, v897, v1094, v1242, v1308, v1432, v1483] (.node [v629, v897, v1094, v1242, v1308, v1349, v1483] .nil .nil) .nil) (.node [v629, v897, v1094, v1308, v1349, v1483, v1544] (.node [v629, v897, v1094, v1308, v1341, v1483] .nil .nil) .nil))) (.node [v629, v897, v1094, v1308, v1373, v1483] (.node [v629, v897, v1094, v1308, v1365, v1483] (.node [v629, v897, v1094, v1308, v1365, v1406, v1483] (.node [v629, v897, v1094, v1308, v1353, v1483, v1504] .nil .nil) .nil) (.node [v629, v897, v1094, v1308, v1366, v1483, v1554] (.node [v629, v897, v1094, v1308, v1366, v1483] .nil .nil) .nil)) (.node [v629, v897, v1094, v1308, v1432, v1483, v1544] (.node [v629, v897, v1094, v1308, v1417, v1483] (.node [v629, v897, v1094, v1308, v1373, v1483, v1590] .nil .nil) .nil) (.node [v758, v897, v1094, v1308, v1483, v1578] (.node [v758, v897, v1094, v1215, v1308, v1483] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrrrr_ok : everyKey (rowOK 5 level5) level6rrrrrr = true := by decide +kernel
def level6rrrrr : BinaryTree (List W) := .node [v629, v897, v1060, v1094, v1308, v1483, v1544] level6rrrrrl level6rrrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrrr_ok : everyKey (rowOK 5 level5) level6rrrrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrrrrl && everyKey (rowOK 5 level5) level6rrrrrr) = true
  rw [level6rrrrrl_ok, level6rrrrrr_ok]
  decide +kernel
def level6rrrr : BinaryTree (List W) := .node [v629, v758, v897, v1094, v1308, v1346, v1483] level6rrrrl level6rrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrr_ok : everyKey (rowOK 5 level5) level6rrrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrrrl && everyKey (rowOK 5 level5) level6rrrrr) = true
  rw [level6rrrrl_ok, level6rrrrr_ok]
  decide +kernel
def level6rrr : BinaryTree (List W) := .node [v405, v629, v758, v897, v1094, v1308, v1483] level6rrrl level6rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrr_ok : everyKey (rowOK 5 level5) level6rrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrrl && everyKey (rowOK 5 level5) level6rrrr) = true
  rw [level6rrrl_ok, level6rrrr_ok]
  decide +kernel
def level6rr : BinaryTree (List W) := .node [v375, v822, v897, v1094, v1308, v1483, v1578] level6rrl level6rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rr_ok : everyKey (rowOK 5 level5) level6rr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrl && everyKey (rowOK 5 level5) level6rrr) = true
  rw [level6rrl_ok, level6rrr_ok]
  decide +kernel
def level6r : BinaryTree (List W) := .node [v375, v629, v897, v1094, v1297, v1308, v1483] level6rl level6rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6r_ok : everyKey (rowOK 5 level5) level6r = true := by
  change (_ && everyKey (rowOK 5 level5) level6rl && everyKey (rowOK 5 level5) level6rr) = true
  rw [level6rl_ok, level6rr_ok]
  decide +kernel
def level6 : BinaryTree (List W) := .node [v375, v511, v629, v897, v1094, v1308, v1483] level6l level6r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6_ok : everyKey (rowOK 5 level5) level6 = true := by
  change (_ && everyKey (rowOK 5 level5) level6l && everyKey (rowOK 5 level5) level6r) = true
  rw [level6l_ok, level6r_ok]
  decide +kernel
theorem closed6 : Closed 6 level6 := closed_next 5 (by decide) level6 level5 closed5 level6_ok
def level7l : BinaryTree (List W) := (.node [v231, v375, v629, v897, v1094, v1308, v1483] (.node [v132, v375, v629, v897, v1094, v1308, v1483] (.node [v88, v375, v629, v897, v1094, v1308, v1483] (.node [v80, v375, v629, v897, v1094, v1308, v1483] (.node [v64, v375, v629, v897, v1094, v1308, v1483] (.node [v36, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v82, v375, v629, v897, v1094, v1308, v1483] .nil .nil)) (.node [v102, v375, v629, v897, v1094, v1308, v1483] (.node [v90, v375, v629, v897, v1094, v1308, v1483] .nil .nil) (.node [v108, v375, v629, v897, v1094, v1308, v1483] .nil .nil))) (.node [v187, v375, v629, v897, v1094, v1308, v1483] (.node [v159, v375, v629, v897, v1094, v1308, v1483] (.node [v137, v375, v629, v897, v1094, v1308, v1483] .nil .nil) (.node [v175, v375, v629, v897, v1094, v1308, v1483] .nil .nil)) (.node [v193, v375, v629, v897, v1094, v1308, v1483] (.node [v190, v375, v629, v897, v1094, v1308, v1483] .nil .nil) (.node [v225, v375, v629, v897, v1094, v1308, v1483] .nil .nil)))) (.node [v375, v480, v897, v1094, v1308, v1483] (.node [v303, v375, v629, v897, v1094, v1308, v1483] (.node [v264, v375, v629, v897, v1094, v1308, v1483] (.node [v237, v629, v897, v1094, v1308, v1483] (.node [v237, v375, v629, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v266, v375, v629, v897, v1094, v1308, v1483] .nil .nil)) (.node [v375, v422, v629, v897, v1094, v1308, v1483] (.node [v375, v419, v629, v897, v1094, v1308, v1483] .nil .nil) (.node [v375, v480, v629, v897, v1094, v1308, v1483] .nil .nil))) (.node [v375, v629, v708, v897, v1094, v1308, v1483] (.node [v375, v497, v897, v1094, v1308, v1483] (.node [v375, v497, v629, v897, v1094, v1308, v1483] .nil .nil) (.node [v375, v513, v629, v897, v1094, v1308, v1483] .nil .nil)) (.node [v375, v629, v727, v897, v1094, v1308, v1483] (.node [v375, v629, v722, v897, v1094, v1308, v1483] .nil .nil) (.node [v375, v629, v737, v897, v1094, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7l_ok : everyKey (rowOK 6 level6) level7l = true := by decide +kernel
def level7r : BinaryTree (List W) := (.node [v375, v629, v897, v1094, v1242, v1308, v1483] (.node [v375, v629, v897, v1019, v1094, v1308, v1483] (.node [v375, v629, v897, v973, v1094, v1308, v1483] (.node [v375, v629, v848, v897, v1094, v1308, v1483] (.node [v375, v629, v814, v897, v1094, v1308, v1483] (.node [v375, v629, v791, v897, v1094, v1308, v1483] .nil .nil) .nil) (.node [v375, v629, v897, v934, v1094, v1308, v1483] .nil .nil)) (.node [v375, v629, v897, v1003, v1094, v1308, v1483] (.node [v375, v629, v897, v996, v1094, v1308, v1483] .nil .nil) (.node [v375, v629, v897, v1010, v1094, v1308, v1483] .nil .nil))) (.node [v375, v629, v897, v1094, v1194, v1308, v1483] (.node [v375, v629, v897, v1056, v1094, v1308, v1483] (.node [v375, v629, v897, v1027, v1094, v1308, v1483] .nil .nil) (.node [v375, v629, v897, v1060, v1094, v1308, v1483] .nil .nil)) (.node [v375, v629, v897, v1094, v1214, v1308, v1483] (.node [v375, v629, v897, v1094, v1205, v1308, v1483] .nil .nil) (.node [v375, v629, v897, v1094, v1215, v1308, v1483] .nil .nil)))) (.node [v375, v629, v897, v1094, v1308, v1483, v1544] (.node [v375, v629, v897, v1094, v1308, v1432, v1483] (.node [v375, v629, v897, v1094, v1308, v1349, v1483] (.node [v375, v629, v897, v1094, v1252, v1308, v1483] .nil .nil) (.node [v375, v629, v897, v1094, v1308, v1406, v1483] .nil .nil)) (.node [v375, v629, v897, v1094, v1308, v1483, v1504] (.node [v375, v629, v897, v1094, v1308, v1462, v1483] .nil .nil) (.node [v375, v629, v897, v1094, v1308, v1483, v1536] .nil .nil))) (.node [v375, v629, v897, v1094, v1308, v1483, v1590] (.node [v375, v629, v897, v1094, v1308, v1483, v1562] (.node [v375, v629, v897, v1094, v1308, v1483, v1554] .nil .nil) (.node [v375, v629, v897, v1094, v1308, v1483, v1578] .nil .nil)) (.node [v375, v897, v1094, v1308, v1483, v1578] (.node [v375, v897, v1094, v1215, v1308, v1483] .nil .nil) (.node [v629, v758, v897, v1094, v1308, v1483] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7r_ok : everyKey (rowOK 6 level6) level7r = true := by decide +kernel
def level7 : BinaryTree (List W) := .node [v375, v629, v758, v897, v1094, v1308, v1483] level7l level7r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7_ok : everyKey (rowOK 6 level6) level7 = true := by
  change (_ && everyKey (rowOK 6 level6) level7l && everyKey (rowOK 6 level6) level7r) = true
  rw [level7l_ok, level7r_ok]
  decide +kernel
theorem closed7 : Closed 7 level7 := closed_next 6 (by decide) level7 level6 closed6 level7_ok
def level8 : BinaryTree (List W) := (.node [v375, v629, v897, v1094, v1308, v1483] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8_ok : everyKey (rowOK 7 level7) level8 = true := by decide +kernel
theorem closed8 : Closed 8 level8 := closed_next 7 (by decide) level8 level7 closed7 level8_ok

theorem lower : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z 8 ins.toFinset :=
  @no_build 8 level8 ins (by decide +kernel) (by decide) closed8 (by decide +kernel)
def witness : List Gate := [⟨.and,[3,5]⟩,⟨.or,[1,2]⟩,⟨.or,[7,6]⟩,⟨.and,[0,8]⟩,⟨.or,[2,3]⟩,⟨.and,[4,10]⟩,⟨.and,[2,6]⟩,⟨.or,[11,12]⟩,⟨.and,[1,13]⟩,⟨.or,[9,14]⟩]
theorem upper : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 10 ∧ ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xeee8eaa8ece8a8a8 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact ⟨witness,15,by simp [witness],rfl,by decide +kernel⟩
end PEqualNP.Outside.L_meta_16281_aux

open PEqualNP.Outside.L_meta_16281_aux in
theorem PEqualNP.Outside.L_meta_16281 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241832 * 2 ^ 32 + 3974670504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241832 * 2 ^ 32 + 3974670504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  have code : 4008241832 * 2 ^ 32 + 3974670504 = 0xeee8eaa8ece8a8a8 := by decide
  simp only [code] at h ⊢
  obtain ⟨C,legal,size,computes⟩ := h
  obtain ⟨gs,o,mono,bound,ev⟩ := replace 0xeee8eaa8ece8a8a8 10 ins (by decide +kernel) sampled rfl lower upper C.gates C.output legal computes
  exact ⟨⟨gs,o⟩,mono,bound.trans size,ev⟩
