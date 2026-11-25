import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_15095

-- The signed circuit search uses the live-wire compression from L-meta-1423.
-- A NOT gate costs one gate in the given circuit and zero in the signed search.
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

-- The upper and lower halves represent opposite target labels on 36 pairs of assignments.
abbrev W := BitVec 72
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 36 := ((x >>> 36) ^^^ x).setWidth 36
def cuts (ws : List W) : BitVec 36 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 36) ++ (0 : BitVec 36)
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

def differs (i : Fin 36) (w : W) : Prop :=
  w.getLsbD (36+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 36) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 36+i.val < 72 := by omega
  have hi' : i.val < 72 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 36) :
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
  change (cuts ws)[j] = (BitVec.allOnes 36)[j]
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
  · change reachable av (BitVec.allOnes 72 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 72)
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

private def bit (k : Fin 72) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 72) :
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

theorem evalAnd (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
theorem evalOr (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
theorem evalNot (xs : List Bool) : GateOp.not.eval xs = !(xs.headD false) := rfl

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 72) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#72)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, evalAnd, evalOr, evalNot, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
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
    (row : ∀ j : Fin 72, Nat.testBit T (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
    (width : ins.length = 6) (rejection : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z n ins.toFinset)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 6, if x i then 2^(i : ℕ) else 0)) : n < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ ins, holds ins.toFinset u := fun u hu =>
    .inr (.inr ⟨u,List.mem_toFinset.mpr hu,.inl rfl⟩)
  have evaluate (k : Fin 72) :
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
    (row : ∀ j : Fin 72, Nat.testBit T (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
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

def signal0 : W := (0x0 : BitVec 36) ++ (0xa42510880 : BitVec 36)
def signal1 : W := (0x0 : BitVec 36) ++ (0xc42118880 : BitVec 36)
def signal2 : W := (0x0 : BitVec 36) ++ (0xe02418080 : BitVec 36)
def signal3 : W := (0x0 : BitVec 36) ++ (0xe40018800 : BitVec 36)
def signal4 : W := (0x0 : BitVec 36) ++ (0xe42500000 : BitVec 36)
def signal5 : W := (0x0 : BitVec 36) ++ (0xe42518880 : BitVec 36)
def signal6 : W := (0x12bab : BitVec 36) ++ (0x611f : BitVec 36)
def signal7 : W := (0x12bab : BitVec 36) ++ (0x1699f : BitVec 36)
def signal8 : W := (0x12bab : BitVec 36) ++ (0xa4251699f : BitVec 36)
def signal9 : W := (0x1b4e9 : BitVec 36) ++ (0x1f0f8 : BitVec 36)
def signal10 : W := (0x1bf42 : BitVec 36) ++ (0x1ff00 : BitVec 36)
def signal11 : W := (0x1bfeb : BitVec 36) ++ (0x777f : BitVec 36)
def signal12 : W := (0x1bfeb : BitVec 36) ++ (0x17fff : BitVec 36)
def signal13 : W := (0x1bfeb : BitVec 36) ++ (0x18ee7 : BitVec 36)
def signal14 : W := (0x1bfeb : BitVec 36) ++ (0x1efff : BitVec 36)
def signal15 : W := (0x1bfeb : BitVec 36) ++ (0x1f7ff : BitVec 36)
def signal16 : W := (0x1bfeb : BitVec 36) ++ (0x1f9ff : BitVec 36)
def signal17 : W := (0x1bfeb : BitVec 36) ++ (0x1feff : BitVec 36)
def signal18 : W := (0x1bfeb : BitVec 36) ++ (0x1ff7f : BitVec 36)
def signal19 : W := (0x1bfeb : BitVec 36) ++ (0x1ff9f : BitVec 36)
def signal20 : W := (0x1bfeb : BitVec 36) ++ (0x1ffff : BitVec 36)
def signal21 : W := (0x1bfeb : BitVec 36) ++ (0xe4250777f : BitVec 36)
def signal22 : W := (0x29a00ad : BitVec 36) ++ (0x1880067 : BitVec 36)
def signal23 : W := (0x29a00ad : BitVec 36) ++ (0x39800e7 : BitVec 36)
def signal24 : W := (0x29a00ad : BitVec 36) ++ (0xc439988e7 : BitVec 36)
def signal25 : W := (0x2e400b9 : BitVec 36) ++ (0x3e000f8 : BitVec 36)
def signal26 : W := (0x2fe0014 : BitVec 36) ++ (0x3fe0000 : BitVec 36)
def signal27 : W := (0x2fe00bd : BitVec 36) ++ (0x1ae007f : BitVec 36)
def signal28 : W := (0x2fe00bd : BitVec 36) ++ (0x256009f : BitVec 36)
def signal29 : W := (0x2fe00bd : BitVec 36) ++ (0x3be00ff : BitVec 36)
def signal30 : W := (0x2fe00bd : BitVec 36) ++ (0x3de00ff : BitVec 36)
def signal31 : W := (0x2fe00bd : BitVec 36) ++ (0x3ee00ff : BitVec 36)
def signal32 : W := (0x2fe00bd : BitVec 36) ++ (0x3f600ff : BitVec 36)
def signal33 : W := (0x2fe00bd : BitVec 36) ++ (0x3f800ff : BitVec 36)
def signal34 : W := (0x2fe00bd : BitVec 36) ++ (0x3fe007f : BitVec 36)
def signal35 : W := (0x2fe00bd : BitVec 36) ++ (0x3fe00e7 : BitVec 36)
def signal36 : W := (0x2fe00bd : BitVec 36) ++ (0x3fe00ff : BitVec 36)
def signal37 : W := (0x2fe00bd : BitVec 36) ++ (0xe41af887f : BitVec 36)
def signal38 : W := (0x2ffbf56 : BitVec 36) ++ (0x3ffff00 : BitVec 36)
def signal39 : W := (0x54000b02 : BitVec 36) ++ (0x7c000f00 : BitVec 36)
def signal40 : W := (0x541a0004 : BitVec 36) ++ (0x7c1e0000 : BitVec 36)
def signal41 : W := (0x541a0b06 : BitVec 36) ++ (0x3c0e0707 : BitVec 36)
def signal42 : W := (0x541a0b06 : BitVec 36) ++ (0x4c160907 : BitVec 36)
def signal43 : W := (0x541a0b06 : BitVec 36) ++ (0x70180e07 : BitVec 36)
def signal44 : W := (0x541a0b06 : BitVec 36) ++ (0x7c0e0f07 : BitVec 36)
def signal45 : W := (0x541a0b06 : BitVec 36) ++ (0x7c160f07 : BitVec 36)
def signal46 : W := (0x541a0b06 : BitVec 36) ++ (0x7c1e0707 : BitVec 36)
def signal47 : W := (0x541a0b06 : BitVec 36) ++ (0x7c1e0e07 : BitVec 36)
def signal48 : W := (0x541a0b06 : BitVec 36) ++ (0x7c1e0f07 : BitVec 36)
def signal49 : W := (0x541a0b06 : BitVec 36) ++ (0xe3e4f8787 : BitVec 36)
def signal50 : W := (0x541bb4ed : BitVec 36) ++ (0x7c1ff0f8 : BitVec 36)
def signal51 : W := (0x56e40bbb : BitVec 36) ++ (0x7fe00ff8 : BitVec 36)
def signal52 : W := (0x288004000 : BitVec 36) ++ (0x38c007100 : BitVec 36)
def signal53 : W := (0x288644010 : BitVec 36) ++ (0x18c267118 : BitVec 36)
def signal54 : W := (0x288644010 : BitVec 36) ++ (0x20c466118 : BitVec 36)
def signal55 : W := (0x288644010 : BitVec 36) ++ (0x380607018 : BitVec 36)
def signal56 : W := (0x288644010 : BitVec 36) ++ (0x38c267118 : BitVec 36)
def signal57 : W := (0x288644010 : BitVec 36) ++ (0x38c467118 : BitVec 36)
def signal58 : W := (0x288644010 : BitVec 36) ++ (0x38c660000 : BitVec 36)
def signal59 : W := (0x288644010 : BitVec 36) ++ (0x38c667118 : BitVec 36)
def signal60 : W := (0x288644010 : BitVec 36) ++ (0xdce37f998 : BitVec 36)
def signal61 : W := (0x28865fffb : BitVec 36) ++ (0x38c678ee7 : BitVec 36)
def signal62 : W := (0x28a9a40ad : BitVec 36) ++ (0x38f9871e7 : BitVec 36)
def signal63 : W := (0x28afe4014 : BitVec 36) ++ (0x38ffe0000 : BitVec 36)
def signal64 : W := (0x28afe40bd : BitVec 36) ++ (0x18dae717f : BitVec 36)
def signal65 : W := (0x2dc7e4014 : BitVec 36) ++ (0x3fc7e0000 : BitVec 36)
def signal66 : W := (0x2dc7e4b16 : BitVec 36) ++ (0x3f0787e1f : BitVec 36)
def signal67 : W := (0x521000000 : BitVec 36) ++ (0x5b1a80000 : BitVec 36)
def signal68 : W := (0x521009440 : BitVec 36) ++ (0x1b1a81660 : BitVec 36)
def signal69 : W := (0x521009440 : BitVec 36) ++ (0x431888660 : BitVec 36)
def signal70 : W := (0x521009440 : BitVec 36) ++ (0x581a09060 : BitVec 36)
def signal71 : W := (0x521009440 : BitVec 36) ++ (0x5b0009600 : BitVec 36)
def signal72 : W := (0x521009440 : BitVec 36) ++ (0x5b1a81660 : BitVec 36)
def signal73 : W := (0x521009440 : BitVec 36) ++ (0x5b1a88660 : BitVec 36)
def signal74 : W := (0x521009440 : BitVec 36) ++ (0x5b1a89660 : BitVec 36)
def signal75 : W := (0x521009440 : BitVec 36) ++ (0xbf3f91ee0 : BitVec 36)
def signal76 : W := (0x521012bab : BitVec 36) ++ (0x5b1a9699f : BitVec 36)
def signal77 : W := (0x52101bf42 : BitVec 36) ++ (0x5b001ff00 : BitVec 36)
def signal78 : W := (0x52101bfeb : BitVec 36) ++ (0x1b1a8777f : BitVec 36)
def signal79 : W := (0x523fe94fd : BitVec 36) ++ (0x5b256969f : BitVec 36)
def signal80 : W := (0x575009f42 : BitVec 36) ++ (0x5fc009f00 : BitVec 36)
def signal81 : W := (0x5751a9f46 : BitVec 36) ++ (0x5cdb69967 : BitVec 36)
def signal82 : W := (0x7a964d450 : BitVec 36) ++ (0x63dcee778 : BitVec 36)
def signal83 : W := (0x8569b2baf : BitVec 36) ++ (0x842110887 : BitVec 36)
def signal84 : W := (0xa8ae560b9 : BitVec 36) ++ (0xa02416098 : BitVec 36)
def signal85 : W := (0xadc016b02 : BitVec 36) ++ (0xa4c016900 : BitVec 36)
def signal86 : W := (0xadefe4014 : BitVec 36) ++ (0xc060000 : BitVec 36)
def signal87 : W := (0xadefe4014 : BitVec 36) ++ (0xa4e560000 : BitVec 36)
def signal88 : W := (0xadefe4014 : BitVec 36) ++ (0xa4e570880 : BitVec 36)
def signal89 : W := (0xadefe4014 : BitVec 36) ++ (0xa4ffe0000 : BitVec 36)
def signal90 : W := (0xadefe4014 : BitVec 36) ++ (0xa7e5e0000 : BitVec 36)
def signal91 : W := (0xadefe4014 : BitVec 36) ++ (0xbce760000 : BitVec 36)
def signal92 : W := (0xadefe4014 : BitVec 36) ++ (0xe4e560000 : BitVec 36)
def signal93 : W := (0xadeff6bbf : BitVec 36) ++ (0xc06611f : BitVec 36)
def signal94 : W := (0xadeff6bbf : BitVec 36) ++ (0xc07699f : BitVec 36)
def signal95 : W := (0xadeff6bbf : BitVec 36) ++ (0xe56619f : BitVec 36)
def signal96 : W := (0xadeff6bbf : BitVec 36) ++ (0x4c16691f : BitVec 36)
def signal97 : W := (0xadeff6bbf : BitVec 36) ++ (0x20c46611f : BitVec 36)
def signal98 : W := (0xadeff6bbf : BitVec 36) ++ (0x84e17699f : BitVec 36)
def signal99 : W := (0xadeff6bbf : BitVec 36) ++ (0xa0e47619f : BitVec 36)
def signal100 : W := (0xadeff6bbf : BitVec 36) ++ (0xa4251689f : BitVec 36)
def signal101 : W := (0xadeff6bbf : BitVec 36) ++ (0xa4c07691f : BitVec 36)
def signal102 : W := (0xadeff6bbf : BitVec 36) ++ (0xa4e56611f : BitVec 36)
def signal103 : W := (0xadeff6bbf : BitVec 36) ++ (0xa4e570887 : BitVec 36)
def signal104 : W := (0xadeff6bbf : BitVec 36) ++ (0xa4e57699f : BitVec 36)
def signal105 : W := (0xadeff6bbf : BitVec 36) ++ (0xe4e57699f : BitVec 36)
def signal106 : W := (0xadeff6bbf : BitVec 36) ++ (0xe4e57e99f : BitVec 36)
def signal107 : W := (0xd2381b4e9 : BitVec 36) ++ (0xc038180e0 : BitVec 36)
def signal108 : W := (0xd7501bf42 : BitVec 36) ++ (0x30000600 : BitVec 36)
def signal109 : W := (0xd7501bf42 : BitVec 36) ++ (0xc70018e00 : BitVec 36)
def signal110 : W := (0xd7501bf42 : BitVec 36) ++ (0xc7001ff00 : BitVec 36)
def signal111 : W := (0xd7501bf42 : BitVec 36) ++ (0xc72118e80 : BitVec 36)
def signal112 : W := (0xd7501bf42 : BitVec 36) ++ (0xc7c018f00 : BitVec 36)
def signal113 : W := (0xd7501bf42 : BitVec 36) ++ (0xdf0019e00 : BitVec 36)
def signal114 : W := (0xd7501bf42 : BitVec 36) ++ (0xe70018e00 : BitVec 36)
def signal115 : W := (0xd779a0004 : BitVec 36) ++ (0xc73980000 : BitVec 36)
def signal116 : W := (0xd779bbfef : BitVec 36) ++ (0x31880667 : BitVec 36)
def signal117 : W := (0xd779bbfef : BitVec 36) ++ (0x31898ee7 : BitVec 36)
def signal118 : W := (0xd779bbfef : BitVec 36) ++ (0x339806e7 : BitVec 36)
def signal119 : W := (0xd779bbfef : BitVec 36) ++ (0x71980e67 : BitVec 36)
def signal120 : W := (0xd779bbfef : BitVec 36) ++ (0x431888667 : BitVec 36)
def signal121 : W := (0xd779bbfef : BitVec 36) ++ (0x873990ee7 : BitVec 36)
def signal122 : W := (0xd779bbfef : BitVec 36) ++ (0xc338986e7 : BitVec 36)
def signal123 : W := (0xd779bbfef : BitVec 36) ++ (0xc439188e7 : BitVec 36)
def signal124 : W := (0xd779bbfef : BitVec 36) ++ (0xc71898e67 : BitVec 36)
def signal125 : W := (0xd779bbfef : BitVec 36) ++ (0xc72118e87 : BitVec 36)
def signal126 : W := (0xd779bbfef : BitVec 36) ++ (0xc73980667 : BitVec 36)
def signal127 : W := (0xd779bbfef : BitVec 36) ++ (0xc73998ee7 : BitVec 36)
def signal128 : W := (0xd779bbfef : BitVec 36) ++ (0xe73998ee7 : BitVec 36)
def signal129 : W := (0xd779bbfef : BitVec 36) ++ (0xe73d98ee7 : BitVec 36)
def signal130 : W := (0xfa901f440 : BitVec 36) ++ (0xf8001f000 : BitVec 36)
def signal131 : W := (0xfa901ff42 : BitVec 36) ++ (0xf8001ff00 : BitVec 36)
def signal132 : W := (0xfabe44010 : BitVec 36) ++ (0xf83e00000 : BitVec 36)
def signal133 : W := (0xfabe5f4f9 : BitVec 36) ++ (0x181a07078 : BitVec 36)
def signal134 : W := (0xfabe5f4f9 : BitVec 36) ++ (0x181a1f0f8 : BitVec 36)
def signal135 : W := (0xfabe5f4f9 : BitVec 36) ++ (0x183e070f8 : BitVec 36)
def signal136 : W := (0xfabe5f4f9 : BitVec 36) ++ (0x381e07078 : BitVec 36)
def signal137 : W := (0xfabe5f4f9 : BitVec 36) ++ (0x581a0f078 : BitVec 36)
def signal138 : W := (0xfabe5f4f9 : BitVec 36) ++ (0xb83e170f8 : BitVec 36)
def signal139 : W := (0xfabe5f4f9 : BitVec 36) ++ (0xd83a1f0f8 : BitVec 36)
def signal140 : W := (0xfabe5f4f9 : BitVec 36) ++ (0xe03c1e0f8 : BitVec 36)
def signal141 : W := (0xfabe5f4f9 : BitVec 36) ++ (0xf81a1f078 : BitVec 36)
def signal142 : W := (0xfabe5f4f9 : BitVec 36) ++ (0xf8241f098 : BitVec 36)
def signal143 : W := (0xfabe5f4f9 : BitVec 36) ++ (0xf83e07078 : BitVec 36)
def signal144 : W := (0xfabe5f4f9 : BitVec 36) ++ (0xf83e180e0 : BitVec 36)
def signal145 : W := (0xfabe5f4f9 : BitVec 36) ++ (0xf83e1f0f8 : BitVec 36)
def signal146 : W := (0xfabe5f4f9 : BitVec 36) ++ (0xfc3e1f8f8 : BitVec 36)
def signal147 : W := (0xfabe5f4f9 : BitVec 36) ++ (0xfc3f1f0f8 : BitVec 36)
def signal148 : W := (0xfabe5f4f9 : BitVec 36) ++ (0xfc3f1f8f8 : BitVec 36)
def signal149 : W := (0xfabfe4014 : BitVec 36) ++ (0xf83fe0000 : BitVec 36)
def signal150 : W := (0xffd004000 : BitVec 36) ++ (0xffc000000 : BitVec 36)
def signal151 : W := (0xffd01ff42 : BitVec 36) ++ (0x1bc007700 : BitVec 36)
def signal152 : W := (0xffd01ff42 : BitVec 36) ++ (0x1bc01ff00 : BitVec 36)
def signal153 : W := (0xffd01ff42 : BitVec 36) ++ (0x1fc007f00 : BitVec 36)
def signal154 : W := (0xffd01ff42 : BitVec 36) ++ (0x3bc007700 : BitVec 36)
def signal155 : W := (0xffd01ff42 : BitVec 36) ++ (0x5bc00f700 : BitVec 36)
def signal156 : W := (0xffd01ff42 : BitVec 36) ++ (0xbfc017f00 : BitVec 36)
def signal157 : W := (0xffd01ff42 : BitVec 36) ++ (0xdfc01ff00 : BitVec 36)
def signal158 : W := (0xffd01ff42 : BitVec 36) ++ (0xe7c01ef00 : BitVec 36)
def signal159 : W := (0xffd01ff42 : BitVec 36) ++ (0xfbc01f700 : BitVec 36)
def signal160 : W := (0xffd01ff42 : BitVec 36) ++ (0xfcc01f900 : BitVec 36)
def signal161 : W := (0xffd01ff42 : BitVec 36) ++ (0xff001fe00 : BitVec 36)
def signal162 : W := (0xffd01ff42 : BitVec 36) ++ (0xffc007700 : BitVec 36)
def signal163 : W := (0xffd01ff42 : BitVec 36) ++ (0xffc018e00 : BitVec 36)
def signal164 : W := (0xffd01ff42 : BitVec 36) ++ (0xffc01ff00 : BitVec 36)
def signal165 : W := (0xffd01ff42 : BitVec 36) ++ (0xffe11ff80 : BitVec 36)
def signal166 : W := (0xffd01ff42 : BitVec 36) ++ (0xffe41ff80 : BitVec 36)
def signal167 : W := (0xffd01ff42 : BitVec 36) ++ (0xffe51ff00 : BitVec 36)
def signal168 : W := (0xffd01ff42 : BitVec 36) ++ (0xffe51ff80 : BitVec 36)
def signal169 : W := (0xffd1bff46 : BitVec 36) ++ (0xffc1fff00 : BitVec 36)
def signal170 : W := (0xffd65ff52 : BitVec 36) ++ (0x1bc267718 : BitVec 36)
def signal171 : W := (0xffd65ff52 : BitVec 36) ++ (0xffc27ff18 : BitVec 36)
def signal172 : W := (0xffd65ff52 : BitVec 36) ++ (0xffc47ff18 : BitVec 36)
def signal173 : W := (0xffd65ff52 : BitVec 36) ++ (0xffc61ff18 : BitVec 36)
def signal174 : W := (0xffd65ff52 : BitVec 36) ++ (0xffc67ff00 : BitVec 36)
def signal175 : W := (0xfff9bffef : BitVec 36) ++ (0xfff99ffe7 : BitVec 36)
def signal176 : W := (0xfffe5fffb : BitVec 36) ++ (0xffe41ff98 : BitVec 36)
def signal177 : W := (0xfffe5fffb : BitVec 36) ++ (0xfffe1fff8 : BitVec 36)
def signal178 : W := (0xffffe4014 : BitVec 36) ++ (0x1bdae0000 : BitVec 36)
def signal179 : W := (0xffffe4014 : BitVec 36) ++ (0x1bffe0000 : BitVec 36)
def signal180 : W := (0xffffe4014 : BitVec 36) ++ (0x1fdbe0000 : BitVec 36)
def signal181 : W := (0xffffe4014 : BitVec 36) ++ (0x3bdee0000 : BitVec 36)
def signal182 : W := (0xffffe4014 : BitVec 36) ++ (0x5bdae0000 : BitVec 36)
def signal183 : W := (0xffffe4014 : BitVec 36) ++ (0xbfffe0000 : BitVec 36)
def signal184 : W := (0xffffe4014 : BitVec 36) ++ (0xdffbe0000 : BitVec 36)
def signal185 : W := (0xffffe4014 : BitVec 36) ++ (0xe7fde0000 : BitVec 36)
def signal186 : W := (0xffffe4014 : BitVec 36) ++ (0xfbfee0000 : BitVec 36)
def signal187 : W := (0xffffe4014 : BitVec 36) ++ (0xfcff60000 : BitVec 36)
def signal188 : W := (0xffffe4014 : BitVec 36) ++ (0xff3f80000 : BitVec 36)
def signal189 : W := (0xffffe4014 : BitVec 36) ++ (0xffdae0000 : BitVec 36)
def signal190 : W := (0xffffe4014 : BitVec 36) ++ (0xffe560000 : BitVec 36)
def signal191 : W := (0xffffe4014 : BitVec 36) ++ (0xffffe0000 : BitVec 36)
def signal192 : W := (0xffffe4014 : BitVec 36) ++ (0xfffff0880 : BitVec 36)
def signal193 : W := (0xffffe4014 : BitVec 36) ++ (0xfffff8080 : BitVec 36)
def signal194 : W := (0xffffe4014 : BitVec 36) ++ (0xfffff8800 : BitVec 36)
def signal195 : W := (0xffffe4014 : BitVec 36) ++ (0xfffff8880 : BitVec 36)
def signal196 : W := (0xffffe4b16 : BitVec 36) ++ (0xffffe0f00 : BitVec 36)
def signal197 : W := (0xffffed454 : BitVec 36) ++ (0x1bdae1660 : BitVec 36)
def signal198 : W := (0xffffed454 : BitVec 36) ++ (0xffffe1660 : BitVec 36)
def signal199 : W := (0xffffed454 : BitVec 36) ++ (0xffffe8660 : BitVec 36)
def signal200 : W := (0xffffed454 : BitVec 36) ++ (0xffffe9060 : BitVec 36)
def signal201 : W := (0xffffed454 : BitVec 36) ++ (0xffffe9600 : BitVec 36)
def signal202 : W := (0xfffff6bbf : BitVec 36) ++ (0xfffff699f : BitVec 36)
def signal203 : W := (0xffffff4fd : BitVec 36) ++ (0xfffff80e0 : BitVec 36)
def signal204 : W := (0xffffff4fd : BitVec 36) ++ (0xffffff0f8 : BitVec 36)
def signal205 : W := (0xfffffff56 : BitVec 36) ++ (0xe7e578e00 : BitVec 36)
def signal206 : W := (0xfffffff56 : BitVec 36) ++ (0xffe57ff00 : BitVec 36)
def signal207 : W := (0xfffffff56 : BitVec 36) ++ (0xfffff8e00 : BitVec 36)
def signal208 : W := (0xfffffff56 : BitVec 36) ++ (0xfffffff00 : BitVec 36)
def signal209 : W := (0xfffffffff : BitVec 36) ++ (0x3d8e677f : BitVec 36)
def signal210 : W := (0xfffffffff : BitVec 36) ++ (0x18da6717f : BitVec 36)
def signal211 : W := (0xfffffffff : BitVec 36) ++ (0x1b1a8767f : BitVec 36)
def signal212 : W := (0xfffffffff : BitVec 36) ++ (0x1bc06771f : BitVec 36)
def signal213 : W := (0xfffffffff : BitVec 36) ++ (0x1bdae0667 : BitVec 36)
def signal214 : W := (0xfffffffff : BitVec 36) ++ (0x1bdae777f : BitVec 36)
def signal215 : W := (0xfffffffff : BitVec 36) ++ (0xbffff7fff : BitVec 36)
def signal216 : W := (0xfffffffff : BitVec 36) ++ (0xdffbfffff : BitVec 36)
def signal217 : W := (0xfffffffff : BitVec 36) ++ (0xe7fdfefff : BitVec 36)
def signal218 : W := (0xfffffffff : BitVec 36) ++ (0xfbfeff7ff : BitVec 36)
def signal219 : W := (0xfffffffff : BitVec 36) ++ (0xfcff7f9ff : BitVec 36)
def signal220 : W := (0xfffffffff : BitVec 36) ++ (0xff3f9feff : BitVec 36)
def signal221 : W := (0xfffffffff : BitVec 36) ++ (0xffdafff7f : BitVec 36)
def signal222 : W := (0xfffffffff : BitVec 36) ++ (0xffe57ff9f : BitVec 36)
def signal223 : W := (0xfffffffff : BitVec 36) ++ (0xffffe777f : BitVec 36)
def signal224 : W := (0xfffffffff : BitVec 36) ++ (0xfffff8ee7 : BitVec 36)

def ins : List W := [signal214,signal104,signal127,signal145,signal164,signal191]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer0 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok0 : everyKey (fun q => !doneTest q) layer0=true := by decide +kernel
theorem closed0 : Closed 0 layer0 := closed_nil _ ok0
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer1 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok1 : everyKey (rowOK 0 layer0) layer1=true := by decide +kernel
theorem closed1 : Closed 1 layer1 := closed_next 0 (by decide) _ _ closed0 ok1
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer2 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok2 : everyKey (rowOK 1 layer1) layer2=true := by decide +kernel
theorem closed2 : Closed 2 layer2 := closed_next 1 (by decide) _ _ closed1 ok2
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer3 : BinaryTree (List W) := (.node [signal83,signal145,signal205,signal214] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok3 : everyKey (rowOK 2 layer2) layer3=true := by decide +kernel
theorem closed3 : Closed 3 layer3 := closed_next 2 (by decide) _ _ closed2 ok3
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer4 : BinaryTree (List W) := (.node [signal87,signal93,signal116,signal145,signal164] (.node [signal41,signal104,signal116,signal164,signal178] (.node [signal22,signal104,signal116,signal133,signal191] (.node [signal8,signal104,signal116,signal145,signal164] (.node [signal7,signal93,signal116,signal145,signal164] (.node [signal6,signal93,signal127,signal133,signal164] (.node [signal6,signal93,signal116,signal145,signal164] .nil .nil) (.node [signal6,signal93,signal127,signal145,signal151] .nil .nil)) (.node [signal7,signal93,signal127,signal145,signal151] (.node [signal7,signal93,signal127,signal133,signal164] .nil .nil) (.node [signal7,signal104,signal116,signal133,signal164] .nil .nil))) (.node [signal11,signal104,signal116,signal133,signal164] (.node [signal11,signal93,signal127,signal133,signal164] (.node [signal11,signal93,signal116,signal145,signal164] .nil .nil) (.node [signal11,signal93,signal127,signal145,signal151] .nil .nil)) (.node [signal22,signal93,signal116,signal145,signal191] (.node [signal21,signal104,signal127,signal145,signal164] .nil .nil) .nil))) (.node [signal27,signal93,signal127,signal133,signal191] (.node [signal23,signal104,signal116,signal133,signal191] (.node [signal23,signal93,signal116,signal145,signal191] (.node [signal22,signal104,signal116,signal145,signal178] .nil .nil) (.node [signal23,signal93,signal127,signal133,signal191] .nil .nil)) (.node [signal24,signal93,signal127,signal145,signal191] (.node [signal23,signal104,signal116,signal145,signal178] .nil .nil) (.node [signal27,signal93,signal116,signal145,signal191] .nil .nil))) (.node [signal38,signal104,signal127,signal145,signal214] (.node [signal27,signal104,signal116,signal145,signal178] (.node [signal27,signal104,signal116,signal133,signal191] .nil .nil) (.node [signal37,signal104,signal127,signal145,signal191] .nil .nil)) (.node [signal41,signal93,signal127,signal151,signal191] (.node [signal41,signal93,signal116,signal164,signal191] .nil .nil) .nil)))) (.node [signal78,signal93,signal127,signal145,signal164] (.node [signal62,signal104,signal145,signal191,signal214] (.node [signal53,signal93,signal133,signal164,signal191] (.node [signal50,signal104,signal127,signal164,signal214] (.node [signal49,signal104,signal127,signal164,signal191] .nil .nil) (.node [signal51,signal104,signal127,signal191,signal214] .nil .nil)) (.node [signal60,signal104,signal145,signal164,signal191] (.node [signal53,signal93,signal145,signal151,signal191] .nil .nil) (.node [signal61,signal104,signal145,signal164,signal214] .nil .nil))) (.node [signal68,signal116,signal145,signal164,signal178] (.node [signal66,signal104,signal164,signal191,signal214] (.node [signal64,signal104,signal116,signal145,signal191] .nil .nil) (.node [signal68,signal116,signal133,signal164,signal191] .nil .nil)) (.node [signal76,signal127,signal145,signal164,signal214] (.node [signal75,signal127,signal145,signal164,signal191] .nil .nil) .nil))) (.node [signal84,signal123,signal164,signal191,signal214] (.node [signal83,signal87,signal109,signal145,signal214] (.node [signal81,signal127,signal164,signal191,signal214] (.node [signal79,signal127,signal145,signal191,signal214] .nil .nil) (.node [signal82,signal145,signal164,signal191,signal214] .nil .nil)) (.node [signal83,signal145,signal164,signal191,signal209] (.node [signal83,signal140,signal164,signal191,signal214] .nil .nil) .nil)) (.node [signal86,signal93,signal127,signal133,signal164] (.node [signal85,signal127,signal145,signal191,signal212] (.node [signal84,signal127,signal164,signal191,signal210] .nil .nil) (.node [signal86,signal93,signal116,signal145,signal164] .nil .nil)) (.node [signal86,signal104,signal116,signal145,signal164] (.node [signal86,signal93,signal127,signal145,signal151] .nil .nil) .nil))))) (.node [signal97,signal127,signal133,signal164,signal191] (.node [signal93,signal127,signal133,signal151,signal191] (.node [signal93,signal116,signal133,signal164,signal191] (.node [signal93,signal108,signal116,signal145,signal191] (.node [signal87,signal93,signal127,signal145,signal151] (.node [signal87,signal93,signal127,signal133,signal164] .nil .nil) (.node [signal87,signal104,signal116,signal133,signal164] .nil .nil)) (.node [signal93,signal109,signal116,signal145,signal191] (.node [signal93,signal108,signal127,signal145,signal191] .nil .nil) (.node [signal93,signal109,signal127,signal133,signal191] .nil .nil))) (.node [signal93,signal118,signal145,signal164,signal191] (.node [signal93,signal116,signal145,signal164,signal178] (.node [signal93,signal116,signal145,signal151,signal191] .nil .nil) (.node [signal93,signal116,signal145,signal164,signal191] .nil .nil)) (.node [signal93,signal121,signal145,signal164,signal191] (.node [signal93,signal119,signal145,signal164,signal191] .nil .nil) .nil))) (.node [signal93,signal127,signal145,signal153,signal191] (.node [signal93,signal127,signal136,signal164,signal191] (.node [signal93,signal127,signal133,signal164,signal191] (.node [signal93,signal127,signal133,signal164,signal178] .nil .nil) (.node [signal93,signal127,signal135,signal164,signal191] .nil .nil)) (.node [signal93,signal127,signal145,signal151,signal178] (.node [signal93,signal127,signal138,signal164,signal191] .nil .nil) (.node [signal93,signal127,signal145,signal151,signal191] .nil .nil))) (.node [signal93,signal127,signal145,signal170,signal191] (.node [signal93,signal127,signal145,signal156,signal191] (.node [signal93,signal127,signal145,signal154,signal191] .nil .nil) (.node [signal93,signal127,signal145,signal164,signal197] .nil .nil)) (.node [signal96,signal116,signal145,signal164,signal191] (.node [signal94,signal116,signal145,signal164,signal191] .nil .nil) .nil)))) (.node [signal104,signal116,signal137,signal164,signal191] (.node [signal104,signal109,signal116,signal133,signal191] (.node [signal101,signal127,signal145,signal151,signal191] (.node [signal99,signal127,signal133,signal164,signal191] (.node [signal98,signal116,signal145,signal164,signal191] .nil .nil) (.node [signal100,signal107,signal164,signal191,signal214] .nil .nil)) (.node [signal104,signal108,signal116,signal133,signal191] (.node [signal104,signal107,signal164,signal191,signal211] .nil .nil) (.node [signal104,signal108,signal116,signal145,signal178] .nil .nil))) (.node [signal104,signal116,signal133,signal164,signal178] (.node [signal104,signal115,signal145,signal164,signal213] (.node [signal104,signal109,signal116,signal145,signal178] .nil .nil) (.node [signal104,signal116,signal133,signal151,signal191] .nil .nil)) (.node [signal104,signal116,signal134,signal164,signal191] (.node [signal104,signal116,signal133,signal164,signal191] .nil .nil) .nil))) (.node [signal104,signal116,signal145,signal164,signal197] (.node [signal104,signal116,signal145,signal164,signal180] (.node [signal104,signal116,signal145,signal151,signal178] (.node [signal104,signal116,signal139,signal164,signal191] .nil .nil) (.node [signal104,signal116,signal145,signal164,signal178] .nil .nil)) (.node [signal104,signal116,signal145,signal164,signal184] (.node [signal104,signal116,signal145,signal164,signal182] .nil .nil) .nil)) (.node [signal104,signal126,signal145,signal164,signal178] (.node [signal104,signal120,signal133,signal164,signal191] (.node [signal104,signal116,signal145,signal170,signal191] .nil .nil) (.node [signal104,signal122,signal133,signal164,signal191] .nil .nil)) (.node [signal104,signal127,signal145,signal205,signal214] (.node [signal104,signal127,signal133,signal151,signal178] .nil .nil) .nil))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok4 : everyKey (rowOK 3 layer3) layer4=true := by decide +kernel
theorem closed4 : Closed 4 layer4 := closed_next 3 (by decide) _ _ closed3 ok4
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer5 : BinaryTree (List W) := (.node [signal87,signal104,signal127,signal145,signal164,signal214] (.node [signal27,signal104,signal127,signal145,signal178,signal214] (.node [signal11,signal93,signal127,signal145,signal164,signal214] (.node [signal7,signal27,signal104,signal127,signal145,signal214] (.node [signal2,signal93,signal127,signal145,signal164,signal191] (.node [signal1,signal53,signal104,signal145,signal164,signal191] (.node [signal0,signal104,signal127,signal133,signal164,signal191] (.node [signal0,signal104,signal116,signal145,signal164,signal191] (.node [signal0,signal68,signal127,signal145,signal164,signal191] .nil .nil) .nil) (.node [signal0,signal104,signal127,signal145,signal151,signal191] .nil .nil)) (.node [signal1,signal104,signal127,signal145,signal164,signal178] (.node [signal1,signal104,signal127,signal133,signal164,signal191] (.node [signal1,signal93,signal127,signal145,signal164,signal191] .nil .nil) .nil) (.node [signal2,signal41,signal104,signal127,signal164,signal191] .nil .nil))) (.node [signal4,signal104,signal116,signal145,signal164,signal191] (.node [signal3,signal93,signal127,signal145,signal164,signal191] (.node [signal3,signal27,signal104,signal127,signal145,signal191] (.node [signal2,signal104,signal116,signal145,signal164,signal191] .nil .nil) .nil) (.node [signal4,signal11,signal104,signal127,signal145,signal164] .nil .nil)) (.node [signal6,signal104,signal127,signal145,signal164,signal214] (.node [signal6,signal93,signal127,signal145,signal164,signal214] (.node [signal5,signal104,signal127,signal145,signal164,signal191] .nil .nil) .nil) (.node [signal7,signal23,signal104,signal127,signal145,signal214] .nil .nil)))) (.node [signal7,signal104,signal127,signal145,signal151,signal214] (.node [signal7,signal87,signal127,signal145,signal164,signal214] (.node [signal7,signal67,signal127,signal145,signal164,signal214] (.node [signal7,signal53,signal104,signal145,signal164,signal214] (.node [signal7,signal41,signal104,signal127,signal164,signal214] .nil .nil) .nil) (.node [signal7,signal68,signal127,signal145,signal164,signal214] .nil .nil)) (.node [signal7,signal104,signal116,signal145,signal164,signal214] (.node [signal7,signal104,signal109,signal127,signal145,signal214] (.node [signal7,signal93,signal127,signal145,signal164,signal214] .nil .nil) .nil) (.node [signal7,signal104,signal127,signal133,signal164,signal214] .nil .nil))) (.node [signal11,signal23,signal104,signal127,signal145,signal214] (.node [signal9,signal40,signal104,signal127,signal164,signal214] (.node [signal8,signal104,signal127,signal145,signal164,signal214] (.node [signal7,signal104,signal127,signal145,signal164,signal214] .nil .nil) .nil) (.node [signal10,signal26,signal104,signal127,signal145,signal214] .nil .nil)) (.node [signal11,signal53,signal104,signal145,signal164,signal214] (.node [signal11,signal41,signal104,signal127,signal164,signal214] (.node [signal11,signal27,signal104,signal127,signal145,signal214] .nil .nil) .nil) (.node [signal11,signal68,signal127,signal145,signal164,signal214] .nil .nil))))) (.node [signal23,signal53,signal104,signal145,signal191,signal214] (.node [signal15,signal104,signal127,signal145,signal164,signal214] (.node [signal11,signal104,signal127,signal145,signal164,signal178] (.node [signal11,signal104,signal127,signal133,signal164,signal214] (.node [signal11,signal104,signal116,signal145,signal164,signal214] (.node [signal11,signal104,signal109,signal127,signal145,signal214] .nil .nil) .nil) (.node [signal11,signal104,signal127,signal145,signal151,signal214] .nil .nil)) (.node [signal13,signal58,signal104,signal145,signal164,signal214] (.node [signal12,signal104,signal127,signal145,signal164,signal214] (.node [signal11,signal104,signal127,signal145,signal164,signal214] .nil .nil) .nil) (.node [signal14,signal104,signal127,signal145,signal164,signal214] .nil .nil))) (.node [signal20,signal104,signal127,signal145,signal164,signal214] (.node [signal18,signal104,signal127,signal145,signal164,signal214] (.node [signal17,signal104,signal127,signal145,signal164,signal214] (.node [signal16,signal104,signal127,signal145,signal164,signal214] .nil .nil) .nil) (.node [signal19,signal104,signal127,signal145,signal164,signal214] .nil .nil)) (.node [signal23,signal41,signal104,signal127,signal191,signal214] (.node [signal22,signal104,signal127,signal145,signal191,signal214] (.node [signal22,signal104,signal116,signal145,signal191,signal214] .nil .nil) .nil) (.node [signal23,signal52,signal104,signal145,signal191,signal214] .nil .nil)))) (.node [signal25,signal39,signal104,signal127,signal191,signal214] (.node [signal23,signal104,signal116,signal145,signal191,signal214] (.node [signal23,signal93,signal127,signal145,signal191,signal214] (.node [signal23,signal87,signal104,signal127,signal145,signal214] (.node [signal23,signal68,signal127,signal145,signal191,signal214] .nil .nil) .nil) (.node [signal23,signal104,signal109,signal145,signal191,signal214] .nil .nil)) (.node [signal23,signal104,signal127,signal145,signal191,signal214] (.node [signal23,signal104,signal127,signal145,signal178,signal214] (.node [signal23,signal104,signal127,signal133,signal191,signal214] .nil .nil) .nil) (.node [signal24,signal104,signal127,signal145,signal191,signal214] .nil .nil))) (.node [signal27,signal93,signal127,signal145,signal191,signal214] (.node [signal27,signal68,signal127,signal145,signal191,signal214] (.node [signal27,signal53,signal104,signal145,signal191,signal214] (.node [signal27,signal41,signal104,signal127,signal191,signal214] .nil .nil) .nil) (.node [signal27,signal87,signal104,signal127,signal145,signal214] .nil .nil)) (.node [signal27,signal104,signal127,signal133,signal191,signal214] (.node [signal27,signal104,signal116,signal145,signal191,signal214] .nil .nil) (.node [signal27,signal104,signal127,signal145,signal151,signal191] .nil .nil)))))) (.node [signal54,signal69,signal145,signal164,signal191,signal214] (.node [signal41,signal104,signal127,signal164,signal191,signal214] (.node [signal36,signal104,signal127,signal145,signal191,signal214] (.node [signal31,signal104,signal127,signal145,signal191,signal214] (.node [signal29,signal104,signal127,signal145,signal191,signal214] (.node [signal28,signal71,signal127,signal145,signal191,signal214] (.node [signal27,signal104,signal127,signal145,signal191,signal214] .nil .nil) .nil) (.node [signal30,signal104,signal127,signal145,signal191,signal214] .nil .nil)) (.node [signal34,signal104,signal127,signal145,signal191,signal214] (.node [signal33,signal104,signal127,signal145,signal191,signal214] (.node [signal32,signal104,signal127,signal145,signal191,signal214] .nil .nil) .nil) (.node [signal35,signal104,signal127,signal145,signal191,signal214] .nil .nil))) (.node [signal41,signal104,signal109,signal127,signal191,signal214] (.node [signal41,signal87,signal104,signal127,signal164,signal214] (.node [signal41,signal68,signal127,signal164,signal191,signal214] (.node [signal41,signal53,signal104,signal164,signal191,signal214] .nil .nil) .nil) (.node [signal41,signal93,signal127,signal164,signal191,signal214] .nil .nil)) (.node [signal41,signal104,signal127,signal151,signal191,signal214] (.node [signal41,signal104,signal127,signal133,signal164,signal191] (.node [signal41,signal104,signal116,signal164,signal191,signal214] .nil .nil) .nil) (.node [signal41,signal104,signal127,signal164,signal178,signal214] .nil .nil)))) (.node [signal53,signal93,signal145,signal164,signal191,signal214] (.node [signal46,signal104,signal127,signal164,signal191,signal214] (.node [signal44,signal104,signal127,signal164,signal191,signal214] (.node [signal43,signal55,signal104,signal164,signal191,signal214] (.node [signal42,signal70,signal127,signal164,signal191,signal214] .nil .nil) .nil) (.node [signal45,signal104,signal127,signal164,signal191,signal214] .nil .nil)) (.node [signal53,signal68,signal145,signal164,signal191,signal214] (.node [signal48,signal104,signal127,signal164,signal191,signal214] (.node [signal47,signal104,signal127,signal164,signal191,signal214] .nil .nil) .nil) (.node [signal53,signal87,signal104,signal145,signal164,signal214] .nil .nil))) (.node [signal53,signal104,signal145,signal151,signal191,signal214] (.node [signal53,signal104,signal116,signal145,signal164,signal191] (.node [signal53,signal104,signal114,signal145,signal191,signal214] (.node [signal53,signal104,signal109,signal145,signal191,signal214] .nil .nil) .nil) (.node [signal53,signal104,signal133,signal164,signal191,signal214] .nil .nil)) (.node [signal53,signal104,signal145,signal164,signal191,signal214] (.node [signal53,signal104,signal145,signal164,signal178,signal214] .nil .nil) (.node [signal53,signal104,signal145,signal171,signal191,signal214] .nil .nil))))) (.node [signal72,signal127,signal145,signal164,signal191,signal214] (.node [signal68,signal92,signal127,signal145,signal164,signal214] (.node [signal63,signal104,signal109,signal127,signal145,signal214] (.node [signal57,signal104,signal145,signal164,signal191,signal214] (.node [signal56,signal104,signal145,signal164,signal191,signal214] (.node [signal54,signal104,signal109,signal145,signal191,signal214] .nil .nil) .nil) (.node [signal59,signal104,signal145,signal164,signal191,signal214] .nil .nil)) (.node [signal65,signal104,signal127,signal145,signal164,signal214] (.node [signal64,signal104,signal127,signal145,signal191,signal214] (.node [signal63,signal104,signal127,signal145,signal164,signal214] .nil .nil) .nil) (.node [signal68,signal87,signal127,signal145,signal164,signal214] .nil .nil))) (.node [signal68,signal127,signal145,signal151,signal191,signal214] (.node [signal68,signal116,signal145,signal164,signal191,signal214] (.node [signal68,signal109,signal127,signal145,signal191,signal214] (.node [signal68,signal93,signal127,signal145,signal164,signal191] .nil .nil) .nil) (.node [signal68,signal127,signal133,signal164,signal191,signal214] .nil .nil)) (.node [signal68,signal127,signal145,signal164,signal198,signal214] (.node [signal68,signal127,signal145,signal164,signal191,signal214] (.node [signal68,signal127,signal145,signal164,signal178,signal214] .nil .nil) .nil) (.node [signal69,signal87,signal127,signal145,signal164,signal214] .nil .nil)))) (.node [signal84,signal127,signal164,signal191,signal214,signal219] (.node [signal78,signal104,signal127,signal145,signal164,signal214] (.node [signal77,signal87,signal104,signal127,signal145,signal214] (.node [signal74,signal127,signal145,signal164,signal191,signal214] (.node [signal73,signal127,signal145,signal164,signal191,signal214] .nil .nil) .nil) (.node [signal77,signal104,signal127,signal145,signal191,signal214] .nil .nil)) (.node [signal83,signal104,signal109,signal145,signal191,signal214] (.node [signal83,signal87,signal127,signal145,signal164,signal214] (.node [signal80,signal104,signal127,signal145,signal191,signal214] .nil .nil) .nil) (.node [signal83,signal145,signal164,signal191,signal214,signal217] .nil .nil))) (.node [signal87,signal104,signal109,signal127,signal145,signal214] (.node [signal86,signal104,signal127,signal145,signal164,signal214] (.node [signal86,signal93,signal127,signal145,signal164,signal214] (.node [signal85,signal127,signal145,signal191,signal214,signal222] .nil .nil) .nil) (.node [signal87,signal93,signal127,signal145,signal164,signal214] .nil .nil)) (.node [signal87,signal104,signal127,signal133,signal164,signal214] (.node [signal87,signal104,signal116,signal145,signal164,signal214] .nil .nil) (.node [signal87,signal104,signal127,signal145,signal151,signal214] .nil .nil))))))) (.node [signal104,signal127,signal135,signal164,signal191,signal214] (.node [signal104,signal109,signal127,signal145,signal178,signal214] (.node [signal93,signal127,signal145,signal151,signal191,signal214] (.node [signal93,signal104,signal127,signal145,signal151,signal191] (.node [signal90,signal104,signal127,signal145,signal164,signal214] (.node [signal88,signal104,signal127,signal145,signal164,signal214] (.node [signal87,signal127,signal145,signal164,signal202,signal214] (.node [signal87,signal104,signal127,signal145,signal206,signal214] .nil .nil) .nil) (.node [signal89,signal104,signal127,signal145,signal164,signal214] .nil .nil)) (.node [signal93,signal104,signal116,signal145,signal164,signal191] (.node [signal92,signal104,signal127,signal145,signal164,signal214] (.node [signal91,signal104,signal127,signal145,signal164,signal214] .nil .nil) .nil) (.node [signal93,signal104,signal127,signal133,signal164,signal191] .nil .nil))) (.node [signal93,signal127,signal133,signal145,signal164,signal191] (.node [signal93,signal116,signal145,signal164,signal191] (.node [signal93,signal116,signal127,signal145,signal164,signal191] (.node [signal93,signal109,signal127,signal145,signal191,signal214] .nil .nil) .nil) (.node [signal93,signal116,signal145,signal164,signal191,signal214] .nil .nil)) (.node [signal93,signal127,signal145,signal151,signal164,signal191] (.node [signal93,signal127,signal133,signal164,signal191,signal214] (.node [signal93,signal127,signal133,signal164,signal191] .nil .nil) .nil) (.node [signal93,signal127,signal145,signal151,signal191] .nil .nil)))) (.node [signal100,signal127,signal145,signal164,signal191,signal214] (.node [signal95,signal127,signal145,signal164,signal191,signal214] (.node [signal93,signal127,signal145,signal164,signal191,signal215] (.node [signal93,signal127,signal145,signal164,signal191,signal214] (.node [signal93,signal127,signal145,signal164,signal178,signal214] .nil .nil) .nil) (.node [signal94,signal127,signal145,signal164,signal191,signal214] .nil .nil)) (.node [signal98,signal127,signal145,signal164,signal191,signal214] (.node [signal97,signal127,signal145,signal164,signal191,signal214] (.node [signal96,signal127,signal145,signal164,signal191,signal214] .nil .nil) .nil) (.node [signal99,signal127,signal145,signal164,signal191,signal214] .nil .nil))) (.node [signal104,signal108,signal116,signal145,signal191,signal214] (.node [signal103,signal127,signal145,signal164,signal191,signal214] (.node [signal102,signal127,signal145,signal164,signal191,signal214] (.node [signal101,signal127,signal145,signal164,signal191,signal214] .nil .nil) .nil) (.node [signal104,signal107,signal164,signal191,signal214,signal220] .nil .nil)) (.node [signal104,signal109,signal116,signal145,signal191,signal214] (.node [signal104,signal108,signal127,signal145,signal191,signal214] .nil .nil) (.node [signal104,signal109,signal127,signal133,signal191,signal214] .nil .nil))))) (.node [signal104,signal116,signal145,signal164,signal191,signal216] (.node [signal104,signal116,signal127,signal133,signal164,signal191] (.node [signal104,signal111,signal127,signal145,signal191,signal214] (.node [signal104,signal109,signal145,signal175,signal191,signal214] (.node [signal104,signal109,signal127,signal145,signal207,signal214] (.node [signal104,signal109,signal127,signal145,signal191,signal214] .nil .nil) .nil) (.node [signal104,signal110,signal127,signal145,signal191,signal214] .nil .nil)) (.node [signal104,signal114,signal127,signal145,signal191,signal214] (.node [signal104,signal113,signal127,signal145,signal191,signal214] (.node [signal104,signal112,signal127,signal145,signal191,signal214] .nil .nil) .nil) (.node [signal104,signal115,signal145,signal164,signal214,signal224] .nil .nil))) (.node [signal104,signal116,signal145,signal151,signal191,signal214] (.node [signal104,signal116,signal133,signal164,signal191] (.node [signal104,signal116,signal133,signal145,signal164,signal191] (.node [signal104,signal116,signal127,signal145,signal164,signal178] .nil .nil) .nil) (.node [signal104,signal116,signal133,signal164,signal191,signal214] .nil .nil)) (.node [signal104,signal116,signal145,signal164,signal178,signal214] (.node [signal104,signal116,signal145,signal164,signal178,signal191] (.node [signal104,signal116,signal145,signal164,signal178] .nil .nil) .nil) (.node [signal104,signal116,signal145,signal164,signal191,signal214] .nil .nil)))) (.node [signal104,signal126,signal145,signal164,signal191,signal214] (.node [signal104,signal121,signal145,signal164,signal191,signal214] (.node [signal104,signal119,signal145,signal164,signal191,signal214] (.node [signal104,signal118,signal145,signal164,signal191,signal214] (.node [signal104,signal117,signal145,signal164,signal191,signal214] .nil .nil) .nil) (.node [signal104,signal120,signal145,signal164,signal191,signal214] .nil .nil)) (.node [signal104,signal124,signal145,signal164,signal191,signal214] (.node [signal104,signal123,signal145,signal164,signal191,signal214] (.node [signal104,signal122,signal145,signal164,signal191,signal214] .nil .nil) .nil) (.node [signal104,signal125,signal145,signal164,signal191,signal214] .nil .nil))) (.node [signal104,signal127,signal133,signal164,signal178,signal214] (.node [signal104,signal127,signal132,signal164,signal204,signal214] (.node [signal104,signal127,signal131,signal145,signal191,signal214] (.node [signal104,signal127,signal130,signal177,signal191,signal214] .nil .nil) .nil) (.node [signal104,signal127,signal133,signal151,signal191,signal214] .nil .nil)) (.node [signal104,signal127,signal133,signal164,signal191,signal218] (.node [signal104,signal127,signal133,signal164,signal191,signal214] .nil .nil) (.node [signal104,signal127,signal134,signal164,signal191,signal214] .nil .nil)))))) (.node [signal104,signal127,signal145,signal164,signal189,signal214] (.node [signal104,signal127,signal145,signal157,signal191,signal214] (.node [signal104,signal127,signal145,signal149,signal164,signal214] (.node [signal104,signal127,signal140,signal164,signal191,signal214] (.node [signal104,signal127,signal138,signal164,signal191,signal214] (.node [signal104,signal127,signal137,signal164,signal191,signal214] (.node [signal104,signal127,signal136,signal164,signal191,signal214] .nil .nil) .nil) (.node [signal104,signal127,signal139,signal164,signal191,signal214] .nil .nil)) (.node [signal104,signal127,signal143,signal164,signal191,signal214] (.node [signal104,signal127,signal142,signal164,signal191,signal214] (.node [signal104,signal127,signal141,signal164,signal191,signal214] .nil .nil) .nil) (.node [signal104,signal127,signal144,signal164,signal191,signal214] .nil .nil))) (.node [signal104,signal127,signal145,signal152,signal191,signal214] (.node [signal104,signal127,signal145,signal151,signal191,signal214] (.node [signal104,signal127,signal145,signal151,signal178,signal214] (.node [signal104,signal127,signal145,signal150,signal208,signal214] .nil .nil) .nil) (.node [signal104,signal127,signal145,signal151,signal191,signal221] .nil .nil)) (.node [signal104,signal127,signal145,signal155,signal191,signal214] (.node [signal104,signal127,signal145,signal154,signal191,signal214] (.node [signal104,signal127,signal145,signal153,signal191,signal214] .nil .nil) .nil) (.node [signal104,signal127,signal145,signal156,signal191,signal214] .nil .nil)))) (.node [signal104,signal127,signal145,signal164,signal180,signal214] (.node [signal104,signal127,signal145,signal162,signal191,signal214] (.node [signal104,signal127,signal145,signal160,signal191,signal214] (.node [signal104,signal127,signal145,signal159,signal191,signal214] (.node [signal104,signal127,signal145,signal158,signal191,signal214] .nil .nil) .nil) (.node [signal104,signal127,signal145,signal161,signal191,signal214] .nil .nil)) (.node [signal104,signal127,signal145,signal164,signal178,signal223] (.node [signal104,signal127,signal145,signal164,signal178,signal214] (.node [signal104,signal127,signal145,signal163,signal191,signal214] .nil .nil) .nil) (.node [signal104,signal127,signal145,signal164,signal179,signal214] .nil .nil))) (.node [signal104,signal127,signal145,signal164,signal185,signal214] (.node [signal104,signal127,signal145,signal164,signal183,signal214] (.node [signal104,signal127,signal145,signal164,signal182,signal214] (.node [signal104,signal127,signal145,signal164,signal181,signal214] .nil .nil) .nil) (.node [signal104,signal127,signal145,signal164,signal184,signal214] .nil .nil)) (.node [signal104,signal127,signal145,signal164,signal187,signal214] (.node [signal104,signal127,signal145,signal164,signal186,signal214] .nil .nil) (.node [signal104,signal127,signal145,signal164,signal188,signal214] .nil .nil))))) (.node [signal104,signal127,signal145,signal165,signal191,signal214] (.node [signal104,signal127,signal145,signal164,signal194,signal214] (.node [signal104,signal127,signal145,signal164,signal191,signal212] (.node [signal104,signal127,signal145,signal164,signal191,signal210] (.node [signal104,signal127,signal145,signal164,signal191,signal209] (.node [signal104,signal127,signal145,signal164,signal190,signal214] .nil .nil) .nil) (.node [signal104,signal127,signal145,signal164,signal191,signal211] .nil .nil)) (.node [signal104,signal127,signal145,signal164,signal192,signal214] (.node [signal104,signal127,signal145,signal164,signal191,signal214] (.node [signal104,signal127,signal145,signal164,signal191,signal213] .nil .nil) .nil) (.node [signal104,signal127,signal145,signal164,signal193,signal214] .nil .nil))) (.node [signal104,signal127,signal145,signal164,signal199,signal214] (.node [signal104,signal127,signal145,signal164,signal197,signal214] (.node [signal104,signal127,signal145,signal164,signal196,signal214] (.node [signal104,signal127,signal145,signal164,signal195,signal214] .nil .nil) .nil) (.node [signal104,signal127,signal145,signal164,signal198,signal214] .nil .nil)) (.node [signal104,signal127,signal145,signal164,signal203,signal214] (.node [signal104,signal127,signal145,signal164,signal201,signal214] (.node [signal104,signal127,signal145,signal164,signal200,signal214] .nil .nil) .nil) (.node [signal104,signal127,signal145,signal164,signal207,signal214] .nil .nil)))) (.node [signal104,signal127,signal145,signal176,signal191,signal214] (.node [signal104,signal127,signal145,signal170,signal191,signal214] (.node [signal104,signal127,signal145,signal168,signal191,signal214] (.node [signal104,signal127,signal145,signal167,signal191,signal214] (.node [signal104,signal127,signal145,signal166,signal191,signal214] .nil .nil) .nil) (.node [signal104,signal127,signal145,signal169,signal191,signal214] .nil .nil)) (.node [signal104,signal127,signal145,signal173,signal191,signal214] (.node [signal104,signal127,signal145,signal172,signal191,signal214] (.node [signal104,signal127,signal145,signal171,signal191,signal214] .nil .nil) .nil) (.node [signal104,signal127,signal145,signal174,signal191,signal214] .nil .nil))) (.node [signal104,signal128,signal145,signal164,signal191,signal214] (.node [signal104,signal127,signal147,signal164,signal191,signal214] (.node [signal104,signal127,signal146,signal164,signal191,signal214] (.node [signal104,signal127,signal145,signal191,signal206,signal214] .nil .nil) .nil) (.node [signal104,signal127,signal148,signal164,signal191,signal214] .nil .nil)) (.node [signal105,signal127,signal145,signal164,signal191,signal214] (.node [signal104,signal129,signal145,signal164,signal191,signal214] .nil .nil) (.node [signal106,signal127,signal145,signal164,signal191,signal214] .nil .nil))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok5 : everyKey (rowOK 4 layer4) layer5=true := by decide +kernel
theorem closed5 : Closed 5 layer5 := closed_next 4 (by decide) _ _ closed4 ok5
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer6 : BinaryTree (List W) := (.node [signal83,signal104,signal127,signal145,signal164,signal191,signal214] (.node [signal28,signal104,signal127,signal145,signal164,signal191,signal214] (.node [signal11,signal104,signal127,signal145,signal164,signal191,signal214] (.node [signal4,signal104,signal127,signal145,signal164,signal191,signal214] (.node [signal2,signal104,signal127,signal145,signal164,signal191,signal214] (.node [signal1,signal104,signal127,signal145,signal164,signal191,signal214] (.node [signal0,signal104,signal127,signal145,signal164,signal191,signal214] .nil .nil) .nil) (.node [signal3,signal104,signal127,signal145,signal164,signal191,signal214] .nil .nil)) (.node [signal9,signal104,signal127,signal145,signal164,signal191,signal214] (.node [signal7,signal104,signal127,signal145,signal164,signal214] (.node [signal7,signal104,signal127,signal145,signal164,signal191,signal214] .nil .nil) .nil) (.node [signal10,signal104,signal127,signal145,signal164,signal191,signal214] .nil .nil))) (.node [signal25,signal104,signal127,signal145,signal164,signal191,signal214] (.node [signal23,signal104,signal127,signal145,signal164,signal191,signal214] (.node [signal13,signal104,signal127,signal145,signal164,signal191,signal214] (.node [signal11,signal104,signal127,signal145,signal164,signal214] .nil .nil) .nil) (.node [signal23,signal104,signal127,signal145,signal191,signal214] .nil .nil)) (.node [signal27,signal104,signal127,signal145,signal164,signal191,signal214] (.node [signal26,signal104,signal127,signal145,signal164,signal191,signal214] .nil .nil) (.node [signal27,signal104,signal127,signal145,signal191,signal214] .nil .nil)))) (.node [signal54,signal104,signal127,signal145,signal164,signal191,signal214] (.node [signal42,signal104,signal127,signal145,signal164,signal191,signal214] (.node [signal41,signal104,signal127,signal145,signal164,signal191,signal214] (.node [signal40,signal104,signal127,signal145,signal164,signal191,signal214] (.node [signal39,signal104,signal127,signal145,signal164,signal191,signal214] .nil .nil) .nil) (.node [signal41,signal104,signal127,signal164,signal191,signal214] .nil .nil)) (.node [signal53,signal104,signal127,signal145,signal164,signal191,signal214] (.node [signal52,signal104,signal127,signal145,signal164,signal191,signal214] (.node [signal43,signal104,signal127,signal145,signal164,signal191,signal214] .nil .nil) .nil) (.node [signal53,signal104,signal145,signal164,signal191,signal214] .nil .nil))) (.node [signal68,signal127,signal145,signal164,signal191,signal214] (.node [signal67,signal104,signal127,signal145,signal164,signal191,signal214] (.node [signal58,signal104,signal127,signal145,signal164,signal191,signal214] (.node [signal55,signal104,signal127,signal145,signal164,signal191,signal214] .nil .nil) .nil) (.node [signal68,signal104,signal127,signal145,signal164,signal191,signal214] .nil .nil)) (.node [signal70,signal104,signal127,signal145,signal164,signal191,signal214] (.node [signal69,signal104,signal127,signal145,signal164,signal191,signal214] .nil .nil) (.node [signal71,signal104,signal127,signal145,signal164,signal191,signal214] .nil .nil))))) (.node [signal104,signal127,signal145,signal151,signal191,signal214] (.node [signal104,signal115,signal127,signal145,signal164,signal191,signal214] (.node [signal93,signal104,signal127,signal145,signal164,signal191,signal214] (.node [signal87,signal104,signal127,signal145,signal164,signal191,signal214] (.node [signal85,signal104,signal127,signal145,signal164,signal191,signal214] (.node [signal84,signal104,signal127,signal145,signal164,signal191,signal214] .nil .nil) .nil) (.node [signal87,signal104,signal127,signal145,signal164,signal214] .nil .nil)) (.node [signal104,signal109,signal127,signal145,signal164,signal191,signal214] (.node [signal104,signal107,signal127,signal145,signal164,signal191,signal214] (.node [signal93,signal127,signal145,signal164,signal191,signal214] .nil .nil) .nil) (.node [signal104,signal109,signal127,signal145,signal191,signal214] .nil .nil))) (.node [signal104,signal127,signal133,signal145,signal164,signal191,signal214] (.node [signal104,signal127,signal130,signal145,signal164,signal191,signal214] (.node [signal104,signal116,signal145,signal164,signal191,signal214] (.node [signal104,signal116,signal127,signal145,signal164,signal191,signal214] .nil .nil) .nil) (.node [signal104,signal127,signal132,signal145,signal164,signal191,signal214] .nil .nil)) (.node [signal104,signal127,signal145,signal150,signal164,signal191,signal214] (.node [signal104,signal127,signal133,signal164,signal191,signal214] .nil .nil) (.node [signal104,signal127,signal145,signal151,signal164,signal191,signal214] .nil .nil)))) (.node [signal104,signal127,signal145,signal164,signal191,signal214,signal216] (.node [signal104,signal127,signal145,signal164,signal191,signal202,signal214] (.node [signal104,signal127,signal145,signal164,signal178,signal191,signal214] (.node [signal104,signal127,signal145,signal164,signal177,signal191,signal214] (.node [signal104,signal127,signal145,signal164,signal175,signal191,signal214] .nil .nil) .nil) (.node [signal104,signal127,signal145,signal164,signal178,signal214] .nil .nil)) (.node [signal104,signal127,signal145,signal164,signal191,signal208,signal214] (.node [signal104,signal127,signal145,signal164,signal191,signal204,signal214] .nil .nil) (.node [signal104,signal127,signal145,signal164,signal191,signal214,signal215] .nil .nil))) (.node [signal104,signal127,signal145,signal164,signal191,signal214,signal221] (.node [signal104,signal127,signal145,signal164,signal191,signal214,signal219] (.node [signal104,signal127,signal145,signal164,signal191,signal214,signal218] (.node [signal104,signal127,signal145,signal164,signal191,signal214,signal217] .nil .nil) .nil) (.node [signal104,signal127,signal145,signal164,signal191,signal214,signal220] .nil .nil)) (.node [signal104,signal127,signal145,signal164,signal191,signal214,signal223] (.node [signal104,signal127,signal145,signal164,signal191,signal214,signal222] .nil .nil) (.node [signal104,signal127,signal145,signal164,signal191,signal214,signal224] .nil .nil))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok6 : everyKey (rowOK 5 layer5) layer6=true := by decide +kernel
theorem closed6 : Closed 6 layer6 := closed_next 5 (by decide) _ _ closed5 ok6
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer7 : BinaryTree (List W) := (.node [signal104,signal127,signal145,signal164,signal191,signal214] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok7 : everyKey (rowOK 6 layer6) layer7=true := by decide +kernel
theorem closed7 : Closed 7 layer7 := closed_next 6 (by decide) _ _ closed6 ok7
def table : ℕ := 2826995840 * 2 ^ 32 + 2692775936
theorem row : ∀j : Fin 72, Nat.testBit table (∑i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i:ℕ) else 0)=goal[j.val] := by decide +kernel
theorem reject : ∀z, z=goal ∨ z = ~~~goal → ¬build basicOps z 7 ins.toFinset := no_build 7 layer7 ins (by decide) (by decide) closed7 (by decide +kernel)
open PEqualNP.CircuitLowerBounds
def monoGates : List Gate := [⟨.and,[1,3]⟩,⟨.or,[4,6]⟩,⟨.and,[2,7]⟩,⟨.and,[5,1]⟩,⟨.or,[8,9]⟩,⟨.and,[1,2]⟩,⟨.or,[3,11]⟩,⟨.and,[0,12]⟩,⟨.and,[13,10]⟩]
theorem upper : ∃(gs : List Gate) (o : ℕ), (∀g∈gs,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2) ∧ gs.length=9 ∧ ∀x : Fin 6 → Bool,Circuit.eval ⟨gs,o⟩ (List.ofFn x)=Nat.testBit table (∑i : Fin 6,if x i then 2^(i:ℕ) else 0) := ⟨monoGates,14,by simp [monoGates],rfl,by decide +kernel⟩
end PEqualNP.Outside.L_meta_15095

open PEqualNP.Outside.L_meta_15095 in
theorem PEqualNP.Outside.L_meta_15095 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (2826995840 * 2 ^ 32 + 2692775936) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (2826995840 * 2 ^ 32 + 2692775936) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro s h
  obtain ⟨C, hfan, hsize, hev⟩ := h
  obtain ⟨gates, o⟩ := C
  have hleg : ∀ g ∈ gates, legal g := by
    intro g hg
    obtain ⟨hop, cap⟩ := hfan g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    exact ⟨hop, cap⟩
  obtain ⟨ds, p, mono, len, ev⟩ := replace table 9 ins (by decide) row rfl reject upper gates o hleg hev
  refine ⟨⟨ds, p⟩, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨hop, cap⟩ := mono g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact ⟨hop, cap⟩
  · exact le_trans len hsize
  · exact ev
