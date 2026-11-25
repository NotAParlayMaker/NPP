import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_15099

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

-- The upper and lower halves represent opposite target labels on 40 pairs of assignments.
abbrev W := BitVec 80
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 40 := ((x >>> 40) ^^^ x).setWidth 40
def cuts (ws : List W) : BitVec 40 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 40) ++ (0 : BitVec 40)
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

def differs (i : Fin 40) (w : W) : Prop :=
  w.getLsbD (40+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 40) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 40+i.val < 80 := by omega
  have hi' : i.val < 80 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 40) :
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
  change (cuts ws)[j] = (BitVec.allOnes 40)[j]
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
  · change reachable av (BitVec.allOnes 80 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 80)
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

private def bit (k : Fin 80) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 80) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 80) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#80)[k.val] = false; simp
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
    (row : ∀ j : Fin 80, Nat.testBit T (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
    (width : ins.length = 6) (rejection : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z n ins.toFinset)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 6, if x i then 2^(i : ℕ) else 0)) : n < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ ins, holds ins.toFinset u := fun u hu =>
    .inr (.inr ⟨u,List.mem_toFinset.mpr hu,.inl rfl⟩)
  have evaluate (k : Fin 80) :
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
    (row : ∀ j : Fin 80, Nat.testBit T (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
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

def signal0 : W := (0x0 : BitVec 40) ++ (0xa4a50a4104 : BitVec 40)
def signal1 : W := (0x0 : BitVec 40) ++ (0xc4210c4104 : BitVec 40)
def signal2 : W := (0x0 : BitVec 40) ++ (0xe0240e0100 : BitVec 40)
def signal3 : W := (0x0 : BitVec 40) ++ (0xe4800e4000 : BitVec 40)
def signal4 : W := (0x0 : BitVec 40) ++ (0xe4a5000000 : BitVec 40)
def signal5 : W := (0x0 : BitVec 40) ++ (0xe4a50e4104 : BitVec 40)
def signal6 : W := (0x28410 : BitVec 40) ++ (0x18e39 : BitVec 40)
def signal7 : W := (0x28410 : BitVec 40) ++ (0x20e39 : BitVec 40)
def signal8 : W := (0xad75f : BitVec 40) ++ (0xe39 : BitVec 40)
def signal9 : W := (0xad75f : BitVec 40) ++ (0xa4f3d : BitVec 40)
def signal10 : W := (0xad75f : BitVec 40) ++ (0xa4a50a4f3d : BitVec 40)
def signal11 : W := (0xd73cf : BitVec 40) ++ (0xc71c6 : BitVec 40)
def signal12 : W := (0xfa5d8 : BitVec 40) ++ (0xf81f8 : BitVec 40)
def signal13 : W := (0xff690 : BitVec 40) ++ (0xffe00 : BitVec 40)
def signal14 : W := (0xff7d8 : BitVec 40) ++ (0xffff8 : BitVec 40)
def signal15 : W := (0xff7df : BitVec 40) ++ (0x1befb : BitVec 40)
def signal16 : W := (0xff7df : BitVec 40) ++ (0xbffff : BitVec 40)
def signal17 : W := (0xff7df : BitVec 40) ++ (0xdffff : BitVec 40)
def signal18 : W := (0xff7df : BitVec 40) ++ (0xe7fff : BitVec 40)
def signal19 : W := (0xff7df : BitVec 40) ++ (0xfbffb : BitVec 40)
def signal20 : W := (0xff7df : BitVec 40) ++ (0xfcffd : BitVec 40)
def signal21 : W := (0xff7df : BitVec 40) ++ (0xffefb : BitVec 40)
def signal22 : W := (0xff7df : BitVec 40) ++ (0xfff3d : BitVec 40)
def signal23 : W := (0xff7df : BitVec 40) ++ (0xe4a501befb : BitVec 40)
def signal24 : W := (0x2990014f : BitVec 40) ++ (0x398001c6 : BitVec 40)
def signal25 : W := (0x2e200168 : BitVec 40) ++ (0x3e0001f8 : BitVec 40)
def signal26 : W := (0x2fb00020 : BitVec 40) ++ (0x3ff00000 : BitVec 40)
def signal27 : W := (0x2fb00168 : BitVec 40) ++ (0x3ff001f8 : BitVec 40)
def signal28 : W := (0x2fb0016f : BitVec 40) ++ (0x1af000fb : BitVec 40)
def signal29 : W := (0x2fb0016f : BitVec 40) ++ (0x2570013d : BitVec 40)
def signal30 : W := (0x2fb0016f : BitVec 40) ++ (0x3bf001ff : BitVec 40)
def signal31 : W := (0x2fb0016f : BitVec 40) ++ (0x3df001ff : BitVec 40)
def signal32 : W := (0x2fb0016f : BitVec 40) ++ (0x3ef001fb : BitVec 40)
def signal33 : W := (0x2fb0016f : BitVec 40) ++ (0x3f7001fd : BitVec 40)
def signal34 : W := (0x2fb0016f : BitVec 40) ++ (0x3ff000fb : BitVec 40)
def signal35 : W := (0x2fb0016f : BitVec 40) ++ (0x3ff001ff : BitVec 40)
def signal36 : W := (0x2fb0016f : BitVec 40) ++ (0xe49afe40fb : BitVec 40)
def signal37 : W := (0x2fbff6b0 : BitVec 40) ++ (0x3ffffe00 : BitVec 40)
def signal38 : W := (0x501905207 : BitVec 40) ++ (0x701807006 : BitVec 40)
def signal39 : W := (0x5c0405a00 : BitVec 40) ++ (0x7c0007e00 : BitVec 40)
def signal40 : W := (0x5c1d00800 : BitVec 40) ++ (0x7c1f00000 : BitVec 40)
def signal41 : W := (0x5c1d05a00 : BitVec 40) ++ (0x7c1f07e00 : BitVec 40)
def signal42 : W := (0x5c1d05a07 : BitVec 40) ++ (0x340f03e03 : BitVec 40)
def signal43 : W := (0x5c1d05a07 : BitVec 40) ++ (0x481704e05 : BitVec 40)
def signal44 : W := (0x5c1d05a07 : BitVec 40) ++ (0x741f07e07 : BitVec 40)
def signal45 : W := (0x5c1d05a07 : BitVec 40) ++ (0x781f07e07 : BitVec 40)
def signal46 : W := (0x5c1d05a07 : BitVec 40) ++ (0x7c0f07e03 : BitVec 40)
def signal47 : W := (0x5c1d05a07 : BitVec 40) ++ (0x7c1707e05 : BitVec 40)
def signal48 : W := (0x5c1d05a07 : BitVec 40) ++ (0x7c1f03e03 : BitVec 40)
def signal49 : W := (0x5c1d05a07 : BitVec 40) ++ (0x7c1f07e07 : BitVec 40)
def signal50 : W := (0x5c1d05a07 : BitVec 40) ++ (0xe364fe3f03 : BitVec 40)
def signal51 : W := (0x5c1dfadd8 : BitVec 40) ++ (0x7c1ff81f8 : BitVec 40)
def signal52 : W := (0x5ee605b68 : BitVec 40) ++ (0x7fe007ff8 : BitVec 40)
def signal53 : W := (0x5eff00820 : BitVec 40) ++ (0x7fff00000 : BitVec 40)
def signal54 : W := (0x2806228430 : BitVec 40) ++ (0x3806038038 : BitVec 40)
def signal55 : W := (0x28c0428c10 : BitVec 40) ++ (0x38c0038e00 : BitVec 40)
def signal56 : W := (0x28c6600820 : BitVec 40) ++ (0x1842700000 : BitVec 40)
def signal57 : W := (0x28c6600820 : BitVec 40) ++ (0x2084700000 : BitVec 40)
def signal58 : W := (0x28c6600820 : BitVec 40) ++ (0x38c6700000 : BitVec 40)
def signal59 : W := (0x28c6600820 : BitVec 40) ++ (0xfce7700000 : BitVec 40)
def signal60 : W := (0x28c6628c30 : BitVec 40) ++ (0x1842718e39 : BitVec 40)
def signal61 : W := (0x28c6628c30 : BitVec 40) ++ (0x2084720e39 : BitVec 40)
def signal62 : W := (0x28c6628c30 : BitVec 40) ++ (0x3846738e39 : BitVec 40)
def signal63 : W := (0x28c6628c30 : BitVec 40) ++ (0x3886738e39 : BitVec 40)
def signal64 : W := (0x28c6628c30 : BitVec 40) ++ (0x38c2738e39 : BitVec 40)
def signal65 : W := (0x28c6628c30 : BitVec 40) ++ (0x38c4738e39 : BitVec 40)
def signal66 : W := (0x28c6628c30 : BitVec 40) ++ (0x38c6718e39 : BitVec 40)
def signal67 : W := (0x28c6628c30 : BitVec 40) ++ (0x38c6738e39 : BitVec 40)
def signal68 : W := (0x28c6628c30 : BitVec 40) ++ (0xdc637dcf3d : BitVec 40)
def signal69 : W := (0x28c66d7bef : BitVec 40) ++ (0x38c67c71c6 : BitVec 40)
def signal70 : W := (0x28e9d28d5f : BitVec 40) ++ (0x38f9838fc6 : BitVec 40)
def signal71 : W := (0x28eff00820 : BitVec 40) ++ (0x38fff00000 : BitVec 40)
def signal72 : W := (0x2d07b2d637 : BitVec 40) ++ (0x3f0783f03e : BitVec 40)
def signal73 : W := (0x2dc7f00820 : BitVec 40) ++ (0x3fc7f00000 : BitVec 40)
def signal74 : W := (0x5210000000 : BitVec 40) ++ (0x5b5a800000 : BitVec 40)
def signal75 : W := (0x5210052080 : BitVec 40) ++ (0x1b5a81b0c2 : BitVec 40)
def signal76 : W := (0x5210052080 : BitVec 40) ++ (0x43188430c2 : BitVec 40)
def signal77 : W := (0x5210052080 : BitVec 40) ++ (0x581a0580c0 : BitVec 40)
def signal78 : W := (0x5210052080 : BitVec 40) ++ (0x5b4005b000 : BitVec 40)
def signal79 : W := (0x5210052080 : BitVec 40) ++ (0x5b5a81b0c2 : BitVec 40)
def signal80 : W := (0x5210052080 : BitVec 40) ++ (0x5b5a85b0c2 : BitVec 40)
def signal81 : W := (0x5210052080 : BitVec 40) ++ (0xbfff8bf1c6 : BitVec 40)
def signal82 : W := (0x52100ad75f : BitVec 40) ++ (0x5b5a8a4f3d : BitVec 40)
def signal83 : W := (0x52100ff7df : BitVec 40) ++ (0x1b5a81befb : BitVec 40)
def signal84 : W := (0x523fb521ef : BitVec 40) ++ (0x5b6575b13d : BitVec 40)
def signal85 : W := (0x57d1d57a87 : BitVec 40) ++ (0x5c9b75cec5 : BitVec 40)
def signal86 : W := (0x7a1627a4b0 : BitVec 40) ++ (0x781e0780f8 : BitVec 40)
def signal87 : W := (0x7ad047ac90 : BitVec 40) ++ (0x7bc007be00 : BitVec 40)
def signal88 : W := (0x7ad6600820 : BitVec 40) ++ (0x7bdef00000 : BitVec 40)
def signal89 : W := (0x7ad667acb0 : BitVec 40) ++ (0x639cf63efb : BitVec 40)
def signal90 : W := (0x852998534f : BitVec 40) ++ (0x8421084104 : BitVec 40)
def signal91 : W := (0x85299ad75f : BitVec 40) ++ (0x84210a4f3d : BitVec 40)
def signal92 : W := (0xa82e2a8578 : BitVec 40) ++ (0xa0240a0138 : BitVec 40)
def signal93 : W := (0xadc04ade10 : BitVec 40) ++ (0xa4800a4e00 : BitVec 40)
def signal94 : W := (0xadeff00820 : BitVec 40) ++ (0x700000 : BitVec 40)
def signal95 : W := (0xadeff00820 : BitVec 40) ++ (0xa4a5700000 : BitVec 40)
def signal96 : W := (0xadeff00820 : BitVec 40) ++ (0xa4a57a4104 : BitVec 40)
def signal97 : W := (0xadeff00820 : BitVec 40) ++ (0xa4bff00000 : BitVec 40)
def signal98 : W := (0xadeff00820 : BitVec 40) ++ (0xa7e5f00000 : BitVec 40)
def signal99 : W := (0xadeff00820 : BitVec 40) ++ (0xbce7700000 : BitVec 40)
def signal100 : W := (0xadeff00820 : BitVec 40) ++ (0xe4a5700000 : BitVec 40)
def signal101 : W := (0xadeff85b6f : BitVec 40) ++ (0xa4a5784104 : BitVec 40)
def signal102 : W := (0xadeffadf7f : BitVec 40) ++ (0x700e39 : BitVec 40)
def signal103 : W := (0xadeffadf7f : BitVec 40) ++ (0x7a4f3d : BitVec 40)
def signal104 : W := (0xadeffadf7f : BitVec 40) ++ (0x25700f3d : BitVec 40)
def signal105 : W := (0xadeffadf7f : BitVec 40) ++ (0x481704e3d : BitVec 40)
def signal106 : W := (0xadeffadf7f : BitVec 40) ++ (0x2084720e39 : BitVec 40)
def signal107 : W := (0xadeffadf7f : BitVec 40) ++ (0x8421784f3d : BitVec 40)
def signal108 : W := (0xadeffadf7f : BitVec 40) ++ (0xa0247a0f39 : BitVec 40)
def signal109 : W := (0xadeffadf7f : BitVec 40) ++ (0xa4807a4e39 : BitVec 40)
def signal110 : W := (0xadeffadf7f : BitVec 40) ++ (0xa4a5700e39 : BitVec 40)
def signal111 : W := (0xadeffadf7f : BitVec 40) ++ (0xa4a57a4f3d : BitVec 40)
def signal112 : W := (0xadeffadf7f : BitVec 40) ++ (0xe4a57a4f3d : BitVec 40)
def signal113 : W := (0xadeffadf7f : BitVec 40) ++ (0xe4a57e4f3d : BitVec 40)
def signal114 : W := (0xd2380d21c8 : BitVec 40) ++ (0xc0380c01c0 : BitVec 40)
def signal115 : W := (0xd7100d7280 : BitVec 40) ++ (0xc7000c7000 : BitVec 40)
def signal116 : W := (0xd739900000 : BitVec 40) ++ (0xc739800000 : BitVec 40)
def signal117 : W := (0xd7399d73cf : BitVec 40) ++ (0x3188030c2 : BitVec 40)
def signal118 : W := (0xd7399d73cf : BitVec 40) ++ (0x3188c71c6 : BitVec 40)
def signal119 : W := (0xd7399d73cf : BitVec 40) ++ (0x3398031c6 : BitVec 40)
def signal120 : W := (0xd7399d73cf : BitVec 40) ++ (0x7198070c6 : BitVec 40)
def signal121 : W := (0xd7399d73cf : BitVec 40) ++ (0x43188430c2 : BitVec 40)
def signal122 : W := (0xd7399d73cf : BitVec 40) ++ (0x87398871c6 : BitVec 40)
def signal123 : W := (0xd7399d73cf : BitVec 40) ++ (0xc3388c31c2 : BitVec 40)
def signal124 : W := (0xd7399d73cf : BitVec 40) ++ (0xc4390c41c4 : BitVec 40)
def signal125 : W := (0xd7399d73cf : BitVec 40) ++ (0xc7188c70c2 : BitVec 40)
def signal126 : W := (0xd7399d73cf : BitVec 40) ++ (0xc7210c7104 : BitVec 40)
def signal127 : W := (0xd7399d73cf : BitVec 40) ++ (0xc7398030c2 : BitVec 40)
def signal128 : W := (0xd7399d73cf : BitVec 40) ++ (0xc7398c71c6 : BitVec 40)
def signal129 : W := (0xd7399d73cf : BitVec 40) ++ (0xe73d8e71c6 : BitVec 40)
def signal130 : W := (0xd7399d73cf : BitVec 40) ++ (0xe7b98e71c6 : BitVec 40)
def signal131 : W := (0xd7399d73cf : BitVec 40) ++ (0xe7bd8c71c6 : BitVec 40)
def signal132 : W := (0xd7399d73cf : BitVec 40) ++ (0xe7bd8e71c6 : BitVec 40)
def signal133 : W := (0xd7399ff7df : BitVec 40) ++ (0x31881befb : BitVec 40)
def signal134 : W := (0xd7399ff7df : BitVec 40) ++ (0xc7398dffff : BitVec 40)
def signal135 : W := (0xd7399ff7df : BitVec 40) ++ (0xc7398e7fff : BitVec 40)
def signal136 : W := (0xfa100fa490 : BitVec 40) ++ (0xf8000f8000 : BitVec 40)
def signal137 : W := (0xfa162fa4b0 : BitVec 40) ++ (0xf8060f8038 : BitVec 40)
def signal138 : W := (0xfa3e200020 : BitVec 40) ++ (0xf83e000000 : BitVec 40)
def signal139 : W := (0xfa3e2fa4b0 : BitVec 40) ++ (0xf83e0f8000 : BitVec 40)
def signal140 : W := (0xfa3e2fa5f8 : BitVec 40) ++ (0x181a0180f8 : BitVec 40)
def signal141 : W := (0xfa3e2fa5f8 : BitVec 40) ++ (0x181a0f81f8 : BitVec 40)
def signal142 : W := (0xfa3e2fa5f8 : BitVec 40) ++ (0x183e0181f8 : BitVec 40)
def signal143 : W := (0xfa3e2fa5f8 : BitVec 40) ++ (0x381e0380f8 : BitVec 40)
def signal144 : W := (0xfa3e2fa5f8 : BitVec 40) ++ (0x581a0580f8 : BitVec 40)
def signal145 : W := (0xfa3e2fa5f8 : BitVec 40) ++ (0xb83e0b81f8 : BitVec 40)
def signal146 : W := (0xfa3e2fa5f8 : BitVec 40) ++ (0xd83a0d81f8 : BitVec 40)
def signal147 : W := (0xfa3e2fa5f8 : BitVec 40) ++ (0xe03c0e01f8 : BitVec 40)
def signal148 : W := (0xfa3e2fa5f8 : BitVec 40) ++ (0xf81a0f80f8 : BitVec 40)
def signal149 : W := (0xfa3e2fa5f8 : BitVec 40) ++ (0xf8240f8138 : BitVec 40)
def signal150 : W := (0xfa3e2fa5f8 : BitVec 40) ++ (0xf83e0180f8 : BitVec 40)
def signal151 : W := (0xfa3e2fa5f8 : BitVec 40) ++ (0xf83e0f81f8 : BitVec 40)
def signal152 : W := (0xfa3e2fa5f8 : BitVec 40) ++ (0xfc3f0fc1fc : BitVec 40)
def signal153 : W := (0xfa3e2fa5f8 : BitVec 40) ++ (0xfcbe0fc1f8 : BitVec 40)
def signal154 : W := (0xfa3e2fa5f8 : BitVec 40) ++ (0xfcbf0f81f8 : BitVec 40)
def signal155 : W := (0xfa3e2fa5f8 : BitVec 40) ++ (0xfcbf0fc1fc : BitVec 40)
def signal156 : W := (0xfa3fbfa5ff : BitVec 40) ++ (0xf83f8f81fe : BitVec 40)
def signal157 : W := (0xfad04fac90 : BitVec 40) ++ (0xf8c00f8e00 : BitVec 40)
def signal158 : W := (0xfafe600820 : BitVec 40) ++ (0xf8fe700000 : BitVec 40)
def signal159 : W := (0xff3fbff7ff : BitVec 40) ++ (0xfc3f0fc1fc : BitVec 40)
def signal160 : W := (0xff3fbff7ff : BitVec 40) ++ (0xff3f8ff1fe : BitVec 40)
def signal161 : W := (0xffd0400800 : BitVec 40) ++ (0xffc0000000 : BitVec 40)
def signal162 : W := (0xffd04fac90 : BitVec 40) ++ (0xffc00f8000 : BitVec 40)
def signal163 : W := (0xffd04ffe90 : BitVec 40) ++ (0x1b4001be00 : BitVec 40)
def signal164 : W := (0xffd04ffe90 : BitVec 40) ++ (0x1b400ffe00 : BitVec 40)
def signal165 : W := (0xffd04ffe90 : BitVec 40) ++ (0x1fc001fe00 : BitVec 40)
def signal166 : W := (0xffd04ffe90 : BitVec 40) ++ (0x3bc003be00 : BitVec 40)
def signal167 : W := (0xffd04ffe90 : BitVec 40) ++ (0x5b4005be00 : BitVec 40)
def signal168 : W := (0xffd04ffe90 : BitVec 40) ++ (0xbfc00bfe00 : BitVec 40)
def signal169 : W := (0xffd04ffe90 : BitVec 40) ++ (0xdf400dfe00 : BitVec 40)
def signal170 : W := (0xffd04ffe90 : BitVec 40) ++ (0xe7800e7e00 : BitVec 40)
def signal171 : W := (0xffd04ffe90 : BitVec 40) ++ (0xfb400fbe00 : BitVec 40)
def signal172 : W := (0xffd04ffe90 : BitVec 40) ++ (0xfc800fce00 : BitVec 40)
def signal173 : W := (0xffd04ffe90 : BitVec 40) ++ (0xffc001be00 : BitVec 40)
def signal174 : W := (0xffd04ffe90 : BitVec 40) ++ (0xffc00ffe00 : BitVec 40)
def signal175 : W := (0xffd04ffe90 : BitVec 40) ++ (0xffe10fff04 : BitVec 40)
def signal176 : W := (0xffd04ffe90 : BitVec 40) ++ (0xffe40fff00 : BitVec 40)
def signal177 : W := (0xffd04ffe90 : BitVec 40) ++ (0xffe50ffe00 : BitVec 40)
def signal178 : W := (0xffd04ffe90 : BitVec 40) ++ (0xffe50fff04 : BitVec 40)
def signal179 : W := (0xffd1dffe97 : BitVec 40) ++ (0xffc18ffe06 : BitVec 40)
def signal180 : W := (0xffd6600820 : BitVec 40) ++ (0xffc6700000 : BitVec 40)
def signal181 : W := (0xfff9dfffdf : BitVec 40) ++ (0xffe10fff04 : BitVec 40)
def signal182 : W := (0xfff9dfffdf : BitVec 40) ++ (0xfff98fffc6 : BitVec 40)
def signal183 : W := (0xfffe600820 : BitVec 40) ++ (0xfffe000000 : BitVec 40)
def signal184 : W := (0xfffe6ffff8 : BitVec 40) ++ (0xfffe0ffff8 : BitVec 40)
def signal185 : W := (0xfffff00820 : BitVec 40) ++ (0x1b5af00000 : BitVec 40)
def signal186 : W := (0xfffff00820 : BitVec 40) ++ (0x1b7ff00000 : BitVec 40)
def signal187 : W := (0xfffff00820 : BitVec 40) ++ (0x1fdbf00000 : BitVec 40)
def signal188 : W := (0xfffff00820 : BitVec 40) ++ (0x3bdef00000 : BitVec 40)
def signal189 : W := (0xfffff00820 : BitVec 40) ++ (0x5b5af00000 : BitVec 40)
def signal190 : W := (0xfffff00820 : BitVec 40) ++ (0xbffff00000 : BitVec 40)
def signal191 : W := (0xfffff00820 : BitVec 40) ++ (0xdf7bf00000 : BitVec 40)
def signal192 : W := (0xfffff00820 : BitVec 40) ++ (0xe7bdf00000 : BitVec 40)
def signal193 : W := (0xfffff00820 : BitVec 40) ++ (0xfb7ef00000 : BitVec 40)
def signal194 : W := (0xfffff00820 : BitVec 40) ++ (0xfcbf700000 : BitVec 40)
def signal195 : W := (0xfffff00820 : BitVec 40) ++ (0xffdaf00000 : BitVec 40)
def signal196 : W := (0xfffff00820 : BitVec 40) ++ (0xffe5700000 : BitVec 40)
def signal197 : W := (0xfffff00820 : BitVec 40) ++ (0xfffff00000 : BitVec 40)
def signal198 : W := (0xfffff00820 : BitVec 40) ++ (0xfffffa4104 : BitVec 40)
def signal199 : W := (0xfffff00820 : BitVec 40) ++ (0xfffffc4104 : BitVec 40)
def signal200 : W := (0xfffff00820 : BitVec 40) ++ (0xfffffe0100 : BitVec 40)
def signal201 : W := (0xfffff00820 : BitVec 40) ++ (0xfffffe4000 : BitVec 40)
def signal202 : W := (0xfffff0096f : BitVec 40) ++ (0xfffff001c6 : BitVec 40)
def signal203 : W := (0xfffff05a27 : BitVec 40) ++ (0xfffff07006 : BitVec 40)
def signal204 : W := (0xfffff528a0 : BitVec 40) ++ (0x1b5af1b0c2 : BitVec 40)
def signal205 : W := (0xfffff528a0 : BitVec 40) ++ (0xfffff1b0c2 : BitVec 40)
def signal206 : W := (0xfffff528a0 : BitVec 40) ++ (0xfffff430c2 : BitVec 40)
def signal207 : W := (0xfffff528a0 : BitVec 40) ++ (0xfffff580c0 : BitVec 40)
def signal208 : W := (0xfffff528a0 : BitVec 40) ++ (0xfffff5b000 : BitVec 40)
def signal209 : W := (0xfffff85b6f : BitVec 40) ++ (0xfffff84104 : BitVec 40)
def signal210 : W := (0xfffffadf7f : BitVec 40) ++ (0xfffffa4f3d : BitVec 40)
def signal211 : W := (0xfffffd29e8 : BitVec 40) ++ (0xfffffc01c0 : BitVec 40)
def signal212 : W := (0xfffffd7aa0 : BitVec 40) ++ (0xfffffc7000 : BitVec 40)
def signal213 : W := (0xfffffd7bef : BitVec 40) ++ (0x1b5af030c2 : BitVec 40)
def signal214 : W := (0xfffffd7bef : BitVec 40) ++ (0xdf7bfc71c6 : BitVec 40)
def signal215 : W := (0xfffffd7bef : BitVec 40) ++ (0xe7bdfc71c6 : BitVec 40)
def signal216 : W := (0xfffffd7bef : BitVec 40) ++ (0xfffff030c2 : BitVec 40)
def signal217 : W := (0xfffffd7bef : BitVec 40) ++ (0xfffffc71c6 : BitVec 40)
def signal218 : W := (0xffffffacb0 : BitVec 40) ++ (0xffffff8000 : BitVec 40)
def signal219 : W := (0xffffffadf8 : BitVec 40) ++ (0xffffff81f8 : BitVec 40)
def signal220 : W := (0xfffffffeb0 : BitVec 40) ++ (0xfffffffe00 : BitVec 40)
def signal221 : W := (0xffffffffff : BitVec 40) ++ (0x318f03efb : BitVec 40)
def signal222 : W := (0xffffffffff : BitVec 40) ++ (0x181a718ef9 : BitVec 40)
def signal223 : W := (0xffffffffff : BitVec 40) ++ (0x1b4071be39 : BitVec 40)
def signal224 : W := (0xffffffffff : BitVec 40) ++ (0x1b5af1befb : BitVec 40)
def signal225 : W := (0xffffffffff : BitVec 40) ++ (0xbffffbffff : BitVec 40)
def signal226 : W := (0xffffffffff : BitVec 40) ++ (0xdf7bfdffff : BitVec 40)
def signal227 : W := (0xffffffffff : BitVec 40) ++ (0xe7bdfe7fff : BitVec 40)
def signal228 : W := (0xffffffffff : BitVec 40) ++ (0xfb7effbffb : BitVec 40)
def signal229 : W := (0xffffffffff : BitVec 40) ++ (0xfcbf7fcffd : BitVec 40)
def signal230 : W := (0xffffffffff : BitVec 40) ++ (0xffdafffefb : BitVec 40)
def signal231 : W := (0xffffffffff : BitVec 40) ++ (0xffe57fff3d : BitVec 40)
def signal232 : W := (0xffffffffff : BitVec 40) ++ (0xfffff1befb : BitVec 40)

def ins : List W := [signal224,signal111,signal128,signal151,signal174,signal197]
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
def layer3 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok3 : everyKey (rowOK 2 layer2) layer3=true := by decide +kernel
theorem closed3 : Closed 3 layer3 := closed_next 2 (by decide) _ _ closed2 ok3
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer4 : BinaryTree (List W) := (.node [signal94,signal102,signal128,signal140,signal174] (.node [signal58,signal102,signal128,signal140,signal174] (.node [signal28,signal102,signal117,signal151,signal197] (.node [signal9,signal102,signal128,signal151,signal163] (.node [signal8,signal102,signal128,signal151,signal163] (.node [signal8,signal102,signal128,signal140,signal174] (.node [signal8,signal102,signal117,signal151,signal174] .nil .nil) .nil) (.node [signal9,signal102,signal128,signal140,signal174] (.node [signal9,signal102,signal117,signal151,signal174] .nil .nil) .nil)) (.node [signal15,signal102,signal128,signal151,signal163] (.node [signal15,signal102,signal128,signal140,signal174] (.node [signal15,signal102,signal117,signal151,signal174] .nil .nil) .nil) (.node [signal23,signal111,signal128,signal151,signal174] .nil .nil))) (.node [signal42,signal102,signal128,signal163,signal197] (.node [signal37,signal111,signal128,signal151,signal224] (.node [signal36,signal111,signal128,signal151,signal197] (.node [signal28,signal102,signal128,signal140,signal197] .nil .nil) .nil) (.node [signal42,signal102,signal117,signal174,signal197] .nil .nil)) (.node [signal52,signal111,signal128,signal197,signal224] (.node [signal51,signal111,signal128,signal174,signal224] (.node [signal50,signal111,signal128,signal174,signal197] .nil .nil) .nil) (.node [signal58,signal102,signal117,signal151,signal174] .nil .nil)))) (.node [signal81,signal128,signal151,signal174,signal197] (.node [signal60,signal111,signal151,signal174,signal213] (.node [signal60,signal102,signal140,signal174,signal197] (.node [signal59,signal102,signal117,signal151,signal174] (.node [signal58,signal102,signal128,signal151,signal163] .nil .nil) .nil) (.node [signal60,signal111,signal133,signal151,signal174] (.node [signal60,signal102,signal151,signal163,signal197] .nil .nil) .nil)) (.node [signal70,signal111,signal151,signal197,signal224] (.node [signal69,signal111,signal151,signal174,signal224] (.node [signal68,signal111,signal151,signal174,signal197] .nil .nil) .nil) (.node [signal72,signal111,signal174,signal197,signal224] .nil .nil))) (.node [signal89,signal151,signal174,signal197,signal224] (.node [signal84,signal128,signal151,signal197,signal224] (.node [signal83,signal102,signal128,signal151,signal174] (.node [signal82,signal128,signal151,signal174,signal224] .nil .nil) .nil) (.node [signal85,signal128,signal174,signal197,signal224] .nil .nil)) (.node [signal93,signal128,signal151,signal197,signal223] (.node [signal92,signal128,signal174,signal197,signal222] (.node [signal90,signal151,signal174,signal197,signal221] .nil .nil) .nil) (.node [signal94,signal102,signal117,signal151,signal174] .nil .nil))))) (.node [signal102,signal128,signal145,signal174,signal197] (.node [signal102,signal119,signal151,signal174,signal197] (.node [signal102,signal117,signal151,signal163,signal197] (.node [signal95,signal102,signal128,signal140,signal174] (.node [signal95,signal102,signal117,signal151,signal174] (.node [signal94,signal102,signal128,signal151,signal163] .nil .nil) .nil) (.node [signal102,signal117,signal140,signal174,signal197] (.node [signal95,signal102,signal128,signal151,signal163] .nil .nil) .nil)) (.node [signal102,signal117,signal151,signal174,signal216] (.node [signal102,signal117,signal151,signal174,signal197] (.node [signal102,signal117,signal151,signal174,signal185] .nil .nil) .nil) (.node [signal102,signal117,signal151,signal174,signal217] .nil .nil))) (.node [signal102,signal128,signal140,signal174,signal185] (.node [signal102,signal128,signal133,signal151,signal174] (.node [signal102,signal122,signal151,signal174,signal197] (.node [signal102,signal120,signal151,signal174,signal197] .nil .nil) .nil) (.node [signal102,signal128,signal140,signal163,signal197] .nil .nil)) (.node [signal102,signal128,signal142,signal174,signal197] (.node [signal102,signal128,signal140,signal174,signal217] (.node [signal102,signal128,signal140,signal174,signal197] .nil .nil) .nil) (.node [signal102,signal128,signal143,signal174,signal197] .nil .nil)))) (.node [signal108,signal128,signal140,signal174,signal197] (.node [signal102,signal128,signal151,signal166,signal197] (.node [signal102,signal128,signal151,signal163,signal217] (.node [signal102,signal128,signal151,signal163,signal197] (.node [signal102,signal128,signal151,signal163,signal185] .nil .nil) .nil) (.node [signal102,signal128,signal151,signal165,signal197] .nil .nil)) (.node [signal102,signal128,signal151,signal174,signal213] (.node [signal102,signal128,signal151,signal174,signal204] (.node [signal102,signal128,signal151,signal168,signal197] .nil .nil) .nil) (.node [signal107,signal117,signal151,signal174,signal197] .nil .nil))) (.node [signal111,signal128,signal136,signal183,signal224] (.node [signal111,signal117,signal140,signal174,signal185] (.node [signal111,signal117,signal140,signal163,signal197] (.node [signal109,signal128,signal151,signal163,signal197] .nil .nil) .nil) (.node [signal111,signal117,signal151,signal163,signal185] .nil .nil)) (.node [signal111,signal128,signal140,signal174,signal213] (.node [signal111,signal128,signal139,signal161,signal224] (.node [signal111,signal128,signal138,signal162,signal224] .nil .nil) .nil) (.node [signal111,signal128,signal151,signal163,signal213] .nil .nil))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok4 : everyKey (rowOK 3 layer3) layer4=true := by decide +kernel
theorem closed4 : Closed 4 layer4 := closed_next 3 (by decide) _ _ closed3 ok4
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer5 : BinaryTree (List W) := (.node [signal95,signal111,signal128,signal151,signal163,signal224] (.node [signal42,signal58,signal111,signal128,signal174,signal224] (.node [signal15,signal102,signal128,signal151,signal174,signal224] (.node [signal9,signal42,signal111,signal128,signal174,signal224] (.node [signal3,signal102,signal128,signal151,signal174,signal197] (.node [signal1,signal60,signal111,signal151,signal174,signal197] (.node [signal0,signal111,signal128,signal140,signal174,signal197] (.node [signal0,signal111,signal117,signal151,signal174,signal197] (.node [signal0,signal75,signal128,signal151,signal174,signal197] .nil .nil) .nil) (.node [signal0,signal111,signal128,signal151,signal163,signal197] .nil .nil)) (.node [signal2,signal102,signal128,signal151,signal174,signal197] (.node [signal2,signal42,signal111,signal128,signal174,signal197] (.node [signal1,signal102,signal128,signal151,signal174,signal197] .nil .nil) .nil) (.node [signal3,signal28,signal111,signal128,signal151,signal197] .nil .nil))) (.node [signal7,signal111,signal128,signal151,signal174,signal224] (.node [signal6,signal60,signal111,signal151,signal174,signal224] (.node [signal5,signal111,signal128,signal151,signal174,signal197] (.node [signal4,signal15,signal111,signal128,signal151,signal174] .nil .nil) .nil) (.node [signal6,signal111,signal128,signal151,signal174,signal224] .nil .nil)) (.node [signal8,signal111,signal128,signal151,signal174,signal224] (.node [signal8,signal102,signal128,signal151,signal174,signal224] .nil .nil) (.node [signal9,signal28,signal111,signal128,signal151,signal224] .nil .nil)))) (.node [signal10,signal111,signal128,signal151,signal174,signal224] (.node [signal9,signal102,signal128,signal151,signal174,signal224] (.node [signal9,signal75,signal128,signal151,signal174,signal224] (.node [signal9,signal74,signal128,signal151,signal174,signal224] (.node [signal9,signal60,signal111,signal151,signal174,signal224] .nil .nil) .nil) (.node [signal9,signal95,signal128,signal151,signal174,signal224] .nil .nil)) (.node [signal9,signal111,signal128,signal151,signal163,signal224] (.node [signal9,signal111,signal128,signal140,signal174,signal224] (.node [signal9,signal111,signal117,signal151,signal174,signal224] .nil .nil) .nil) (.node [signal9,signal111,signal128,signal151,signal174,signal224] .nil .nil))) (.node [signal15,signal28,signal111,signal128,signal151,signal224] (.node [signal13,signal26,signal111,signal128,signal151,signal224] (.node [signal12,signal40,signal111,signal128,signal174,signal224] (.node [signal11,signal58,signal111,signal151,signal174,signal224] .nil .nil) .nil) (.node [signal14,signal111,signal128,signal151,signal174,signal224] .nil .nil)) (.node [signal15,signal60,signal111,signal151,signal174,signal224] (.node [signal15,signal42,signal111,signal128,signal174,signal224] .nil .nil) (.node [signal15,signal75,signal128,signal151,signal174,signal224] .nil .nil))))) (.node [signal28,signal75,signal128,signal151,signal197,signal224] (.node [signal20,signal111,signal128,signal151,signal174,signal224] (.node [signal15,signal111,signal128,signal151,signal174,signal224] (.node [signal15,signal111,signal128,signal151,signal163,signal224] (.node [signal15,signal111,signal128,signal140,signal174,signal224] (.node [signal15,signal111,signal117,signal151,signal174,signal224] .nil .nil) .nil) (.node [signal15,signal111,signal128,signal151,signal174,signal185] .nil .nil)) (.node [signal18,signal111,signal128,signal151,signal174,signal224] (.node [signal17,signal111,signal128,signal151,signal174,signal224] (.node [signal16,signal111,signal128,signal151,signal174,signal224] .nil .nil) .nil) (.node [signal19,signal111,signal128,signal151,signal174,signal224] .nil .nil))) (.node [signal27,signal111,signal128,signal151,signal197,signal224] (.node [signal24,signal55,signal111,signal151,signal197,signal224] (.node [signal22,signal111,signal128,signal151,signal174,signal224] (.node [signal21,signal111,signal128,signal151,signal174,signal224] .nil .nil) .nil) (.node [signal25,signal39,signal111,signal128,signal197,signal224] .nil .nil)) (.node [signal28,signal58,signal111,signal128,signal151,signal224] (.node [signal28,signal42,signal111,signal128,signal197,signal224] .nil .nil) (.node [signal28,signal60,signal111,signal151,signal197,signal224] .nil .nil)))) (.node [signal29,signal78,signal128,signal151,signal197,signal224] (.node [signal28,signal111,signal128,signal151,signal163,signal197] (.node [signal28,signal111,signal117,signal151,signal197,signal224] (.node [signal28,signal102,signal128,signal151,signal197,signal224] (.node [signal28,signal95,signal111,signal128,signal151,signal224] .nil .nil) .nil) (.node [signal28,signal111,signal128,signal140,signal197,signal224] .nil .nil)) (.node [signal28,signal111,signal128,signal151,signal197,signal224] (.node [signal28,signal111,signal128,signal151,signal185,signal224] .nil .nil) (.node [signal28,signal111,signal128,signal151,signal217,signal224] .nil .nil))) (.node [signal34,signal111,signal128,signal151,signal197,signal224] (.node [signal32,signal111,signal128,signal151,signal197,signal224] (.node [signal31,signal111,signal128,signal151,signal197,signal224] (.node [signal30,signal111,signal128,signal151,signal197,signal224] .nil .nil) .nil) (.node [signal33,signal111,signal128,signal151,signal197,signal224] .nil .nil)) (.node [signal38,signal54,signal111,signal174,signal197,signal224] (.node [signal35,signal111,signal128,signal151,signal197,signal224] .nil .nil) (.node [signal41,signal111,signal128,signal174,signal197,signal224] .nil .nil)))))) (.node [signal60,signal111,signal151,signal174,signal185,signal224] (.node [signal56,signal60,signal111,signal151,signal174,signal224] (.node [signal42,signal111,signal128,signal174,signal217,signal224] (.node [signal42,signal111,signal117,signal174,signal197,signal224] (.node [signal42,signal95,signal111,signal128,signal174,signal224] (.node [signal42,signal75,signal128,signal174,signal197,signal224] (.node [signal42,signal60,signal111,signal174,signal197,signal224] .nil .nil) .nil) (.node [signal42,signal102,signal128,signal174,signal197,signal224] .nil .nil)) (.node [signal42,signal111,signal128,signal174,signal185,signal224] (.node [signal42,signal111,signal128,signal163,signal197,signal224] (.node [signal42,signal111,signal128,signal140,signal174,signal197] .nil .nil) .nil) (.node [signal42,signal111,signal128,signal174,signal197,signal224] .nil .nil))) (.node [signal47,signal111,signal128,signal174,signal197,signal224] (.node [signal45,signal111,signal128,signal174,signal197,signal224] (.node [signal44,signal111,signal128,signal174,signal197,signal224] (.node [signal43,signal77,signal128,signal174,signal197,signal224] .nil .nil) .nil) (.node [signal46,signal111,signal128,signal174,signal197,signal224] .nil .nil)) (.node [signal49,signal111,signal128,signal174,signal197,signal224] (.node [signal48,signal111,signal128,signal174,signal197,signal224] .nil .nil) (.node [signal53,signal111,signal128,signal151,signal174,signal224] .nil .nil)))) (.node [signal58,signal111,signal151,signal174,signal217,signal224] (.node [signal58,signal102,signal128,signal151,signal174,signal224] (.node [signal58,signal60,signal111,signal151,signal174,signal224] (.node [signal57,signal111,signal128,signal151,signal174,signal224] (.node [signal56,signal111,signal128,signal151,signal174,signal224] .nil .nil) .nil) (.node [signal58,signal75,signal128,signal151,signal174,signal224] .nil .nil)) (.node [signal58,signal111,signal128,signal151,signal163,signal224] (.node [signal58,signal111,signal128,signal140,signal174,signal224] (.node [signal58,signal111,signal117,signal151,signal174,signal224] .nil .nil) .nil) (.node [signal58,signal111,signal128,signal151,signal174,signal224] .nil .nil))) (.node [signal60,signal102,signal151,signal174,signal197,signal224] (.node [signal60,signal75,signal151,signal174,signal197,signal224] (.node [signal59,signal111,signal128,signal151,signal174,signal224] (.node [signal59,signal111,signal117,signal151,signal174,signal224] .nil .nil) .nil) (.node [signal60,signal95,signal111,signal151,signal174,signal224] .nil .nil)) (.node [signal60,signal111,signal140,signal174,signal197,signal224] (.node [signal60,signal111,signal117,signal151,signal174,signal197] .nil .nil) (.node [signal60,signal111,signal151,signal163,signal197,signal224] .nil .nil))))) (.node [signal75,signal128,signal151,signal174,signal197,signal224] (.node [signal71,signal111,signal128,signal151,signal174,signal224] (.node [signal63,signal111,signal151,signal174,signal197,signal224] (.node [signal61,signal76,signal151,signal174,signal197,signal224] (.node [signal60,signal111,signal151,signal174,signal217,signal224] (.node [signal60,signal111,signal151,signal174,signal197,signal224] .nil .nil) .nil) (.node [signal62,signal111,signal151,signal174,signal197,signal224] .nil .nil)) (.node [signal66,signal111,signal151,signal174,signal197,signal224] (.node [signal65,signal111,signal151,signal174,signal197,signal224] (.node [signal64,signal111,signal151,signal174,signal197,signal224] .nil .nil) .nil) (.node [signal67,signal111,signal151,signal174,signal197,signal224] .nil .nil))) (.node [signal75,signal117,signal151,signal174,signal197,signal224] (.node [signal75,signal100,signal128,signal151,signal174,signal224] (.node [signal75,signal95,signal128,signal151,signal174,signal224] (.node [signal73,signal111,signal128,signal151,signal174,signal224] .nil .nil) .nil) (.node [signal75,signal102,signal128,signal151,signal174,signal197] .nil .nil)) (.node [signal75,signal128,signal151,signal163,signal197,signal224] (.node [signal75,signal128,signal140,signal174,signal197,signal224] .nil .nil) (.node [signal75,signal128,signal151,signal174,signal185,signal224] .nil .nil)))) (.node [signal90,signal151,signal174,signal197,signal224,signal227] (.node [signal83,signal111,signal128,signal151,signal174,signal224] (.node [signal79,signal128,signal151,signal174,signal197,signal224] (.node [signal75,signal128,signal151,signal174,signal217,signal224] (.node [signal75,signal128,signal151,signal174,signal205,signal224] .nil .nil) .nil) (.node [signal80,signal128,signal151,signal174,signal197,signal224] .nil .nil)) (.node [signal87,signal111,signal128,signal151,signal197,signal224] (.node [signal86,signal111,signal128,signal174,signal197,signal224] .nil .nil) (.node [signal88,signal111,signal128,signal151,signal174,signal224] .nil .nil))) (.node [signal94,signal111,signal128,signal151,signal174,signal224] (.node [signal93,signal128,signal151,signal197,signal224,signal231] (.node [signal92,signal128,signal174,signal197,signal224,signal229] (.node [signal91,signal111,signal128,signal151,signal174,signal224] .nil .nil) .nil) (.node [signal94,signal102,signal128,signal151,signal174,signal224] .nil .nil)) (.node [signal95,signal111,signal117,signal151,signal174,signal224] (.node [signal95,signal102,signal128,signal151,signal174,signal224] .nil .nil) (.node [signal95,signal111,signal128,signal140,signal174,signal224] .nil .nil))))))) (.node [signal111,signal128,signal151,signal157,signal197,signal224] (.node [signal111,signal117,signal151,signal174,signal185,signal224] (.node [signal102,signal128,signal151,signal163,signal197] (.node [signal102,signal111,signal128,signal140,signal174,signal197] (.node [signal98,signal111,signal128,signal151,signal174,signal224] (.node [signal96,signal111,signal128,signal151,signal174,signal224] (.node [signal95,signal128,signal151,signal174,signal210,signal224] (.node [signal95,signal111,signal128,signal151,signal174,signal224] .nil .nil) .nil) (.node [signal97,signal111,signal128,signal151,signal174,signal224] .nil .nil)) (.node [signal101,signal111,signal128,signal151,signal174,signal224] (.node [signal100,signal111,signal128,signal151,signal174,signal224] (.node [signal99,signal111,signal128,signal151,signal174,signal224] .nil .nil) .nil) (.node [signal102,signal111,signal117,signal151,signal174,signal197] .nil .nil))) (.node [signal102,signal128,signal140,signal151,signal174,signal197] (.node [signal102,signal117,signal151,signal174,signal197] (.node [signal102,signal117,signal128,signal151,signal174,signal197] (.node [signal102,signal111,signal128,signal151,signal163,signal197] .nil .nil) .nil) (.node [signal102,signal117,signal151,signal174,signal197,signal224] .nil .nil)) (.node [signal102,signal128,signal140,signal174,signal197,signal224] (.node [signal102,signal128,signal140,signal174,signal197] .nil .nil) (.node [signal102,signal128,signal151,signal163,signal174,signal197] .nil .nil)))) (.node [signal107,signal128,signal151,signal174,signal197,signal224] (.node [signal102,signal128,signal151,signal174,signal217,signal224] (.node [signal102,signal128,signal151,signal174,signal197,signal224] (.node [signal102,signal128,signal151,signal174,signal185,signal224] (.node [signal102,signal128,signal151,signal163,signal197,signal224] .nil .nil) .nil) (.node [signal102,signal128,signal151,signal174,signal197,signal225] .nil .nil)) (.node [signal105,signal128,signal151,signal174,signal197,signal224] (.node [signal104,signal128,signal151,signal174,signal197,signal224] (.node [signal103,signal128,signal151,signal174,signal197,signal224] .nil .nil) .nil) (.node [signal106,signal128,signal151,signal174,signal197,signal224] .nil .nil))) (.node [signal111,signal115,signal151,signal182,signal197,signal224] (.node [signal110,signal128,signal151,signal174,signal197,signal224] (.node [signal109,signal128,signal151,signal174,signal197,signal224] (.node [signal108,signal128,signal151,signal174,signal197,signal224] .nil .nil) .nil) (.node [signal111,signal114,signal160,signal174,signal197,signal224] .nil .nil)) (.node [signal111,signal117,signal140,signal174,signal197,signal224] (.node [signal111,signal116,signal151,signal174,signal217,signal224] .nil .nil) (.node [signal111,signal117,signal151,signal163,signal197,signal224] .nil .nil))))) (.node [signal111,signal128,signal137,signal174,signal197,signal224] (.node [signal111,signal123,signal151,signal174,signal197,signal224] (.node [signal111,signal118,signal151,signal174,signal197,signal224] (.node [signal111,signal117,signal151,signal174,signal216,signal224] (.node [signal111,signal117,signal151,signal174,signal197,signal226] (.node [signal111,signal117,signal151,signal174,signal197,signal224] .nil .nil) .nil) (.node [signal111,signal117,signal151,signal174,signal217,signal224] .nil .nil)) (.node [signal111,signal121,signal151,signal174,signal197,signal224] (.node [signal111,signal120,signal151,signal174,signal197,signal224] (.node [signal111,signal119,signal151,signal174,signal197,signal224] .nil .nil) .nil) (.node [signal111,signal122,signal151,signal174,signal197,signal224] .nil .nil))) (.node [signal111,signal128,signal133,signal151,signal174,signal224] (.node [signal111,signal126,signal151,signal174,signal197,signal224] (.node [signal111,signal125,signal151,signal174,signal197,signal224] (.node [signal111,signal124,signal151,signal174,signal197,signal224] .nil .nil) .nil) (.node [signal111,signal127,signal151,signal174,signal197,signal224] .nil .nil)) (.node [signal111,signal128,signal135,signal151,signal174,signal224] (.node [signal111,signal128,signal134,signal151,signal174,signal224] .nil .nil) (.node [signal111,signal128,signal136,signal184,signal197,signal224] .nil .nil)))) (.node [signal111,signal128,signal142,signal174,signal197,signal224] (.node [signal111,signal128,signal140,signal174,signal197,signal224] (.node [signal111,signal128,signal140,signal163,signal197,signal224] (.node [signal111,signal128,signal139,signal174,signal197,signal224] (.node [signal111,signal128,signal138,signal174,signal219,signal224] .nil .nil) .nil) (.node [signal111,signal128,signal140,signal174,signal185,signal224] .nil .nil)) (.node [signal111,signal128,signal140,signal174,signal217,signal224] (.node [signal111,signal128,signal140,signal174,signal197,signal228] .nil .nil) (.node [signal111,signal128,signal141,signal174,signal197,signal224] .nil .nil))) (.node [signal111,signal128,signal147,signal174,signal197,signal224] (.node [signal111,signal128,signal145,signal174,signal197,signal224] (.node [signal111,signal128,signal144,signal174,signal197,signal224] (.node [signal111,signal128,signal143,signal174,signal197,signal224] .nil .nil) .nil) (.node [signal111,signal128,signal146,signal174,signal197,signal224] .nil .nil)) (.node [signal111,signal128,signal149,signal174,signal197,signal224] (.node [signal111,signal128,signal148,signal174,signal197,signal224] .nil .nil) (.node [signal111,signal128,signal150,signal174,signal197,signal224] .nil .nil)))))) (.node [signal111,signal128,signal151,signal174,signal199,signal224] (.node [signal111,signal128,signal151,signal174,signal183,signal224] (.node [signal111,signal128,signal151,signal166,signal197,signal224] (.node [signal111,signal128,signal151,signal163,signal197,signal224] (.node [signal111,signal128,signal151,signal162,signal197,signal224] (.node [signal111,signal128,signal151,signal161,signal220,signal224] (.node [signal111,signal128,signal151,signal158,signal174,signal224] .nil .nil) .nil) (.node [signal111,signal128,signal151,signal163,signal185,signal224] .nil .nil)) (.node [signal111,signal128,signal151,signal164,signal197,signal224] (.node [signal111,signal128,signal151,signal163,signal217,signal224] (.node [signal111,signal128,signal151,signal163,signal197,signal230] .nil .nil) .nil) (.node [signal111,signal128,signal151,signal165,signal197,signal224] .nil .nil))) (.node [signal111,signal128,signal151,signal171,signal197,signal224] (.node [signal111,signal128,signal151,signal169,signal197,signal224] (.node [signal111,signal128,signal151,signal168,signal197,signal224] (.node [signal111,signal128,signal151,signal167,signal197,signal224] .nil .nil) .nil) (.node [signal111,signal128,signal151,signal170,signal197,signal224] .nil .nil)) (.node [signal111,signal128,signal151,signal173,signal197,signal224] (.node [signal111,signal128,signal151,signal172,signal197,signal224] .nil .nil) (.node [signal111,signal128,signal151,signal174,signal180,signal224] .nil .nil)))) (.node [signal111,signal128,signal151,signal174,signal193,signal224] (.node [signal111,signal128,signal151,signal174,signal188,signal224] (.node [signal111,signal128,signal151,signal174,signal186,signal224] (.node [signal111,signal128,signal151,signal174,signal185,signal232] (.node [signal111,signal128,signal151,signal174,signal185,signal224] .nil .nil) .nil) (.node [signal111,signal128,signal151,signal174,signal187,signal224] .nil .nil)) (.node [signal111,signal128,signal151,signal174,signal191,signal224] (.node [signal111,signal128,signal151,signal174,signal190,signal224] (.node [signal111,signal128,signal151,signal174,signal189,signal224] .nil .nil) .nil) (.node [signal111,signal128,signal151,signal174,signal192,signal224] .nil .nil))) (.node [signal111,signal128,signal151,signal174,signal197,signal222] (.node [signal111,signal128,signal151,signal174,signal196,signal224] (.node [signal111,signal128,signal151,signal174,signal195,signal224] (.node [signal111,signal128,signal151,signal174,signal194,signal224] .nil .nil) .nil) (.node [signal111,signal128,signal151,signal174,signal197,signal221] .nil .nil)) (.node [signal111,signal128,signal151,signal174,signal197,signal224] (.node [signal111,signal128,signal151,signal174,signal197,signal223] .nil .nil) (.node [signal111,signal128,signal151,signal174,signal198,signal224] .nil .nil))))) (.node [signal111,signal128,signal151,signal175,signal197,signal224] (.node [signal111,signal128,signal151,signal174,signal209,signal224] (.node [signal111,signal128,signal151,signal174,signal204,signal224] (.node [signal111,signal128,signal151,signal174,signal202,signal224] (.node [signal111,signal128,signal151,signal174,signal201,signal224] (.node [signal111,signal128,signal151,signal174,signal200,signal224] .nil .nil) .nil) (.node [signal111,signal128,signal151,signal174,signal203,signal224] .nil .nil)) (.node [signal111,signal128,signal151,signal174,signal207,signal224] (.node [signal111,signal128,signal151,signal174,signal206,signal224] (.node [signal111,signal128,signal151,signal174,signal205,signal224] .nil .nil) .nil) (.node [signal111,signal128,signal151,signal174,signal208,signal224] .nil .nil))) (.node [signal111,signal128,signal151,signal174,signal215,signal224] (.node [signal111,signal128,signal151,signal174,signal213,signal224] (.node [signal111,signal128,signal151,signal174,signal212,signal224] (.node [signal111,signal128,signal151,signal174,signal211,signal224] .nil .nil) .nil) (.node [signal111,signal128,signal151,signal174,signal214,signal224] .nil .nil)) (.node [signal111,signal128,signal151,signal174,signal217,signal224] (.node [signal111,signal128,signal151,signal174,signal216,signal224] .nil .nil) (.node [signal111,signal128,signal151,signal174,signal218,signal224] .nil .nil)))) (.node [signal111,signal128,signal155,signal174,signal197,signal224] (.node [signal111,signal128,signal151,signal181,signal197,signal224] (.node [signal111,signal128,signal151,signal178,signal197,signal224] (.node [signal111,signal128,signal151,signal177,signal197,signal224] (.node [signal111,signal128,signal151,signal176,signal197,signal224] .nil .nil) .nil) (.node [signal111,signal128,signal151,signal179,signal197,signal224] .nil .nil)) (.node [signal111,signal128,signal153,signal174,signal197,signal224] (.node [signal111,signal128,signal152,signal174,signal197,signal224] .nil .nil) (.node [signal111,signal128,signal154,signal174,signal197,signal224] .nil .nil))) (.node [signal111,signal131,signal151,signal174,signal197,signal224] (.node [signal111,signal129,signal151,signal174,signal197,signal224] (.node [signal111,signal128,signal159,signal174,signal197,signal224] (.node [signal111,signal128,signal156,signal174,signal197,signal224] .nil .nil) .nil) (.node [signal111,signal130,signal151,signal174,signal197,signal224] .nil .nil)) (.node [signal112,signal128,signal151,signal174,signal197,signal224] (.node [signal111,signal132,signal151,signal174,signal197,signal224] .nil .nil) (.node [signal113,signal128,signal151,signal174,signal197,signal224] .nil .nil))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok5 : everyKey (rowOK 4 layer4) layer5=true := by decide +kernel
theorem closed5 : Closed 5 layer5 := closed_next 4 (by decide) _ _ closed4 ok5
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer6 : BinaryTree (List W) := (.node [signal90,signal111,signal128,signal151,signal174,signal197,signal224] (.node [signal38,signal111,signal128,signal151,signal174,signal197,signal224] (.node [signal13,signal111,signal128,signal151,signal174,signal197,signal224] (.node [signal4,signal111,signal128,signal151,signal174,signal197,signal224] (.node [signal2,signal111,signal128,signal151,signal174,signal197,signal224] (.node [signal1,signal111,signal128,signal151,signal174,signal197,signal224] (.node [signal0,signal111,signal128,signal151,signal174,signal197,signal224] .nil .nil) .nil) (.node [signal3,signal111,signal128,signal151,signal174,signal197,signal224] .nil .nil)) (.node [signal11,signal111,signal128,signal151,signal174,signal197,signal224] (.node [signal9,signal111,signal128,signal151,signal174,signal224] (.node [signal9,signal111,signal128,signal151,signal174,signal197,signal224] .nil .nil) .nil) (.node [signal12,signal111,signal128,signal151,signal174,signal197,signal224] .nil .nil))) (.node [signal26,signal111,signal128,signal151,signal174,signal197,signal224] (.node [signal24,signal111,signal128,signal151,signal174,signal197,signal224] (.node [signal15,signal111,signal128,signal151,signal174,signal224] (.node [signal15,signal111,signal128,signal151,signal174,signal197,signal224] .nil .nil) .nil) (.node [signal25,signal111,signal128,signal151,signal174,signal197,signal224] .nil .nil)) (.node [signal28,signal111,signal128,signal151,signal197,signal224] (.node [signal28,signal111,signal128,signal151,signal174,signal197,signal224] .nil .nil) (.node [signal29,signal111,signal128,signal151,signal174,signal197,signal224] .nil .nil)))) (.node [signal60,signal111,signal128,signal151,signal174,signal197,signal224] (.node [signal43,signal111,signal128,signal151,signal174,signal197,signal224] (.node [signal42,signal111,signal128,signal151,signal174,signal197,signal224] (.node [signal40,signal111,signal128,signal151,signal174,signal197,signal224] (.node [signal39,signal111,signal128,signal151,signal174,signal197,signal224] .nil .nil) .nil) (.node [signal42,signal111,signal128,signal174,signal197,signal224] .nil .nil)) (.node [signal58,signal111,signal128,signal151,signal174,signal197,signal224] (.node [signal55,signal111,signal128,signal151,signal174,signal197,signal224] (.node [signal54,signal111,signal128,signal151,signal174,signal197,signal224] .nil .nil) .nil) (.node [signal58,signal111,signal128,signal151,signal174,signal224] .nil .nil))) (.node [signal75,signal128,signal151,signal174,signal197,signal224] (.node [signal74,signal111,signal128,signal151,signal174,signal197,signal224] (.node [signal61,signal111,signal128,signal151,signal174,signal197,signal224] (.node [signal60,signal111,signal151,signal174,signal197,signal224] .nil .nil) .nil) (.node [signal75,signal111,signal128,signal151,signal174,signal197,signal224] .nil .nil)) (.node [signal77,signal111,signal128,signal151,signal174,signal197,signal224] (.node [signal76,signal111,signal128,signal151,signal174,signal197,signal224] .nil .nil) (.node [signal78,signal111,signal128,signal151,signal174,signal197,signal224] .nil .nil))))) (.node [signal111,signal128,signal151,signal163,signal197,signal224] (.node [signal111,signal117,signal128,signal151,signal174,signal197,signal224] (.node [signal102,signal111,signal128,signal151,signal174,signal197,signal224] (.node [signal95,signal111,signal128,signal151,signal174,signal197,signal224] (.node [signal93,signal111,signal128,signal151,signal174,signal197,signal224] (.node [signal92,signal111,signal128,signal151,signal174,signal197,signal224] .nil .nil) .nil) (.node [signal95,signal111,signal128,signal151,signal174,signal224] .nil .nil)) (.node [signal111,signal115,signal128,signal151,signal174,signal197,signal224] (.node [signal111,signal114,signal128,signal151,signal174,signal197,signal224] (.node [signal102,signal128,signal151,signal174,signal197,signal224] .nil .nil) .nil) (.node [signal111,signal116,signal128,signal151,signal174,signal197,signal224] .nil .nil))) (.node [signal111,signal128,signal140,signal174,signal197,signal224] (.node [signal111,signal128,signal138,signal151,signal174,signal197,signal224] (.node [signal111,signal128,signal136,signal151,signal174,signal197,signal224] (.node [signal111,signal117,signal151,signal174,signal197,signal224] .nil .nil) .nil) (.node [signal111,signal128,signal140,signal151,signal174,signal197,signal224] .nil .nil)) (.node [signal111,signal128,signal151,signal161,signal174,signal197,signal224] (.node [signal111,signal128,signal151,signal160,signal174,signal197,signal224] .nil .nil) (.node [signal111,signal128,signal151,signal163,signal174,signal197,signal224] .nil .nil)))) (.node [signal111,signal128,signal151,signal174,signal197,signal224,signal225] (.node [signal111,signal128,signal151,signal174,signal197,signal210,signal224] (.node [signal111,signal128,signal151,signal174,signal185,signal197,signal224] (.node [signal111,signal128,signal151,signal174,signal184,signal197,signal224] (.node [signal111,signal128,signal151,signal174,signal182,signal197,signal224] .nil .nil) .nil) (.node [signal111,signal128,signal151,signal174,signal185,signal224] .nil .nil)) (.node [signal111,signal128,signal151,signal174,signal197,signal219,signal224] (.node [signal111,signal128,signal151,signal174,signal197,signal217,signal224] .nil .nil) (.node [signal111,signal128,signal151,signal174,signal197,signal220,signal224] .nil .nil))) (.node [signal111,signal128,signal151,signal174,signal197,signal224,signal230] (.node [signal111,signal128,signal151,signal174,signal197,signal224,signal228] (.node [signal111,signal128,signal151,signal174,signal197,signal224,signal227] (.node [signal111,signal128,signal151,signal174,signal197,signal224,signal226] .nil .nil) .nil) (.node [signal111,signal128,signal151,signal174,signal197,signal224,signal229] .nil .nil)) (.node [signal111,signal128,signal151,signal174,signal197,signal224,signal232] (.node [signal111,signal128,signal151,signal174,signal197,signal224,signal231] .nil .nil) (.node [signal111,signal128,signal151,signal174,signal217,signal224] .nil .nil))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok6 : everyKey (rowOK 5 layer5) layer6=true := by decide +kernel
theorem closed6 : Closed 6 layer6 := closed_next 5 (by decide) _ _ closed5 ok6
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer7 : BinaryTree (List W) := (.node [signal111,signal128,signal151,signal174,signal197,signal224] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok7 : everyKey (rowOK 6 layer6) layer7=true := by decide +kernel
theorem closed7 : Closed 7 layer7 := closed_next 6 (by decide) _ _ closed6 ok7
def table : ℕ := 2827520128 * 2 ^ 32 + 2826993792
theorem row : ∀j : Fin 80, Nat.testBit table (∑i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i:ℕ) else 0)=goal[j.val] := by decide +kernel
theorem reject : ∀z, z=goal ∨ z = ~~~goal → ¬build basicOps z 7 ins.toFinset := no_build 7 layer7 ins (by decide) (by decide) closed7 (by decide +kernel)
open PEqualNP.CircuitLowerBounds
def monoGates : List Gate := [⟨.or,[3,4]⟩,⟨.or,[2,1]⟩,⟨.and,[6,5]⟩,⟨.and,[7,0]⟩,⟨.or,[2,8]⟩,⟨.and,[1,10]⟩,⟨.and,[4,3]⟩,⟨.or,[11,12]⟩,⟨.and,[13,9]⟩]
theorem upper : ∃(gs : List Gate) (o : ℕ), (∀g∈gs,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2) ∧ gs.length=9 ∧ ∀x : Fin 6 → Bool,Circuit.eval ⟨gs,o⟩ (List.ofFn x)=Nat.testBit table (∑i : Fin 6,if x i then 2^(i:ℕ) else 0) := ⟨monoGates,14,by simp [monoGates],rfl,by decide +kernel⟩
end PEqualNP.Outside.L_meta_15099

open PEqualNP.Outside.L_meta_15099 in
theorem PEqualNP.Outside.L_meta_15099 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (2827520128 * 2 ^ 32 + 2826993792) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (2827520128 * 2 ^ 32 + 2826993792) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
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
