import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_15817

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

abbrev W := BitVec 108
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

theorem evalAnd (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
theorem evalOr (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
theorem evalNot (xs : List Bool) : GateOp.not.eval xs = !(xs.headD false) := rfl

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

def v0 : W := 0x44fe7e7639cff003312990a62ac
def v1 : W := 0xbb1193f9cff33cc8444546158ca
def v2 : W := 0xc3e1e38e0e3c3f07838a3828705
def v3 : W := 0xfc01fc0ff03fc3b006d02d40d50
def v4 : W := 0xfffe000fffc0037ee8003bfb000
def v5 : W := 0xfffffff0000003fddffec000000
def v6 : W := 0xc7fffff80e303c0111288000000
def v7 : W := 0x3fe01f81fe03fcb7855a1568a55
def v8 : W := 0x3fffc000fffc0ceeed016bbd50
def v9 : W := 0x3fe03fff03fc04dd92eed40d50
def v10 : W := 0x1ffffffc0008337fefbfb000
def v11 : W := 0x3c1fe381f1fc3c796b8a03d3705
def v12 : W := 0x3c1e1c7e0e3c3cfa5c74f828705
def v13 : W := 0x47106ff63fccff7842956b5559a
def v14 : W := 0x44ef93f630333fb6ac457dee8ca
def v15 : W := 0x44ee6c09cff33f359bbb86158ca
def v16 : W := 0x78f07077c1cf03cfc7cf7e3dfcf
def v17 : W := 0xbb01818639cff3feeed750a62ac
def v18 : W := 0xb8ff8279c9f033b337f9bde6ffc
def v19 : W := 0x871f9df837f3cf04b2a3a88e5a9
def v20 : W := 0xff01ff8ffe3fffb006d02d40d50
def v21 : W := 0xffff838ffff03f7ee8003bfb000
def v22 : W := 0xbb007e79c60ff37dd929ab5d2ac
def v23 : W := 0xc7fffffe3ffffc03312990a62ac
def v24 : W := 0xfffffff80e303ffddffec000000
def v25 : W := 0xffefed8ff63ccccb756cd6b3a66
def v26 : W := 0x1fe70003ff08117f98404ffc
def v27 : W := 0xff03fc00000002d40d50
def v28 : W := 0x3fe03f00000004dd92ec000000
def v29 : W := 0x639cff002200110a62ac
def v30 : W := 0x44fe7e700000000111288000000
def v31 : W := 0x38101071c1c300c8444546158ca
def v32 : W := 0x9c03002200110a62ac
def v33 : W := 0x830183880e303c0000000000000
def v34 : W := 0xe0e3c3c0200003828705
def v35 : W := 0x3c1e1c70000000f85c74c000000
def v36 : W := 0x9cff33c00000106158ca
def v37 : W := 0x44ee6c00000003359bba8000000
def v38 : W := 0xbb018180000003fcced64000000
def v39 : W := 0xe3ffffc02200138ae7ad
def v40 : W := 0xffffffc02200116b7aee
def v41 : W := 0xfffcff00220013bff2ac
def v42 : W := 0xfffc0000220003bfb000
def v43 : W := 0x1fff00000008117fec000000
def v44 : W := 0xff9fff00220013de6ffc
def v45 : W := 0xffff33c0220013fff8ca
def v46 : W := 0x1e380003c3c01038a0000705
def v47 : W := 0x3c1e0001f1c00078680003d3000
def v48 : W := 0x193f000333c80044544048ca
def v49 : W := 0x44ee000630000336a80039ea000
def v50 : W := 0x7e70000ff001112980042ac
def v51 : W := 0xbb000009c600037cc8002b59000
def v52 : W := 0x1fc00003fc08006d00400d50
def v53 : W := 0x3fe00000fc0004ee80012bb000
def v54 : W := 0xfe027009c03003312990a62ac
def v55 : W := 0xb8018009c03003b006d02d40d50
def v56 : W := 0x10127009c3300000010004088
def v57 : W := 0xfffffffffffffccb756dd6b7aee
def v58 : W := 0x1fff0003ffc81156dc404aee
def v59 : W := 0x1fff000333c8117ffc4048ca
def v60 : W := 0xfe02700000000111288000000
def v61 : W := 0x3e1e3800e3c3c07838a1028705
def v62 : W := 0x3e003800e003c07810a1028205
def v63 : W := 0x3c001c01f003c0b004500540850
def v64 : W := 0x31003f00fc03c484005421508a
def v65 : W := 0x44006c06300cc33002902940510
def v66 : W := 0x3fe02700fc0304ff92992bf2ac
def v67 : W := 0x3fffff0000000cddffec000000
def v68 : W := 0xfffffffff03fc3fddffeed40d50
def v69 : W := 0x3fe03f00fc03c4b712dd2b72ae
def v70 : W := 0x40e06006000c0307838a3828705
def v71 : W := 0x41e1c7031c3c000302180860a8
def v72 : W := 0x8301818806300f0482822808501
def v73 : W := 0xfffffff639cff3ffffffd0a62ac
def v74 : W := 0x44007c0639cff002200110a62ac
def v75 : W := 0x3c1e1c71f1c3c0c87465c6978ea
def v76 : W := 0x3c1e1071f1c300f86c4547d78ca
def v77 : W := 0x3c101c71f1c3c0f8445547558da
def v78 : W := 0x3c1e1c71c1c300f85c75c6158ca
def v79 : W := 0x40e06206080c300301081020204
def v80 : W := 0xc7fffffe3fffff07b3abb8ae7ad
def v81 : W := 0x3ffe1ff0000000fddd7ec000000
def v82 : W := 0x3ffe0001ffc0007ee80013fb000
def v83 : W := 0x44007c06300fc00000000000000
def v84 : W := 0xfcfffe7ff9fff3b337f9bde6ffc
def v85 : W := 0x44fe7c7631cfc003312990a62ac
def v86 : W := 0x44fe000639c00002200010a2000
def v87 : W := 0xfffe7e7fffcff37ff929bbff2ac
def v88 : W := 0x44effff0000003b59ffec000000
def v89 : W := 0x44ee6c06300cc003312890a2224
def v90 : W := 0xbb018189c6300cc844444611842
def v91 : W := 0x8301818e0e3c3f0682823828705
def v92 : W := 0xc7fffffe0e3c3f0793aab828705
def v93 : W := 0x7cfe0007f1c0037ee8003bfb000
def v94 : W := 0x47fe7ff00000004dd92ec000000
def v95 : W := 0x44fffff00000008117fec000000
def v96 : W := 0x44fe7e76300fc00111288000000
def v97 : W := 0x44fe7e70000003359bba8000000
def v98 : W := 0x47fe6ff00000037ddbbec000000
def v99 : W := 0x7c007c07f00fc3b006d02d40d50
def v100 : W := 0x7c007c07f00fc0b004500540850
def v101 : W := 0x7cfe7c70000003fddffec000000
def v102 : W := 0x7cfe0007f9c0007a680013f3000
def v103 : W := 0x7cfe7e70000000f95d7cc000000
def v104 : W := 0xc3e1838e0e303f0680003828000
def v105 : W := 0xbb100009cfc0004840000211000
def v106 : W := 0xffff93fffff33ffeec457fff8ca
def v107 : W := 0x8301e388063c3f05838a2808705
def v108 : W := 0x830183880e303f0482822808501
def v109 : W := 0xfbf1f3ffcfff3fcfc7cf7e3dfcf
def v110 : W := 0x8301838e0e3c3c0200003828705
def v111 : W := 0x83e183880e303f07838a3828705
def v112 : W := 0x83e183880e303c07810a1028205
def v113 : W := 0x8301e3880e3c3c01038a0000705
def v114 : W := 0xb8019009c033008004400400840
def v115 : W := 0xff11fffffffffff846d56f55dda
def v116 : W := 0xbbff83f0000003fddffec000000
def v117 : W := 0xbbfe0009cfc0004ee80012bb000
def v118 : W := 0xbb1193f0000000c844444000000
def v119 : W := 0xfffffff9cff33ffddfffc6158ca
def v120 : W := 0xbb1183f9cff03cc8444546158ca
def v121 : W := 0xbbfe0009cfc0037ee8003bfb000
def v122 : W := 0xc301e38e0e3c3f0002802800500
def v123 : W := 0xc001e00e003c030002802800500
def v124 : W := 0xffe1ff8ffe3fffb787da3d68f55
def v125 : W := 0xbbff93f0000000cddd6ec000000
def v126 : W := 0xc3e0000e0e00030680003828000
def v127 : W := 0xffffe38ffffc3f7feb8a3bfb705
def v128 : W := 0xfc01fc0ff9fff3b226d13de6ffc
def v129 : W := 0xc7fffff00000030593aa8000000
def v130 : W := 0xc3e1e38e0e3c3c0301081020204
def v131 : W := 0xc3e1e3880e303f05838a0000000
def v132 : W := 0xc3e1e38000000305838a0000000
def v133 : W := 0xfffffffe0e3c3fffdffef828705
def v134 : W := 0xc3ffe3f00000034ddbaec000000
def v135 : W := 0xfc01fc00000003b006d00000000
def v136 : W := 0xfc007c0ff00fc33000002940000
def v137 : W := 0xfc00000ff000033000002940000
def v138 : W := 0xfffffc0fffffc3feeed03ffbd50
def v139 : W := 0xfc01fc0ff03fc08004400400840
def v140 : W := 0xfffe0001f1c0037ce80003d3000
def v141 : W := 0xfcfffe7ff03fc3b117f8ad40d50
def v142 : W := 0xfcfffe70000003b117f88000000
def v143 : W := 0xfcfe000ff9c00332200039e2000
def v144 : W := 0xfffe00000000037cc8000000000
def v145 : W := 0xffffffffffc003fffffefbfb000
def v146 : W := 0xfffe000fffc0004a600012b3000
def v147 : W := 0xfffe0009cfc0037cc8000211000
def v148 : W := 0xfffe03f00000037dd92ec000000
def v149 : W := 0xfffe000ffffc3f7ee8003bfb705
def v150 : W := 0xfffffff806300ffddffee808501
def v151 : W := 0xfffffff0003c3ffddffec000705
def v152 : W := 0xfffffff0000000c9556cc000000
def v153 : W := 0xffff93f0000003fccc444000000
def v154 : W := 0xfffe7e700000037dd9288000000
def v155 : W := 0xfffffff6300cc3fddffee940510
def v156 : W := 0xfffffff1f003c3fddffec540850
def v157 : W := 0xfffffff0003fc3fddffec400d50
def v158 : W := 0xfffffff6300fc3fddffec000000
def v159 : W := 0xfffffff9c6300ffddffec611842
def v160 : W := 0xfffffff9c03303fddffec400840
def v161 : W := 0xfffffff9c03003fddffeed40d50
def v162 : W := 0xfffffff9c60003fddffeeb59000
def v163 : W := 0xfffffffff00003fddffee940000
def v164 : W := 0xfffffffe003c03fddffee800500
def v165 : W := 0xfffffff9cfc003fddffec211000
def v166 : W := 0xc7efe38e3e3c3f37ab8a39ea705
def v167 : W := 0xffffe00ffffc037eea803bfb500
def v168 : W := 0xffff818ffff00f7eea823bfb501
def v169 : W := 0xfffe7c0fffcfc37ee8003bfb000
def v170 : W := 0xfffe6c0fffccc37eea903bfb510
def v171 : W := 0xc7e1ef8e3e3cff37839a3968715
def v172 : W := 0xff01fd8ff63fcfb486d22d48d51
def v173 : W := 0xc7e1ff8e3e3fff07838a3828705
def v174 : W := 0xffe1e38ffe3c3f37838a3968705
def v175 : W := 0xc7ffe38e3ffc3f07a38a38aa705
def v176 : W := 0xc7efef8e3e3cff07b3aab8aa725
def v177 : W := 0xc7efef8e0e3c3f379bbab828705
def v178 : W := 0xff11fffffffffcc8444546158ca
def v179 : W := 0xfffe1c70000003fcdc74c000000

def ins6 : List W := [v0, v1, v2, v3, v4, v5]
theorem nd6 : ins6.Nodup := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem rows6 : ∀ j : Fin 108, Nat.testBit (4008372936 * 2 ^ 32 + 4006144704) (∑ i : Fin 6, if (ins6.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
def tree_0 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_0 : everyKey (fun q => !doneTest q) tree_0 = true := by decide +kernel
theorem closed_0 : Closed 0 tree_0 := closed_nil tree_0 ok_tree_0
def tree_1 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_1 : everyKey (rowOK 0 tree_0) tree_1 = true := by decide +kernel
theorem closed_1 : Closed 1 tree_1 := closed_next 0 (by decide) tree_1 tree_0 closed_0 ok_tree_1
def tree_2 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_2 : everyKey (rowOK 1 tree_1) tree_2 = true := by decide +kernel
theorem closed_2 : Closed 2 tree_2 := closed_next 1 (by decide) tree_2 tree_1 closed_1 ok_tree_2
def tree_3 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_3 : everyKey (rowOK 2 tree_2) tree_3 = true := by decide +kernel
theorem closed_3 : Closed 3 tree_3 := closed_next 2 (by decide) tree_3 tree_2 closed_2 ok_tree_3
def tree_4 : BinaryTree (List W) := (.node [v0,v1,v6,v3,v4] (.node [v7,v0,v1,v4,v5] (.node [v8,v0,v1,v2,v5] (.node [v9,v0,v1,v2,v4] (.node [v10,v0,v1,v2,v3] .nil .nil) .nil) (.node [v11,v0,v1,v3,v5] (.node [v12,v0,v1,v3,v4] .nil .nil) .nil)) (.node [v0,v13,v2,v4,v5] (.node [v14,v0,v2,v3,v5] (.node [v15,v0,v2,v3,v4] .nil .nil) .nil) (.node [v0,v16,v3,v4,v5] .nil .nil))) (.node [v17,v1,v2,v3,v4] (.node [v18,v1,v2,v4,v5] (.node [v19,v1,v3,v4,v5] (.node [v0,v1,v20,v21,v5] .nil .nil) .nil) (.node [v22,v1,v2,v3,v5] .nil .nil)) (.node [v1,v23,v20,v4,v5] (.node [v1,v23,v3,v21,v5] (.node [v1,v23,v3,v4,v24] .nil .nil) .nil) (.node [v2,v3,v25,v4,v5] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_4 : everyKey (rowOK 3 tree_3) tree_4 = true := by decide +kernel
theorem closed_4 : Closed 4 tree_4 := closed_next 3 (by decide) tree_4 tree_3 closed_3 ok_tree_4
def tree_5ll : BinaryTree (List W) := (.node [v26,v0,v1,v2,v3,v5] (.node [v27,v28,v0,v1,v2,v4] (.node [v29,v0,v1,v2,v3,v4] (.node [v29,v30,v1,v2,v3,v4] (.node [v29,v31,v0,v1,v3,v4] (.node [v32,v0,v1,v2,v3,v4] .nil .nil) .nil) (.node [v29,v0,v33,v1,v3,v4] .nil .nil)) (.node [v34,v35,v0,v1,v3,v4] (.node [v36,v37,v0,v2,v3,v4] (.node [v29,v38,v1,v2,v3,v4] .nil .nil) .nil) (.node [v39,v0,v1,v2,v3,v4] .nil .nil))) (.node [v40,v0,v1,v2,v3,v4] (.node [v41,v0,v1,v2,v3,v4] (.node [v42,v43,v0,v1,v2,v3] (.node [v44,v0,v1,v2,v3,v4] .nil .nil) .nil) (.node [v45,v0,v1,v2,v3,v4] .nil .nil)) (.node [v46,v47,v0,v1,v3,v5] (.node [v48,v49,v0,v2,v3,v5] (.node [v50,v51,v1,v2,v3,v5] .nil .nil) .nil) (.node [v52,v53,v0,v1,v2,v5] .nil .nil)))) (.node [v28,v31,v0,v1,v3,v4] (.node [v54,v55,v1,v2,v4,v5] (.node [v56,v2,v3,v4,v5,v57] (.node [v58,v0,v1,v2,v3,v5] (.node [v59,v0,v1,v2,v3,v5] .nil .nil) .nil) (.node [v60,v0,v1,v2,v3,v4] .nil .nil)) (.node [v61,v0,v1,v3,v4,v5] (.node [v62,v63,v0,v1,v4,v5] (.node [v64,v65,v0,v2,v4,v5] .nil .nil) .nil) (.node [v66,v0,v1,v2,v4,v5] .nil .nil))) (.node [v67,v0,v1,v2,v3,v4] (.node [v28,v0,v1,v2,v4,v68] (.node [v28,v0,v1,v2,v3,v4] (.node [v28,v0,v33,v1,v3,v4] .nil .nil) .nil) (.node [v69,v0,v1,v2,v4,v5] .nil .nil)) (.node [v31,v30,v0,v1,v3,v4] (.node [v31,v70,v0,v3,v4,v5] (.node [v71,v72,v1,v3,v4,v5] .nil .nil) .nil) (.node [v31,v0,v33,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5ll : everyKey (rowOK 4 tree_4) tree_5ll = true := by decide +kernel
def tree_5lr : BinaryTree (List W) := (.node [v30,v1,v2,v3,v4,v73] (.node [v74,v0,v1,v2,v3,v4] (.node [v75,v0,v1,v3,v4,v5] (.node [v76,v0,v1,v3,v4,v5] (.node [v77,v0,v1,v3,v4,v5] (.node [v31,v0,v1,v3,v4,v68] .nil .nil) .nil) (.node [v78,v0,v1,v3,v4,v5] .nil .nil)) (.node [v79,v1,v80,v3,v4,v5] (.node [v81,v0,v1,v2,v3,v4] (.node [v82,v0,v1,v2,v3,v5] .nil .nil) .nil) (.node [v83,v1,v2,v84,v4,v5] .nil .nil))) (.node [v85,v1,v2,v3,v4,v5] (.node [v86,v1,v2,v3,v87,v5] (.node [v88,v0,v1,v2,v3,v4] (.node [v89,v90,v2,v3,v4,v5] .nil .nil) .nil) (.node [v85,v33,v1,v3,v4,v5] .nil .nil)) (.node [v30,v0,v1,v2,v3,v4] (.node [v30,v0,v33,v1,v3,v4] (.node [v30,v0,v91,v1,v3,v4] .nil .nil) .nil) (.node [v30,v0,v1,v92,v3,v4] .nil .nil)))) (.node [v0,v93,v1,v2,v3,v5] (.node [v0,v94,v1,v2,v3,v4] (.node [v0,v95,v1,v2,v3,v4] (.node [v96,v0,v1,v2,v3,v4] (.node [v97,v0,v1,v2,v3,v4] .nil .nil) .nil) (.node [v0,v98,v1,v2,v3,v4] .nil .nil)) (.node [v0,v99,v1,v2,v4,v5] (.node [v0,v99,v33,v1,v4,v5] (.node [v0,v100,v1,v2,v4,v5] .nil .nil) .nil) (.node [v0,v93,v33,v1,v3,v5] .nil .nil))) (.node [v0,v91,v1,v3,v4,v5] (.node [v0,v101,v1,v2,v3,v4] (.node [v0,v101,v33,v1,v3,v4] (.node [v0,v102,v1,v2,v3,v5] .nil .nil) .nil) (.node [v0,v103,v1,v2,v3,v4] .nil .nil)) (.node [v0,v33,v1,v3,v4,v24] (.node [v0,v33,v1,v3,v4,v5] .nil .nil) (.node [v0,v33,v1,v3,v4,v68] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lr : everyKey (rowOK 4 tree_4) tree_5lr = true := by decide +kernel
def tree_5l : BinaryTree (List W) := .node [v31,v0,v1,v3,v4,v5] tree_5ll tree_5lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5l : everyKey (rowOK 4 tree_4) tree_5l = true := by
  change (_ && everyKey _ tree_5ll && everyKey _ tree_5lr) = true
  rw [ok_tree_5ll, ok_tree_5lr]
  decide +kernel
def tree_5rl : BinaryTree (List W) := (.node [v0,v1,v104,v3,v4,v5] (.node [v0,v105,v2,v3,v106,v5] (.node [v0,v107,v1,v3,v4,v5] (.node [v0,v108,v1,v3,v4,v5] (.node [v0,v33,v109,v3,v4,v5] (.node [v0,v33,v1,v20,v4,v5] .nil .nil) .nil) (.node [v0,v110,v1,v3,v4,v5] .nil .nil)) (.node [v0,v111,v1,v3,v4,v5] (.node [v0,v112,v1,v3,v4,v5] (.node [v0,v113,v1,v3,v4,v5] .nil .nil) .nil) (.node [v0,v114,v2,v115,v4,v5] .nil .nil))) (.node [v0,v1,v116,v2,v3,v4] (.node [v0,v1,v117,v2,v3,v5] (.node [v0,v118,v2,v3,v4,v119] (.node [v0,v120,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v121,v2,v3,v5] .nil .nil)) (.node [v0,v1,v122,v3,v4,v5] (.node [v0,v1,v123,v124,v4,v5] (.node [v0,v1,v125,v2,v3,v4] .nil .nil) .nil) (.node [v0,v1,v126,v3,v127,v5] .nil .nil)))) (.node [v0,v1,v2,v3,v128,v4] (.node [v0,v1,v2,v129,v3,v4] (.node [v0,v1,v130,v3,v4,v5] (.node [v0,v1,v131,v3,v4,v5] (.node [v0,v1,v132,v3,v4,v133] .nil .nil) .nil) (.node [v0,v1,v2,v134,v3,v4] .nil .nil)) (.node [v0,v1,v2,v135,v4,v68] (.node [v0,v1,v2,v136,v4,v5] (.node [v0,v1,v2,v137,v138,v5] .nil .nil) .nil) (.node [v0,v1,v2,v139,v4,v5] .nil .nil))) (.node [v0,v1,v2,v3,v140,v5] (.node [v0,v1,v2,v3,v141,v4] (.node [v0,v1,v2,v3,v142,v4] (.node [v0,v1,v2,v3,v143,v5] .nil .nil) .nil) (.node [v0,v1,v2,v3,v144,v145] .nil .nil)) (.node [v0,v1,v2,v3,v146,v5] (.node [v0,v1,v2,v3,v147,v5] .nil .nil) (.node [v0,v1,v2,v3,v4,v148] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rl : everyKey (rowOK 4 tree_4) tree_5rl = true := by decide +kernel
def tree_5rr : BinaryTree (List W) := (.node [v0,v1,v2,v3,v149,v5] (.node [v0,v1,v2,v3,v4,v150] (.node [v0,v1,v2,v3,v4,v151] (.node [v0,v1,v2,v3,v4,v152] (.node [v0,v1,v2,v3,v4,v153] (.node [v0,v1,v2,v3,v4,v154] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v5] .nil .nil)) (.node [v0,v1,v2,v3,v4,v155] (.node [v0,v1,v2,v3,v4,v156] (.node [v0,v1,v2,v3,v4,v157] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v158] .nil .nil))) (.node [v0,v1,v2,v3,v4,v159] (.node [v0,v1,v2,v3,v4,v160] (.node [v0,v1,v2,v3,v4,v161] (.node [v0,v1,v2,v3,v4,v24] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v162] .nil .nil)) (.node [v0,v1,v2,v3,v4,v163] (.node [v0,v1,v2,v3,v4,v164] (.node [v0,v1,v2,v3,v4,v165] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v68] .nil .nil)))) (.node [v0,v1,v166,v3,v4,v5] (.node [v0,v1,v2,v3,v167,v5] (.node [v0,v1,v2,v3,v168,v5] (.node [v0,v1,v2,v3,v169,v5] (.node [v0,v1,v2,v3,v170,v5] .nil .nil) .nil) (.node [v0,v1,v2,v3,v21,v5] .nil .nil)) (.node [v0,v1,v171,v3,v4,v5] (.node [v0,v1,v2,v20,v4,v5] (.node [v0,v1,v2,v172,v4,v5] .nil .nil) .nil) (.node [v0,v1,v173,v3,v4,v5] .nil .nil))) (.node [v0,v1,v3,v174,v4,v5] (.node [v0,v1,v175,v3,v4,v5] (.node [v0,v1,v176,v3,v4,v5] (.node [v0,v1,v177,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v92,v3,v4,v5] .nil .nil)) (.node [v33,v1,v23,v3,v4,v5] (.node [v0,v2,v3,v178,v4,v5] .nil .nil) (.node [v1,v2,v23,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rr : everyKey (rowOK 4 tree_4) tree_5rr = true := by decide +kernel
def tree_5r : BinaryTree (List W) := .node [v0,v1,v2,v3,v4,v179] tree_5rl tree_5rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5r : everyKey (rowOK 4 tree_4) tree_5r = true := by
  change (_ && everyKey _ tree_5rl && everyKey _ tree_5rr) = true
  rw [ok_tree_5rl, ok_tree_5rr]
  decide +kernel
def tree_5 : BinaryTree (List W) := .node [v0,v33,v1,v3,v21,v5] tree_5l tree_5r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5 : everyKey (rowOK 4 tree_4) tree_5 = true := by
  change (_ && everyKey _ tree_5l && everyKey _ tree_5r) = true
  rw [ok_tree_5l, ok_tree_5r]
  decide +kernel
theorem closed_5 : Closed 5 tree_5 := closed_next 4 (by decide) tree_5 tree_4 closed_4 ok_tree_5
def tree_6l : BinaryTree (List W) := (.node [v28,v0,v1,v2,v3,v4] (.node [v46,v0,v1,v2,v3,v4,v5] (.node [v27,v0,v1,v2,v3,v4,v5] (.node [v36,v0,v1,v2,v3,v4,v5] (.node [v29,v0,v1,v2,v3,v4,v5] (.node [v29,v0,v1,v2,v3,v4] .nil .nil) .nil) (.node [v34,v0,v1,v2,v3,v4,v5] .nil .nil)) (.node [v50,v0,v1,v2,v3,v4,v5] (.node [v42,v0,v1,v2,v3,v4,v5] .nil .nil) (.node [v48,v0,v1,v2,v3,v4,v5] .nil .nil))) (.node [v54,v0,v1,v2,v3,v4,v5] (.node [v43,v0,v1,v2,v3,v4,v5] (.node [v52,v0,v1,v2,v3,v4,v5] .nil .nil) (.node [v56,v0,v1,v2,v3,v4,v5] .nil .nil)) (.node [v62,v0,v1,v2,v3,v4,v5] (.node [v64,v0,v1,v2,v3,v4,v5] .nil .nil) (.node [v53,v0,v1,v2,v3,v4,v5] .nil .nil)))) (.node [v79,v0,v1,v2,v3,v4,v5] (.node [v63,v0,v1,v2,v3,v4,v5] (.node [v31,v0,v1,v2,v3,v4,v5] (.node [v71,v0,v1,v2,v3,v4,v5] (.node [v28,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v31,v0,v1,v3,v4,v5] .nil .nil)) (.node [v35,v0,v1,v2,v3,v4,v5] (.node [v47,v0,v1,v2,v3,v4,v5] .nil .nil) (.node [v70,v0,v1,v2,v3,v4,v5] .nil .nil))) (.node [v37,v0,v1,v2,v3,v4,v5] (.node [v83,v0,v1,v2,v3,v4,v5] (.node [v65,v0,v1,v2,v3,v4,v5] .nil .nil) (.node [v49,v0,v1,v2,v3,v4,v5] .nil .nil)) (.node [v86,v0,v1,v2,v3,v4,v5] (.node [v89,v0,v1,v2,v3,v4,v5] .nil .nil) (.node [v30,v0,v1,v2,v3,v4] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6l : everyKey (rowOK 5 tree_5) tree_6l = true := by decide +kernel
def tree_6r : BinaryTree (List W) := (.node [v0,v1,v2,v135,v3,v4,v5] (.node [v0,v105,v1,v2,v3,v4,v5] (.node [v0,v114,v1,v2,v3,v4,v5] (.node [v0,v33,v1,v3,v4,v5] (.node [v0,v33,v1,v2,v3,v4,v5] (.node [v0,v72,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v55,v1,v2,v3,v4,v5] .nil .nil)) (.node [v0,v38,v1,v2,v3,v4,v5] (.node [v0,v51,v1,v2,v3,v4,v5] .nil .nil) (.node [v0,v90,v1,v2,v3,v4,v5] .nil .nil))) (.node [v0,v1,v132,v2,v3,v4,v5] (.node [v0,v1,v123,v2,v3,v4,v5] (.node [v0,v118,v1,v2,v3,v4,v5] .nil .nil) (.node [v0,v1,v126,v2,v3,v4,v5] .nil .nil)) (.node [v0,v1,v2,v109,v3,v4,v5] (.node [v0,v1,v2,v80,v3,v4,v5] .nil .nil) (.node [v0,v1,v2,v137,v3,v4,v5] .nil .nil)))) (.node [v0,v1,v2,v3,v4,v138,v5] (.node [v0,v1,v2,v3,v144,v4,v5] (.node [v0,v1,v2,v3,v115,v4,v5] (.node [v0,v1,v2,v3,v84,v4,v5] .nil .nil) (.node [v0,v1,v2,v3,v124,v4,v5] .nil .nil)) (.node [v0,v1,v2,v3,v4,v106,v5] (.node [v0,v1,v2,v3,v4,v87,v5] .nil .nil) (.node [v0,v1,v2,v3,v4,v127,v5] .nil .nil))) (.node [v0,v1,v2,v3,v4,v5,v68] (.node [v0,v1,v2,v3,v4,v5,v119] (.node [v0,v1,v2,v3,v4,v5,v73] .nil .nil) (.node [v0,v1,v2,v3,v4,v5,v133] .nil .nil)) (.node [v0,v1,v2,v3,v4,v5,v57] (.node [v0,v1,v2,v3,v4,v5,v145] .nil .nil) (.node [v0,v1,v2,v3,v4,v68] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6r : everyKey (rowOK 5 tree_5) tree_6r = true := by decide +kernel
def tree_6 : BinaryTree (List W) := .node [v30,v0,v1,v2,v3,v4,v5] tree_6l tree_6r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6 : everyKey (rowOK 5 tree_5) tree_6 = true := by
  change (_ && everyKey _ tree_6l && everyKey _ tree_6r) = true
  rw [ok_tree_6l, ok_tree_6r]
  decide +kernel
theorem closed_6 : Closed 6 tree_6 := closed_next 5 (by decide) tree_6 tree_5 closed_5 ok_tree_6
def tree_7 : BinaryTree (List W) := (.node [v0,v1,v2,v3,v4,v5] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_7 : everyKey (rowOK 6 tree_6) tree_7 = true := by decide +kernel
theorem closed_7 : Closed 7 tree_7 := closed_next 6 (by decide) tree_7 tree_6 closed_6 ok_tree_7
theorem lower6 : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z 7 ins6.toFinset := @no_build 7 tree_7 ins6 nd6 (by decide) closed_7 (by decide +kernel)
def gates6 : List Gate := [⟨.or, [0, 3]⟩, ⟨.or, [1, 4]⟩, ⟨.and, [6, 4]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [1, 9]⟩, ⟨.and, [7, 5]⟩, ⟨.or, [3, 11]⟩, ⟨.and, [0, 12]⟩, ⟨.or, [13, 10]⟩]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem upper6 : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 9 ∧ ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit (4008372936 * 2 ^ 32 + 4006144704) (∑ i : Fin 6, if x i then 2^(i : ℕ) else 0) := by
  exact ⟨gates6, 14, by simp [gates6], rfl, by decide +kernel⟩

end PEqualNP.Outside.L_meta_15817

open PEqualNP.Outside.L_meta_15817 in
theorem PEqualNP.Outside.L_meta_15817 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372936 * 2 ^ 32 + 4006144704) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372936 * 2 ^ 32 + 4006144704) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro s h
  obtain ⟨C, basis, size, computes⟩ := h
  obtain ⟨gates, output, mono, bound, correct⟩ :=
    replace (4008372936 * 2 ^ 32 + 4006144704) 9 ins6 nd6 rows6 rfl
      lower6 upper6 C.gates C.output basis computes
  exact ⟨⟨gates, output⟩, mono, bound.trans size, correct⟩
