import PEqualNP.Defs

-- Deleting vertex 3 saves a binary gate. The remaining six-input function
-- requires at least nine binary gates when complements are free.
-- The explicit eleven-gate monotone witness then replaces any input using a NOT.
namespace PEqualNP.Outside.L_meta_10854_aux
namespace CoreSigned

-- The signed live-wire search follows L-meta-8463 and L-meta-1449, Apache-2.0.

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

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
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

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
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

def F (x : Fin 6 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 3) || (x 1 && x 5) || (x 2 && x 3) || (x 2 && x 4)

end CoreSigned

namespace SignedProjection
variable {α β : Type} [DecidableEq α] [DecidableEq β] [Zero β]

def avail (pin : α → β) (S : Finset α) := (S.image pin).erase 0
def lost (pin : α → β) (S : Finset α) := (S.filter fun x => pin x = 0).card

theorem avail_mem (pin : α → β) {S : Finset α} {x : β} :
    x ∈ avail pin S ↔ x ≠ 0 ∧ ∃ a ∈ S, pin a = x := by simp [avail]

theorem avail_mono (pin : α → β) {S T : Finset α} (h : S ⊆ T) : avail pin S ⊆ avail pin T := by
  intro y hy
  obtain ⟨hn,x,hx,rfl⟩ := (avail_mem pin).mp hy
  exact (avail_mem pin).mpr ⟨hn,x,h hx,rfl⟩

theorem avail_cases (pin : α → β) {S : Finset α} {c : α} {x : β} (h : x ∈ avail pin (insert c S)) :
    x = pin c ∨ x ∈ avail pin S := by
  obtain ⟨hn,y,hy,rfl⟩ := (avail_mem pin).mp h
  rcases Finset.mem_insert.mp hy with rfl|hy
  · exact Or.inl rfl
  · exact Or.inr ((avail_mem pin).mpr ⟨hn,y,hy,rfl⟩)

theorem lost_insert (pin : α → β) (c : α) (S : Finset α) :
    lost pin (insert c S) = lost pin S + (if pin c = 0 ∧ c ∉ S then 1 else 0) := by
  by_cases mem : c ∈ S
  · rw [Finset.insert_eq_of_mem mem,ite_eq_right (fun q => q.2 mem),Nat.add_zero]
  · by_cases h : pin c = 0
    · rw [ite_eq_left ⟨h,mem⟩]
      unfold lost
      rw [Finset.filter_insert,ite_eq_left h,Finset.card_insert_of_notMem]
      exact fun q => mem (Finset.mem_filter.mp q).1
    · rw [ite_eq_right (fun q => h q.1),Nat.add_zero]
      unfold lost
      rw [Finset.filter_insert,ite_eq_right h]

theorem projected (pin : α → β) (ops : α → α → Finset α) (ops2 : β → β → Finset β) (goal : α)
    (hgoal : pin goal ≠ 0)
    (maps : ∀ {a b c}, c ∈ ops a b → pin c ∈ ops2 (pin a) (pin b))
    (idA : ∀ {a b c}, c ∈ ops2 a b → a = 0 → c = 0 ∨ c = b)
    (idB : ∀ {a b c}, c ∈ ops2 a b → b = 0 → c = 0 ∨ c = a)
    (idS : ∀ {a b c}, c ∈ ops2 a b → a = b → c = 0 ∨ c = b)
    {k : Nat} {S : Finset α} (h : CoreSigned.live ops goal k S) :
    ∃ j, j + lost pin S ≤ k ∧ ∃ T ⊆ avail pin S, CoreSigned.live ops2 (pin goal) j T := by
  induction k generalizing S with
  | zero =>
    change S = {goal} at h
    subst S
    exact ⟨0,by simp [lost,hgoal],{(pin goal)},by simp [avail,hgoal],rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a,_,b,_,ne,c,op,fresh,U,rfl,tail⟩
    · obtain ⟨j,hj,ws,sub,hws⟩ := ih skip
      exact ⟨j,by omega,ws,sub,hws⟩
    let prev := insert a (insert b U)
    have cnew : c ∉ U := fun h => fresh (by simp [h])
    have repr := maps op
    obtain ⟨j,limit,T,sub,path⟩ := ih tail
    have both (ha : pin a = 0) (hb : pin b = 0) : pin c = 0 := by
      exact (idA repr ha).elim id (fun e => e.trans hb)
    have skipcost : lost pin prev ≤ lost pin (insert c U) + 1 := by
      simp only [prev,lost_insert]
      split_ifs <;> grind
    have liftU : avail pin U ⊆ avail pin prev := avail_mono pin (by intro u hu; simp [prev,hu])
    by_cases useful : pin c ∈ T ∧ pin c ∉ avail pin prev
    · have nz := ((avail_mem pin).mp (sub useful.1)).1
      have df (v : α) (hv : v ∈ prev) : pin c ≠ pin v := by
        intro e
        exact useful.2 ((avail_mem pin).mpr ⟨nz,v,hv,e.symm⟩)
      have da := df a (by simp [prev])
      have db := df b (by simp [prev])
      have ha : pin a ≠ 0 := fun e => (idA repr e).elim nz db
      have hb : pin b ≠ 0 := fun e => (idB repr e).elim nz da
      have distinct : pin a ≠ pin b := fun e => (idS repr e).elim nz db
      have vcost : lost pin prev ≤ lost pin (insert c U) := by
        simp only [prev,lost_insert]
        split_ifs <;> grind
      let V := T.erase (pin c)
      have old (v : β) (hv : v ∈ V) : v ∈ avail pin U :=
        (avail_cases pin (sub (Finset.mem_erase.mp hv).2)).resolve_left (Finset.mem_erase.mp hv).1
      let B := insert (pin a) (insert (pin b) V)
      refine ⟨j+1,by change j+1+lost pin prev ≤ k+1; omega,B,?_,Or.inr ?_⟩
      · intro v hv
        rcases Finset.mem_insert.mp hv with rfl|hv
        · exact (avail_mem pin).mpr ⟨ha,a,by simp,rfl⟩
        rcases Finset.mem_insert.mp hv with rfl|hv
        · exact (avail_mem pin).mpr ⟨hb,b,by simp,rfl⟩
        exact liftU (old _ hv)
      · refine ⟨pin a,by simp [B],pin b,by simp [B],distinct,pin c,?_,?_,V,rfl,?_⟩
        · exact repr
        · simp [B,V,da,db]
        · rwa [show insert (pin c) V = T from Finset.insert_erase useful.1]
    · refine ⟨j,by change j+lost pin prev ≤ k+1; omega,T,?_,path⟩
      intro v hv
      rcases avail_cases pin (sub hv) with rfl|old
      · by_contra miss
        exact useful ⟨hv,miss⟩
      · exact liftU old


end SignedProjection

namespace SignedProjection
variable {n : Nat}

def signedOps (a b : BitVec n) := [a &&& b, a ||| b, a &&& ~~~b, b &&& ~~~a].toFinset

theorem zero_left {a b c : BitVec n} (h : c ∈ signedOps a b) (eq : a = 0) : c = 0 ∨ c = b := by
  subst a
  simpa [signedOps,or_comm] using h

theorem zero_right {a b c : BitVec n} (h : c ∈ signedOps a b) (eq : b = 0) : c = 0 ∨ c = a := by
  subst b
  simpa [signedOps,or_comm] using h

theorem equal_inputs {a b c : BitVec n} (h : c ∈ signedOps a b) (eq : a = b) : c = 0 ∨ c = b := by
  subst a
  simpa [signedOps,or_comm] using h

def signedPin (mask : BitVec n) (base : Fin n) (x : BitVec n) : BitVec n :=
  (if x[base.val] then ~~~x else x) &&& mask

theorem masked_ops (m : BitVec n) {a b c : BitVec n} (h : c ∈ signedOps a b) :
    c &&& m ∈ signedOps (a &&& m) (b &&& m) := by
  simp only [signedOps,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at *
  rcases h with rfl|rfl|rfl|rfl
  · left; ext i h; simp [Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  · right;left; ext i h; simp only [BitVec.getElem_or,BitVec.getElem_and]; cases a[i] <;> cases b[i] <;> simp
  · right;right;left; ext i h
    simp only [BitVec.getElem_and,BitVec.getElem_not]
    cases a[i] <;> cases b[i] <;> cases m[i] <;> decide
  · right;right;right; ext i h
    simp only [BitVec.getElem_and,BitVec.getElem_not]
    cases a[i] <;> cases b[i] <;> cases m[i] <;> decide

def polarity (b : Bool) (x : BitVec n) := if b then ~~~x else x

theorem polarity_ops (i : Fin n) {a b c : BitVec n} (h : c ∈ signedOps a b) :
    polarity (c[i.val]) c ∈ signedOps (polarity (a[i.val]) a) (polarity (b[i.val]) b) := by
  simp only [signedOps,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at *
  rcases h with rfl|rfl|rfl|rfl <;>
    simp only [BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not] <;>
    cases a[i.val] <;> cases b[i.val] <;>
    simp [polarity,BitVec.not_and,BitVec.not_or,BitVec.and_comm,BitVec.or_comm]

theorem signedPin_ops (m : BitVec n) (i : Fin n) {a b c : BitVec n} (h : c ∈ signedOps a b) :
    signedPin m i c ∈ signedOps (signedPin m i a) (signedPin m i b) :=
  masked_ops m (polarity_ops i h)

theorem live_build {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α}
    {k : Nat} {S V : Finset α} (h : CoreSigned.live ops goal k S) (sub : S ⊆ V) :
    CoreSigned.build ops goal k V := by
  induction k generalizing S V with
  | zero => change S = {goal} at h; subst S; exact sub (Finset.mem_singleton_self _)
  | succ k ih =>
    rcases h with skip|⟨a,ha,b,hb,ne,c,opc,_,rest,eq,tail⟩
    · exact Or.inl (ih skip sub)
    · refine Or.inr ⟨a,sub ha,b,sub hb,ne,c,opc,ih tail ?_⟩
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl|hr
      · simp
      · exact Finset.mem_insert_of_mem (sub (eq ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hr)))

end SignedProjection

namespace SignedProjection
variable {α : Type} [DecidableEq α]

def generated (ops : α → α → Finset α) (stock : Finset α) : List (α × α × α) → Finset α → Prop
  | [], result => stock = result
  | (a,b,w) :: rest, result =>
    a ∈ stock ∧ b ∈ stock ∧ a ≠ b ∧ w ∈ ops a b ∧ generated ops (insert w stock) rest result

theorem extend_generated {ops : α → α → Finset α} {goal : α} {stock result : Finset α}
    {recipe : List (α × α × α)} {k : ℕ}
    (h : generated ops stock recipe result) (tail : CoreSigned.build ops goal k result) :
    CoreSigned.build ops goal (k + recipe.length) stock := by
  induction recipe generalizing stock with
  | nil => change stock = result at h; simpa [h] using tail
  | cons step rest ih =>
    obtain ⟨a,b,w⟩ := step
    rcases h with ⟨ha,hb,hn,ho,hrest⟩
    change CoreSigned.build ops goal (k+rest.length+1) stock
    exact Or.inr ⟨a,ha,b,hb,hn,w,ho,ih hrest⟩

theorem pad_build {ops : α → α → Finset α} {goal : α} {S : Finset α} {a b : Nat}
    (le : a ≤ b) (ha : CoreSigned.build ops goal a S) : CoreSigned.build ops goal b S := by
  induction le with
  | refl => exact ha
  | step _ ih => exact Or.inl ih

end SignedProjection

namespace SignedProjection
variable {n : Nat}

theorem exclude_cut (m : BitVec n) (i : Fin n) (goal : BitVec n) (k cap : ℕ)
    (S A U : Finset (BitVec n)) (recipes : List (BitVec n × BitVec n × BitVec n))
    (nonzero : signedPin m i goal ≠ 0)
    (bound : ¬ CoreSigned.build signedOps (signedPin m i goal) cap A)
    (regen : generated signedOps A recipes U) (sub : avail (signedPin m i) S ⊆ U)
    (budget : recipes.length + k ≤ cap + lost (signedPin m i) S) :
    ¬ CoreSigned.live signedOps goal k S := by
  intro h
  obtain ⟨j, hj, T, ht, path⟩ := projected (signedPin m i) signedOps signedOps goal nonzero
    (signedPin_ops m i) zero_left zero_right equal_inputs h
  have localRun := live_build path (ht.trans sub)
  exact bound (pad_build (by omega) (extend_generated regen localRun))

end SignedProjection

namespace SignedProjection
open CoreSigned (live build first_live live_card pairs pick_two live_separates)

abbrev Word := BitVec 64
def signedList (a b : Word) := [a &&& b, a ||| b, a &&& ~~~b, b &&& ~~~a]
theorem ops_swap (a b : Word) : signedOps a b = signedOps b a := by
  ext z
  simp only [signedOps, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto
def keepChoices (a b : Word) (r : List Word) : List (List Word) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List Word} {a b : Word} {needed : Finset Word}
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

theorem singleton_list {goal : Word} {ws : List Word} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def insertW (v : Word) : List Word → List Word
  | [] => [v]
  | x :: xs => if v ≤ x then v :: x :: xs else x :: insertW v xs

def ordered (ws : List Word) := ws.foldr insertW []

theorem insertW_perm (v : Word) (ws : List Word) : (insertW v ws).Perm (v :: ws) := by
  induction ws with
  | nil => exact .refl _
  | cons x xs ih =>
    simp only [insertW]
    split
    · exact .refl _
    · exact (ih.cons x).trans (.swap _ _ _)

theorem ordered_perm (ws : List Word) : (ordered ws).Perm ws := by
  induction ws with
  | nil => exact .refl _
  | cons x xs ih => exact (insertW_perm x (ordered xs)).trans (ih.cons x)

theorem perm_set {u v : List Word} (p : u.Perm v) : u.toFinset = v.toFinset := by
  ext a
  simpa only [List.mem_toFinset] using (p.mem_iff : a ∈ u ↔ a ∈ v)


def children (k : Nat) (ws : List Word) : List (List Word) :=
  (pairs ws).flatMap fun (a,b,r) => (signedList a b).flatMap fun z =>
    if z ∈ ws then [] else
      (keepChoices a b r).filterMap fun kept =>
        if kept.length ≤ k then some (ordered (z :: kept)) else none

theorem zero_prune {goal : Word} (nz : goal ≠ 0) {k : Nat} {S : Finset Word}
    (h : live signedOps goal k S) : ∃ j ≤ k, ∃ T ⊆ S.erase 0, live signedOps goal j T := by
  obtain ⟨j,le,T,sub,path⟩ := projected id signedOps signedOps goal nz (fun q => q)
    zero_left zero_right equal_inputs h
  refine ⟨j,by omega,T,?_,path⟩
  simpa [avail] using sub

theorem step_no (goal : Word) (n : Nat) (ws : List Word) (hn : ws.Nodup)
    (done_ : ws ≠ [goal])
    (children_ : ∀ qs ∈ children n ws, ¬ live signedOps goal n qs.toFinset)
    : ¬ live signedOps goal (n+1) ws.toFinset := by
  intro h
  rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
  · exact done_ (singleton_list hn done)
  obtain ⟨r,hm,hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
  have go {a b : Word} (hp : ws.Perm (a :: b :: r)) (hmem : (a,b,r) ∈ pairs ws)
      (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ signedOps a b) : False := by
    obtain ⟨kept,hkeep,hnk,hfin⟩ := recover_kept hp hn hset
    have hznew : z ∉ kept := by
      intro hu
      apply hout
      rw [hset]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu))
    have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
    have hraw : live signedOps goal n (z :: kept).toFinset := by simpa [hfin] using tail
    have hc := live_card hraw
    rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
    have hzws : z ∉ ws := by simpa using hout
    have hp' := ordered_perm (z :: kept)
    have mem : ordered (z :: kept) ∈ children n ws := by
      apply List.mem_flatMap.mpr
      refine ⟨(a,b,r),hmem,List.mem_flatMap.mpr ⟨z,List.mem_toFinset.mp hop,?_⟩⟩
      simpa only [hzws,ite_false] using
        (List.mem_filterMap.mpr ⟨kept,hkeep,by simp [show kept.length ≤ n by omega]⟩ :
          ordered (z::kept) ∈ ((keepChoices a b r).filterMap fun kept =>
            if kept.length ≤ n then some (ordered (z :: kept)) else none))
    exact children_ _ mem ((perm_set hp').symm ▸ hraw)
  rcases hm with direct|swap
  · exact go hp direct hs hz
  · exact go (hp.trans (.swap _ _ _)) swap (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)
end SignedProjection

namespace SignedProjection
abbrev V64 := BitVec 64

def bitAt (w : V64) (n : Nat) := w.getLsbD n
def mismatch (g : V64) (ws : List V64) (p q : Nat) :=
  (bitAt g p != bitAt g q) && ws.all (fun w => bitAt w p == bitAt w q)

theorem mismatch_sound {g : V64} {ws : List V64} {p q : Nat} (pp : p < 64) (qq : q < 64)
    (cert : mismatch g ws p q = true) (k : ℕ) : ¬ CoreSigned.live signedOps g k ws.toFinset := by
  intro h
  have parts := Bool.and_eq_true_iff.mp cert
  let D : V64 → Prop := fun w => bitAt w p ≠ bitAt w q
  have dg : D g := by simpa [D] using parts.1
  have hop (a b : V64) (z : V64) (hz : z ∈ signedOps a b) (dz : D z) : D a ∨ D b := by
    by_contra! fail
    apply dz
    obtain ⟨ea,eb⟩ := fail
    simp only [D, not_not] at ea eb
    change bitAt a p = bitAt a q at ea
    change bitAt b p = bitAt b q at eb
    simp only [signedOps, List.mem_toFinset,List.mem_cons, List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl <;>
      simpa only [bitAt, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not,
        pp,qq,decide_true, Bool.true_and, show a.getLsbD p = a.getLsbD q from ea,
        show b.getLsbD p = b.getLsbD q from eb]
  obtain ⟨x,hx,dx⟩ := CoreSigned.live_separates D dg hop h
  exact dx (beq_iff_eq.mp (List.all_eq_true.mp parts.2 x (List.mem_toFinset.mp hx)))

end SignedProjection

namespace SignedProjection
abbrev View := Word × Fin 64 × Word × List Word × Nat × (Nat → Nat)
abbrev Node := Nat × Nat × List Word × (Nat → Nat)
def vm (v : View) := v.1
def va (v : View) := v.2.1
def vg (v : View) := v.2.2.1
def vs (v : View) := v.2.2.2.1
def vk (v : View) := v.2.2.2.2.1
def vh (v : View) := v.2.2.2.2.2
def nv (a : Node) := a.1
def nk (a : Node) := a.2.1
def ns (a : Node) := a.2.2.1
def nh (a : Node) := a.2.2.2

def recipeRun : Nat → Nat → List Word → Option (List (Word × Word × Word) × List Word)
  | 0, code, ws => if code = 1 then some ([],ws) else none
  | fuel+1, code, ws => if code = 1 then some ([],ws) else
    let i := code % 16
    let j := (code / 16) % 16
    let o := (code / 256) % 4
    match ws[i]?, ws[j]? with
    | some a, some b => if a = b then none else
      let w := (signedList a b).getD o 0
      match recipeRun fuel (code / 1024) (ws++[w]) with
      | some (rs,ws') => some ((a,b,w)::rs,ws')
      | none => none
    | _,_ => none

theorem recipeRun_sound (fuel code : Nat) (ws : List Word) {rs out}
    (h : recipeRun fuel code ws = some (rs,out)) :
    generated signedOps ws.toFinset rs out.toFinset := by
  induction fuel generalizing code ws rs out with
  | zero =>
    simp only [recipeRun] at h
    split at h
    · cases h; rfl
    · contradiction
  | succ k ih =>
    simp only [recipeRun] at h
    split at h
    · cases h; rfl
    split at h <;> try contradiction
    rename_i a b ha hb
    split at h <;> try contradiction
    rename_i ne
    split at h <;> try contradiction
    rename_i tail end_ ht
    cases h
    set r := (code / 256) % 4
    let w := (signedList a b).getD r 0
    change a ∈ ws.toFinset ∧ b ∈ ws.toFinset ∧ a ≠ b ∧ w ∈ signedOps a b ∧ _
    refine ⟨List.mem_toFinset.mpr (List.mem_of_getElem? ha),
      List.mem_toFinset.mpr (List.mem_of_getElem? hb),ne,?_,?_⟩
    · have hr : r < 4 := Nat.mod_lt _ (by decide)
      change w ∈ (signedList a b).toFinset
      simp only [List.mem_toFinset]
      have hr' : r < (signedList a b).length := by simpa [signedList] using hr
      simpa [w, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr'] using
        (List.getElem_mem (l := signedList a b) (i := r) hr')
    · have eq : (ws++[w]).toFinset = insert w ws.toFinset := by
        ext x
        simp [or_comm]
      rw [← eq]
      exact ih _ _ ht

def ViewOK (v : View) := ¬ CoreSigned.build signedOps (vg v) (vk v) (vs v).toFinset

def cutOK (v : View) (g : Word) (k : Nat) (ws : List Word) (recipe : Nat) : Bool :=
  let p := signedPin (vm v) (va v)
  if p g != vg v || p g == 0 then false else
    match recipeRun 12 recipe (vs v) with
    | none => false
    | some (rs,out) =>
      decide (avail p ws.toFinset ⊆ out.toFinset) &&
      decide (rs.length+k ≤ vk v + lost p ws.toFinset)

theorem cutOK_sound {v : View} {g : Word} {k : Nat} {ws : List Word} {recipe : Nat}
    (hv : ViewOK v) (hc : cutOK v g k ws recipe = true) :
    ¬ CoreSigned.live signedOps g k ws.toFinset := by
  simp only [cutOK] at hc
  split at hc <;> try contradiction
  rename_i ok
  split at hc <;> try contradiction
  rename_i rs out hr
  have parts := Bool.and_eq_true_iff.mp hc
  have good : signedPin (vm v) (va v) g = vg v ∧ signedPin (vm v) (va v) g ≠ 0 := by
    simpa using ok
  apply exclude_cut (vm v) (va v) g k (vk v) ws.toFinset (vs v).toFinset out.toFinset rs good.2
    (good.1 ▸ hv) (recipeRun_sound _ _ _ hr) (of_decide_eq_true parts.1)
    (of_decide_eq_true parts.2)

end SignedProjection
namespace SignedProjection

def quickCut (v : View) (g : Word) (k : Nat) (ws : List Word) (receipt : Nat) : Bool :=
  let p := signedPin (vm v) (va v)
  if p g != vg v || p g == 0 then false else
    match recipeRun 12 receipt (vs v) with
    | none => false
    | some (rs,out) =>
      decide ws.Nodup &&
      ws.all (fun w => p w == 0 || out.contains (p w)) &&
      decide (rs.length+k ≤ vk v + ws.countP (fun w => p w = 0))

theorem quickCut_sound {v : View} {g : Word} {k : Nat} {ws : List Word} {receipt : Nat}
    (hv : ViewOK v) (ok : quickCut v g k ws receipt = true) :
    ¬ CoreSigned.live signedOps g k ws.toFinset := by
  simp only [quickCut] at ok
  split at ok <;> try contradiction
  rename_i good
  split at ok <;> try contradiction
  rename_i rs out hr
  have parts := Bool.and_eq_true_iff.mp ok
  have pp := Bool.and_eq_true_iff.mp parts.1
  have nd := of_decide_eq_true pp.1
  have gg : signedPin (vm v) (va v) g = vg v ∧ signedPin (vm v) (va v) g ≠ 0 := by
    simpa using good
  apply exclude_cut (vm v) (va v) g k (vk v) ws.toFinset (vs v).toFinset out.toFinset rs gg.2
    (gg.1 ▸ hv) (recipeRun_sound _ _ _ hr)
  · intro x hx
    obtain ⟨ne,w,hw,rfl⟩ := (avail_mem _).mp hx
    have has := List.all_eq_true.mp pp.2 w (List.mem_toFinset.mp hw)
    simp only [Bool.or_eq_true,beq_iff_eq,List.contains_iff_mem] at has
    exact List.mem_toFinset.mpr (has.resolve_left ne)
  · unfold lost
    rw [List.Nodup.card_eq_countP nd]
    exact of_decide_eq_true parts.2

end SignedProjection

namespace SignedProjection.QFast
abbrev Table (α : Type) := Nat × (Nat → Option α)
def get {α : Type} (t : Table α) (i : Nat) : Option α := if i < t.1 then t.2 i else none

def checkHint (views : Table View) (nodes : Table Node) (vID : Nat) (g : Word)
    (k : Nat) (ws : List Word) (hint : Nat) : Bool :=
  let val := hint/4
  match hint % 4 with
  | 0 => mismatch g ws (val % 64) ((val/64)%64)
  | 1 => match (get nodes val) with
    | some a => (nv a == vID) && (nk a == k) && (ns a == ws)
    | none => false
  | 2 =>
    let j := val % 1024
    if j < vID then
      match (get views j) with
      | some v => quickCut v g k ws (val/1024)
      | none => false
    else false
  | _ => (k == 0 && ws.toFinset != {g}) || decide (k+1 < ws.toFinset.card)

theorem checkHint_sound {views : Table View} {nodes : Table Node} {vID : Nat} {g : Word}
    {k : Nat} {ws : List Word} {h : Nat}
    (known : ∀ i < vID, ∀ v, (get views i) = some v → ViewOK v)
    (closed : ∀ (i : Nat) (a : Node), (get nodes i) = some a → nv a = vID → nk a = k →
      ¬ CoreSigned.live signedOps g k (ns a).toFinset)
    (ok : checkHint views nodes vID g k ws h = true) : ¬ CoreSigned.live signedOps g k ws.toFinset := by
  simp only [checkHint] at ok
  split at ok
  · exact mismatch_sound (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) ok k
  · split at ok <;> try contradiction
    rename_i a ha
    simp only [Bool.and_eq_true,beq_iff_eq] at ok
    exact ok.2 ▸ closed _ a ha ok.1.1 ok.1.2
  · split at ok <;> try contradiction
    rename_i lt
    split at ok <;> try contradiction
    rename_i v hv
    exact quickCut_sound (known _ lt _ hv) ok
  · simp only [Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,bne_iff_ne,decide_eq_true_eq] at ok
    intro h
    rcases ok with ⟨rfl,ne⟩|wide
    · exact ne h
    · exact (Nat.not_lt_of_ge (CoreSigned.live_card h)) wide

def scanFrom {α : Type} (f : Nat → α → Bool) : Nat → List α → Bool
  | _, [] => true
  | i, x::xs => f i x && scanFrom f (i+1) xs

theorem scanFrom_sound {α : Type} (f : Nat → α → Bool) {i : Nat} {xs : List α}
    (ok : scanFrom f i xs = true) {x : α} (hx : x ∈ xs) : ∃ j, f j x = true := by
  induction xs generalizing i with
  | nil => simp at hx
  | cons a xs ih =>
    have parts := Bool.and_eq_true_iff.mp ok
    rcases List.mem_cons.mp hx with rfl|hm
    · exact ⟨_,parts.1⟩
    · exact ih parts.2 hm

def evalNode (views : Table View) (nodes : Table Node) (a : Node) : Bool :=
  match (get views (nv a)) with
  | none => false
  | some v => decide (ns a).Nodup && (ns a != [vg v]) &&
    match nk a with
    | 0 => true
    | k+1 => scanFrom (fun i ws => checkHint views nodes (nv a) (vg v) k ws (nh a i)) 0
               (children k (ns a))

def evalRoot (views : Table View) (nodes : Table Node) (i : Nat) (v : View) : Bool :=
  scanFrom (fun q ws => checkHint views nodes i (vg v) (vk v) ws (vh v q)) 0 (vs v).sublists

theorem view_from_earlier (views : Table View) (nodes : Table Node) (vID : Nat) (v : View)
    (hv : (get views vID) = some v)
    (earlier : ∀ i < vID, ∀ w, (get views i) = some w → ViewOK w)
    (hroots : evalRoot views nodes vID v = true)
    (hnodes : ∀ (i : Nat) (a : Node), (get nodes i) = some a → evalNode views nodes a = true) :
    ViewOK v := by
  have closed (k : Nat) : ∀ (i : Nat) (a : Node), (get nodes i) = some a → nv a = vID → nk a = k →
      ¬ CoreSigned.live signedOps (vg v) k (ns a).toFinset := by
    induction k with
    | zero =>
      intro i a found owner fuel h
      have ok := hnodes i a found
      simp only [evalNode,owner,hv,fuel,Bool.and_true,Bool.and_eq_true,decide_eq_true_eq,bne_iff_ne] at ok
      exact ok.2 (singleton_list ok.1 h)
    | succ k ih =>
      intro i a found owner fuel
      have ok := hnodes i a found
      simp only [evalNode,owner,hv,fuel,Bool.and_eq_true,decide_eq_true_eq,bne_iff_ne] at ok
      apply step_no _ _ _ ok.1.1 ok.1.2
      intro ws hm
      obtain ⟨j,good⟩ := scanFrom_sound _ ok.2 hm
      exact checkHint_sound earlier ih good
  intro build_
  classical
  obtain ⟨S, sub, path⟩ := CoreSigned.compress build_
  let ws := (vs v).filter (· ∈ S)
  have eq : ws.toFinset = S := by
    ext w
    simp only [ws,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (sub hw)
  obtain ⟨q,hq⟩ := scanFrom_sound _ hroots (show ws ∈ (vs v).sublists from
    List.mem_sublists.mpr (List.filter_sublist ..))
  exact checkHint_sound earlier (closed _) hq (eq.symm ▸ path)

theorem whole_sound (views : Table View) (nodes : Table Node)
    (allRoots : ∀ (i : Nat) (v : View), (get views i) = some v → evalRoot views nodes i v = true)
    (allNodes : ∀ (i : Nat) (a : Node), (get nodes i) = some a → evalNode views nodes a = true)
    (i : Nat) (v : View) (hv : (get views i) = some v) : ViewOK v := by
  induction i using Nat.strong_induction_on generalizing v with
  | ind i ih => exact view_from_earlier views nodes i v hv ih (allRoots i v hv) allNodes

def checkRootAt (views : Table View) (nodes : Table Node) (i : Nat) : Bool :=
  match (get views i) with
  | some v => evalRoot views nodes i v
  | none => true

def checkNodeAt (views : Table View) (nodes : Table Node) (i : Nat) : Bool :=
  match (get nodes i) with
  | some a => evalNode views nodes a
  | none => true

def passBlock (check : Nat → Bool) (start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => passBlock check start n && check (start+n)

theorem block_at (check : Nat → Bool) {s n i} (ok : passBlock check s n = true)
    (lo : s ≤ i) (hi : i < s+n) : check i = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    have parts := Bool.and_eq_true_iff.mp ok
    by_cases lt : i < s+n
    · exact ih parts.1 lt
    · have eq : i = s+n := by omega
      exact eq ▸ parts.2

theorem merge_blocks {c : Nat → Bool} {s a b : Nat} (x : passBlock c s a = true)
    (y : passBlock c (s+a) b = true) : passBlock c s (a+b) = true := by
  induction b with
  | zero => simpa using x
  | succ b ih =>
    have parts := Bool.and_eq_true_iff.mp y
    change passBlock c s (a+b) && c (s+(a+b)) = true
    exact Bool.and_eq_true_iff.mpr ⟨ih parts.1,by simpa [Nat.add_assoc] using parts.2⟩

theorem certified_view (views : Table View) (nodes : Table Node)
    (roots : passBlock (checkRootAt views nodes) 0 views.1 = true)
    (states : passBlock (checkNodeAt views nodes) 0 nodes.1 = true)
    {i : Nat} {v : View} (hv : (get views i) = some v) : ViewOK v := by
  apply whole_sound views nodes _ _ i v hv
  · intro j w hw
    have hj : j < views.1 := by by_contra! lo; simp [get, Nat.not_lt_of_ge lo] at hw
    have ok := block_at _ roots (i := j) (Nat.zero_le _) (by omega)
    simpa [checkRootAt,hw] using ok
  · intro j a ha
    have hj : j < nodes.1 := by by_contra! lo; simp [get, Nat.not_lt_of_ge lo] at ha
    have ok := block_at _ states (i := j) (Nat.zero_le _) (by omega)
    simpa [checkNodeAt,ha] using ok

end SignedProjection.QFast


namespace SevenUpper
open PEqualNP.CircuitLowerBounds

def witness : List Gate :=
  [⟨.or, [0, 6]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [7, 8]⟩, ⟨.and, [1, 4]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [11, 14]⟩, ⟨.or, [15, 16]⟩]

theorem fits : ∀ g ∈ witness, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  simp [witness]

theorem size : witness.length = 11 := rfl

set_option maxRecDepth 100000 in
theorem correct : ∀ x : Fin 7 → Bool, Circuit.eval ⟨witness, 17⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide +kernel
end SevenUpper

namespace Direct64
open PEqualNP.CircuitLowerBounds SignedProjection
abbrev W := BitVec 64
abbrev basicOps (a b : W) := signedOps a b
abbrev goal : W := ~~~0xfffefffcfefeee00
open CoreSigned (build)
def tableA (x : Fin 6 → Bool) :=
  Nat.testBit 0xfffefffcfefeee00 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

set_option maxRecDepth 100000 in
theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

set_option maxRecDepth 100000 in
theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

set_option maxRecDepth 100000 in
theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 100000 in
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
  · exact add _ (by simp [basicOps,SignedProjection.signedOps] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,SignedProjection.signedOps] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,SignedProjection.signedOps] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,SignedProjection.signedOps] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

set_option maxRecDepth 100000 in
theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 64) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 64) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#64)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

set_option maxRecDepth 100000 in
theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 100000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
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

set_option maxRecDepth 100000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
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


def cols : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

theorem sample64 : ∀ k : Fin 64, tableA (fun i => (cols.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
  decide +kernel

theorem zero_open (k : ℕ) {t : W} (av : Finset W) (hz : ∀ u ∈ av, u.getLsbD 0 = false)
    (h : build basicOps t k av) : t.getLsbD 0 = false := by
  induction k generalizing av with
  | zero => exact hz t h
  | succ k ih =>
    rcases h with skip | ⟨a,ha,b,hb,_,z,hop,tail⟩
    · exact ih av hz skip
    · apply ih (insert z av) _ tail
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl|hu
      · simp only [basicOps,signedOps,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hop
        rcases hop with rfl|rfl|rfl|rfl <;> simp only [BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,hz a ha,hz b hb,Bool.false_and,Bool.or_self]
      · exact hz u hu

theorem low (reject : ¬ build basicOps (0xfffefffcfefeee00 : W) 8 cols.toFinset)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = tableA x) : 8 < binaryCost gs := by
  by_contra! low
  have width : cols.length = 6 := rfl
  have init : ∀ u ∈ cols, holds cols.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 64) :
      (gs.foldl step (cols.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (cols.getD i.val 0)
    have same : List.ofFn x = cols.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < cols.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (cols.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample64 k
  obtain ⟨t, ht, run⟩ := compile gs o hg cols cols.toFinset init evaluate

  have h0 : ∀ u ∈ cols.toFinset, u.getLsbD 0 = false := by
    intro u hu
    simp only [cols,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  rcases ht with rfl|rfl
  · have odd : goal.getLsbD 0 ≠ false := by decide +kernel
    exact odd (zero_open _ _ h0 run)
  · apply reject
    apply pad_build low
    exact run
end Direct64


-- Variable restriction and wire relabelling use the argument of L-meta-10660.
-- The restriction below also counts the gates whose operation is NOT.

namespace SevenSearch
namespace Elim
open PEqualNP.CircuitLowerBounds
def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

def Const {Y : Type} (f : Y → Bool) : Prop := ∃ c, ∀ y, f y = c

def Drop {Y : Type} (n : ℕ) (F : ℕ → Y → Bool) (j : ℕ) : Prop :=
  Const (F (n + j)) ∨ ∃ w < n + j, ∀ y, F (n + j) y = F w y

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)


def rds (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not => g.inputs.take 1
  | _ => g.inputs

theorem eval_congr (g : Gate) (u v : ℕ → Bool)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (huv : ∀ i ∈ rds g, u i = v i) : g.op.eval (g.inputs.map u) = g.op.eval (g.inputs.map v) := by
  rcases hop with h | h | h
  · simp only [rds, h] at huv
    rw [List.map_congr_left huv]
  · simp only [rds, h] at huv
    rw [List.map_congr_left huv]
  · simp only [rds, h] at huv
    rw [h]
    cases hi : g.inputs with
    | nil => rfl
    | cons a t =>
      have := huv a (by simp [hi])
      simp [GateOp.eval, this]

theorem getD_sn (l : List Bool) (b : Bool) (t : ℕ) :
    (l ++ [b]).getD t false = if t = l.length then b else l.getD t false := by
  rcases lt_trichotomy t l.length with h | h | h
  · rw [if_neg (by omega)]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]


end Elim
end SevenSearch

namespace SevenTrack
open PEqualNP.CircuitLowerBounds SevenSearch.Elim

def ntag (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false

def tagged (gs : List Gate) (i : ℕ) : Bool := (gs[i]?.map ntag).getD false

theorem restrictTagged (n m : ℕ) (gs : List Gate) (F : ℕ → (Fin m → Bool) → Bool)
    (hops : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hin : ∀ i < n, Const (F i) ∨ ∃ k < m, ∀ y, F i y = (List.ofFn y).getD k false)
    (hF : ∀ (j : ℕ) (hj : j < gs.length) (y : Fin m → Bool), F (n + j) y =
      gs[j].op.eval (gs[j].inputs.map fun i => if i < n + j then F i y else false)) :
    ∀ K ≤ gs.length, ∃ (ds : List Gate) (S : Finset ℕ),
      (∀ g ∈ ds, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) ∧
      (∀ (j : ℕ) (hj : j < ds.length), ∀ i ∈ ds[j].inputs, i < m + j) ∧
      (∀ j ∈ S, j < K ∧ ¬ Drop n F j) ∧ ds.length ≤ S.card ∧
      (ds.filter ntag).length = (S.filter (tagged gs ·)).card ∧
      ∀ w < n + K, Const (F w) ∨
        ∃ k < m + ds.length, ∀ y, F w y = (run ds (List.ofFn y)).getD k false := by
  intro K
  induction K with
  | zero =>
    intro _
    refine ⟨[], ∅, by simp, by simp, by simp, by simp, by simp, fun w hw => ?_⟩
    simpa [run] using hin w (by omega)
  | succ K ih =>
    intro hK
    obtain ⟨ds, S, h1, hb, h2, h3, htag, h4⟩ := ih (by omega)
    have h2' : ∀ j ∈ S, j < K + 1 ∧ ¬ Drop n F j := fun j hj =>
      ⟨by have := (h2 j hj).1; omega, (h2 j hj).2⟩
    by_cases hd : Drop n F K
    · refine ⟨ds, S, h1, hb, h2', h3, htag, fun w hw => ?_⟩
      rcases Nat.lt_or_ge w (n + K) with h | h
      · exact h4 w h
      · rw [show w = n + K by omega]
        rcases hd with hc | ⟨u, hu, he⟩
        · exact Or.inl hc
        · rcases h4 u hu with ⟨c, hc⟩ | ⟨k, hk, hk'⟩
          · exact Or.inl ⟨c, fun y => (he y).trans (hc y)⟩
          · exact Or.inr ⟨k, hk, fun y => (he y).trans (hk' y)⟩
    · have hnc : ¬ Const (F (n + K)) := fun h => hd (Or.inl h)
      have hne : ∀ u < n + K, ¬ ∀ y, F (n + K) y = F u y := fun u hu h => hd (Or.inr ⟨u, hu, h⟩)
      have addg : ∀ g : Gate, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) →
          ntag g = tagged gs K → g.inputs.length ≤ 2 → (∀ i ∈ g.inputs, i < m + ds.length) →
          (∀ y, F (n + K) y = g.op.eval (g.inputs.map fun i =>
            (run ds (List.ofFn y)).getD i false)) →
          ∃ (ds : List Gate) (S : Finset ℕ),
            (∀ g ∈ ds, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
              g.inputs.length ≤ 2) ∧
            (∀ (j : ℕ) (hj : j < ds.length), ∀ i ∈ ds[j].inputs, i < m + j) ∧
            (∀ j ∈ S, j < K + 1 ∧ ¬ Drop n F j) ∧ ds.length ≤ S.card ∧
      (ds.filter ntag).length = (S.filter (tagged gs ·)).card ∧
            ∀ w < n + (K + 1), Const (F w) ∨
              ∃ k < m + ds.length, ∀ y, F w y = (run ds (List.ofFn y)).getD k false := by
        intro g ho hopTag hl hgb hg
        have hKS : K ∉ S := fun h => by have := (h2 K h).1; omega
        refine ⟨ds ++ [g], insert K S, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro g' hg'
          rcases List.mem_append.1 hg' with h | h
          · exact h1 g' h
          · rw [List.mem_singleton.1 h]; exact ⟨ho, hl⟩
        · intro j hj i hi
          rcases Nat.lt_or_ge j ds.length with h | h
          · rw [List.getElem_append_left h] at hi
            exact hb j h i hi
          · have hjj : j = ds.length := by simp at hj; omega
            subst hjj
            exact hgb i (by simpa using hi)
        · intro j hj
          rcases Finset.mem_insert.1 hj with rfl | h
          · exact ⟨by omega, hd⟩
          · exact h2' j h
        · rw [Finset.card_insert_of_notMem hKS]; simp; omega
        · have hno : K ∉ S.filter (tagged gs ·) := fun h => hKS (Finset.mem_filter.mp h).1
          rw [List.filter_append, List.length_append, htag, Finset.filter_insert]
          cases hn : tagged gs K <;> simp [hn, hopTag, hno]
        · intro w hw
          rcases Nat.lt_or_ge w (n + K) with h | h
          · rcases h4 w h with hc | ⟨k, hk, hk'⟩
            · exact Or.inl hc
            · refine Or.inr ⟨k, by simp; omega, fun y => ?_⟩
              rw [run_snoc, getD_lt _ _ _ (by rw [run_length, List.length_ofFn]; exact hk)]
              exact hk' y
          · refine Or.inr ⟨m + ds.length, by simp, fun y => ?_⟩
            have hl' : (run ds (List.ofFn y)).length = m + ds.length := by
              rw [run_length, List.length_ofFn]
            rw [show w = n + K by omega, run_snoc, ← hl', getD_at]
            exact hg y
      have hval : ∀ i, (∃ c, ∀ y, (if i < n + K then F i y else false) = c) ∨
          (i < n + K ∧ ∃ k < m + ds.length, ∀ y,
            F i y = (run ds (List.ofFn y)).getD k false) := by
        intro i
        by_cases hi : i < n + K
        · rcases h4 i hi with ⟨c, hc⟩ | h
          · exact Or.inl ⟨c, fun y => by rw [if_pos hi]; exact hc y⟩
          · exact Or.inr ⟨hi, h⟩
        · exact Or.inl ⟨false, fun y => by rw [if_neg hi]⟩
      have hj : K < gs.length := by omega
      have hFK := hF K hj
      obtain ⟨hop, hlen⟩ := hops _ (List.getElem_mem hj)
      generalize gs[K].inputs = I at *
      generalize hO : gs[K].op = o at *
      match I, hlen with
      | [], _ =>
        refine absurd ⟨o.eval [], fun y => ?_⟩ hnc
        simpa using hFK y
      | [a], _ =>
        rcases hval a with ⟨c, hc⟩ | ⟨ha, k, hk, hk'⟩
        · refine absurd ⟨o.eval [c], fun y => ?_⟩ hnc
          rw [hFK y, List.map_singleton, hc y]
        · rcases hop with rfl | rfl | rfl
          · refine absurd (fun y => ?_) (hne a ha)
            rw [hFK y]; simp [GateOp.eval, ha]
          · refine absurd (fun y => ?_) (hne a ha)
            rw [hFK y]; simp [GateOp.eval, ha]
          · refine addg ⟨GateOp.not, [k]⟩ (by simp) (by simp [tagged, List.getElem?_eq_getElem hj, ntag, hO]) (by simp) (by simpa using hk) fun y => ?_
            rw [hFK y]; simp [GateOp.eval, ha, hk' y]
      | [a, b], _ =>
        rcases hop with rfl | rfl | rfl
        · rcases hval a with ⟨c, hc⟩ | ⟨ha, k, hk, hk'⟩
          · have he : ∀ y, F (n + K) y = (c && if b < n + K then F b y else false) := by
              intro y
              rw [hFK y, List.map_cons, List.map_singleton, hc y]; simp [GateOp.eval]
            cases c
            · exact absurd ⟨false, fun y => by rw [he y]; rfl⟩ hnc
            · by_cases hb' : b < n + K
              · exact absurd (fun y => by rw [he y, if_pos hb']; rfl) (hne b hb')
              · exact absurd ⟨false, fun y => by rw [he y, if_neg hb']; rfl⟩ hnc
          · rcases hval b with ⟨c, hc⟩ | ⟨hb', l, hl, hl'⟩
            · have he : ∀ y, F (n + K) y = (F a y && c) := by
                intro y
                rw [hFK y, List.map_cons, List.map_singleton, hc y]; simp [GateOp.eval, ha]
              cases c
              · exact absurd ⟨false, fun y => by rw [he y]; simp⟩ hnc
              · exact absurd (fun y => by rw [he y]; simp) (hne a ha)
            · refine addg ⟨GateOp.and, [k, l]⟩ (by simp) (by simp [tagged, List.getElem?_eq_getElem hj, ntag, hO]) (by simp) (by simpa using ⟨hk, hl⟩) fun y => ?_
              rw [hFK y]; simp [GateOp.eval, ha, hb', hk' y, hl' y]
        · rcases hval a with ⟨c, hc⟩ | ⟨ha, k, hk, hk'⟩
          · have he : ∀ y, F (n + K) y = (c || if b < n + K then F b y else false) := by
              intro y
              rw [hFK y, List.map_cons, List.map_singleton, hc y]; simp [GateOp.eval]
            cases c
            · by_cases hb' : b < n + K
              · exact absurd (fun y => by rw [he y, if_pos hb']; rfl) (hne b hb')
              · exact absurd ⟨false, fun y => by rw [he y, if_neg hb']; rfl⟩ hnc
            · exact absurd ⟨true, fun y => by rw [he y]; rfl⟩ hnc
          · rcases hval b with ⟨c, hc⟩ | ⟨hb', l, hl, hl'⟩
            · have he : ∀ y, F (n + K) y = (F a y || c) := by
                intro y
                rw [hFK y, List.map_cons, List.map_singleton, hc y]; simp [GateOp.eval, ha]
              cases c
              · exact absurd (fun y => by rw [he y]; simp) (hne a ha)
              · exact absurd ⟨true, fun y => by rw [he y]; simp⟩ hnc
            · refine addg ⟨GateOp.or, [k, l]⟩ (by simp) (by simp [tagged, List.getElem?_eq_getElem hj, ntag, hO]) (by simp) (by simpa using ⟨hk, hl⟩) fun y => ?_
              rw [hFK y]; simp [GateOp.eval, ha, hb', hk' y, hl' y]
        · rcases hval a with ⟨c, hc⟩ | ⟨ha, k, hk, hk'⟩
          · refine absurd ⟨!c, fun y => ?_⟩ hnc
            rw [hFK y, List.map_cons, hc y]; simp [GateOp.eval]
          · refine addg ⟨GateOp.not, [k]⟩ (by simp) (by simp [tagged, List.getElem?_eq_getElem hj, ntag, hO]) (by simp) (by simpa using hk) fun y => ?_
            rw [hFK y]; simp [GateOp.eval, ha, hk' y]

theorem circuitTagged (n m : ℕ) (C : Circuit) (X : (Fin m → Bool) → List Bool)
    (hops : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hX : ∀ y, (X y).length = n)
    (hin : ∀ i < n, (∃ c, ∀ y, (X y).getD i false = c) ∨
      ∃ k < m, ∀ y, (X y).getD i false = (List.ofFn y).getD k false)
    (hrec : ∀ (j : ℕ) (hj : j < C.gates.length) (y : Fin m → Bool),
      (C.wires (X y)).getD (n + j) false = C.gates[j].op.eval
        (C.gates[j].inputs.map fun i => if i < n + j then (C.wires (X y)).getD i false else false))
    (hinw : ∀ i < n, ∀ y, (C.wires (X y)).getD i false = (X y).getD i false)
    (hout : C.output < n + C.gates.length)
    (hnc : ¬ ∃ c, ∀ y, C.eval (X y) = c) :
    ∃ (D : Circuit) (S : Finset ℕ),
      (∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) ∧
      (∀ (j : ℕ) (hj : j < D.gates.length), ∀ i ∈ D.gates[j].inputs, i < m + j) ∧
      D.output < m + D.gates.length ∧ D.gates.length ≤ S.card ∧
      (D.gates.filter ntag).length = (S.filter (tagged C.gates ·)).card ∧
      (∀ j ∈ S, j < C.gates.length ∧
        ¬ Drop n (fun w (y : Fin m → Bool) => (C.wires (X y)).getD w false) j) ∧
      ∀ y, D.eval (List.ofFn y) = C.eval (X y) := by
  obtain ⟨ds, S, h1, hb, h2, h3, htag, h4⟩ := restrictTagged n m C.gates
    (fun w y => (C.wires (X y)).getD w false) hops (fun i hi => by
      rcases hin i hi with ⟨c, hc⟩ | ⟨k, hk, h⟩
      · exact Or.inl ⟨c, fun y => (hinw i hi y).trans (hc y)⟩
      · exact Or.inr ⟨k, hk, fun y => (hinw i hi y).trans (h y)⟩) hrec C.gates.length le_rfl
  rcases h4 C.output hout with hc | ⟨k, hk, hk'⟩
  · exact absurd hc hnc
  · exact ⟨⟨ds, k⟩, S, h1, hb, hk, h3, htag, h2, fun y => (hk' y).symm⟩

end SevenTrack

namespace SevenDrop
open PEqualNP.CircuitLowerBounds SevenSearch.Elim

theorem const_read_drop {Y : Type} (n j : ℕ) (F : ℕ → Y → Bool) (g : Gate)
    (hop : g.op = .and ∨ g.op = .or ∨ g.op = .not) (hlen : g.inputs.length ≤ 2)
    (ev : ∀ y, F (n+j) y = g.op.eval (g.inputs.map (fun q => if q < n+j then F q y else false)))
    {r : ℕ} (hr : r ∈ rds g) (hc : Const (F r)) (hlt : r < n+j) :
    Drop n F j ∧ (g.op = .not → Const (F (n+j))) := by
  obtain ⟨b, hb⟩ := hc
  have hin : ∀ y, (if r < n+j then F r y else false) = b := by simpa [hlt] using hb
  have two : ∀ q : ℕ, (∀ y, F (n+j) y = (b && if q < n+j then F q y else false)) ∨
      (∀ y, F (n+j) y = (b || if q < n+j then F q y else false)) → Drop n F j := by
    intro q h
    by_cases hq : q < n+j
    · simp only [hq, if_true] at h
      rcases h with h|h <;> cases b
      · exact Or.inl ⟨false, fun y => by rw [h y]; rfl⟩
      · exact Or.inr ⟨q,hq,fun y => by rw [h y]; rfl⟩
      · exact Or.inr ⟨q,hq,fun y => by rw [h y]; rfl⟩
      · exact Or.inl ⟨true,fun y => by rw [h y]; rfl⟩
    · simp only [hq, if_false] at h
      rcases h with h|h
      · exact Or.inl ⟨b && false, h⟩
      · exact Or.inl ⟨b || false,h⟩
  generalize hi : g.inputs = I at *
  generalize ho : g.op = o at *
  match I, hlen with
  | [], _ =>
    rcases hop with rfl | rfl | rfl <;> simp [rds, ho, hi] at hr
  | [a], _ =>
    have ha : a = r := by
      rcases hop with rfl | rfl | rfl <;> simpa [rds, ho, hi, eq_comm] using hr
    subst a
    have e : Const (F (n+j)) := ⟨o.eval [b], fun y => by rw [ev y,List.map_singleton,hin]⟩
    exact ⟨Or.inl e,fun _ => e⟩
  | [a,c], _ =>
    rcases hop with rfl | rfl | rfl
    · refine ⟨?_, by simp⟩
      have hr' : r = a ∨ r = c := by simpa [rds, ho, hi] using hr
      rcases hr' with rfl|rfl
      · exact two c (Or.inl fun y => by rw [ev y, List.map_cons, List.map_singleton, hin y]; simp [GateOp.eval])
      · exact two a (Or.inl fun y => by rw [ev y, List.map_cons, List.map_singleton, hin y]; simp [GateOp.eval,Bool.and_comm])
    · refine ⟨?_, by simp⟩
      have hr' : r = a ∨ r = c := by simpa [rds, ho, hi] using hr
      rcases hr' with rfl|rfl
      · exact two c (Or.inr fun y => by rw [ev y, List.map_cons, List.map_singleton, hin y]; simp [GateOp.eval])
      · exact two a (Or.inr fun y => by rw [ev y, List.map_cons, List.map_singleton, hin y]; simp [GateOp.eval,Bool.or_comm])
    · have hr' : r = a := by simpa [rds, ho, hi] using hr
      subst a
      have e : Const (F (n+j)) := ⟨!b,fun y => by rw [ev y, List.map_cons, hin y]; rfl⟩
      exact ⟨Or.inl e, fun _ => e⟩

theorem exists_binary_drop {Y : Type} (n : ℕ) (gs : List Gate) (F : ℕ → Y → Bool) (A B : ℕ → Bool)
    (hops : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hrec : ∀ (j : ℕ) (hj : j < gs.length) y, F (n+j) y = gs[j].op.eval
      (gs[j].inputs.map fun i => if i < n+j then F i y else false))
    (hA : ∀ (j : ℕ) (hj : j < gs.length), A (n+j) = gs[j].op.eval
      (gs[j].inputs.map fun i => if i < n+j then A i else false))
    (hB : ∀ (j : ℕ) (hj : j < gs.length), B (n+j) = gs[j].op.eval
      (gs[j].inputs.map fun i => if i < n+j then B i else false))
    (hin : ∀ w < n, A w ≠ B w → Const (F w))
    {out : ℕ} (hout : out < n + gs.length) (hd : A out ≠ B out) (hnc : ¬ Const (F out)) :
    ∃ j, ∃ hj : j < gs.length, gs[j].op ≠ .not ∧ Drop n F j := by
  by_contra! h
  apply hnc
  have allw : ∀ w < n+gs.length, A w ≠ B w → Const (F w) := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro bound diff
      by_cases hw : w < n
      · exact hin w hw diff
      let j := w-n
      have hj : j < gs.length := by dsimp [j];omega
      have eqw : w = n+j := by dsimp [j];omega
      obtain ⟨hop,hl⟩ := hops _ (List.getElem_mem hj)
      have hex : ∃ r ∈ rds gs[j], (if r < n+j then A r else false) ≠ (if r < n+j then B r else false) := by
        by_contra! hzero
        apply diff
        rw [eqw,hA j hj,hB j hj]
        exact eval_congr _ _ _ hop hzero
      obtain ⟨r, hr, hne⟩ := hex
      by_cases hr_lt : r < n+j
      · simp only [hr_lt,if_true] at hne
        have hrw : r < w := by omega
        have hc := ih r hrw (by omega) hne
        obtain ⟨hdrop, hnot⟩ := const_read_drop n j F _ hop hl (hrec j hj) hr hc hr_lt
        rw [eqw]
        by_cases hg : gs[j].op = .not
        · exact hnot hg
        · exact False.elim (h j hj hg hdrop)
      · simp [hr_lt] at hne
  exact allw out hout hd
end SevenDrop


namespace BinaryPin
open PEqualNP.CircuitLowerBounds SevenSearch.Elim SevenTrack SevenDrop

def bc (gs : List Gate) : ℕ := gs.length - (gs.filter ntag).length

theorem tag_card (gs : List Gate) :
    ((Finset.range gs.length).filter (tagged gs ·)).card = (gs.filter ntag).length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih =>
    have sub : (Finset.range gs.length).filter (tagged (gs ++ [g]) ·) =
        (Finset.range gs.length).filter (tagged gs ·) := by
      apply Finset.filter_congr
      intro i hi
      simp [tagged,List.getElem?_append_left (Finset.mem_range.mp hi)]
    have atg : tagged (gs ++ [g]) gs.length = ntag g := by simp [tagged]
    have fresh : gs.length ∉ (Finset.range gs.length).filter (tagged gs ·) := by simp
    simp only [List.length_append,List.length_singleton,Finset.range_add_one, Finset.filter_insert, sub,
      List.filter_append]
    cases h : ntag g <;> simp [atg,h,fresh,ih]

theorem project {n m : ℕ} (v : Fin n) (pi : Fin n → Fin m) (f : (Fin n → Bool) → Bool)
    (x : Fin n → Bool) (ess : f (Function.update x v false) ≠ f (Function.update x v true))
    (nc : ∃ y z : Fin m → Bool, f (Function.update (y ∘ pi) v false) ≠ f (Function.update (z ∘ pi) v false))
    (C : Circuit)
    (hops : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) :
    ∃ D : Circuit,
      (∀ g ∈ D.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) ∧
      (∀ y : Fin m → Bool, D.eval (List.ofFn y) = f (Function.update (y ∘ pi) v false)) ∧
      bc D.gates + 1 ≤ bc C.gates := by
  let pin := fun y => Function.update (y ∘ pi) v false
  let x0 := Function.update x v false
  let x1 := Function.update x v true
  let X := fun y => List.ofFn (pin y)
  let F := fun w (y : Fin m → Bool) => (C.wires (X y)).getD w false
  let A := fun w => (C.wires (List.ofFn x0)).getD w false
  let B := fun w => (C.wires (List.ofFn x1)).getD w false
  have wire : ∀ xs, C.wires xs = run C.gates xs := fun _ => rfl
  have dif : A C.output ≠ B C.output := by
    change C.eval (List.ofFn x0) ≠ C.eval (List.ofFn x1)
    rw [hev,hev]
    exact ess
  have nconst : ¬ Const (F C.output) := by
    rintro ⟨v,hv⟩
    obtain ⟨u,w,hd⟩ := nc
    apply hd
    exact (hev (pin u)).symm.trans ((hv u).trans ((hv w).symm.trans (hev (pin w))))
  have out : C.output < n + C.gates.length := by
    by_contra! h
    apply dif
    simp [A,B,wire,List.getD_eq_default,run_length,h]
  have recF : ∀ j (hj : j < C.gates.length) y, F (n+j) y = C.gates[j].op.eval
      (C.gates[j].inputs.map fun i => if i < n+j then F i y else false) := by
    intro j hj y
    simpa [F,X,wire] using run_gate C.gates (X y) j hj
  have recA : ∀ j (hj : j < C.gates.length), A (n+j) = C.gates[j].op.eval
      (C.gates[j].inputs.map fun i => if i < n+j then A i else false) := by
    intro j hj
    simpa [A,wire] using run_gate C.gates (List.ofFn x0) j hj
  have recB : ∀ j (hj : j < C.gates.length), B (n+j) = C.gates[j].op.eval
      (C.gates[j].inputs.map fun i => if i < n+j then B i else false) := by
    intro j hj
    simpa [B,wire] using run_gate C.gates (List.ofFn x1) j hj
  have inputs : ∀ (k : Fin n) y, F k.val y = pin y k := by
    intro k y
    dsimp [F, X]
    rw [wire,run_input _ _ _ (by simpa using k.isLt),List.getD_eq_getElem _ _ (by simpa using k.isLt),List.getElem_ofFn]
  have varies : ∀ k < n, A k ≠ B k → Const (F k) := by
    intro k hk hkdiff
    have h5 : k = v.val := by
      by_contra hk5
      apply hkdiff
      simp only [A,B,wire]
      rw [run_input _ _ _ (by simpa using hk),run_input _ _ _ (by simpa using hk)]
      rw [List.getD_eq_getElem _ _ (by simpa using hk),List.getD_eq_getElem _ _ (by simpa using hk)]
      simp only [List.getElem_ofFn]
      rw [show x0 = Function.update x v false from rfl, show x1 = Function.update x v true from rfl,
        Function.update_of_ne (show (⟨k,hk⟩ : Fin n) ≠ v from fun h => hk5 (congrArg Fin.val h)),
        Function.update_of_ne (show (⟨k,hk⟩ : Fin n) ≠ v from fun h => hk5 (congrArg Fin.val h))]
    subst k
    exact ⟨false,fun y => (inputs v y).trans (by simp [pin])⟩
  obtain ⟨j,hj,hjop,hjdrop⟩ := exists_binary_drop n C.gates F A B hops recF recA recB varies out dif nconst
  have hin : ∀ i < n, (∃ c, ∀ y, (X y).getD i false = c) ∨ ∃ k < m, ∀ y, (X y).getD i false = (List.ofFn y).getD k false := by
    intro i hi
    let a : Fin n := ⟨i,hi⟩
    have hv : ∀ y, (X y).getD i false = pin y a := by
      intro y
      have q := inputs a y
      change (run C.gates (X y)).getD i false = pin y a at q
      rw [run_input _ _ _ (by simpa [X] using hi)] at q
      exact q
    by_cases h : a = v
    · exact Or.inl ⟨false,fun y => (hv y).trans (by simp [h,pin])⟩
    · refine Or.inr ⟨(pi a).val,(pi a).isLt,fun y => ?_⟩
      rw [hv, List.getD_eq_getElem _ _ (by simpa using (pi a).isLt),List.getElem_ofFn]
      exact Function.update_of_ne h _ _
  obtain ⟨D,S,hg,_,_,hc,ht,hs,he⟩ := circuitTagged n m C X hops (by simp [X]) hin recF
    (fun i hi y => run_input _ _ _ (by simpa [X] using hi)) out nconst
  refine ⟨D,hg,fun y => (he y).trans (hev _), ?_⟩
  let p := fun k => tagged C.gates k = true
  have hjtag : ¬p j := by
    dsimp [p,tagged]
    rw [List.getElem?_eq_getElem hj]
    generalize heq : C.gates[j] = gate at *
    obtain ⟨op,args⟩ := gate
    cases op <;> simp_all [ntag]
  have sep := Finset.card_filter_add_card_filter_not (s := S) p
  have sep0 := Finset.card_filter_add_card_filter_not (s := Finset.range C.gates.length) p
  have loc : S.filter (fun a => ¬p a) ⊆ ((Finset.range C.gates.length).filter (fun a => ¬p a)).erase j := by
    intro i hi
    obtain ⟨hi,hn⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_erase.mpr ⟨?_,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hs i hi).1,hn⟩⟩
    rintro rfl
    exact (hs i hi).2 hjdrop
  have hb := Finset.card_le_card loc
  rw [Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,hjtag⟩)] at hb
  have positive : 0 < ((Finset.range C.gates.length).filter (fun a => ¬p a)).card :=
    Finset.card_pos.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,hjtag⟩⟩
  dsimp [p] at sep sep0 hb positive
  rw [tag_card,Finset.card_range] at sep0
  dsimp [bc]
  omega
end BinaryPin

namespace SevenFinish
open PEqualNP.CircuitLowerBounds BinaryPin SevenTrack SignedProjection

def target (x : Fin 7 → Bool) := decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)
def forget : Fin 7 → Fin 6 := ![0,1,2,0,3,4,5]

set_option maxRecDepth 100000 in
theorem pin_table : ∀ y : Fin 6 → Bool, target (Function.update (y ∘ forget) 3 false) =
    Direct64.tableA y := by decide +kernel

theorem split_gate_count (gs : List Gate) : Direct64.binaryCost gs + (gs.filter ntag).length = gs.length := by
  have h (g : Gate) : Direct64.isBinary g = !(ntag g) := by cases g with | mk op ins => cases op <;> rfl
  unfold Direct64.binaryCost
  induction gs with
  | nil => rfl
  | cons g gs ih => by_cases b : ntag g = true <;> simp [List.filter_cons,h,b] <;> omega

theorem finish (reject : ¬ CoreSigned.build signedOps (0xfffefffcfefeee00 : BitVec 64) 8 Direct64.cols.toFinset) :
∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o hg _ hf
  by_cases hn : ∃ g ∈ gs, g.op = .not
  · let C : Circuit := ⟨gs,o⟩
    obtain ⟨D, basis, computes, drop⟩ := project (3 : Fin 7) forget target (fun i => decide (i = 0))
      (by decide +kernel) ⟨fun _ => false, fun _ => true, by decide +kernel⟩ C hg hf
    have floor := Direct64.low reject D.gates D.output basis (fun y => (computes y).trans (pin_table y))
    have total := split_gate_count D.gates
    obtain ⟨g,hm,ho⟩ := hn
    have nonempty : 0 < (gs.filter ntag).length := List.length_pos_iff.mpr <| List.ne_nil_of_mem
      (List.mem_filter.mpr ⟨hm, by simp [ntag,ho]⟩ : g ∈ gs.filter ntag)
    change bc D.gates + 1 ≤ bc gs at drop
    unfold bc at drop
    have lower : 11 ≤ gs.length := by omega
    exact ⟨SevenUpper.witness,17,SevenUpper.fits,SevenUpper.size.le.trans lower,SevenUpper.correct⟩
  · refine ⟨gs,o,?_,le_rfl,hf⟩
    intro g hm
    obtain ⟨hop,hin⟩ := hg g hm
    refine ⟨?_,hin⟩
    rcases hop with ha|ho|hneg
    · exact Or.inl ha
    · exact Or.inr ho
    · exact (hn ⟨g,hm,hneg⟩).elim
end SevenFinish


namespace SignedProjection

def ew0 : Word := 0x1000200

def ew1 : Word := 0x1000400

def ew2 : Word := 0x1020000

def ew3 : Word := 0x1100000

def ew4 : Word := 0x5000500

def ew5 : Word := 0x5080508

def ew6 : Word := 0x20022002

def ew7 : Word := 0x30003000

def ew8 : Word := 0x30030000

def ew9 : Word := 0x40044004

def ew10 : Word := 0x44444444

def ew11 : Word := 0x50005000

def ew12 : Word := 0x50050000

def ew13 : Word := 0x50505050

def ew14 : Word := 0x55005500

def ew15 : Word := 0x55550000

def ew16 : Word := 0xff00ff00

def ew17 : Word := 0xffffff00

def ew18 : Word := 0x1000001000

def ew19 : Word := 0x1200000000

def ew20 : Word := 0x10001000000

def ew21 : Word := 0x10200000000

def ew22 : Word := 0x40400000404

def ew23 : Word := 0x40400004040

def ew24 : Word := 0x40800000408

def ew25 : Word := 0x50000000500

def ew26 : Word := 0x50000005000

def ew27 : Word := 0x50500000000

def ew28 : Word := 0x50a00000000

def ew29 : Word := 0x80800000404

def ew30 : Word := 0xa0000000500

def ew31 : Word := 0xa0a00000000

def ew32 : Word := 0xa0a00000a0a

def ew33 : Word := 0xc0c00000c0c

def ew34 : Word := 0xf0000000f00

def ew35 : Word := 0xf0f00000000

def ew36 : Word := 0x202000002020

def ew37 : Word := 0x210000002100

def ew38 : Word := 0x212100000000

def ew39 : Word := 0x400400004004

def ew40 : Word := 0x444400004444

def ew41 : Word := 0x500000005000

def ew42 : Word := 0x500500000000

def ew43 : Word := 0x505000005050

def ew44 : Word := 0x550000005500

def ew45 : Word := 0x555500000000

def ew46 : Word := 0xff000000ff00

def ew47 : Word := 0xffff00000000

def ew48 : Word := 0xffff0000ff00

def ew49 : Word := 0x1000000020000

def ew50 : Word := 0x1000000100000

def ew51 : Word := 0x1000400000000

def ew52 : Word := 0x1001000000000

def ew53 : Word := 0x1010000000000

def ew54 : Word := 0x5000500000000

def ew55 : Word := 0x5000500400040

def ew56 : Word := 0x8000800040004

def ew57 : Word := 0xa000000050000

def ew58 : Word := 0xa000a00000000

def ew59 : Word := 0xa000a000a000a

def ew60 : Word := 0xc000c000c000c

def ew61 : Word := 0xf0000000f0000

def ew62 : Word := 0xf000f00000000

def ew63 : Word := 0x20002000100010

def ew64 : Word := 0x22000000110000

def ew65 : Word := 0x22002200000000

def ew66 : Word := 0x22002222002200

def ew67 : Word := 0x30003030003000

def ew68 : Word := 0x33000033000000

def ew69 : Word := 0x33003300000000

def ew70 : Word := 0xff00ff00000000

def ew71 : Word := 0xff00ff00ff0000

def ew72 : Word := 0x100010001000100

def ew73 : Word := 0x101010100000000

def ew74 : Word := 0x101010110001000

def ew75 : Word := 0x102010201000100

def ew76 : Word := 0x202000000000202

def ew77 : Word := 0x202020220202020

def ew78 : Word := 0x202202002022020

def ew79 : Word := 0x300000000000300

def ew80 : Word := 0x300030030003000

def ew81 : Word := 0x300300003003000

def ew82 : Word := 0x303000000000000

def ew83 : Word := 0x303000003030000

def ew84 : Word := 0x303000030300000

def ew85 : Word := 0x303030300000000

def ew86 : Word := 0x303303000000000

def ew87 : Word := 0x404040404040404

def ew88 : Word := 0x404040440404040

def ew89 : Word := 0x408040804080408

def ew90 : Word := 0x500050005000500

def ew91 : Word := 0x500050050005000

def ew92 : Word := 0x504050450405040

def ew93 : Word := 0x505000005050000

def ew94 : Word := 0x505000050500000

def ew95 : Word := 0x505050500000000

def ew96 : Word := 0x505050540404040

def ew97 : Word := 0x505050550005000

def ew98 : Word := 0x505050550500000

def ew99 : Word := 0x508050805080508

def ew100 : Word := 0x50a0000050a0000

def ew101 : Word := 0x50a0500050a0500

def ew102 : Word := 0x50a050a00000000

def ew103 : Word := 0x50a050a04080408

def ew104 : Word := 0x50a050a05000500

def ew105 : Word := 0xf0f0f0f00000000

def ew106 : Word := 0xf0f0f0f0f0f0000

def ew107 : Word := 0x1000001010000010

def ew108 : Word := 0x1010202010102020

def ew109 : Word := 0x1020102010201020

def ew110 : Word := 0x1100000011000000

def ew111 : Word := 0x1100001100000000

def ew112 : Word := 0x1100110011001100

def ew113 : Word := 0x1100220011002200

def ew114 : Word := 0x1111000011110000

def ew115 : Word := 0x1111222200000000

def ew116 : Word := 0x1122000011220000

def ew117 : Word := 0x1122112200000000

def ew118 : Word := 0x2222222222222222

def ew119 : Word := 0x3030303030303030

def ew120 : Word := 0x3232323232323232

def ew121 : Word := 0x3300330033003300

def ew122 : Word := 0x3330333033303330

def ew123 : Word := 0x3333000033330000

def ew124 : Word := 0x3333330033333300

def ew125 : Word := 0x3333333300000000

def ew126 : Word := 0x3333333322222222

def ew127 : Word := 0x3333333333330000

def ew128 : Word := 0x5500550055005500

def ew129 : Word := 0x5555550055555500

def ew130 : Word := 0x8888888844444444

def ew131 : Word := 0xa00aa00aa00aa00a

def ew132 : Word := 0xa0a0a0a050505050

def ew133 : Word := 0xaa00aa0055005500

def ew134 : Word := 0xaaaa000055550000

def ew135 : Word := 0xaaaaaaaa00000000

def ew136 : Word := 0xaaaaaaaaaaaaaaaa

def ew137 : Word := 0xaaaaaaaaffaaffaa

def ew138 : Word := 0xc00cc00cc00cc00c

def ew139 : Word := 0xcccccccccccccccc

def ew140 : Word := 0xf000f000f000f000

def ew141 : Word := 0xf00f0000f00f0000

def ew142 : Word := 0xf00ff00f00000000

def ew143 : Word := 0xf0f0f0f0f0f0f0f0

def ew144 : Word := 0xf0fff0fff0f0f0f0

def ew145 : Word := 0xff00ff0000000000

def ew146 : Word := 0xff00ff00ff00ff00

def ew147 : Word := 0xff00ffffff00ff00

def ew148 : Word := 0xff0fff0fff00ff00

def ew149 : Word := 0xffccffcccccccccc

def ew150 : Word := 0xfff0fff0fff0fff0

def ew151 : Word := 0xffff0000ffff0000

def ew152 : Word := 0xffff0000ffffff00

def ew153 : Word := 0xffff00ffffff0000

def ew154 : Word := 0xffffff00ffff0000

def ew155 : Word := 0xffffff00ffffff00

def ew156 : Word := 0xffffffff00000000

def ew157 : Word := 0xffffffff0000ff00

def ew158 : Word := 0xffffffff55005500

def ew159 : Word := 0xffffffffaaaaaaaa

def ew160 : Word := 0xffffffffff00ff00

def ew161 : Word := 0xffffffffffff0000

def labelsBlock0 : Array Nat := #[
  0x1104,
  0xa20,
  0x920,
  0x904,
  0x1440,
  0x2208,
  0x2820,
  0x1410,
  0x1140,
  0x1240,
  0x2410,
  0x106a,
  0x1208,
  0x1c30,
  0x2480,
  0xa08
]

def labelsBlock1 : Array Nat := #[
  0x2280,
  0x2880,
  0xe30,
  0x1c60,
  0x1052,
  0x230c,
  0x105a,
  0x3184,
  0xa00,
  0x900,
  0x31c0,
  0x3860,
  0x1200,
  0x2384,
  0xd14,
  0x1100
]

def labelsBlock2 : Array Nat := #[
  0xe18,
  0xd30,
  0x1400,
  0x38c0,
  0x2200,
  0x2400,
  0xa0c,
  0x1430,
  0x2584,
  0xd04,
  0x2830,
  0xd20,
  0xe10,
  0x2308,
  0x2218,
  0x2800
]

def labelsBlock3 : Array Nat := #[
  0x930,
  0xa30,
  0xe20,
  0x2284,
  0x2514,
  0x2860,
  0x914,
  0x107e,
  0x104e,
  0x1042,
  0x2304,
  0x3104,
  0x101e,
  0x2430,
  0x1160,
  0x220c
]

def labelsBlock4 : Array Nat := #[
  0x1056,
  0xa04,
  0xe08,
  0x1c40,
  0x2510,
  0x1618,
  0x1c10,
  0xd10,
  0x1480,
  0xd00,
  0x2c30,
  0x3140,
  0x1c20,
  0x1120,
  0x1414,
  0x1114
]

def labelsBlock5 : Array Nat := #[
  0x2884,
  0x102a,
  0x102e,
  0x103e,
  0x2984,
  0x2804,
  0x130c,
  0x2504,
  0x1418,
  0x14c0,
  0x28c0,
  0x1c00,
  0xe00,
  0x2810,
  0x1184,
  0x2414
]

def labelsBlock6 : Array Nat := #[
  0x105e,
  0x11c0,
  0x3100,
  0x3820,
  0x110c,
  0x1460,
  0x2210,
  0x3840,
  0x1022,
  0x2c20,
  0x2300,
  0x2500,
  0x3800,
  0x3880,
  0x54207e,
  0x960
]

def labelsBlock7 : Array Nat := #[
  0x2920,
  0x2580,
  0x1920,
  0x1610,
  0x1036,
  0x2840,
  0x53207e,
  0x74207e,
  0x54307e,
  0x2900,
  0x101a,
  0x1012,
  0x1002,
  0x1304,
  0x1a20,
  0x100e
]

def labelsBlock8 : Array Nat := #[
  0x74307e,
  0xc24,
  0x1844,
  0x24c0,
  0x2c80,
  0x2c00,
  0x984,
  0x1420,
  0x2420,
  0x1066,
  0x2484,
  0x3440,
  0x63207e,
  0x64207e,
  0x2124,
  0x2144
]

def labelsBlock9 : Array Nat := #[
  0x1514,
  0x1110,
  0x2440,
  0x1680,
  0x1c80,
  0x1404,
  0x940,
  0x2904,
  0x1046,
  0x54007e,
  0x74107e,
  0x3240,
  0x1904,
  0x44207e,
  0xa60,
  0xc90
]

def labelsBlock10 : Array Nat := #[
  0x18a0,
  0x980,
  0x2c10,
  0x104a,
  0x107a,
  0x1076,
  0x1032,
  0x103a,
  0x90c,
  0xb04,
  0x72007e,
  0x52107e,
  0x2418,
  0x2610,
  0xa40,
  0x1220
]

def labelsBlock11 : Array Nat := #[
  0x11d,
  0x125,
  0x53206a,
  0x52106a,
  0x1072,
  0x1086,
  0x14d44207e,
  0x1082,
  0x106e,
  0x1026,
  0x2190,
  0x21a0,
  0x22c0,
  0x1960,
  0x100a,
  0x1016
]

def labelsBlock12 : Array Nat := #[
  0x5d,
  0x1e80,
  0x65,
  0x6d,
  0x75,
  0x7d,
  0x85,
  0x32c0,
  0x95,
  0x99,
  0xa5,
  0xb1,
  0xb5,
  0xb9,
  0x1a60,
  0x1006
]

def labelsBlock13 : Array Nat := #[
  0x1504,
  0x1062,
  0xb0c,
  0x2380,
  0x101,
  0x109,
  0x2618,
  0x121,
  0x129,
  0x12d,
  0x131,
  0x141,
  0x149,
  0x62407e,
  0x159,
  0x52407e
]

def labelsBlock14 : Array Nat := #[
  0x171,
  0x175,
  0x1984,
  0x1510,
  0x15c0,
  0x3114,
  0x2cc0,
  0x16c0,
  0x61,
  0x79,
  0x1cc0,
  0x59,
  0x69,
  0x71,
  0x81,
  0x89
]

def labelsBlock15 : Array Nat := #[
  0x8d,
  0x1360,
  0x9d,
  0xc1,
  0x3160,
  0xa1,
  0xa9,
  0xad,
  0xbd,
  0xc5,
  0xc9,
  0x2960,
  0x1560,
  0x1c14,
  0xd9,
  0xdd
]

def labelsBlock16 : Array Nat := #[
  0xe1,
  0xe5,
  0xe9,
  0xa18,
  0xf9,
  0x720052,
  0x631072,
  0x530052,
  0x61306e,
  0x111,
  0x150d32082,
  0x150d32086,
  0x532082,
  0x532086,
  0x3180,
  0x119
]

def labelsBlock17 : Array Nat := #[
  0x135,
  0x13d,
  0x543082,
  0x543086,
  0x14d,
  0x151,
  0x155,
  0x542082,
  0x542086,
  0x161,
  0x169,
  0x16d,
  0x17d,
  0x181,
  0x189,
  0x18d
]

def labelsBlock18 : Array Nat := #[
  0x195,
  0xfd,
  0x105,
  0x10d,
  0x115,
  0x139,
  0x145,
  0x15d,
  0x165,
  0x179,
  0x185,
  0x191,
  0x199,
  0x1,
  0x5,
  0x9
]

def labelsBlock19 : Array Nat := #[
  0xd,
  0x11,
  0x15,
  0x19,
  0x1d,
  0x21,
  0x25,
  0x29,
  0x2d,
  0x31,
  0x35,
  0x39,
  0x3d,
  0x41,
  0x45,
  0x49
]

def labelsBlock20 : Array Nat := #[
  0x4d,
  0x51,
  0x55,
  0x91,
  0xcd,
  0xd1,
  0xd5,
  0xed,
  0xf1,
  0xf5,
  0x19d
]

def labelsGet (i : Nat) : Nat :=
  if i < 160 then
    if i < 80 then
      if i < 32 then
        if i < 16 then
          labelsBlock0.getD (i-0) 3
        else
          labelsBlock1.getD (i-16) 3
      else
        if i < 48 then
          labelsBlock2.getD (i-32) 3
        else
          if i < 64 then
            labelsBlock3.getD (i-48) 3
          else
            labelsBlock4.getD (i-64) 3
    else
      if i < 112 then
        if i < 96 then
          labelsBlock5.getD (i-80) 3
        else
          labelsBlock6.getD (i-96) 3
      else
        if i < 128 then
          labelsBlock7.getD (i-112) 3
        else
          if i < 144 then
            labelsBlock8.getD (i-128) 3
          else
            labelsBlock9.getD (i-144) 3
  else
    if i < 240 then
      if i < 192 then
        if i < 176 then
          labelsBlock10.getD (i-160) 3
        else
          labelsBlock11.getD (i-176) 3
      else
        if i < 208 then
          labelsBlock12.getD (i-192) 3
        else
          if i < 224 then
            labelsBlock13.getD (i-208) 3
          else
            labelsBlock14.getD (i-224) 3
    else
      if i < 288 then
        if i < 256 then
          labelsBlock15.getD (i-240) 3
        else
          if i < 272 then
            labelsBlock16.getD (i-256) 3
          else
            labelsBlock17.getD (i-272) 3
      else
        if i < 304 then
          labelsBlock18.getD (i-288) 3
        else
          if i < 320 then
            labelsBlock19.getD (i-304) 3
          else
            labelsBlock20.getD (i-320) 3

def decodeHints (enc i : Nat) := labelsGet ((enc >>> (i * 9)) % 512)

def localHints (stride dict enc i : Nat) : Nat :=
  let q := (enc >>> (stride*i)) % (2^stride)
  labelsGet ((dict >>> (9*q)) % 512)

def viewsBlock0 : Array View := #[
  ⟨0x1020408,⟨3,by decide⟩,0x20400,[ew1,ew2],2,decodeHints 0x96898c826⟩,
  ⟨0x1100220,⟨5,by decide⟩,0x100200,[ew0,ew3],2,decodeHints 0x970d89c36⟩,
  ⟨0x1200001200,⟨9,by decide⟩,0x200001000,[ew18,ew19],2,decodeHints 0x97a051c81⟩,
  ⟨0x10201020000,⟨17,by decide⟩,0x201000000,[ew20,ew21],2,decodeHints 0x982091e82⟩,
  ⟨0x1000400100040,⟨6,by decide⟩,0x400100000,[ew50,ew51],2,decodeHints 0x989605c58⟩,
  ⟨0x1001000020020,⟨5,by decide⟩,0x1000020000,[ew49,ew52],2,decodeHints 0x9913cbe4f⟩,
  ⟨0x1010000101000,⟨12,by decide⟩,0x10000100000,[ew50,ew53],2,decodeHints 0x9989c5427⟩,
  ⟨0x30033003,⟨0,by decide⟩,0x30022000,[ew6,ew7,ew8],3,decodeHints 0x9a08452490007cb649⟩,
  ⟨0x50055005,⟨0,by decide⟩,0x50044000,[ew9,ew11,ew12],3,decodeHints 0x9a848845c06070b65c⟩,
  ⟨0x50500000505,⟨0,by decide⟩,0x50400000400,[ew22,ew25,ew27],3,decodeHints 0x9b0041e18028905e18⟩,
  ⟨0x50500005050,⟨4,by decide⟩,0x50400004000,[ew23,ew26,ew27],3,decodeHints 0x9b848402c17198ba2c⟩,
  ⟨0x50a0000050a,⟨1,by decide⟩,0x50800000400,[ew24,ew25,ew28],3,decodeHints 0x9c0044c410a8e8aa41⟩,
  ⟨0xa0a00000505,⟨0,by decide⟩,0xa0800000400,[ew29,ew30,ew31],3,decodeHints 0x9c8041e18169a8f218⟩,
  ⟨0x212100002121,⟨0,by decide⟩,0x212000002000,[ew36,ew37,ew38],3,decodeHints 0x9d0ac3c491a1ac5e49⟩,
  ⟨0x500500005005,⟨0,by decide⟩,0x500400004000,[ew39,ew41,ew42],3,decodeHints 0x9d848845c028910a5c⟩,
  ⟨0xa000a00050005,⟨0,by decide⟩,0xa000800040000,[ew56,ew57,ew58],3,decodeHints 0x9e024181c169a8c41c⟩
]

def viewsBlock1 : Array View := #[
  ⟨0x22002200110011,⟨0,by decide⟩,0x22002000100000,[ew63,ew64,ew65],3,decodeHints 0x9e8100e22221acc422⟩,
  ⟨0x303000000000303,⟨0,by decide⟩,0x302000000000200,[ew76,ew79,ew82],3,decodeHints 0x9f00806191d988d819⟩,
  ⟨0x1100001111000011,⟨0,by decide⟩,0x1100001010000000,[ew107,ew110,ew111],3,decodeHints 0x9f84c8c5b05094d85b⟩,
  ⟨0x55555555,⟨0,by decide⟩,0x54544400,[ew10,ew13,ew14,ew15],3,localHints 3 0x34010020c0e03c4418 0xf754108cb408⟩,
  ⟨0xf0f00000f0f,⟨0,by decide⟩,0xf0c00000e00,[ew32,ew33,ew34,ew35],4,decodeHints 0x5c8080202018643019028144824178643019⟩,
  ⟨0x555500005555,⟨0,by decide⟩,0x555400004400,[ew40,ew43,ew44,ew45],4,decodeHints 0x5c8041c01078601e18028904a24178604a18⟩,
  ⟨0xf000f000f000f,⟨0,by decide⟩,0xe000c000e0000,[ew59,ew60,ew61,ew62],3,localHints 3 0x29824100512000381f 0xf7540891b408⟩,
  ⟨0x33003333003300,⟨8,by decide⟩,0x32003032002200,[ew66,ew67,ew68,ew69],4,localHints 3 0x500263d440349802 0xc28408818408⟩,
  ⟨0x303030330303030,⟨4,by decide⟩,0x302030030302000,[ew77,ew80,ew84,ew85],4,localHints 3 0x5043c2a109740e47 0xce82488d0248⟩,
  ⟨0x303303003033030,⟨4,by decide⟩,0x302303002022000,[ew78,ew81,ew83,ew86],4,localHints 3 0x508424f0f2441447 0xd58898248288⟩,
  ⟨0x505050505050505,⟨0,by decide⟩,0x504050404040400,[ew87,ew90,ew93,ew95],4,decodeHints 0x5c8041e18060701e18028905e18060705e18⟩,
  ⟨0x505050550505050,⟨4,by decide⟩,0x504050450504000,[ew88,ew91,ew94,ew95],5,localHints 3 0xa1848402e331740e2c 0xfa82488d0248⟩,
  ⟨0x50a050a050a050a,⟨1,by decide⟩,0x50a0508040a0400,[ew89,ew90,ew100,ew102],5,localHints 3 0xa20044c151d1540041 0xfa82488d0248⟩,
  ⟨0x1111222211112222,⟨1,by decide⟩,0x1110222010102200,[ew108,ew113,ew114,ew115],4,localHints 3 0x51408342b9392a03 0xd404408c0440⟩,
  ⟨0x1122112211221122,⟨1,by decide⟩,0x1122112010220000,[ew109,ew112,ew116,ew117],4,localHints 3 0x518263e1a154ae00 0xd64000651000⟩,
  ⟨0x3333333333333333,⟨0,by decide⟩,0x3332333032322200,[ew118,ew119,ew121,ew123,ew125],6,localHints 4 0x51c0802018284a000f8bc4419 0xa8987070431370106655205043132010⟩
]

def viewsBlock2 : Array View := #[
  ⟨0xaaaaaaaa55555555,⟨0,by decide⟩,0xaaaaaaa854544400,[ew130,ew132,ew133,ew134,ew135],6,localHints 4 0x14802004180f169a8d6620e1e44418 0xcaba8080931380107656205043132010⟩,
  ⟨0xf00ff00ff00ff00f,⟨0,by decide⟩,0xf00ef00cf00ee000,[ew131,ew138,ew140,ew141,ew142],6,localHints 4 0x14909084520512214001c0f96cb849 0xcaba9010534320108877601053432010⟩,
  ⟨0xffffffffffffffff,⟨0,by decide⟩,0xfffefffcfefeee00,[ew136,ew139,ew143,ew146,ew151,ew156],8,localHints 4 0x52808010100c0a2412800381f178883019 0xebcbdbcba010a01064542454a010201099887788301070106454245430102010⟩
]

def viewsGet (i : Nat) : Option View :=
  if i < 16 then
    viewsBlock0[(i-0)]?
  else
    if i < 32 then
      viewsBlock1[(i-16)]?
    else
      viewsBlock2[(i-32)]?

def nodesBlock0 : Array Node := #[
  ⟨0,2,[ew1,ew2],localHints 2 0x1f278c826 0x235e84⟩,
  ⟨1,2,[ew0,ew3],localHints 2 0x329bc9c36 0x235e84⟩,
  ⟨2,2,[ew18,ew19],localHints 2 0x5d27d1c81 0x235e84⟩,
  ⟨3,2,[ew20,ew21],localHints 2 0x5da811e82 0x235e84⟩,
  ⟨4,2,[ew50,ew51],localHints 2 0x5e1645c58 0x235e84⟩,
  ⟨5,2,[ew49,ew52],localHints 2 0x41984be4f 0x235e84⟩,
  ⟨6,2,[ew50,ew53],localHints 2 0x2d1645427 0x235e84⟩,
  ⟨7,3,[ew6,ew7,ew8],localHints 4 0x5b0f8001a49108a48608 0x258168155262367057066353024314322010⟩,
  ⟨8,3,[ew9,ew11,ew12],localHints 4 0x5b0e0301a5c091088609 0x258168155262367057066353024314322010⟩,
  ⟨9,3,[ew22,ew25,ew27],localHints 4 0x2f120140c180083c2210 0x258168155262367057066353024314322010⟩,
  ⟨10,3,[ew23,ew26,ew27],localHints 4 0x5d330b8542c090802210 0x258168155262367057066353024314322010⟩,
  ⟨11,3,[ew24,ew25,ew28],localHints 4 0x551d0540c4100898a01d 0x258168155262367057066353024314322010⟩,
  ⟨12,3,[ew29,ew30,ew31],localHints 4 0x79350b4e0180083ca81d 0x258168155262367057066353024314322010⟩,
  ⟨13,3,[ew36,ew37,ew38],localHints 4 0x2f358d00c49158782271 0x258168155262367057066353024314322010⟩,
  ⟨14,3,[ew39,ew41,ew42],localHints 4 0x8512014945c091090810 0x258168155262367057066353024314322010⟩,
  ⟨15,3,[ew56,ew57,ew58],localHints 4 0x62350b4961c048302e1d 0x258168155262367057066353024314322010⟩
]

def nodesBlock1 : Array Node := #[
  ⟨16,3,[ew63,ew64,ew65],localHints 4 0x623591096220201c2e28 0x258168155262367057066353024314322010⟩,
  ⟨17,3,[ew76,ew79,ew82],localHints 4 0x6c310ecc6190100c461a 0x258168155262367057066353024314322010⟩,
  ⟨18,3,[ew107,ew110,ew111],localHints 4 0x6c12828365b09918da0e 0x258168155262367057066353024314322010⟩,
  ⟨23,4,[ew66,ew67,ew68,ew69],localHints 5 0x5f389104c070690ca11e9c97a17378345621140c02602 0x34cc85ad13919660ae2f6c5eb585a179a014402633d0f0340e5adcd601600200932928380c000c040948310020⟩,
  ⟨24,4,[ew77,ew80,ew84,ew85],localHints 5 0xe50b920ba592308c1a273d39054e3481380e47108783411 0x2c0b34d27091525126208440948a02135ee295cd608a51ac614a42b50d2319d012942730ca5088830106210400⟩,
  ⟨25,4,[ew78,ew81,ew83,ew86],localHints 5 0xda49444a1eafdcc440d0d0be0a4893d0647108784608 0x34cc5420b391908142214203078908138413182e688c21a98b4216a48d08198e029c0630ca3008830906210020⟩,
  ⟨27,4,[ew88,ew91,ew92,ew94,ew95],localHints 4 0x241641a11150b88a0708080247b 0x46b46a6a545426722494826761545431210⟩,
  ⟨27,2,[ew55,ew88,ew98],localHints 3 0x4503920402c 0xe02e3408⟩,
  ⟨27,3,[ew55,ew88,ew94,ew95],localHints 3 0x600b8ba4503840402c 0x77b1700e03752e3408⟩,
  ⟨27,3,[ew88,ew91,ew96,ew98],localHints 4 0x8c27601208a07093044093 0x5454948471165454331210⟩,
  ⟨27,4,[ew88,ew91,ew94,ew95,ew96],localHints 4 0x54c2741ec8c27090b9ce45038444010 0xd6344336c3b11a162193837760543431210⟩,
  ⟨27,3,[ew73,ew88,ew91,ew98],decodeHints 0x2301c4e073981cb007160b040111501c90204a0812612⟩,
  ⟨27,4,[ew73,ew88,ew91,ew94,ew95],localHints 4 0x619184e6639960582a17144f607088802012 0x47f42732e4d4c70b4a49923876454323210⟩,
  ⟨27,2,[ew74,ew91,ew98],localHints 3 0xd03920242c 0xe02e3408⟩,
  ⟨27,3,[ew74,ew91,ew94,ew95],localHints 3 0x620a8cc0d03840242c 0x77b1700e03752e3408⟩,
  ⟨27,3,[ew88,ew91,ew97,ew98],decodeHints 0x5c070681c1a070681c40203981cb007620482448608482494⟩
]

def nodesBlock2 : Array Node := #[
  ⟨27,4,[ew88,ew91,ew94,ew95,ew97],localHints 4 0x5cc510045d40d749e854732c01c2410 0xdd288225c2bb5a982827116150142320110⟩,
  ⟨27,3,[ew54,ew88,ew91,ew98],decodeHints 0x2301c4e073981cb007160b040101701d2820240492612⟩,
  ⟨27,4,[ew54,ew88,ew91,ew94,ew95],localHints 4 0x631748c27151ccb02c17144f407088802012 0x4bf4eb2d4c40b10a4948821776454321010⟩,
  ⟨27,4,[ew88,ew91,ew95,ew98],localHints 5 0x51171181a27633152873229600ec36124c902c090802210 0x29499529146414a4318092913c412942e688a21ad804a40b50d291a0602940730ca3008830906210020⟩,
  ⟨27,5,[ew88,ew91,ew94,ew95],localHints 5 0xf02c921de5d77118460d13bb4ccec170a8e6c722960a2073d0b1d612101ec2210 0x4a3684a5ef4f37a4a1e8c8dd8105f8b85ce10de348e964d5084d69348d08911f1381d1801ef391c44916d4b1084b16a4910810066390262906310020⟩,
  ⟨28,2,[ew5,ew89,ew101],localHints 3 0x26000042a3a 0xe38e3408⟩,
  ⟨28,3,[ew89,ew99,ew101,ew102],localHints 4 0x3b641340c15130003a01 0x2852474632324540323210⟩,
  ⟨28,3,[ew5,ew89,ew90,ew100],localHints 3 0x6415800262a8042a3a 0x77d1750e0d758e3408⟩,
  ⟨28,4,[ew89,ew90,ew99,ew100,ew102],localHints 4 0x7635791f1923e03054ac000e89802f1 0x4dc46b6a545426722494826761545431210⟩,
  ⟨28,3,[ew72,ew89,ew101,ew102],decodeHints 0xec0c001d0e82a06209044c00268540c15280000201⟩,
  ⟨28,4,[ew72,ew89,ew90,ew100,ew102],localHints 4 0x1d8d5943a3e990821d03054a47c000f84c01 0x3fe3167113d3cc67b3a3918767653432100⟩,
  ⟨28,4,[ew89,ew90,ew100,ew102,ew103],localHints 4 0x305ca04d008543a7c2b0004c3e 0xb6233226a20110169112827765432321010⟩,
  ⟨28,2,[ew75,ew101,ew102],localHints 3 0x61d0740241 0xe02e3408⟩,
  ⟨28,3,[ew89,ew101,ew102,ew104],decodeHints 0x2a15000989a00001400c0065804024d008183a013e800c800⟩,
  ⟨28,3,[ew4,ew89,ew101,ew102],decodeHints 0x154bc001d0e82a013e800c800030544c0000874024d⟩,
  ⟨28,4,[ew89,ew90,ew101,ew102],localHints 5 0x761766b30a4261d0540c7d2b19000ca648043a4d 0xa92c151825255140903d4a72520529ad600a5129614ac2a5092209d0229447304a5090220084310400⟩
]

def nodesBlock3 : Array Node := #[
  ⟨28,3,[ew75,ew90,ew100,ew102],localHints 4 0x3565818747e000f80241 0x358305600370156513432010⟩,
  ⟨28,4,[ew89,ew90,ew100,ew102,ew104],localHints 4 0x542e35133d0a0cc799fc0c7d32000021d 0xee2dd225c2bb59a92827116150142320110⟩,
  ⟨28,4,[ew4,ew89,ew90,ew100,ew102],localHints 4 0x1d978aa50668e8fa6403054a47f00098021d 0x3fe3dc6c3b3aa6193830110765343221010⟩,
  ⟨28,5,[ew89,ew90,ew100,ew102],localHints 5 0x3b0b86c6afa2abe4a0f8268e9ee153e018face2b190a4007b105ea01131fc3a3e 0x4a3484ee1c4ef594a20878dd7c5617b55ce78e0348d23481084829348d0879212105d288610791c44916d4b1084b16a4910838466110062906310400⟩,
  ⟨29,4,[ew108,ew113,ew114,ew115],localHints 5 0x33df6972a08d2c571a06d2a4e141bc52130f0d80803 0x429125ae4a8a1680280f5c1ea501600180e421c6681000ad87530eb585413a1213242841cc608ca40008310400⟩,
  ⟨30,4,[ew109,ew112,ew116,ew117],localHints 5 0x3b0b86c6a557e8349a502b8d00cd04813c00133fbf0503e 0x2c8b355272895450260c541894814a639e02940e6b0a5229614ac2a5112909d0429487304a508c240008310400⟩,
  ⟨31,5,[ew118,ew119,ew120,ew121,ew123,ew125],decodeHints 0x7635000bc5e060180c0027018280c0a0300112003a00c22030895cae0a033400007000a406360181008440517c1400038000e032380c2202010a04230⟩,
  ⟨31,5,[ew118,ew119,ew121,ew123,ew125,ew126],decodeHints 0x281407000000e001d97800600180c72034b84406030009c06040703808572b8d008221101c0029018d80602010d0345f0001c0007018440611388111404⟩,
  ⟨31,5,[ew118,ew119,ew121,ew122,ew123,ew125],decodeHints 0x763500028c00a1e01c00070028814060511800270000c060a030280c070001c000402078263622028be0a0f87c00070400804082391c3c08010ac6002⟩,
  ⟨31,5,[ew118,ew119,ew121,ew123,ew124,ew125],decodeHints 0x1814060518c143505000000605018140301834462712894140607010080e261301a0e0210cca0422028be0a5200804a3011c81002040080408010ac6002⟩,
  ⟨31,5,[ew118,ew119,ew121,ew123,ew125,ew127],decodeHints 0x2814000006c2e350184422030199c3603019b4b4034481008980222c1c0407010080e1480c6c030102010020112cc2020102010020c8640608010ac6002⟩,
  ⟨31,6,[ew118,ew119,ew121,ew123,ew125],localHints 6 0x3b8105c36351798202230689c4ad103089120e14c00261e1b111fe1a1a17c780a0f8014a071ca8c320352044107415bf84228182600802 0x552b5222e530beeb6c55251254c8eb3ca52ba8a8e3a8c50c20c9cc3e8492a689e620c48c5415250a08e59205149018e32204220814a284141086049254171f55d30c79d71b3c130c5405da3d85146585d65405142004933894134494924404103c930d38028d2c030c2c9289200100205047185103080040⟩,
  ⟨32,6,[ew130,ew132,ew133,ew134,ew135],localHints 6 0xc417259e4e0a60689cd6681114c504209882066a0e8b4881c0601c300f2a0246412188e40801 0x60b7e17203a17207df60b38b08875e08739e08775d0883880886c80822cb09c6da0882c860135959539959534d60138e5952975812d758128a5952cb08149409320809349108120808039008f35008f38e08034d0802cc08628c0862cb08028a0862090801c90802080861c6080080084045084083080040⟩,
  ⟨33,6,[ew131,ew138,ew140,ew141,ew142],localHints 6 0x76172f215085b5390c1a2408128385c048b434151f8143e0006124d02929820841d198f02421 0x8c08c0a03a10a06df08c38c08859e1dd39e09d5961c83886c865c1da31c6da6591c830808139809759809738e0815810812d50933150932cb08130c1d31540812140811451d32081c04121d138e09140f08038e24030d2462cd24630c2402cb1c620a24014a2402081c6145080100082041082103080040⟩,
  ⟨34,6,[ew136,ew139,ew143,ew146,ew151,ew156,ew158],decodeHints 0xa05000341a00000186a000183c2203018440c03018001a030204c2604348185406110880e001480c6c030480402090081820010e07018005480d5003008c862010406804023801834060f87c000c0c8640608040111408040046601⟩,
  ⟨34,7,[ew128,ew136,ew139,ew143,ew146,ew151,ew156],localHints 6 0xec2e1b1aa5ca8251101c1c290f0d848100507152d2540c82431168682a3f8287c1819142283a331c4100c052003428000780c26041baa802090b02c1002 0xcd0cd50db5d3331030a44ac50cb145129028a38a0cc30f38e28c2889f0b50c2d9e721042dbaf20cbc8baeb4c308aec24a289aea20a285429a27a684101679c566610c98465914c30492514a28592310a2850858488a11a014814175f79041e75c05041b31a05968130c0996420980ca2810810570422080975812010550421451955011454d144341049144341034e38330c3ce38d30c0822c228a0892422080892422081c5143104185143104083002040⟩
]

def nodesBlock4 : Array Node := #[
  ⟨34,6,[ew136,ew139,ew143,ew146,ew151,ew159,ew160],decodeHints 0x28142a0b000ec1a0006000000c0180c0c11030f41a0006800ae571a054d20615018442203800081309810743a0a8d0020608004381c060001201008240232188042a1a1f8fc040200030000c50a850c11388111404698046601⟩,
  ⟨34,7,[ew136,ew139,ew143,ew146,ew151,ew156,ew159],localHints 6 0x50a0ec2e402f1802c976a044460d1395c4407070a4261e1b0dc74101a07030091904862021c0547f07000320c03079c4508a0234c16990e8cc3401 0x5174485d0ec0e3f33cfc0f3b338fc0fc52cb1c2f3d23cb4cb32d30cb8c2ed2cc4cca92b2aaea31230ca0ca4f3e9a2730f3071478c58e31631c51c76e68d29a36db1d24a39251cf9479248cf3c782284c32181f1cc30010071e71c11c01e00049d71b75c49201b6c039a60f69838e00f3d82d900c6402cb60c3001405875d611500701315404551349204504515140f3c138e04f3c538e04c3052cb34c3012cb0492851c71492011c7043185000103081000⟩,
  ⟨34,6,[ew136,ew139,ew143,ew150,ew151,ew156,ew160],decodeHints 0x281400461380000061a80006030f02c0c11032180e00038003c131b0d910881e8180e00038000804160b0401e0081820010e0701800048040209008c862012391c3c200101834020f87c000c040080408010ac6002010046602⟩,
  ⟨34,7,[ew136,ew139,ew143,ew146,ew150,ew151,ew156],localHints 6 0xec2e1b1a8e0c0a26a8188c0d1380e1014038106c240802838370b0b01232090c45a1a0a8fc0a1f000308e1e0408056211804c16ab0e8cc0202 0xfc0fc51cb1c2f3d13ee79e6d146d79e6d14648e390f3e48e390f3ccaac6d146baaa31144ca2990f3e4a2730f3c516630598679e15146579e1914648e318f3c68e314f3db16218589b30c18518516105181f7a07d144179e04e7593dd64e3813cf65b6417010440596d964a68131a04a29930c0450571985c458118101355445151348045100f40b3902cf3c038e2c52c014000500b14b2cc34028d00c30b28a0050081892051c0180003005041103080040⟩,
  ⟨34,6,[ew136,ew139,ew143,ew146,ew148,ew151,ew156],localHints 5 0x1a8141a03128184407098115aac0e02464312217c141f00030102b180046602 0xe9d9f5ab2727c9ec9b2727c9f18bdd36ad68794e7294e728a6097bcc77084e7084e135825a549420e628005280050106000820⟩,
  ⟨34,7,[ew105,ew136,ew139,ew143,ew146,ew151,ew156],localHints 6 0x4a1e88c1a27128880e29098786cad6b2b03818048c82431220d0be1f06064100f15884601d198280a170a00212110b00c700e022682037008681602 0xe3ce4124903d039238ad0a31248cd3329228ac4ac8e3b2c7028e28106f2524870473edb873ae1edb4138e1eab2b28aaeaa4728a0e7a054921679834920db9633a58db6c338e8d89032a40d862328a0c10e11e28468031c301e7c249209e74049200e7196dc64e3806db64a68061a00a2996180010161d75815401c00140010c31944c00c00414414913d040f38e3d040f38e2cc30928a34c30b28a0492011c71051460c31851440c3042081000042081000⟩,
  ⟨34,6,[ew129,ew139,ew143,ew146,ew151,ew155,ew156],localHints 5 0x631a87c322313894980d0710cca0412028fc09190c40c05059c81030158400202 0x94251c46d1ad250946734c5ed67227084eb5a4e128c1ef438410882d605810b02b504084a0e0014c0280050106000820⟩,
  ⟨34,4,[ew136,ew143,ew149,ew155,ew161],decodeHints 0x18004e03120900a0a0c0601e031289414051480c6c03190046201168147e050c864060f010046602010ac6002⟩,
  ⟨34,5,[ew136,ew143,ew149,ew151,ew155,ew156],decodeHints 0x6051e80c4e05580140003120900a0a0c0601e0300abd5c011289414051480c6c0343a1c4e0e190046201168147e050c864060f011352c02010046602010ac6002⟩,
  ⟨34,5,[ew136,ew139,ew143,ew145,ew155,ew161],decodeHints 0x18004e030301422031289414051480c6c03021d61604120900a0a0c0601e03009d56001008c86201168147e050c864060f011d61402010ac6002010046602⟩,
  ⟨34,6,[ew136,ew139,ew143,ew145,ew151,ew155,ew156],decodeHints 0x6051e80c4e055881400030301422030a09cb4271289414051480c6c0343a1c4e0e0208e1a04120900a0a0c0601e0300abd5c010088dae01008c86201168147e050c864060f011352c020108e1802010ac6002010046602⟩,
  ⟨34,6,[ew70,ew136,ew139,ew143,ew151,ew155,ew156],decodeHints 0x178bc0c0331818ea060000cd2061501852031b00d0e871383802060800430180780c02af5700402321880404060d00832190183c044d4b008042b180080401198080a050a00c22032d09c4627070101c040800420010d0083402⟩,
  ⟨34,6,[ew136,ew139,ew143,ew146,ew155,ew156,ew161],decodeHints 0x28140000068586a171a9781a5a1389cea751aac40603261301ab30222c1c0407010080e0210cca04009f8120100a6c2001080040210048040209008c86201011c810020112cc2028700804b2040080408010ac6002010046602⟩,
  ⟨34,6,[ew17,ew136,ew139,ew143,ew146,ew151,ew156],decodeHints 0x763b0b8145e2f088141a6d1389c4a2505014984c06838084332810482402828027e048041201008240232188045a051f814047204008100201020042b180080401198080c05000001a170180c281102038080e00840021001068041a⟩,
  ⟨34,7,[ew136,ew139,ew143,ew146,ew151,ew155,ew156],localHints 6 0x220601c18db41b1a801b2066c00c2c2712931660e2184cca24050dc207e048c82431168682a3f02c3d680b0a1c81a40118205621140c008760e8cc0202 0x33b2cd534f4b2ccd34cdc323d34f1c2f3534e93ee350badb2c2d34cbb2cad34cf3ea2d0a8f34d2e92cf3e815f9e44e791f7c54d390f90540514f16442490d98596614d36496414f1622e388f8452c505381d7e07534c17df74474178104405d79d04f05b35c6c46c13416c46c12c104405b2db04f05915a6446011410155d64d35955004d348c44040000c00c41000f00a34e28c28034028c2802c000c00a2ca007008149207180140003004041103080040⟩,
  ⟨34,6,[ew136,ew139,ew143,ew146,ew151,ew156,ew157],decodeHints 0xa050005c1a00000182e000180c2214030440c3d4e000b400020381c04348185406110880e000210cca040480402090081820010e0701800048040209008c862010400804080101834020f87c000c040080408010ac6002010046602⟩
]

def nodesBlock5 : Array Node := #[
  ⟨34,6,[ew46,ew70,ew136,ew139,ew143,ew151,ew156],decodeHints 0xd86c33800d20615018442203800020608004381c0600002321880404060d0083e1f00030042b180080401198080a050b800da00070101c040800420010d0083402178bc0c031380c06291b00c30180780c32190183c2203⟩,
  ⟨34,7,[ew46,ew136,ew139,ew143,ew146,ew151,ew156],localHints 6 0xec2e1b6da704a2203838861332890200a0e0c82431168682a3f0f8305621140c03a331c4440c050680046030a2d40837460041216200081608 0xec0ec50cb1c303903af45135040d45111040b2ee34434b38e264b6a42daa4909410aabb093ac26baea38e24b268369a0b9c93491909a592695040692419a8c53a315a68638e14414634618718534518b1a126284780624609d7de41079d70241008e6c069b00e38269a0040023420830803400970982596175822420950871861d55021824d14444104914444102c43c138e2cb30134c04b04b2492c42812492061841451c61841450420840000c2081000⟩,
  ⟨34,5,[ew136,ew143,ew146,ew149,ew151,ew161],decodeHints 0x120900a0a008241201018147a030197960030c0601e031289414052401008921900462011480c6c03168147e050102010020100466020c864060f010ac6002⟩,
  ⟨34,6,[ew136,ew143,ew146,ew149,ew151,ew156],localHints 6 0x3b0bb70bc24080707ad70689c3009128284407070c82c12188a4261e1b0b434151f8143e00060e0c01d1980432030403c5621140c00802 0x40e42f4b0beeb50490292b2b8acad248a8a228faa442a90f3ca41021d21d49239da4848822721d410a2798840820a94692518a1889080628df4a37e28814927e084142106081f41005c79d28a35c6c128a0586992086585c12080145954925544c04920104473d11d04003cf00c00e28a34c2c02801c8240189008207186003004045103080040⟩,
  ⟨34,6,[ew136,ew139,ew143,ew146,ew154,ew156],localHints 6 0xec2e351e9681a27128880e0e1484c3c3612040141c0c0242c32090c45a1a0a8fc0a1f0003032030403c5621140c008b60e8cc0202 0x3ec3ed46eb6cb0f44f32c32a451aacacc44c32932a3cfaa9a0c3cc15d9e446791d7454519259853e61659643cf1618e230c8a180530c0517de75f79144175d04e71a3dc68e3813cf68a6c131b04a29a30c0590571585c458114101355445151348045100f40b3902cf3c038e2cc34028d00c30b28a007008149207180140003004041103080040⟩,
  ⟨34,6,[ew136,ew139,ew143,ew146,ew151,ew154,ew156],localHints 5 0x183635000f422232d094080e148d8480a048606431168fc0a080c80c1e2b180046602 0x3c9ea7a9e277b3274636706362e6b5a09a56b4a56b499a468c53013de213de2738a6135825a549021000210039cc50106000820⟩,
  ⟨34,6,[ew136,ew139,ew143,ew145,ew146,ew151,ew161],decodeHints 0x18147a0301979620303014281b1a8d4ce031289414052401008921480c6c030206e2604120900a0a0082412010c0601e030086db801008c86201168147e050102010020c864060f0106e2402010ac6002010046602⟩,
  ⟨34,7,[ew136,ew139,ew143,ew145,ew146,ew151,ew156],localHints 6 0x1d85dbc5e1eb601a276e81a2d150a0444a220383852130f0d96a24080283818048de2832090c45a1a0a8fc0a1f0003032030403c2c385b82c5621140c0089d0e8cc0202 0x13313e95efae784d54d035035554c37743540d4d3db5d104d0ccdc8a555bcdbcd4d3c4dc2f4d334db8a410162b6a56daa2885555aabb054ec16baea4d3167a68410a2798541014d14d28a34d9452850559238a48d55418a205285f4e17d24814d37ce80142004e39f41004d04d79e34474134104d05b15c6c468114101765855561758055501350f4943d34c04923d044039101040f38e00d00d28a34c2c0280007008149207180140003004041103080040⟩,
  ⟨34,6,[ew48,ew136,ew139,ew143,ew146,ew151,ew156],decodeHints 0x3b0d8000c67030f5380011800d20615018442203800084332810020608004381c060001201008240232188040406308083e1f00030100201020042b180080401198080a050306c1a000180c2223070101c04008240209010200408⟩,
  ⟨34,7,[ew136,ew139,ew143,ew146,ew151,ew156,ew160],localHints 6 0x58c8502e1b1ab7406380b0f4460d5c1a4942a1101c1d186a84c6e100e024641218ad0c00b8bb5034060f8001854088205621140c0086e0e8cc0202 0x2baf4414d0eccea32a285683b238ec0ec50431c2f3903acbad2d4b6c4102eb2ecaea2e8a2938ea68a0b38e16715e51e7957855051659a14108659054108628c53a31628a138e16015e2de79f7852c568468174104405a75a04405c41070470140104d6da39b68d34138e6846812c104405a2da0440581596045c114129628050001500a50a01301141045244040000e3ca34f28e38034d28c2802c000c00a2ca007008149207180140003004041103080040⟩,
  ⟨34,6,[ew136,ew137,ew139,ew143,ew146,ew151,ew156],decodeHints 0x3b2f0005e2f0880c06000680c4a250501444220380052031b00c482402828381c0600152035400c0232188042a050a814000c00030060f018442604098100209008242a050a814000c00030060201898042b1800804010e8081002⟩,
  ⟨34,6,[ew136,ew139,ew143,ew146,ew151,ew152,ew156],decodeHints 0x360503014c6050d8140000178bc36050180c46110688c4e2712894140507010080e261301a0e0210cca04120900a0a080040210009f81201048040209008c86201168147e0552808040b011c81002040080408010ac6002010046602⟩,
  ⟨34,6,[ew16,ew136,ew139,ew143,ew146,ew151,ew161],localHints 5 0x2f089d44a484919c480a190c45a3f158c06614030146a1b2f00c2604008240408 0xef79cb2b76d6b39a2b0425c96292b55506210c431887390e2a82820004010802f704236858a5a92941cc6290a41886208020⟩,
  ⟨34,6,[ew16,ew47,ew136,ew139,ew143,ew146,ew151],localHints 5 0x360880e670e0c8621f060ac60332f0bc2225120285a3f0698c0003098100209010200c05 0x3ff5a7deea4dc39b7bba485290bac97184dc4318876a8c65a0e6994a20841c07bc0e035805a549420e6398a42906218820⟩,
  ⟨34,7,[ew16,ew136,ew139,ew143,ew146,ew151,ew156],localHints 6 0x708ec2ee02f0e05e23128880e0e12040141c19048622d0d0547e1f061505621140c03a336f8180b1b0685000110184c08374680412168d0081608 0xdccdc51cb1c2f35136e12d30430445130f3ec34db0f3cc34d265ae846ba25949451a29a8936a269a6834d24424a30a2842893091919e696799144696519b90536415b6c634d1441463061871853051841a226388784624609e81f4517de74245108d7006dc00d3426db01a00230209a0803000970982596175822420950871861d55021824c448145138f3c434d40f3ce34d1042c130b04a28424910a2812492061841451c61841450420840000c2081000⟩,
  ⟨34,6,[ew136,ew139,ew143,ew144,ew146,ew151,ew156],localHints 5 0xd45e27028185c070f0115aac0e06024442f8283e0006064060f108046602 0x10ad2339b14a8c16f755a88a22659955655688a2265996528aa0a7bce873885135a2135a26296a4a507318a400c6000c6000820⟩
]

def nodesBlock6 : Array Node := #[
  ⟨34,6,[ew136,ew139,ew143,ew146,ew151,ew153,ew156],localHints 5 0x14360017844da23348a9120b02038523608024303218818c2080c80c1e2b180046602 0x3deeabaaeab9cded463634636706baacaace7494e7289a06129e2139c2139c26b4a61316202920021000210039cc50106000820⟩,
  ⟨34,7,[ew70,ew136,ew139,ew143,ew146,ew151,ew156],localHints 6 0x363517b6db20d139a4942a1101c52130f0d83818048c824310f8303208078ac4228180746616030163a170a001be1101c701c043b8406e011c0681602 0xed4e4134d0d743933835330d34cb50b2f02f238ec70bcb38b22db894d326db084d326aac83ab22aa8938e227a682cba279882cb1071064d31871844c411e9633a58de78438e8db9042e411b6e32cb1071212228478042040030024d30830804c000e7dc79f70e38079e70b7406dd00b2dc6db01801921a6585c02000160071041d65401005144814d23d040338e45040f38e3433012cb0492432082892412081461871041c61851040420830000c2081000⟩,
  ⟨34,6,[ew106,ew136,ew139,ew146,ew151,ew156,ew161],localHints 5 0x9444171a844ce1b3696936100c12cc219078cc168b070108603048041002 0x1ad6734c5c96b1095a1093910431885180843189ef590010800e680010818c22c025012631d06398c7310a41886208020⟩,
  ⟨34,6,[ew71,ew136,ew139,ew143,ew146,ew151,ew156],decodeHints 0xc6061a8185e2f0300c069c0680cd20615018984c0683852031b00c020608004027e0480430180780c02321880404063080804720400832190183c042b180080401198080a050a01800000b83422030204c0813048041201040081002⟩,
  ⟨34,7,[ew136,ew139,ew143,ew146,ew151,ew156,ew161],localHints 6 0xa001c0d63e600b380ce116f1b446da2d479708b070a4261e1b0dd36100c0242832090c4164b0d100c21b0bac832030403c5621140c008780e8cc0202 0x19675415d736743d5d334103d93d967233132cbecb30b0cbcc31032cbadb1040cacc3193293eaa689cc3cc9999455451591595551591634248d98c54058d98c53c51591633e31608a130c8607c530c04405a79a68468178104405c41d70470140105905a3da6846813c168a6c131b04a29a30c0590571585c458114101200b54b2d22c05400120134144d244040000f00b38b2cf2c03802cc34028d00c30b28a007008149207180140003004041103080040⟩,
  ⟨34,6,[ew136,ew139,ew143,ew146,ew147,ew151,ew156],localHints 5 0x763502850223d0680cd22a1101c260408070123218818c21f00030102b180046602 0xfde1f7b56ae7b9d59562e7b9ed6aaa8a9ce478463084630129e2738c76884d6884d1316202920420e628005280050106000820⟩,
  ⟨34,7,[ew47,ew136,ew139,ew143,ew146,ew151,ew156],localHints 6 0x76e13388c1a27458880e29098786c9b0e0601232090c4961a3087c18190403c5621140c03a330d8142e00900442c030a0380880080dc02401c2dc1602 0xb2f50d34d02d031330ed333934cc0cc331332410cb1c0c40c24b24a4ef28b2894c92adb8942e26db4a41026ab2b30caeaa4930c1481474e81c81c54c515d9e542795d74541095a98532615a6a530c14b1632648c88852450040204e18047c04c001079b75e6d040075d6cc70069c00c31b69a0170182596175802400150081452155001402cb4814d22c344141034e38330c3ce38d30c04a28b2492ca2812491871c81452071c6145044044000103081000⟩,
  ⟨34,8,[ew136,ew139,ew143,ew146,ew151,ew156],decodeHints 0x9600036000a05c0a3b9585c36350a0000a009500c0c2f948440a2f940440c069380c0a030a00c1a039308c00009288c1a270a00c0003920101425058380a255c038140a058100a050a0380e220581000220a0100e070583800005a8103c290584c06039184c3c360581006031b8040a241b84014241b8400a051b804140a0a004181c1b824001c1b824180c0a00400001b8241e181b80406181b8041e0f1b8240603058046e011b84808321b8486e310580408015b8082a2d058680a05910682a3f058080a050a008001f05820181f20020000005808180c908200619058081e195a0080603058201e0f05808500205884082b0588450300580808021b8083a02058dc02011b8dc3a33058080202⟩
]

def nodesGet (i : Nat) : Option Node :=
  if i < 48 then
    if i < 16 then
      nodesBlock0[(i-0)]?
    else
      if i < 32 then
        nodesBlock1[(i-16)]?
      else
        nodesBlock2[(i-32)]?
  else
    if i < 80 then
      if i < 64 then
        nodesBlock3[(i-48)]?
      else
        nodesBlock4[(i-64)]?
    else
      if i < 96 then
        nodesBlock5[(i-80)]?
      else
        nodesBlock6[(i-96)]?

def fastViews : QFast.Table View := ⟨35,viewsGet⟩

def fastNodes : QFast.Table Node := ⟨104,nodesGet⟩

end SignedProjection



namespace SignedProjection

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_0 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 0 16 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_16 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 16 16 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_32 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 32 3 = true := by decide +kernel

theorem joinRoots_0_0 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 0 32 = true :=
  @QFast.merge_blocks (QFast.checkRootAt fastViews fastNodes) 0 16 16 blockRoots_0 blockRoots_16

theorem joinRoots_1_0 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 0 35 = true :=
  @QFast.merge_blocks (QFast.checkRootAt fastViews fastNodes) 0 32 3 joinRoots_0_0 blockRoots_32

theorem certifiedRoots : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 0 35 = true := joinRoots_1_0

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 12 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 24 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_36 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 36 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 48 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_60 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 60 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_72 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 72 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_84 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 84 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_96 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 96 8 = true := by decide +kernel

theorem joinNodes_0_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 12 12 blockNodes_0 blockNodes_12

theorem joinNodes_0_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 24 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 24 12 12 blockNodes_24 blockNodes_36

theorem joinNodes_0_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 48 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 48 12 12 blockNodes_48 blockNodes_60

theorem joinNodes_0_72 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 72 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 72 12 12 blockNodes_72 blockNodes_84

theorem joinNodes_1_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 48 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 24 24 joinNodes_0_0 joinNodes_0_24

theorem joinNodes_1_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 48 48 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 48 24 24 joinNodes_0_48 joinNodes_0_72

theorem joinNodes_2_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 96 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 48 48 joinNodes_1_0 joinNodes_1_48

theorem joinNodes_3_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 104 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 96 8 joinNodes_2_0 blockNodes_96

theorem certifiedNodes : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 104 = true := joinNodes_3_0

end SignedProjection

namespace SignedProjection
def bMatches (z : Option View) : Bool :=
  match z with
  | none => false
  | some v => vg v == (0xfffefffcfefeee00 : Word) && vk v == 8 && (vs v).toFinset == Direct64.cols.toFinset

theorem rootNegative : ¬ CoreSigned.build signedOps (0xfffefffcfefeee00 : BitVec 64) 8 Direct64.cols.toFinset := by
  have shape : bMatches (QFast.get fastViews 34) = true := by decide +kernel
  cases ev : QFast.get fastViews 34 with
  | none => simp [ev, bMatches] at shape
  | some v =>
    have valid := QFast.certified_view fastViews fastNodes certifiedRoots certifiedNodes ev
    simp only [ev,bMatches,Bool.and_eq_true,beq_iff_eq] at shape
    change ¬ CoreSigned.build signedOps (vg v) (vk v) (vs v).toFinset at valid
    rwa [shape.1.1,shape.1.2,shape.2] at valid
end SignedProjection
end PEqualNP.Outside.L_meta_10854_aux

open PEqualNP.Outside.L_meta_10854_aux in
theorem PEqualNP.Outside.L_meta_10854 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  SevenFinish.finish SignedProjection.rootNegative
