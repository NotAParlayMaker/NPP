import PEqualNP.Defs

-- The witness has twelve binary gates. Any circuit with a NOT and fewer gates
-- would have at most ten binary gates even with every negation available for free.
-- Finite signed-circuit certificates below exclude that possibility.
-- Signed-wire search and gate projections adapt the project’s Apache 2.0 proofs.
namespace PEqualNP.Outside.L_meta_12150_aux
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
namespace SignedProjection.QFast

def rowAt (m : Array Nat) (k : Fin 64) := Fin.ofNat 64 (m[k.val]?.getD 0)
def rowWord (m : Array Nat) (w : Word) : Word :=
  (BitVec.ofBoolListLE (List.ofFn (fun k : Fin 64 => w[(rowAt m k).val]))).cast List.length_ofFn

theorem rowWord_bit (m : Array Nat) (w : Word) (j : Nat) (hj : j < 64) :
    (rowWord m w)[j] = w[(rowAt m ⟨j,hj⟩).val] := by
  rw [← BitVec.getLsbD_eq_getElem hj]
  simp only [rowWord, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj, dite_true, Option.getD_some]

theorem rowWord_and (m : Array Nat) (x y : Word) : rowWord m (x &&& y) = rowWord m x &&& rowWord m y :=
  BitVec.eq_of_getElem_eq fun j hj => by simp only [rowWord_bit,BitVec.getElem_and]
theorem rowWord_or (m : Array Nat) (x y : Word) : rowWord m (x ||| y) = rowWord m x ||| rowWord m y :=
  BitVec.eq_of_getElem_eq fun j hj => by simp only [rowWord_bit,BitVec.getElem_or]
theorem rowWord_not (m : Array Nat) (x : Word) : rowWord m (~~~x) = ~~~rowWord m x :=
  BitVec.eq_of_getElem_eq fun j hj => by simp only [rowWord_bit,BitVec.getElem_not]

def viewMap (m : Array Nat) (v : View) (w : Word) := signedPin (vm v) (va v) (rowWord m w)
theorem viewMap_ops (m : Array Nat) (v : View) {a b c : Word} (hc : c ∈ signedOps a b) :
    viewMap m v c ∈ signedOps (viewMap m v a) (viewMap m v b) := by
  apply signedPin_ops
  simp only [signedOps,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hc ⊢
  rcases hc with rfl|rfl|rfl|rfl
  · exact Or.inl (rowWord_and ..)
  · exact Or.inr (Or.inl (rowWord_or ..))
  · exact Or.inr (Or.inr (Or.inl (by rw [rowWord_and,rowWord_not])))
  · exact Or.inr (Or.inr (Or.inr (by rw [rowWord_and,rowWord_not])))

def viewAliasOK (m : Array Nat) (src dst : View) : Bool :=
  (vg dst != 0) && (viewMap m dst (vg src) == vg dst) && decide (vk src ≤ vk dst) &&
  (vs src).all fun w => viewMap m dst w == 0 || (vs dst).contains (viewMap m dst w)

theorem viewAlias_sound {m : Array Nat} {src dst : View} (yes : ViewOK dst)
    (valid : viewAliasOK m src dst = true) : ViewOK src := by
  simp only [viewAliasOK,Bool.and_eq_true, bne_iff_ne,beq_iff_eq,decide_eq_true_eq] at valid
  obtain ⟨⟨⟨nz,go⟩,le⟩,all⟩ := valid
  intro run
  obtain ⟨S,sub,path⟩ := CoreSigned.compress run
  have ng := fun h : viewMap m dst (vg src) = 0 => nz (go.symm.trans h)
  obtain ⟨j,hj,T,ts,tail⟩ := projected (viewMap m dst) signedOps signedOps _ ng
    (viewMap_ops m dst) zero_left zero_right equal_inputs path
  have supply : T ⊆ (vs dst).toFinset := by
    intro y hy
    obtain ⟨pn,w,hw,rfl⟩ := (avail_mem _).mp (ts hy)
    have h := List.all_eq_true.mp all w (List.mem_toFinset.mp (sub hw))
    simp only [Bool.or_eq_true,beq_iff_eq] at h
    exact List.mem_toFinset.mpr (List.contains_iff_mem.mp (h.resolve_left pn))
  rw [go] at tail
  exact yes (pad_build (by omega) (live_build tail supply))

abbrev AliasTable := Nat → Option (Nat × Array Nat)
def symCheckRoot (aliases : AliasTable) (views : Table View) (nodes : Table Node) (i : Nat) : Bool :=
  match get views i with
  | none => true
  | some v => match aliases i with
    | none => evalRoot views nodes i v
    | some (j,m) => decide (j < i) &&
      match get views j with
      | none => false
      | some w => viewAliasOK m v w

theorem symCertified (aliases : AliasTable) (views : Table View) (nodes : Table Node)
    (roots : passBlock (symCheckRoot aliases views nodes) 0 views.1 = true)
    (states : passBlock (checkNodeAt views nodes) 0 nodes.1 = true)
    {i : Nat} {v : View} (hv : get views i = some v) : ViewOK v := by
  have allNodes (j : Nat) (a : Node) (ha : get nodes j = some a) : evalNode views nodes a = true := by
    have hj : j < nodes.1 := by by_contra! lo; simp [get, Nat.not_lt_of_ge lo] at ha
    have ok := block_at _ states (i := j) (Nat.zero_le _) (by omega)
    simpa [checkNodeAt,ha] using ok
  induction i using Nat.strong_induction_on generalizing v with
  | ind i ih =>
    have hi : i < views.1 := by by_contra! lo; simp [get, Nat.not_lt_of_ge lo] at hv
    have ok := block_at _ roots (i := i) (Nat.zero_le _) (by omega)
    simp only [symCheckRoot,hv] at ok
    cases he : aliases i with
    | none =>
      exact view_from_earlier views nodes i v hv ih (by simpa only [he] using ok) allNodes
    | some x =>
      rcases x with ⟨j,m⟩
      simp only [he,Bool.and_eq_true,decide_eq_true_eq] at ok
      cases hh : get views j with
      | none => simp [hh] at ok
      | some w => exact viewAlias_sound (ih j ok.1 hh) (by simpa only [hh] using ok.2)

end SignedProjection.QFast


namespace LowerSymSix
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.and,[0,1]⟩, ⟨.or,[2,6]⟩, ⟨.or,[3,6]⟩, ⟨.and,[4,5]⟩, ⟨.or,[0,1]⟩, ⟨.and,[7,9]⟩, ⟨.and,[2,8]⟩, ⟨.or,[3,11]⟩, ⟨.or,[4,5]⟩, ⟨.and,[10,13]⟩, ⟨.or,[12,15]⟩, ⟨.and,[14,16]⟩],17⟩

theorem size : witness.size = 12 := rfl

theorem monotone : Monotone2 witness := by
  simp [Monotone2,witness]

set_option maxRecDepth 16000 in
theorem correct : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) =
    Nat.testBit (4276682368 * 2 ^ 32 + 4269801472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel

end LowerSymSix

namespace Direct64
open PEqualNP.CircuitLowerBounds SignedProjection
abbrev W := BitVec 64
abbrev basicOps (a b : W) := signedOps a b
abbrev goal : W := ~~~0xfee8fe80fe800000
open CoreSigned (build)
def tableB (x : Fin 6 → Bool) :=
  Nat.testBit (4276682368 * 2 ^ 32 + 4269801472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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

theorem sample64 : ∀ k : Fin 64, tableB (fun i => (cols.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
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

theorem low (reject : ¬ build basicOps (0xfee8fe80fe800000 : W) 10 cols.toFinset)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = tableB x) : 10 < binaryCost gs := by
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

namespace LowerSymSix
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem finish
    (reject : ¬ CoreSigned.build SignedProjection.signedOps (0xfee8fe80fe800000 : BitVec 64) 10 Direct64.cols.toFinset) :
∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276682368 * 2 ^ 32 + 4269801472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276682368 * 2 ^ 32 + 4269801472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  rintro s ⟨C, hg, hs, he⟩
  by_cases neg : ∃ g ∈ C.gates, g.op = .not
  · obtain ⟨g, hm, op⟩ := neg
    have lo := Direct64.low reject C.gates C.output hg he
    have proper : Direct64.binaryCost C.gates < C.gates.length := by
      apply List.length_filter_lt_length_iff_exists.mpr
      exact ⟨g, hm, by simp [Direct64.isBinary, op]⟩
    have cap : C.gates.length ≤ s := hs
    exact ⟨witness, monotone, by rw [size]; omega, correct⟩
  · refine ⟨C, ?_, hs, he⟩
    intro g hm
    obtain ⟨hop, hin⟩ := hg g hm
    refine ⟨?_, hin⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (neg ⟨g, hm, h⟩).elim

end LowerSymSix


namespace SignedProjection

def ew0 : Word := 0xaa0000

def ew1 : Word := 0xcc0000

def ew2 : Word := 0xf00000

def ew3 : Word := 0xaa00000

def ew4 : Word := 0xcc00000

def ew5 : Word := 0xf000000

def ew6 : Word := 0x22880000

def ew7 : Word := 0x30c00000

def ew8 : Word := 0x33000000

def ew9 : Word := 0x44880000

def ew10 : Word := 0x50a00000

def ew11 : Word := 0x55000000

def ew12 : Word := 0x82820000

def ew13 : Word := 0x84840000

def ew14 : Word := 0x88880000

def ew15 : Word := 0x90900000

def ew16 : Word := 0x99000000

def ew17 : Word := 0xa0a00000

def ew18 : Word := 0xa5000000

def ew19 : Word := 0xaaaa0000

def ew20 : Word := 0xaaaaaaaa

def ew21 : Word := 0xc0c00000

def ew22 : Word := 0xc3000000

def ew23 : Word := 0xcccc0000

def ew24 : Word := 0xcccccccc

def ew25 : Word := 0xeeee0000

def ew26 : Word := 0xf0f00000

def ew27 : Word := 0xf0f0f0f0

def ew28 : Word := 0xfafa0000

def ew29 : Word := 0xfcfc0000

def ew30 : Word := 0xff000000

def ew31 : Word := 0xff00ff00

def ew32 : Word := 0xffff0000

def ew33 : Word := 0x8800880088

def ew34 : Word := 0xa000a000a0

def ew35 : Word := 0x444488880000

def ew36 : Word := 0x5050a0a00000

def ew37 : Word := 0x5500aa000000

def ew38 : Word := 0x555500000000

def ew39 : Word := 0xaaaa00000000

def ew40 : Word := 0xaaaa0000aaaa

def ew41 : Word := 0xcccc00000000

def ew42 : Word := 0xcccc0000cccc

def ew43 : Word := 0xf0f000000000

def ew44 : Word := 0xf0f00000f0f0

def ew45 : Word := 0xff0000000000

def ew46 : Word := 0xff000000ff00

def ew47 : Word := 0xffff00000000

def ew48 : Word := 0x8000800880088

def ew49 : Word := 0x8008800080088

def ew50 : Word := 0x8008800880088

def ew51 : Word := 0xa000000aa0000

def ew52 : Word := 0xa00000a000000

def ew53 : Word := 0xa000a0a000a00

def ew54 : Word := 0xa00aa00000000

def ew55 : Word := 0xa0a00000a0a00

def ew56 : Word := 0xc00000c000000

def ew57 : Word := 0xc000c0c000c00

def ew58 : Word := 0xc0c00000c0c00

def ew59 : Word := 0xf000000000000

def ew60 : Word := 0xf0000000f0000

def ew61 : Word := 0xf00000f000000

def ew62 : Word := 0xf000f00000000

def ew63 : Word := 0xf0f0000000000

def ew64 : Word := 0x20002000a000a0

def ew65 : Word := 0x2000a0002000a0

def ew66 : Word := 0x2000a000a000a0

def ew67 : Word := 0x22000000aa0000

def ew68 : Word := 0x2200aa00000000

def ew69 : Word := 0x2a0000002a0000

def ew70 : Word := 0x2a000000aa0000

def ew71 : Word := 0x2a002a00000000

def ew72 : Word := 0x2a00aa00000000

def ew73 : Word := 0x80000000800000

def ew74 : Word := 0x80008000000000

def ew75 : Word := 0x80008000800080

def ew76 : Word := 0x88000000000000

def ew77 : Word := 0x88000000880000

def ew78 : Word := 0x88004400880044

def ew79 : Word := 0x88008800000000

def ew80 : Word := 0x88008800880088

def ew81 : Word := 0x88440000884400

def ew82 : Word := 0xa0000000000000

def ew83 : Word := 0xa0000000a00000

def ew84 : Word := 0xa0005000a00050

def ew85 : Word := 0xa000a000000000

def ew86 : Word := 0xa000a000a000a0

def ew87 : Word := 0xa0500000a05000

def ew88 : Word := 0xaa000000000000

def ew89 : Word := 0xaa000000aa0000

def ew90 : Word := 0xaa005500000000

def ew91 : Word := 0xaa00aa00000000

def ew92 : Word := 0xaa00aa00aa00aa

def ew93 : Word := 0xaa550000000000

def ew94 : Word := 0xc000c000c000c0

def ew95 : Word := 0xcc000000cc0000

def ew96 : Word := 0xcc00cc00000000

def ew97 : Word := 0xcc00cc00cc00cc

def ew98 : Word := 0xf0000000f00000

def ew99 : Word := 0xf000f000000000

def ew100 : Word := 0xf000f000f000f0

def ew101 : Word := 0xff000000000000

def ew102 : Word := 0xff000000ff0000

def ew103 : Word := 0xff00ff00000000

def ew104 : Word := 0x208020802080208

def ew105 : Word := 0x300030003000300

def ew106 : Word := 0x30c0000030c0000

def ew107 : Word := 0x30c030c00000000

def ew108 : Word := 0x408040804080408

def ew109 : Word := 0x500050005000500

def ew110 : Word := 0x50a0000050a0000

def ew111 : Word := 0x50a050a00000000

def ew112 : Word := 0x800040008000400

def ew113 : Word := 0x808000008080000

def ew114 : Word := 0x808020208080202

def ew115 : Word := 0x808040400000000

def ew116 : Word := 0x808040408080404

def ew117 : Word := 0x808080802020202

def ew118 : Word := 0x808080804040404

def ew119 : Word := 0x808080808080808

def ew120 : Word := 0x900090009000900

def ew121 : Word := 0x909000009090000

def ew122 : Word := 0x909090900000000

def ew123 : Word := 0xa0005000a000500

def ew124 : Word := 0xa000a0005000500

def ew125 : Word := 0xa000a000a000a00

def ew126 : Word := 0xa0a000000000a0a

def ew127 : Word := 0xa0a000005050000

def ew128 : Word := 0xa0a00000a0a0000

def ew129 : Word := 0xa0a050500000000

def ew130 : Word := 0xa0a0a0a00000000

def ew131 : Word := 0xa0a0a0a0a0a0a0a

def ew132 : Word := 0xc0003000c000300

def ew133 : Word := 0xc000c0003000300

def ew134 : Word := 0xc000c000c000c00

def ew135 : Word := 0xc0c000000000c0c

def ew136 : Word := 0xc0c000003030000

def ew137 : Word := 0xc0c00000c0c0000

def ew138 : Word := 0xc0c030300000000

def ew139 : Word := 0xc0c0c0c00000000

def ew140 : Word := 0xc0c0c0c0c0c0c0c

def ew141 : Word := 0xf00000000000f00

def ew142 : Word := 0xf0000000f000000

def ew143 : Word := 0xf000f0000000000

def ew144 : Word := 0xf000f000f000f00

def ew145 : Word := 0xf0f000000000000

def ew146 : Word := 0xf0f00000f0f0000

def ew147 : Word := 0xf0f0f0f00000000

def ew148 : Word := 0x2020101020201010

def ew149 : Word := 0x2020202020202020

def ew150 : Word := 0x2200110022001100

def ew151 : Word := 0x2200220022002200

def ew152 : Word := 0x2222000022220000

def ew153 : Word := 0x2222111100000000

def ew154 : Word := 0x2222222200000000

def ew155 : Word := 0x2222222222222222

def ew156 : Word := 0x3000300030003000

def ew157 : Word := 0x3030000030300000

def ew158 : Word := 0x3030303000000000

def ew159 : Word := 0x3030303030303030

def ew160 : Word := 0x3300000033000000

def ew161 : Word := 0x3300330000000000

def ew162 : Word := 0x3300330033003300

def ew163 : Word := 0x3333000000000000

def ew164 : Word := 0x3333000033330000

def ew165 : Word := 0x3333333300000000

def ew166 : Word := 0x4040404040404040

def ew167 : Word := 0x4444000044440000

def ew168 : Word := 0x4444444444444444

def ew169 : Word := 0x5000500050005000

def ew170 : Word := 0x5050000050500000

def ew171 : Word := 0x5050505000000000

def ew172 : Word := 0x5050505050505050

def ew173 : Word := 0x5500000055000000

def ew174 : Word := 0x5500550055005500

def ew175 : Word := 0x5555000000000000

def ew176 : Word := 0x5555000055550000

def ew177 : Word := 0x5555555500000000

def ew178 : Word := 0x8080404080804040

def ew179 : Word := 0x8080808080808080

def ew180 : Word := 0x8282000082820000

def ew181 : Word := 0x8484000084840000

def ew182 : Word := 0x8800440000880044

def ew183 : Word := 0x8800440088004400

def ew184 : Word := 0x8800880088008800

def ew185 : Word := 0x8888000088880000

def ew186 : Word := 0x8888222288882222

def ew187 : Word := 0x8888444400000000

def ew188 : Word := 0x8888444488884444

def ew189 : Word := 0x8888888800000000

def ew190 : Word := 0x8888888888888888

def ew191 : Word := 0x9090000090900000

def ew192 : Word := 0x9900000099000000

def ew193 : Word := 0x9999000000000000

def ew194 : Word := 0xa000500000a00050

def ew195 : Word := 0xa0005000a0005000

def ew196 : Word := 0xa000a000a000a000

def ew197 : Word := 0xa0a00000a0a00000

def ew198 : Word := 0xa0a0505000000000

def ew199 : Word := 0xa0a05050a0a05050

def ew200 : Word := 0xa0a0a0a000000000

def ew201 : Word := 0xa0a0a0a0a0a0a0a0

def ew202 : Word := 0xa5000000a5000000

def ew203 : Word := 0xa5a5000000000000

def ew204 : Word := 0xaa00000000aa0000

def ew205 : Word := 0xaa000000aa000000

def ew206 : Word := 0xaa00550000000000

def ew207 : Word := 0xaa005500aa005500

def ew208 : Word := 0xaa00aa00aa00aa00

def ew209 : Word := 0xaaaa000000000000

def ew210 : Word := 0xaaaa0000aaaa0000

def ew211 : Word := 0xaaaa555500000000

def ew212 : Word := 0xaaaaaaaa00000000

def ew213 : Word := 0xaaaaaaaaaaaaaaaa

def ew214 : Word := 0xc000c000c000c000

def ew215 : Word := 0xc0c00000c0c00000

def ew216 : Word := 0xc0c03030c0c03030

def ew217 : Word := 0xc0c0c0c000000000

def ew218 : Word := 0xc0c0c0c0c0c0c0c0

def ew219 : Word := 0xc3000000c3000000

def ew220 : Word := 0xc3c3000000000000

def ew221 : Word := 0xcc000000cc000000

def ew222 : Word := 0xcc003300cc003300

def ew223 : Word := 0xcc00cc00cc00cc00

def ew224 : Word := 0xcccc000000000000

def ew225 : Word := 0xcccc0000cccc0000

def ew226 : Word := 0xcccc333300000000

def ew227 : Word := 0xcccccccc00000000

def ew228 : Word := 0xcccccccccccccccc

def ew229 : Word := 0xeeee0000eeee0000

def ew230 : Word := 0xf0000000f0000000

def ew231 : Word := 0xf000f000f000f000

def ew232 : Word := 0xf0f0000000000000

def ew233 : Word := 0xf0f00000f0f00000

def ew234 : Word := 0xf0f0f0f000000000

def ew235 : Word := 0xf0f0f0f0f0f0f0f0

def ew236 : Word := 0xfafa0000fafa0000

def ew237 : Word := 0xfcfc0000fcfc0000

def ew238 : Word := 0xff00000000000000

def ew239 : Word := 0xff000000ff000000

def ew240 : Word := 0xff00ff0000000000

def ew241 : Word := 0xff00ff00ff00ff00

def ew242 : Word := 0xffff000000000000

def ew243 : Word := 0xffff0000ffff0000

def ew244 : Word := 0xffffffff00000000

def labelsBlock0 : Array Nat := #[
  0x174c,
  0x1944,
  0x1754,
  0x334c,
  0x1086,
  0x171c,
  0x271c,
  0x1960,
  0x1758,
  0x109a,
  0x1a60,
  0x1a48,
  0x1c60,
  0x3554,
  0x10a6,
  0x33c4
]

def labelsBlock1 : Array Nat := #[
  0x1744,
  0x10c6,
  0x278c,
  0x2794,
  0x1c50,
  0x338c,
  0x35c4,
  0x10f2,
  0x330c,
  0x101e,
  0x1940,
  0x1714,
  0x170c,
  0x2714,
  0x270c,
  0x10d6
]

def labelsBlock2 : Array Nat := #[
  0x1924,
  0x2924,
  0x1a40,
  0x110a,
  0x33c8,
  0x1c40,
  0x3658,
  0x3344,
  0x1022,
  0x2a28,
  0x3594,
  0x3544,
  0x1750,
  0x1748,
  0x1026,
  0x1072
]

def labelsBlock3 : Array Nat := #[
  0x35d0,
  0x1920,
  0x2aa0,
  0x36c8,
  0x105e,
  0x39c4,
  0x36d0,
  0x10da,
  0x3514,
  0x102a,
  0x2ca0,
  0x1032,
  0x1900,
  0x1718,
  0x3348,
  0x10e6
]

def labelsBlock4 : Array Nat := #[
  0x2984,
  0x1904,
  0x10de,
  0x1a28,
  0x108a,
  0x103a,
  0x1052,
  0x19c4,
  0x2784,
  0x3944,
  0x3384,
  0x1704,
  0x2a20,
  0x2904,
  0x1b4c,
  0x1d54
]

def labelsBlock5 : Array Nat := #[
  0x3584,
  0x2a88,
  0x4100f2,
  0x2798,
  0x1e58,
  0x1056,
  0x29a0,
  0x2c30,
  0x110e,
  0x1700,
  0x2704,
  0x3304,
  0x1042,
  0x51005e,
  0x52005e,
  0x52105e
]

def labelsBlock6 : Array Nat := #[
  0x1740,
  0x3504,
  0x61005e,
  0x71005e,
  0x3648,
  0x62005e,
  0x72005e,
  0x62105e,
  0x72105e,
  0x1096,
  0x41010a,
  0x10f6,
  0x1954,
  0x2c20,
  0x14401005e,
  0x41005e
]

def labelsBlock7 : Array Nat := #[
  0x14802005e,
  0x42005e,
  0x14842105e,
  0x42105e,
  0x2718,
  0x105a,
  0x107e,
  0x108e,
  0x10aa,
  0x1092,
  0x4100e6,
  0x4200e6,
  0x4210e6,
  0x1a00,
  0x1a58,
  0x1a20
]

def labelsBlock8 : Array Nat := #[
  0x10b6,
  0x3308,
  0x1b44,
  0x1d44,
  0x2920,
  0x2a08,
  0x1710,
  0x1708,
  0x10fa,
  0x10e2,
  0x104a,
  0x109e,
  0x1112,
  0x2a00,
  0x1e48,
  0x2c90
]

def labelsBlock9 : Array Nat := #[
  0x3550,
  0x3300,
  0x2900,
  0x100e,
  0x1012,
  0x1016,
  0x10ca,
  0x144010032,
  0x3650,
  0x410032,
  0x510032,
  0x610032,
  0x710032,
  0x148020032,
  0x420032,
  0x520032
]

def labelsBlock10 : Array Nat := #[
  0x620032,
  0x720032,
  0x148421032,
  0x421032,
  0x521032,
  0x621032,
  0x721032,
  0x10ea,
  0x1950,
  0x1a50,
  0x194c,
  0x51,
  0x59,
  0x3d,
  0x49,
  0x7d
]

def labelsBlock11 : Array Nat := #[
  0x75,
  0xb5,
  0xad,
  0x1046,
  0x1c00,
  0x3500,
  0x2700,
  0x100a,
  0x1006,
  0x1002,
  0x55,
  0x5d,
  0x61,
  0x65,
  0x81,
  0x85
]

def labelsBlock12 : Array Nat := #[
  0x89,
  0x99,
  0x9d,
  0xb9,
  0xbd,
  0xcd,
  0x3698,
  0x106a,
  0x1066,
  0x106e,
  0x1062,
  0x1076,
  0x107a,
  0x104e,
  0x1036,
  0x1082
]

def labelsBlock13 : Array Nat := #[
  0x103e,
  0x1b28,
  0x1d30,
  0x39a0,
  0x3388,
  0x1440100de,
  0xf5,
  0x4100de,
  0x5100de,
  0x6100de,
  0x7100de,
  0x1480200de,
  0x109,
  0x4200de,
  0x5200de,
  0x6200de
]

def labelsBlock14 : Array Nat := #[
  0x7200de,
  0x1484210de,
  0x4210de,
  0x11d,
  0x5210de,
  0x6210de,
  0x7210de,
  0x10ae,
  0x10ee,
  0x4100f6,
  0x10ba,
  0x4200f6,
  0x10a2,
  0x1c20,
  0x4210f6,
  0x10ce
]

def labelsBlock15 : Array Nat := #[
  0x1720,
  0x3600,
  0x2708,
  0x2710,
  0x2c00,
  0x1a4c,
  0x1b48,
  0x1c54,
  0x1d50,
  0x1c58,
  0x1e50,
  0x5,
  0x9,
  0xd,
  0x11,
  0x15
]

def labelsBlock16 : Array Nat := #[
  0x19,
  0x1d,
  0x21,
  0x25,
  0x29,
  0x2d,
  0x31,
  0x39,
  0x45,
  0x41,
  0x4d,
  0x71,
  0x6d,
  0x79,
  0x91,
  0x95
]

def labelsBlock17 : Array Nat := #[
  0xa9,
  0xa5,
  0xb1,
  0xc5,
  0xc9,
  0xd5,
  0xd9,
  0x69,
  0x8d,
  0xa1,
  0xc1,
  0xd1,
  0xdd,
  0x2a80,
  0x1928,
  0x1b20
]

def labelsBlock18 : Array Nat := #[
  0x2c80,
  0x1930,
  0x1d20,
  0x7230c2,
  0x3920,
  0xed,
  0x10c2,
  0x10b2,
  0x10be,
  0x10d2,
  0xf9,
  0xfd,
  0x101,
  0x105,
  0x10d,
  0x111
]

def labelsBlock19 : Array Nat := #[
  0x115,
  0x119,
  0x121,
  0x125,
  0x129,
  0x12d,
  0x410112,
  0x10fe,
  0x420112,
  0x1102,
  0x421112,
  0x1106,
  0x135,
  0x139,
  0x13d,
  0x1
]

def labelsBlock20 : Array Nat := #[
  0x35,
  0x101a,
  0xe1,
  0x1728,
  0x1730,
  0x1738,
  0x102e,
  0xe5,
  0xe9,
  0xf1,
  0x3640,
  0x3540,
  0x3340,
  0x131,
  0x141
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
  ⟨0xff00000,⟨20,by decide⟩,0xe800000,[ew3,ew4,ew5],3,decodeHints 0x9f820042c362a1522c⟩,
  ⟨0x33cc0000,⟨18,by decide⟩,0x32800000,[ew6,ew7,ew8],3,decodeHints 0x0⟩,
  ⟨0x55aa0000,⟨17,by decide⟩,0x54800000,[ew9,ew10,ew11],3,decodeHints 0x0⟩,
  ⟨0x99990000,⟨16,by decide⟩,0x98800000,[ew14,ew15,ew16],3,decodeHints 0x0⟩,
  ⟨0xa5a50000,⟨16,by decide⟩,0xa4800000,[ew13,ew17,ew18],3,decodeHints 0x0⟩,
  ⟨0xc3c30000,⟨16,by decide⟩,0xc2800000,[ew12,ew21,ew22],3,decodeHints 0x0⟩,
  ⟨0xf00000f000000,⟨24,by decide⟩,0x800000e000000,[ew52,ew56,ew59],3,decodeHints 0x0⟩,
  ⟨0x88008800880088,⟨3,by decide⟩,0x88008000800000,[ew75,ew77,ew79],3,decodeHints 0x0⟩,
  ⟨0xa000a000a000a0,⟨5,by decide⟩,0xa0008000800000,[ew75,ew83,ew85],3,decodeHints 0x0⟩,
  ⟨0xaa000000aa0000,⟨17,by decide⟩,0xa8000000800000,[ew77,ew83,ew88],3,decodeHints 0x0⟩,
  ⟨0xaa00aa00000000,⟨33,by decide⟩,0xa8008000000000,[ew79,ew85,ew88],3,decodeHints 0x0⟩,
  ⟨0x808040408080404,⟨2,by decide⟩,0x808040008000000,[ew112,ew113,ew115],3,decodeHints 0x0⟩,
  ⟨0xffff0000,⟨16,by decide⟩,0xfe800000,[ew19,ew23,ew26,ew30],5,decodeHints 0xa0020042c000b4206000868441a128684460⟩,
  ⟨0xf000f0f000f00,⟨8,by decide⟩,0x800000e000000,[ew53,ew57,ew61,ew62],4,localHints 3 0x5048e0a03880fe31 0xce3408ae3408⟩,
  ⟨0xaa00aa00aa00aa,⟨1,by decide⟩,0xa8008000800000,[ew80,ew86,ew89,ew91],6,decodeHints 0xa100800100286c384b030743c5a0c16cc24b⟩,
  ⟨0xaa550000aa5500,⟨8,by decide⟩,0xa8540000800000,[ew81,ew87,ew89,ew93],4,decodeHints 0x170080010a2d1286f014930da4c14930daf0⟩
]

def viewsBlock1 : Array View := #[
  ⟨0xa0a05050a0a0505,⟨0,by decide⟩,0xa0804000a000000,[ew116,ew123,ew128,ew129],4,decodeHints 0xa30c80201188c4783c149310a8d40a44783c⟩,
  ⟨0x5555aaaa0000,⟨17,by decide⟩,0x5400aa800000,[ew35,ew36,ew37,ew38],5,decodeHints 0x0⟩,
  ⟨0xffff00000000,⟨32,by decide⟩,0xfe8000000000,[ew39,ew41,ew43,ew45],5,decodeHints 0x0⟩,
  ⟨0xf0f00000f0f00,⟨8,by decide⟩,0x80e0000000000,[ew55,ew58,ew60,ew63],4,decodeHints 0x0⟩,
  ⟨0xaa005500aa0055,⟨0,by decide⟩,0xa8000000800000,[ew78,ew84,ew89,ew90],4,decodeHints 0x0⟩,
  ⟨0xcc00cc00cc00cc,⟨2,by decide⟩,0xc8008000800000,[ew80,ew94,ew95,ew96],6,decodeHints 0x0⟩,
  ⟨0xf000f000f000f0,⟨4,by decide⟩,0xe0008000800000,[ew86,ew94,ew98,ew99],6,decodeHints 0x0⟩,
  ⟨0xff000000ff0000,⟨16,by decide⟩,0xe8000000800000,[ew89,ew95,ew98,ew101],6,decodeHints 0x0⟩,
  ⟨0x30c030c030c030c,⟨2,by decide⟩,0x208020002000000,[ew104,ew105,ew106,ew107],4,decodeHints 0x0⟩,
  ⟨0x50a050a050a050a,⟨1,by decide⟩,0x408040004000000,[ew108,ew109,ew110,ew111],4,decodeHints 0x0⟩,
  ⟨0x909090909090909,⟨0,by decide⟩,0x808080008000000,[ew119,ew120,ew121,ew122],4,decodeHints 0x0⟩,
  ⟨0xa0a0a0a05050505,⟨0,by decide⟩,0xa080a0004000000,[ew118,ew124,ew127,ew130],4,decodeHints 0x0⟩,
  ⟨0xa0a0a0a0a0a0a0a,⟨1,by decide⟩,0xa080a000a000000,[ew119,ew125,ew128,ew130],4,decodeHints 0x0⟩,
  ⟨0xc0c03030c0c0303,⟨0,by decide⟩,0xc0802000c000000,[ew114,ew132,ew137,ew138],4,decodeHints 0x0⟩,
  ⟨0xc0c0c0c03030303,⟨0,by decide⟩,0xc080c0002000000,[ew117,ew133,ew136,ew139],4,decodeHints 0x0⟩,
  ⟨0xc0c0c0c0c0c0c0c,⟨2,by decide⟩,0xc080c000c000000,[ew119,ew134,ew137,ew139],4,decodeHints 0x0⟩
]

def viewsBlock2 : Array View := #[
  ⟨0xf0f000000000f0f,⟨0,by decide⟩,0xe08000000000000,[ew126,ew135,ew141,ew145],4,decodeHints 0x0⟩,
  ⟨0xf0f00000f0f0000,⟨16,by decide⟩,0xe0800000e000000,[ew128,ew137,ew142,ew145],4,decodeHints 0x0⟩,
  ⟨0xf0f0f0f00000000,⟨32,by decide⟩,0xe080e0000000000,[ew130,ew139,ew143,ew145],4,decodeHints 0x0⟩,
  ⟨0x2222111122221111,⟨0,by decide⟩,0x2220100022000000,[ew148,ew150,ew152,ew153],4,decodeHints 0x0⟩,
  ⟨0x2222222222222222,⟨1,by decide⟩,0x2220220022000000,[ew149,ew151,ew152,ew154],4,decodeHints 0x0⟩,
  ⟨0x3030303030303030,⟨4,by decide⟩,0x3020300030000000,[ew149,ew156,ew157,ew158],4,decodeHints 0x0⟩,
  ⟨0x3333000033330000,⟨16,by decide⟩,0x3220000032000000,[ew152,ew157,ew160,ew163],4,decodeHints 0x0⟩,
  ⟨0x3333333300000000,⟨32,by decide⟩,0x3220320000000000,[ew154,ew158,ew161,ew163],4,decodeHints 0x0⟩,
  ⟨0x5050505050505050,⟨4,by decide⟩,0x5040500050000000,[ew166,ew169,ew170,ew171],4,decodeHints 0x0⟩,
  ⟨0x5555000055550000,⟨16,by decide⟩,0x5440000054000000,[ew167,ew170,ew173,ew175],4,decodeHints 0x0⟩,
  ⟨0x8888444488884444,⟨2,by decide⟩,0x8888440088800000,[ew178,ew183,ew185,ew187],4,decodeHints 0x0⟩,
  ⟨0x8888888888888888,⟨3,by decide⟩,0x8888888088800000,[ew179,ew184,ew185,ew189],4,decodeHints 0x0⟩,
  ⟨0x9999000099990000,⟨16,by decide⟩,0x9888000098800000,[ew185,ew191,ew192,ew193],4,decodeHints 0x0⟩,
  ⟨0xa0a05050a0a05050,⟨4,by decide⟩,0xa0a05000a0800000,[ew178,ew195,ew197,ew198],4,decodeHints 0x0⟩,
  ⟨0xa0a0a0a0a0a0a0a0,⟨5,by decide⟩,0xa0a0a080a0800000,[ew179,ew196,ew197,ew200],4,decodeHints 0x0⟩,
  ⟨0xa5a50000a5a50000,⟨16,by decide⟩,0xa4a00000a4800000,[ew181,ew197,ew202,ew203],4,decodeHints 0x0⟩
]

def viewsBlock3 : Array View := #[
  ⟨0xaa00550000aa0055,⟨0,by decide⟩,0xaa00540000800000,[ew182,ew194,ew204,ew206],5,decodeHints 0x0⟩,
  ⟨0xaaaa0000aaaa0000,⟨17,by decide⟩,0xaaa80000aa800000,[ew185,ew197,ew205,ew209],4,decodeHints 0x0⟩,
  ⟨0xaaaa555500000000,⟨32,by decide⟩,0xaaa8540000000000,[ew187,ew198,ew206,ew209],4,decodeHints 0x0⟩,
  ⟨0xc0c0c0c0c0c0c0c0,⟨6,by decide⟩,0xc0c0c080c0800000,[ew179,ew214,ew215,ew217],4,decodeHints 0x0⟩,
  ⟨0xc3c30000c3c30000,⟨16,by decide⟩,0xc2c00000c2800000,[ew180,ew215,ew219,ew220],4,decodeHints 0x0⟩,
  ⟨0xcccc0000cccc0000,⟨18,by decide⟩,0xccc80000cc800000,[ew185,ew215,ew221,ew224],4,decodeHints 0x0⟩,
  ⟨0xf0f00000f0f00000,⟨20,by decide⟩,0xf0e00000f0800000,[ew197,ew215,ew230,ew232],4,decodeHints 0x0⟩,
  ⟨0xffff000000000000,⟨48,by decide⟩,0xfee8000000000000,[ew209,ew224,ew232,ew238],6,decodeHints 0x0⟩,
  ⟨0xffffffff,⟨0,by decide⟩,0xfe800000,[ew20,ew24,ew27,ew31,ew32],6,decodeHints 0x1d820042c000b4206000868441a128684460028f436860e21c9659208f0fa3c5a0f0fa59⟩,
  ⟨0xff00ff00ff00ff,⟨0,by decide⟩,0xe8008000800000,[ew92,ew97,ew100,ew102,ew103],8,decodeHints 0xa3820042c000b42060028f436860e21c9659031d03af30f3c8b4b60c204b69130ad5e259⟩,
  ⟨0xf0f0f0f0f0f0f0f,⟨0,by decide⟩,0xe080e000e000000,[ew131,ew140,ew144,ew146,ew147],6,decodeHints 0xa401c140700868441a100c4fe31208f0fa3c10a10988426a491a920c204b691208f0fa3c⟩,
  ⟨0xaaaa5555aaaa5555,⟨0,by decide⟩,0xaaa85400aa800000,[ew188,ew199,ew207,ew210,ew211],7,decodeHints 0xa480800100080402101ea190e591e0f0785914930da4c42a35e88d40a456a591e0f07859⟩,
  ⟨0xaaaaaaaaaaaaaaaa,⟨1,by decide⟩,0xaaa8aa80aa800000,[ew190,ew201,ew208,ew210,ew212],7,decodeHints 0x2280800100080402100286c384b20904824b030743c5a269349a5a0c16cc24b20904824b⟩,
  ⟨0xffff0000ffff0000,⟨16,by decide⟩,0xfee80000fe800000,[ew210,ew225,ew233,ew239,ew242],8,decodeHints 0xa6820042c000b4206000868441a128684460018f84f4c15d2e946000868441a128684460⟩,
  ⟨0xffff0000ffff,⟨0,by decide⟩,0xfe8000000000,[ew40,ew42,ew44,ew46,ew47],6,decodeHints 0x0⟩,
  ⟨0x3333333333333333,⟨0,by decide⟩,0x3220320032000000,[ew155,ew159,ew162,ew164,ew165],6,decodeHints 0x0⟩
]

def viewsBlock4 : Array View := #[
  ⟨0x5555555555555555,⟨0,by decide⟩,0x5440540054000000,[ew168,ew172,ew174,ew176,ew177],6,decodeHints 0x0⟩,
  ⟨0xcccc3333cccc3333,⟨0,by decide⟩,0xccc83200cc800000,[ew186,ew216,ew222,ew225,ew226],7,decodeHints 0x0⟩,
  ⟨0xcccccccccccccccc,⟨2,by decide⟩,0xccc8cc80cc800000,[ew190,ew218,ew223,ew225,ew227],7,decodeHints 0x0⟩,
  ⟨0xf0f0f0f0f0f0f0f0,⟨4,by decide⟩,0xf0e0f080f0800000,[ew201,ew218,ew231,ew233,ew234],7,decodeHints 0x0⟩,
  ⟨0xffffffff00000000,⟨32,by decide⟩,0xfee8fe8000000000,[ew212,ew227,ew234,ew240,ew242],8,decodeHints 0x0⟩,
  ⟨0xffffffffffffffff,⟨0,by decide⟩,0xfee8fe80fe800000,[ew213,ew228,ew235,ew241,ew243,ew244],10,decodeHints 0xa7020042c000b4206000868441a128684460028f436860e21c9659208f0fa3c5a0f0fa59031d03af30f3c8b4b626a491a927a2491ab60c204b69130ad5e259208f0fa3c5a0f0fa59⟩
]

def viewsGet (i : Nat) : Option View :=
  if i < 32 then
    if i < 16 then
      viewsBlock0[(i-0)]?
    else
      viewsBlock1[(i-16)]?
  else
    if i < 48 then
      viewsBlock2[(i-32)]?
    else
      if i < 64 then
        viewsBlock3[(i-48)]?
      else
        viewsBlock4[(i-64)]?

def nodesBlock0 : Array Node := #[
  ⟨0,3,[ew3,ew4,ew5],localHints 4 0xa9541b0fc2c040081407 0x258168155262367057066353024314322010⟩,
  ⟨12,4,[ew14,ew19,ew23,ew26,ew30],localHints 4 0x4a141106816070524c9c01000300408 0xddc4bb943237aa493238876545432321100⟩,
  ⟨12,4,[ew19,ew23,ew25,ew26,ew30],localHints 4 0x4a14410401401058b4000c038081093 0xddc88c8c5454b878aa54928787665431210⟩,
  ⟨12,4,[ew17,ew19,ew23,ew26,ew30],localHints 4 0x4a1411068160c4a01c9e01000081408 0xddc4bb941221aa496872126545433212100⟩,
  ⟨12,4,[ew19,ew23,ew26,ew28,ew30],localHints 4 0x106140608820010581c00084a0b0040a 0x8787d8c8b5aa78011099508787645432210⟩,
  ⟨12,4,[ew0,ew19,ew23,ew26,ew30],localHints 4 0x2511050201a0581c0200060081408 0xcca7bb7a994186743462126554343212100⟩,
  ⟨12,4,[ew11,ew19,ew23,ew26,ew30],localHints 4 0x419b104aa080685a2c058041800050080e08 0xf6e6d6c6bb43a6099458823765454323210⟩,
  ⟨12,4,[ew19,ew21,ew23,ew26,ew30],localHints 4 0x4a141102818952a000041a0082c1007 0xddc3bb23a98737366554432011001100110⟩,
  ⟨12,4,[ew19,ew23,ew26,ew29,ew30],localHints 4 0x11c14060292a1a0082c102d000b00407 0x6767d7c7b36767a13198876055044302210⟩,
  ⟨12,4,[ew1,ew19,ew23,ew26,ew30],localHints 4 0x251102834141682c0200060081007 0xcc85ba5434a995877400110654343221010⟩,
  ⟨12,4,[ew8,ew19,ew23,ew26,ew30],localHints 4 0x471f844107b3d4162d160041800050080e08 0xf9e9d92cc45b9a988417721665454321010⟩,
  ⟨12,4,[ew2,ew19,ew23,ew26,ew30],localHints 4 0x2506088340b160500200010281007 0xcb5aa852332995801107730654432321010⟩,
  ⟨12,4,[ew5,ew19,ew23,ew26,ew30],localHints 4 0x12be9f2107c3dc282d160041800050080e08 0xf94e9d9cc43b9a988417721665432321010⟩,
  ⟨12,5,[ew19,ew23,ew26,ew30],decodeHints 0x8300028258283002255c83028145c80002018200816228182802225c028160b5c00802014a82800104a808181081008000080828180a80020021a7f81c161a5b81c02015b820160b4a01c002d4a020182d7f02000007e81c18074981c042c49820142c7e02004027d81c1407⟩,
  ⟨14,3,[ew72,ew80,ew86,ew89],decodeHints 0xe0700a120d86c0a1308040000f0c06006050f0780c000e8740c02⟩,
  ⟨14,4,[ew73,ew80,ew86,ew89,ew91],decodeHints 0x3018018183c1e0300ca050150483a1d03034944a0a84c90480903e0e061c8180a05000000402⟩
]

def nodesBlock1 : Array Node := #[
  ⟨14,4,[ew69,ew80,ew86,ew89,ew91],localHints 4 0xf0703a0d0d92006060a8142c120003c2602 0x6896ff89ee64dd8cbb61aa4298987654332100⟩,
  ⟨14,3,[ew70,ew80,ew86,ew91],decodeHints 0xf0780c000e8740c0208040000f0c06006050e0700a120d86c0a13⟩,
  ⟨14,4,[ew74,ew80,ew86,ew89,ew91],decodeHints 0x301801814562b06800381c028544e2701808361b028a820100003c0c06840145c05090002602⟩,
  ⟨14,4,[ew71,ew80,ew86,ew89,ew91],localHints 4 0xf0703a1b1504006060a8142c120003c2602 0x6876ff83ee67dd80cc6baa3298767653432010⟩,
  ⟨14,3,[ew75,ew77,ew83,ew91],decodeHints 0x309841a062d96c060602814324a2d1680c03000003248010085048⟩,
  ⟨14,4,[ew75,ew77,ew86,ew89,ew91],decodeHints 0x1c0e00606030ac0c032814054ab138180606028141e161403c3a1d0300c262a1704c0000010085013⟩,
  ⟨14,3,[ew75,ew79,ew85,ew89],localHints 4 0x184b606258142a2b0c89c5010 0xaa4699268832776504300210⟩,
  ⟨14,4,[ew75,ew79,ew86,ew89,ew91],decodeHints 0x1c0e01a05158ac1aac029400a150301894050a8141e161403c040d1c808361b0285420100104c5002⟩,
  ⟨14,4,[ew75,ew80,ew83,ew89,ew91],decodeHints 0xc0600606158181a06028140c2703034944a0aaac1e160c83c3c1e0300c24151704800000c8480402⟩,
  ⟨14,4,[ew75,ew80,ew85,ew89,ew91],decodeHints 0xc060060503018a005150144e2701ab00a4a028a81e160c83c00031c800381c0285400120c8002010⟩,
  ⟨14,5,[ew75,ew80,ew86,ew89,ew91],localHints 5 0x6056bd282f04ebb06929742a850e40cae01c245c05568542c00140641e02 0x85e8cdd196b435036b4abc95adc2d63420a6b9508b18c26b433a85ada4e6242030905088c20110465288427b5ae5adcd6b16b521093192841cc6108822904300820⟩,
  ⟨14,4,[ew65,ew80,ew86,ew89,ew91],localHints 4 0xc0703a0d250400c03150540a120004c1e02 0xff899893ee36dd9cbb62aa3198987655432100⟩,
  ⟨14,3,[ew66,ew80,ew89,ew91],decodeHints 0xc06006050e8740c020d86c0a130f0780c000e0700a1208040000f⟩,
  ⟨14,4,[ew76,ew80,ew86,ew89,ew91],decodeHints 0x7038068143c1e03000381c028483a1d03008361b0284c20100005806060a8161600140001e02⟩,
  ⟨14,4,[ew68,ew80,ew86,ew89,ew91],localHints 4 0x6038270186c2016030a82a05090002602 0xeeb42b32dd43ccb0aa41992877645432321010⟩,
  ⟨14,3,[ew77,ew79,ew86,ew88],localHints 4 0xc25a000e0324b090745c1b 0x996726528827065044030210⟩
]

def nodesBlock2 : Array Node := #[
  ⟨14,4,[ew77,ew79,ew86,ew89,ew91],localHints 4 0x1c2bc56500e8a8900d1c86c20000904c5c02 0xff8edd84c443bb2a12943408706655430210⟩,
  ⟨14,4,[ew77,ew80,ew83,ew86,ew91],decodeHints 0xf0780c031c0e01a06000003a1d030349048092ac262a0c84c3018018182a12140480a050c8540402⟩,
  ⟨14,4,[ew77,ew80,ew86,ew88,ew91],decodeHints 0x1c0e03c1e030000050150003a1d032bc262a0c84c0048000580a061c8140a150c814381c02848361b⟩,
  ⟨14,5,[ew77,ew80,ew86,ew89,ew91],localHints 5 0xe1801e282fc3abe069217416868e406b0030a80b0c140015a12170642602 0x36e94bd29adcad665e08dc116b334c455cc331946258825d433a856ba4e611046a50842118c184826346107b5ae5adcd6b16b109225250631c84398c52104300820⟩,
  ⟨14,4,[ew64,ew80,ew86,ew89,ew91],localHints 4 0xc07824270d8a8900d018180a150003c0413 0xff75ee87545dcc71bb5a911287665454331210⟩,
  ⟨14,4,[ew67,ew80,ew86,ew89,ew91],localHints 4 0x301e0e92820160680c0c05000480413 0xdd75cc532332bb51a110993875654432321010⟩,
  ⟨14,4,[ew79,ew80,ew85,ew86,ew89],decodeHints 0xe0700a151c0e01a05158ac361b028a82010002b0040d0c8083018018140600140000c060c80c4e27⟩,
  ⟨14,4,[ew79,ew80,ew86,ew88,ew89],decodeHints 0x1c0e0381c02848562b06800361b02abc040d0c8082010000580c05170140c030c8183c1e030003a1d⟩,
  ⟨14,5,[ew79,ew80,ew86,ew89,ew91],localHints 5 0xe1842b6087036be1504176160681a1e2e0aac00b0e140495c001c84c3202 0x97e963d2def4e5247e0c3c19ef25c864d88bb112932cc00806f784210a6a09d4094d273092408480424610085c17b9ab5b12962d6a4a50631c84398c52102310400⟩,
  ⟨14,4,[ew49,ew80,ew86,ew89,ew91],localHints 4 0xc07806500d8400c0d0a8a80a120b0002602 0xffd9ee9dcc649890bb06aa0398987655432210⟩,
  ⟨14,3,[ew50,ew86,ew89,ew91],decodeHints 0xc06006050f0780c000e0700a120e8740c020d86c0a1308040000f⟩,
  ⟨14,4,[ew80,ew82,ew86,ew89,ew91],decodeHints 0x3018018143c1e03000381c028481a06150142c000e8740c020d86c0a1308040000f014403202⟩,
  ⟨14,4,[ew54,ew80,ew86,ew89,ew91],localHints 4 0x702b0e0343610078182a05090002602 0xdda4cca2bb430a109941882766545432321010⟩,
  ⟨14,3,[ew80,ew83,ew85,ew88],localHints 4 0x502e2d860b41e0112c3813 0x469416911481776355432210⟩,
  ⟨14,4,[ew80,ew83,ew85,ew89,ew91],localHints 4 0xc2c43c151c8705c27019289012010400013 0xff7edd4c9417b1aa14918873633035432210⟩,
  ⟨14,4,[ew80,ew83,ew86,ew88,ew91],decodeHints 0xc0603c1e032c42415140480a061c8140a1514014381c0e8740c02011282a0224008040f0d86c0a13⟩
]

def nodesBlock3 : Array Node := #[
  ⟨14,5,[ew80,ew83,ew86,ew89,ew91],localHints 5 0x61881e6180e243959014001d03034942e0aafc9028092f01f110c8095a13 0xcb696fd2ed6cbde87e0f6c1defbdac741d8b5a108ab9d47be8e74def422435c90c88cf113e007400f789c202da26084b1014029d2240847114c500c022084310020⟩,
  ⟨14,4,[ew48,ew80,ew86,ew89,ew91],localHints 4 0xc0ac38150e84c9003068180a2a0b0002402 0xff85ee72dd5cbb87545a292387665454232100⟩,
  ⟨14,4,[ew51,ew80,ew86,ew89,ew91],localHints 4 0x380f1403a100780c0c05000480413 0xcc65bb53a33299510110883765654432321010⟩,
  ⟨14,4,[ew80,ew85,ew86,ew88,ew89],decodeHints 0xc060381c02ac40003140000c05170140c03140183c1e0d86c0a131389c060208040000f0e8740c02⟩,
  ⟨14,5,[ew80,ew85,ew86,ew89,ew91],localHints 5 0x618a1c618540d14172c824391380d821b028a85010002f41f130c84d5c02 0xb76ad0d59ce5e56749e0e725294af07b60eb5ded64a6a37568a54d6b9a9525ad3088ce7039e283c4e701a012d805300b5894229d004a007394c500c022084310020⟩,
  ⟨14,4,[ew33,ew80,ew86,ew89,ew91],localHints 4 0x1c0783812139281e0d0300c54050a8002c02 0xff84ee72dd4c7b784a45212978764543212100⟩,
  ⟨14,4,[ew34,ew80,ew86,ew89,ew91],localHints 4 0x18159403a1b0981806050a800040f 0xcc546b654a4399618847011065654343221010⟩,
  ⟨14,5,[ew80,ew86,ew88,ew89,ew91],localHints 5 0xc2a1e6287188128b0a164390e819842e0d81580138a8656010010002c0f 0xa62a0e7318c6334673990c994a13b148628e70ae2a2ac26584a552b4148419843208a221b9e883d0e70da34296362c6a52128198603800600ca3008830906210020⟩,
  ⟨14,6,[ew80,ew86,ew89,ew91],localHints 5 0xc4703d1b018723415090e43a068c8345c1b02c6054131404032020045c2c0f 0x6aefb9521b6d2f7d2e0b38e1994ef93ce10c0ee33cd7668e9638d6bace9329211921d12a210791c42a16c6912c2916b5212828066390262906310020⟩,
  ⟨57,8,[ew92,ew97,ew100,ew102,ew103],localHints 6 0x30340f00c38750a8483a0d0d8a826102a8581e74030987a056314c5a00198905808011146c30 0x80c7a181b3e181b79e80c3cc7083df71a79f71a3cf70878871a31d7086dd70830c71a6da4c33d94d56194d53cf4c36034d53174c35974c330c4d55954d12144c34944c32084d14910843d008a39008a3cf08438408a30d0842cd08430c08a2ca0862090841c90842080861c60800c50840450840c3080040⟩,
  ⟨58,6,[ew131,ew140,ew144,ew146,ew147],localHints 6 0x19e18221359c03021059a152033098cb3f8c8ec226532508211497062202b10c34016402d8e24078bc1407 0x94c82495c4247dc8207cc40c8c84228db82285b4108488087db31e7c871e74830c75b71b6813d96964195563cf54141061629760131754128a55630c5431945412144c11864c320848041148b3d108b4100803cf38b30d38028d08030c08b28a0842090801891c02081c41861400c01440410840c3080040⟩,
  ⟨59,6,[ew89,ew188,ew199,ew207,ew210,ew211],localHints 6 0x9234e46851e1b644d290c8098578fb463d1d478412c03598a4623d68118a20140000b83a3c008ee32 0xd40d88e8e241034e3613a025080938e29040a29f2cd34928919878439e11860638e11c74634d19c6c434d19318425a1134c624608e64061900e3826180165c234d09654034d0890804d40092424c20064821120861801003d041138e45040f38e28a30a34c28b20a2481461871041c61851040420830000c2081000⟩,
  ⟨59,7,[ew188,ew199,ew207,ew210,ew211],localHints 6 0x40b51672642a5807251e044a26d43a0d004f361305257430f46282272a88c013b840f002001707432 0x68e7637a24636a275d84e44e80845f25975f79945124874871935b24839b68834d25938e54341808145854141008345154139708335754338e08134d2435160812085415132432081444521c04121404511c441014038f1c434f14438e1c034d2442cc1c02081402ca2442080800c61c40461440c3080040⟩,
  ⟨61,6,[ew185,ew229,ew233,ew239,ew242],localHints 5 0x9235238adaa164b895201a0a0c0222701835046e272a802100003c1927048080e2c 0xba589671fd6719bba5e9b9ddace1face1ceb9de761e76615366167361d29885ef8ca358c9ef886218c93488674885298ca73884e78c8a58c8e7884a1189f0199d0199ef189c21896d18d291b16a18929198e8188a8188e7198a51906018820⟩,
  ⟨61,7,[ew185,ew210,ew225,ew233,ew239,ew242],localHints 6 0x248d48e2b6b85932250a260443648098340b18358764201834686f270046e0006028040e048100e08 0x74a30a3223e332232174a3ca7483a07de3e07de38e7483c83086dc30729c3076db30828a0c63cf0d839a0d83cf0c638e0d85190c62990c65140d828a0c62080d81c70d82080c61c61013cf1135971133cf10159611329510151510128a1135141012081131c71132081011c10c10c10c31860c31120d13cf0c338e0d03cf0c338e0cd2cb0c328a0cc2cb0c328a0c22080c31c70c92080c21c70c30c50c21850c40c00c2040⟩,
  ⟨61,7,[ew210,ew225,ew229,ew233,ew239,ew242],localHints 6 0x9235238adb0164d094843b1a0506e2706a08201f078287c0313174020b1684400240601c0802040241cd6 0x7cd38d3a44253a43a37cd40d7c95e28604228605d77c940938969e38735e38769a38934d28a41029d29d28a41029c29c28a34d28e69a28a34d29b69a2852492991c728a2492851c75044180935d85134100845c450431608e34d51430c08434d5132550841d55042490931c70410520841442834110483d12884100433c328334d04e30c28a34d04330c28824b0431cb2832490481c7082086083143082104043043082040⟩
]

def nodesBlock4 : Array Node := #[
  ⟨61,7,[ew152,ew210,ew225,ew233,ew239,ew242],localHints 6 0x491a91c56d94d89428981107c6c3e130b4480c160ec840d018d0c401058dc2c00088381402038240808 0x7cc34c3633e43633627cc3cc7c84218093e18094107c83c834875e35431e35475d34830c6853cf09941c6993cf0854106992db08531b6852cb09930c6852080995146992080855051803d81955d81953cf1805c018030c1862cb18d30c1802cb1952161805161802081955140821931801800821451924101863cf1914101863cf18e30c1862cb18d30c1862cb18124918620818a249181208187184081144082083081000⟩,
  ⟨61,7,[ew167,ew210,ew225,ew233,ew239,ew242],localHints 6 0x9235238adb4164e094282706a08200f48068600c070b076421300c6863058046e33000280411048100e08 0x7ca30a3243a53243237ca38a7c76e28603a28606db7c738730775e31429e31475d30728a0c539c0d86dc0d838e0c56c50c52da0c328a0cc2cb0c528a0d81d90c55190c51c70d851410138e4d53d711538e4c13cf1152964c12d610128a4d52cb1011c74d55141151c74c15010c34d20c31450c10c10d13cf0c338e0d03cf0c338e0cd2cb0c328a0cc2cb0c328a0c22080c31c70c92080c21c70c30c60c21450c40c00c2040⟩,
  ⟨61,6,[ew197,ew225,ew236,ew239,ew242],localHints 5 0x9235238f834276d83d3a2205890222b0680d0670279b00328038b42002000102c0a 0xaa589671dd6719baa5c989dda8ca3a8c9ce89e278c93989e7989d298ca73a91d8bd9f8bd9cea91e46127460134602736112988240890e489244880e710df0105d0105ef10dc310d6d109291316a10d291204610ce61048510c0510c8310400⟩,
  ⟨61,7,[ew197,ew210,ew225,ew233,ew239,ew242],localHints 6 0x248d48e64128504edd07a7844331f098340b6e09076420680c68712780418000487c040a070100e08 0x68a30a3223a332232168a38a0893e00983a00983cf08938e09879f08929f08979e09828a68539d71b3dd71b38e6853c530551930429930451430528a0846040852450856050842440c13970d25970d238e0c15960d22950c15150c128a0d25140810810822490820d30c11450d21040d21450c11010913cf08238e0903cf08238e08d2cb08228a08c2cb08228a082088082248087145082104086145082104083080082040⟩,
  ⟨61,7,[ew210,ew225,ew233,ew236,ew239,ew242],localHints 6 0x923523908763415a0c280c13b781e9f068883e09080dc2c9001898bc010581c00046e0b0220801038600a 0x60c34c3643e536436360c3cc1453cf1621621453cf16116114530c14d2cb14530c1602cb4895df2113df4915d72093c948975e20d30c49275d20930c08209c2092096033db6995db6993cf6035c33432d63403163402cb34330c1405401435031431431405002002534834534832492004401443cf0813901413cf08438414430c08d2cb14530c0842cb20820a2042042082490840842080871410c60840061440c3081000⟩,
  ⟨61,7,[ew128,ew210,ew225,ew233,ew239,ew242],localHints 6 0x491a91cc8250a09dbea0110dc6690130b45830050ec8403068d0ca010584418000f83c1c090101c0808 0x70c34c36342436336270c40c6893e10594216993cf0494106997e00493206897df05930c70341e7463de7464107033c33432db35331b3532cb34330c0536536832436836430532531404101545d81544101405c014030c1452cb14d30c1402cb0411561401400412491540d51404d51400c31544d31524101453cf1514101453cf14e30c1452cb14d30c1452cb14a1480412481441861450c31471861440c3041042041000⟩,
  ⟨61,7,[ew170,ew210,ew225,ew233,ew239,ew242],localHints 6 0x9235238ad06277003d420d110402c3e0d02c5a240702876421300c68660a00418000487c6c02088100e08 0x74a30a3243a532432374a38a0887220993a209971c0883880882e108228a08c2cb08828a7443a07de7207de38e74470430459b31229b31259630428a09221a08465a0842080926520c13984d43d80d438e4c13cf0d42974c15970c128a4d45960824d50822080810810c11044d44920d41044c14810913cf08238e0903cf08238e08d2cb08228a08c2cb08228a082089082208087145082104086145082104083080082040⟩,
  ⟨61,6,[ew210,ew215,ew237,ew239,ew242],localHints 5 0x92352389c446447150fd29080f9c22401a884c1a009c8160f0f8285a08000106607 0x72d4b571fd5715b72deb399fa3a0fa3a1ef398e63a13939979399293a16b10db8105f8105ad10de310ed71096b12ad510d6b1505310cd3711f28c1b28c1ef711a45116c5012c5016b5112938100390c439104380c010065110251106310020⟩,
  ⟨61,7,[ew210,ew215,ew225,ew233,ew239,ew242],localHints 6 0x248d48e2b128504e0d1138c76421a15000021f38848035189834013982c2c0c07824140e088200807 0x3cc2cc2e24232e22e13cc40c04872004942004971c04841004979f04831f04879e04930c18541d18771d18741018571c18729b18531b18528a18730c04504504120804119a05938e04141005838e04141005759604130c04b59604130c0410550412150460540411543c24134913934914103c23822c230d2c028d2c030c2c228a0402400422020422420402001801c01821421821c21801400400400421020420c2040040⟩,
  ⟨61,7,[ew210,ew225,ew233,ew237,ew239,ew242],localHints 6 0x923523908763432238280c4c03414e31f39048035209834012f82c220e168dc0004198b03e08010246c07 0x4d03d03e45253e43e34d051014551416216214551416116114538e14f41014538e16041028969f20751f28769a20950928975e20f41028a75d20941008209c20920914351408169b14151408368314338e08f41014538e0834102082192032032082490830832080984c45175954975955144c44843c44113c03913c04103c438e14034014430414434414030020024b2841cb2842492001c00800c61440461440c3080040⟩,
  ⟨61,7,[ew137,ew210,ew225,ew233,ew239,ew242],localHints 6 0x491a91c56250a260203e72a944c1a1b8585836038ec8403068d0ce0b0087c180005010040e088901208 0x68b34b36342436336268b40b5c93e11964215d63cf1894105d67e01892e05c97df1962cb0454100543de0544100453c504530c0412cb04d30c0452cb18605d04504518624968041c6c265c6c24106806403402d83533183532cb34030c1935935c02405c05801932530531550405150401450535130524100413cf0514100413cf04e30c0412cb04d30c0412cb04a048186248186187186145044082041000043082041000⟩,
  ⟨61,7,[ew157,ew210,ew225,ew233,ew239,ew242],localHints 6 0x9235239911c27110407ce6122984c1a058b4660f0481c76420680c68680a00418000f828040e088c00808 0x68a30a3243a532432368a38a0483e20553a20553cf0483880482e104128a04c2cb04828a1c63a04d43e01d438e4c63cf1d45df4c629f1c65d74d428a0414de04120804604668039d71b65d71b38e6806403002983125d831228a3005d70522160405560402080525524d25121c01801c05004d21920513cf04138e0503cf04138e04d2cb04128a04c2cb04128a041049041208047045041185044082041000043082041000⟩,
  ⟨61,8,[ew210,ew225,ew233,ew239,ew242],localHints 6 0x9235238ac2c250a09c1e0d114d6681099cc87c421200c76260d004680b98cc05b2f004b8192d960b25608014a81407 0x5524524685a946846755259254b8266255a662582054b58b44b8e44494a44498e344b4925435a262182262159654380344341f44149f4414104434927812dc74325c6c32cb6812415445996175196175965445044444934404134404924444103c02cd38424d3042cb2802402000c61c40461440c3080040⟩,
  ⟨69,9,[ew190,ew213,ew228,ew235,ew241,ew243,ew244],localHints 6 0x30150193482400f4d838e909094284c3f8c84436420a4625621868163045a280c8910ba0123b02a2040e73d1387e013496000795383014021185c0e08 0x553cf56f4675574cf3b136533cc5f26f06726f05d73cc6593f047154c4f154c4513f04d32c966f6eb5ef2eb659b895d72eb4ed54946d2c94d3b2b4512c9a6a3c632a2c6a693c930c0c56590e65e80e66590c55d70e64d30c54670c54d30e64510e47650c53250c575d0e430c0c52490e41860e42490c51850816590a08a30a06590818a20a04d30817e10814d30a07df09c31e08175e08130c09c75d08124909c18609c2490811810810810831450820826d865921a5d76da6592185d75524d32164515544d321245140d38e20f30c40f38e20d30c2c724920a1862ca2492071860820840821440820c0082040⟩,
  ⟨69,9,[ew201,ew213,ew228,ew235,ew241,ew243,ew244],localHints 6 0x180a80c9a41201b5da3a12bb0281d9c06dd613110cd082918958861a05890888a0322442e8020ec0a88103a8f64f1f80418003b4dcd423010bd4e0a2c05c0e08 0x5d5db87776f85f7db6a556d544e6757736f577365944e6db4734f45ce5745ce4d347355574d6db1b06727706db18d6595f055518d4f15cd5551b04d3ba6b6f18d3afb8db6d1a638e2476ec76866c2686dbac765926856a5c74ea247555a684d32477e74443a72447df44738e2449842c73472479871843440816db0a29250a26db0819240a25550818630815550a286109e3a00817e008138e09e7df08108108334d0820820811c709e10409e1c708110175a6db19c65975c6db19a6595d45551984d35d65551944d348f41019138e49141018f38e08208c08234c2ca1c72481042481c71851040820c0082040⟩,
  ⟨69,9,[ew213,ew218,ew228,ew235,ew241,ew243,ew244],localHints 6 0xc054064d20900daed1d094d214261fc642245224433b1da2040ef2a0fc005801110e8069d0a4083d02bb8a6430d004f80b0b0301e23054e4a417040bd4e07 0x553d776b6637576d7549361334e9746b26346b296534e61837287354e4f354e8613724d368a6180af9716af61808a96556f4d308a87054a4d30af861b4bb2e08a3aeb4ab2c08b38e20761822996b2296182079652294d320786a2074d32298612093282073a820730c20938e20720721c28a2082086a66180a79656a76180a69655624d30a48615634d30a286181e7df08d38e80d7df09e38e20821d14429d20871b1441db1436196915991516185c35961514d45434141434d349141014338f34030f14038e34330c1402c00832831432c30802801402402031c31432432001c0140100083183143103080040⟩
]

def nodesBlock5 : Array Node := #[
  ⟨69,10,[ew213,ew228,ew235,ew241,ew243,ew244],localHints 6 0x180a80c9a41200783812128503a210d84c4022084f8e806460a47a053594c861a008fc1658168027a0c118b02e08014f01407 0x4d4aac4eb62c4ebaaa4d461438f8293a76293a782038f6183a776838f52838f75d3a751430a6265e48263246185ca8203245254ca76530a5144e475d38a8a33883e33888a238a3cf1c36215de8211de6185c38201de51f4c375f1c35144de75d1c335c3813dc1c134d3833cf1c129b30321b1c328a6812011446195d25991526185c45961525154c44551445144d24511443d03803501403cf38434d14028b30420b14428a2402001400c61c40461440c3080040⟩
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
    if i < 64 then
      nodesBlock3[(i-48)]?
    else
      if i < 80 then
        nodesBlock4[(i-64)]?
      else
        nodesBlock5[(i-80)]?

def fastViews : QFast.Table View := ⟨70,viewsGet⟩

def fastNodes : QFast.Table Node := ⟨81,nodesGet⟩

end SignedProjection


namespace SignedProjection
def aliasMap1 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63]
def aliasMap2 : Array Nat := #[0,63,0,62,0,61,0,60,0,0,0,0,0,0,0,0,0,59,0,58,0,57,0,56,0,0,0,0,0,0,0,0,0,55,0,54,0,53,0,52,0,0,0,0,0,0,0,0,0,51,0,50,0,49,0,48,0,0,0,0,0,0,0,0]
def aliasMap3 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,33,35,37,39,49,51,53,55,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap4 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,17,19,21,23,49,51,53,55,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap5 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,7,21,23,37,39,53,55,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap6 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,7,19,23,35,39,51,55,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap7 : Array Nat := #[0,0,0,0,0,0,0,0,31,30,29,28,0,0,0,0,0,0,0,0,0,0,0,0,23,22,21,20,0,0,0,0,63,62,61,60,0,0,0,0,0,0,0,0,0,0,0,0,55,54,53,52,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap8 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,27,26,25,24,51,50,49,48,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap9 : Array Nat := #[0,0,0,0,0,0,0,0,31,30,27,26,0,0,0,0,0,0,0,0,0,0,0,0,23,22,19,18,0,0,0,0,63,62,59,58,0,0,0,0,0,0,0,0,0,0,0,0,55,54,51,50,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap10 : Array Nat := #[0,0,0,0,0,0,0,0,63,0,62,0,55,0,54,0,0,31,0,30,0,23,0,22,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,57,0,56,0,49,0,48,0,0,25,0,24,0,17,0,16,0,0,0,0,0,0,0,0]
def aliasMap11 : Array Nat := #[0,0,0,0,0,0,0,0,31,29,27,25,0,0,0,0,0,0,0,0,0,0,0,0,23,21,19,17,0,0,0,0,63,61,59,57,0,0,0,0,0,0,0,0,0,0,0,0,55,53,51,49,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap12 : Array Nat := #[0,0,0,0,0,0,0,0,63,0,61,0,55,0,53,0,0,31,0,29,0,23,0,21,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,58,0,56,0,50,0,48,0,0,26,0,24,0,18,0,16,0,0,0,0,0,0,0,0]
def aliasMap13 : Array Nat := #[0,0,0,0,0,0,0,0,63,0,59,0,55,0,51,0,0,31,0,27,0,23,0,19,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,60,0,56,0,52,0,48,0,0,28,0,24,0,20,0,16,0,0,0,0,0,0,0,0]
def aliasMap14 : Array Nat := #[0,0,0,0,0,0,0,0,16,0,18,0,20,0,22,0,0,48,0,50,0,52,0,54,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,24,0,26,0,28,0,30,0,0,56,0,58,0,60,0,62,0,0,0,0,0,0,0,0]
def aliasMap15 : Array Nat := #[0,0,0,0,0,0,0,0,16,0,17,0,20,0,21,0,0,48,0,49,0,52,0,53,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,24,0,25,0,28,0,29,0,0,56,0,57,0,60,0,61,0,0,0,0,0,0,0,0]
def aliasMap16 : Array Nat := #[0,0,0,0,0,0,0,0,16,0,17,0,18,0,19,0,0,48,0,49,0,50,0,51,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,24,0,25,0,26,0,27,0,0,56,0,57,0,58,0,59,0,0,0,0,0,0,0,0]
def aliasMap17 : Array Nat := #[0,16,0,17,0,18,0,19,0,0,0,0,0,0,0,0,0,20,0,21,0,22,0,23,0,0,0,0,0,0,0,0,0,48,0,49,0,50,0,51,0,0,0,0,0,0,0,0,0,52,0,53,0,54,0,55,0,0,0,0,0,0,0,0]
def aliasMap18 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16,17,22,23,24,25,30,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap19 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16,18,21,23,24,26,29,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap20 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16,19,20,23,24,27,28,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap21 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,17,19,21,23,24,26,28,30,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap22 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,18,19,22,23,24,25,28,29,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap23 : Array Nat := #[0,4,0,5,0,6,0,7,0,12,0,13,0,14,0,15,0,20,0,21,0,22,0,23,0,28,0,29,0,30,0,31,0,36,0,37,0,38,0,39,0,44,0,45,0,46,0,47,0,52,0,53,0,54,0,55,0,60,0,61,0,62,0,63]
def aliasMap24 : Array Nat := #[0,2,0,3,0,6,0,7,0,10,0,11,0,14,0,15,0,18,0,19,0,22,0,23,0,26,0,27,0,30,0,31,0,34,0,35,0,38,0,39,0,42,0,43,0,46,0,47,0,50,0,51,0,54,0,55,0,58,0,59,0,62,0,63]
def aliasMap25 : Array Nat := #[0,0,1,0,4,0,5,0,8,0,9,0,12,0,13,0,0,18,0,19,0,22,0,23,0,26,0,27,0,30,0,31,32,0,33,0,36,0,37,0,40,0,41,0,44,0,45,0,0,50,0,51,0,54,0,55,0,58,0,59,0,62,0,63]
def aliasMap26 : Array Nat := #[63,0,61,0,0,0,0,0,55,0,53,0,0,0,0,0,0,46,0,44,0,0,0,0,0,38,0,36,0,0,0,0,59,0,57,0,0,0,0,0,51,0,49,0,0,0,0,0,0,42,0,40,0,0,0,0,0,34,0,32,0,0,0,0]
def aliasMap27 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,10,19,27,34,42,51,59,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap28 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,4,6,17,19,21,23,40,42,44,46,57,59,61,63,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap29 : Array Nat := #[0,0,0,0,0,0,0,0,63,0,55,0,31,0,23,0,0,61,0,53,0,29,0,21,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,46,0,38,0,14,0,6,0,0,44,0,36,0,12,0,4,0,0,0,0,0,0,0,0]
def aliasMap30 : Array Nat := #[0,0,0,0,0,0,0,0,63,0,55,0,31,0,23,0,0,59,0,51,0,27,0,19,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,46,0,38,0,14,0,6,0,0,42,0,34,0,10,0,2,0,0,0,0,0,0,0,0]
def aliasMap31 : Array Nat := #[0,0,4,0,0,0,0,0,8,0,12,0,0,0,0,0,0,17,0,21,0,0,0,0,0,25,0,29,0,0,0,0,32,0,36,0,0,0,0,0,40,0,44,0,0,0,0,0,0,49,0,53,0,0,0,0,0,57,0,61,0,0,0,0]
def aliasMap32 : Array Nat := #[0,0,0,0,0,0,0,0,32,34,36,38,0,0,0,0,0,0,0,0,0,0,0,0,49,51,53,55,0,0,0,0,0,2,4,6,0,0,0,0,0,0,0,0,0,0,0,0,17,19,21,23,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap33 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,32,34,36,38,17,19,21,23,40,42,44,46,25,27,29,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap34 : Array Nat := #[63,0,62,0,0,0,0,0,47,0,46,0,0,0,0,0,0,31,0,30,0,0,0,0,0,15,0,14,0,0,0,0,55,0,54,0,0,0,0,0,39,0,38,0,0,0,0,0,0,23,0,22,0,0,0,0,0,7,0,6,0,0,0,0]
def aliasMap35 : Array Nat := #[63,0,61,0,0,0,0,0,47,0,45,0,0,0,0,0,0,31,0,29,0,0,0,0,0,15,0,13,0,0,0,0,55,0,53,0,0,0,0,0,39,0,37,0,0,0,0,0,0,23,0,21,0,0,0,0,0,7,0,5,0,0,0,0]
def aliasMap36 : Array Nat := #[63,0,59,0,0,0,0,0,47,0,43,0,0,0,0,0,0,31,0,27,0,0,0,0,0,15,0,11,0,0,0,0,55,0,51,0,0,0,0,0,39,0,35,0,0,0,0,0,0,23,0,19,0,0,0,0,0,7,0,3,0,0,0,0]
def aliasMap37 : Array Nat := #[0,2,4,6,0,0,0,0,8,10,12,14,0,0,0,0,16,18,20,22,0,0,0,0,24,26,28,30,0,0,0,0,32,34,36,38,0,0,0,0,40,42,44,46,0,0,0,0,48,50,52,54,0,0,0,0,56,58,60,62,0,0,0,0]
def aliasMap38 : Array Nat := #[0,0,0,0,0,0,0,0,32,0,33,0,34,0,35,0,0,48,0,49,0,50,0,51,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,40,0,41,0,42,0,43,0,0,56,0,57,0,58,0,59,0,0,0,0,0,0,0,0]
def aliasMap39 : Array Nat := #[0,0,0,0,0,0,0,0,8,9,10,11,0,0,0,0,0,0,0,0,0,0,0,0,56,57,58,59,0,0,0,0,0,1,2,3,0,0,0,0,0,0,0,0,0,0,0,0,48,49,50,51,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap40 : Array Nat := #[0,0,0,0,0,0,0,0,2,0,18,0,34,0,50,0,0,3,0,19,0,35,0,51,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,10,0,26,0,42,0,58,0,0,11,0,27,0,43,0,59,0,0,0,0,0,0,0,0]
def aliasMap41 : Array Nat := #[0,0,1,0,0,0,0,0,8,0,9,0,0,0,0,0,0,34,0,35,0,0,0,0,0,42,0,43,0,0,0,0,16,0,17,0,0,0,0,0,24,0,25,0,0,0,0,0,0,50,0,51,0,0,0,0,0,58,0,59,0,0,0,0]
def aliasMap42 : Array Nat := #[0,0,1,0,0,0,0,0,8,0,9,0,0,0,0,0,0,18,0,19,0,0,0,0,0,26,0,27,0,0,0,0,32,0,33,0,0,0,0,0,40,0,41,0,0,0,0,0,0,50,0,51,0,0,0,0,0,58,0,59,0,0,0,0]
def aliasMap43 : Array Nat := #[0,0,0,0,0,0,0,0,1,0,17,0,33,0,49,0,0,3,0,19,0,35,0,51,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,9,0,25,0,41,0,57,0,0,11,0,27,0,43,0,59,0,0,0,0,0,0,0,0]
def aliasMap44 : Array Nat := #[0,0,2,0,0,0,0,0,8,0,10,0,0,0,0,0,0,33,0,35,0,0,0,0,0,41,0,43,0,0,0,0,16,0,18,0,0,0,0,0,24,0,26,0,0,0,0,0,0,49,0,51,0,0,0,0,0,57,0,59,0,0,0,0]
def aliasMap45 : Array Nat := #[0,0,0,0,0,0,0,0,32,40,48,56,0,0,0,0,0,0,0,0,0,0,0,0,35,43,51,59,0,0,0,0,0,8,16,24,0,0,0,0,0,0,0,0,0,0,0,0,3,11,19,27,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap46 : Array Nat := #[0,0,0,0,0,0,0,0,33,40,49,56,0,0,0,0,0,0,0,0,0,0,0,0,35,42,51,58,0,0,0,0,1,8,17,24,0,0,0,0,0,0,0,0,0,0,0,0,3,10,19,26,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap47 : Array Nat := #[0,0,0,0,0,0,0,0,34,40,50,56,0,0,0,0,0,0,0,0,0,0,0,0,35,41,51,57,0,0,0,0,2,8,18,24,0,0,0,0,0,0,0,0,0,0,0,0,3,9,19,25,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap48 : Array Nat := #[0,0,0,0,0,0,0,0,8,9,10,11,0,0,0,0,0,0,0,0,0,0,0,0,40,41,42,43,0,0,0,0,16,17,18,19,0,0,0,0,0,0,0,0,0,0,0,0,48,49,50,51,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap49 : Array Nat := #[0,0,0,0,0,0,0,0,4,0,20,0,36,0,52,0,0,6,0,22,0,38,0,54,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,12,0,28,0,44,0,60,0,0,14,0,30,0,46,0,62,0,0,0,0,0,0,0,0]
def aliasMap50 : Array Nat := #[0,1,4,5,0,0,0,0,8,9,12,13,0,0,0,0,16,17,20,21,0,0,0,0,24,25,28,29,0,0,0,0,32,33,36,37,0,0,0,0,40,41,44,45,0,0,0,0,48,49,52,53,0,0,0,0,56,57,60,61,0,0,0,0]
def aliasMap51 : Array Nat := #[0,0,0,0,0,0,0,0,32,0,33,0,36,0,37,0,0,48,0,49,0,52,0,53,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,40,0,41,0,44,0,45,0,0,56,0,57,0,60,0,61,0,0,0,0,0,0,0,0]
def aliasMap52 : Array Nat := #[0,0,0,0,0,0,0,0,4,0,20,0,36,0,52,0,0,5,0,21,0,37,0,53,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,12,0,28,0,44,0,60,0,0,13,0,29,0,45,0,61,0,0,0,0,0,0,0,0]
def aliasMap53 : Array Nat := #[0,0,0,0,0,0,0,0,1,0,17,0,33,0,49,0,0,5,0,21,0,37,0,53,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,9,0,25,0,41,0,57,0,0,13,0,29,0,45,0,61,0,0,0,0,0,0,0,0]
def aliasMap54 : Array Nat := #[0,4,0,5,0,6,0,7,0,0,0,0,0,0,0,0,0,20,0,21,0,22,0,23,0,0,0,0,0,0,0,0,0,36,0,37,0,38,0,39,0,0,0,0,0,0,0,0,0,52,0,53,0,54,0,55,0,0,0,0,0,0,0,0]
def aliasMap55 : Array Nat := #[0,2,0,3,0,6,0,7,0,0,0,0,0,0,0,0,0,18,0,19,0,22,0,23,0,0,0,0,0,0,0,0,0,34,0,35,0,38,0,39,0,0,0,0,0,0,0,0,0,50,0,51,0,54,0,55,0,0,0,0,0,0,0,0]
def aliasMap56 : Array Nat := #[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap57 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def rootAliases : QFast.AliasTable
  | 1 => some (0, aliasMap22)
  | 2 => some (0, aliasMap21)
  | 3 => some (0, aliasMap20)
  | 4 => some (0, aliasMap19)
  | 5 => some (0, aliasMap18)
  | 6 => some (0, aliasMap8)
  | 7 => some (0, aliasMap6)
  | 8 => some (0, aliasMap5)
  | 9 => some (0, aliasMap4)
  | 10 => some (0, aliasMap3)
  | 11 => some (0, aliasMap27)
  | 17 => some (12, aliasMap33)
  | 18 => some (12, aliasMap57)
  | 19 => some (13, aliasMap48)
  | 20 => some (13, aliasMap32)
  | 21 => some (14, aliasMap55)
  | 22 => some (14, aliasMap54)
  | 23 => some (14, aliasMap17)
  | 24 => some (13, aliasMap47)
  | 25 => some (13, aliasMap46)
  | 26 => some (13, aliasMap45)
  | 27 => some (16, aliasMap44)
  | 28 => some (15, aliasMap43)
  | 29 => some (16, aliasMap42)
  | 30 => some (16, aliasMap41)
  | 31 => some (15, aliasMap40)
  | 32 => some (13, aliasMap39)
  | 33 => some (15, aliasMap16)
  | 34 => some (15, aliasMap38)
  | 35 => some (16, aliasMap31)
  | 36 => some (15, aliasMap53)
  | 37 => some (15, aliasMap52)
  | 38 => some (15, aliasMap15)
  | 39 => some (15, aliasMap51)
  | 40 => some (15, aliasMap49)
  | 41 => some (15, aliasMap14)
  | 42 => some (15, aliasMap30)
  | 43 => some (16, aliasMap36)
  | 44 => some (15, aliasMap13)
  | 45 => some (15, aliasMap29)
  | 46 => some (16, aliasMap35)
  | 47 => some (15, aliasMap12)
  | 48 => some (12, aliasMap28)
  | 49 => some (13, aliasMap11)
  | 50 => some (16, aliasMap26)
  | 51 => some (16, aliasMap34)
  | 52 => some (15, aliasMap10)
  | 53 => some (13, aliasMap9)
  | 54 => some (13, aliasMap7)
  | 55 => some (14, aliasMap2)
  | 62 => some (56, aliasMap56)
  | 63 => some (58, aliasMap50)
  | 64 => some (58, aliasMap37)
  | 65 => some (59, aliasMap25)
  | 66 => some (60, aliasMap24)
  | 67 => some (60, aliasMap23)
  | 68 => some (61, aliasMap1)
  | _ => none
end SignedProjection


namespace SignedProjection

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 16 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_16 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 16 16 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_32 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 32 16 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_48 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 48 16 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_64 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 64 6 = true := by decide +kernel

theorem joinRoots_0_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 32 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 16 16 blockRoots_0 blockRoots_16

theorem joinRoots_0_32 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 32 32 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 32 16 16 blockRoots_32 blockRoots_48

theorem joinRoots_1_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 64 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 32 32 joinRoots_0_0 joinRoots_0_32

theorem joinRoots_2_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 70 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 64 6 joinRoots_1_0 blockRoots_64

theorem certifiedRoots : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 70 = true := joinRoots_2_0

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
theorem blockNodes_72 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 72 9 = true := by decide +kernel

theorem joinNodes_0_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 12 12 blockNodes_0 blockNodes_12

theorem joinNodes_0_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 24 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 24 12 12 blockNodes_24 blockNodes_36

theorem joinNodes_0_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 48 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 48 12 12 blockNodes_48 blockNodes_60

theorem joinNodes_1_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 48 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 24 24 joinNodes_0_0 joinNodes_0_24

theorem joinNodes_1_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 48 33 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 48 24 9 joinNodes_0_48 blockNodes_72

theorem joinNodes_2_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 81 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 48 33 joinNodes_1_0 joinNodes_1_48

theorem certifiedNodes : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 81 = true := joinNodes_2_0

end SignedProjection

namespace SignedProjection
def bMatches (z : Option View) : Bool :=
  match z with
  | none => false
  | some v => vg v == (0xfee8fe80fe800000 : Word) && vk v == 10 && (vs v).toFinset == Direct64.cols.toFinset

theorem rootNegative : ¬ CoreSigned.build signedOps (0xfee8fe80fe800000 : BitVec 64) 10 Direct64.cols.toFinset := by
  have shape : bMatches (QFast.get fastViews 69) = true := by decide +kernel
  cases ev : QFast.get fastViews 69 with
  | none => simp [ev, bMatches] at shape
  | some v =>
    have valid := QFast.symCertified rootAliases fastViews fastNodes certifiedRoots certifiedNodes ev
    simp only [ev,bMatches,Bool.and_eq_true,beq_iff_eq] at shape
    change ¬ CoreSigned.build signedOps (vg v) (vk v) (vs v).toFinset at valid
    rwa [shape.1.1,shape.1.2,shape.2] at valid
end SignedProjection
end PEqualNP.Outside.L_meta_12150_aux

open PEqualNP.Outside.L_meta_12150_aux in
theorem PEqualNP.Outside.L_meta_12150 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276682368 * 2 ^ 32 + 4269801472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276682368 * 2 ^ 32 + 4269801472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  LowerSymSix.finish SignedProjection.rootNegative
