import PEqualNP.Defs

-- The witness has 13 binary gates. Any circuit with a NOT and fewer gates
-- would have at most 11 binary gates even with every negation available for free.
-- Finite signed-circuit certificates below exclude that possibility.
-- Signed-wire search and gate projections adapt the project’s Apache 2.0 proofs.
namespace PEqualNP.Outside.L_meta_12138_aux
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


namespace SignedProjection.QFast.ANode

def coords (p : Fin 12) : Array Nat := match p.val with
  | 0 => #[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63]
  | 1 => #[0,1,4,5,2,3,6,7,8,9,12,13,10,11,14,15,16,17,20,21,18,19,22,23,24,25,28,29,26,27,30,31,32,33,36,37,34,35,38,39,40,41,44,45,42,43,46,47,48,49,52,53,50,51,54,55,56,57,60,61,58,59,62,63]
  | 2 => #[0,2,1,3,4,6,5,7,8,10,9,11,12,14,13,15,16,18,17,19,20,22,21,23,24,26,25,27,28,30,29,31,32,34,33,35,36,38,37,39,40,42,41,43,44,46,45,47,48,50,49,51,52,54,53,55,56,58,57,59,60,62,61,63]
  | 3 => #[0,4,1,5,2,6,3,7,8,12,9,13,10,14,11,15,16,20,17,21,18,22,19,23,24,28,25,29,26,30,27,31,32,36,33,37,34,38,35,39,40,44,41,45,42,46,43,47,48,52,49,53,50,54,51,55,56,60,57,61,58,62,59,63]
  | 4 => #[0,2,4,6,1,3,5,7,8,10,12,14,9,11,13,15,16,18,20,22,17,19,21,23,24,26,28,30,25,27,29,31,32,34,36,38,33,35,37,39,40,42,44,46,41,43,45,47,48,50,52,54,49,51,53,55,56,58,60,62,57,59,61,63]
  | 5 => #[0,4,2,6,1,5,3,7,8,12,10,14,9,13,11,15,16,20,18,22,17,21,19,23,24,28,26,30,25,29,27,31,32,36,34,38,33,37,35,39,40,44,42,46,41,45,43,47,48,52,50,54,49,53,51,55,56,60,58,62,57,61,59,63]
  | 6 => #[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63]
  | 7 => #[0,1,4,5,2,3,6,7,8,9,12,13,10,11,14,15,32,33,36,37,34,35,38,39,40,41,44,45,42,43,46,47,16,17,20,21,18,19,22,23,24,25,28,29,26,27,30,31,48,49,52,53,50,51,54,55,56,57,60,61,58,59,62,63]
  | 8 => #[0,2,1,3,4,6,5,7,8,10,9,11,12,14,13,15,32,34,33,35,36,38,37,39,40,42,41,43,44,46,45,47,16,18,17,19,20,22,21,23,24,26,25,27,28,30,29,31,48,50,49,51,52,54,53,55,56,58,57,59,60,62,61,63]
  | 9 => #[0,4,1,5,2,6,3,7,8,12,9,13,10,14,11,15,32,36,33,37,34,38,35,39,40,44,41,45,42,46,43,47,16,20,17,21,18,22,19,23,24,28,25,29,26,30,27,31,48,52,49,53,50,54,51,55,56,60,57,61,58,62,59,63]
  | 10 => #[0,2,4,6,1,3,5,7,8,10,12,14,9,11,13,15,32,34,36,38,33,35,37,39,40,42,44,46,41,43,45,47,16,18,20,22,17,19,21,23,24,26,28,30,25,27,29,31,48,50,52,54,49,51,53,55,56,58,60,62,57,59,61,63]
  | _ => #[0,4,2,6,1,5,3,7,8,12,10,14,9,13,11,15,32,36,34,38,33,37,35,39,40,44,42,46,41,45,43,47,16,20,18,22,17,21,19,23,24,28,26,30,25,29,27,31,48,52,50,54,49,53,51,55,56,60,58,62,57,61,59,63]

def inv (p : Fin 12) : Fin 12 := match p.val with
  | 3 => 4
  | 4 => 3
  | 9 => 10
  | 10 => 9
  | _ => p

def atRow (p : Fin 12) (y : Fin 64) := Fin.ofNat 64 ((coords p)[y.val]?.getD 0)

theorem undo : ∀ (p : Fin 12) (y : Fin 64), atRow p (atRow (inv p) y) = y := by decide +kernel

def rewire (p : Fin 12) (w : Word) : Word :=
  (BitVec.ofBoolListLE (List.ofFn (fun k : Fin 64 => w[(atRow p k).val]))).cast List.length_ofFn

theorem rewire_bit (p : Fin 12) (w : Word) (j : Nat) (hj : j < 64) :
    (rewire p w)[j] = w[(atRow p ⟨j,hj⟩).val] := by
  rw [← BitVec.getLsbD_eq_getElem hj]
  simp only [rewire, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj, dite_true, Option.getD_some]

theorem rewire_inj (p : Fin 12) : Function.Injective (rewire p) := by
  intro a b h
  ext j hj
  let k := atRow (inv p) ⟨j,hj⟩
  have e : (rewire p a)[k.val] = (rewire p b)[k.val] := by rw [h]
  simpa only [rewire_bit,Fin.eta,k,undo] using e

theorem rewire_and (p : Fin 12) (x y : Word) : rewire p (x &&& y) = rewire p x &&& rewire p y :=
  BitVec.eq_of_getElem_eq fun j hj => by simp only [rewire_bit,BitVec.getElem_and]
theorem rewire_or (p : Fin 12) (x y : Word) : rewire p (x ||| y) = rewire p x ||| rewire p y :=
  BitVec.eq_of_getElem_eq fun j hj => by simp only [rewire_bit,BitVec.getElem_or]
theorem rewire_not (p : Fin 12) (x : Word) : rewire p (~~~x) = ~~~rewire p x :=
  BitVec.eq_of_getElem_eq fun j hj => by simp only [rewire_bit,BitVec.getElem_not]

theorem rewire_ops (p : Fin 12) {a b c : Word} (h : c ∈ signedOps a b) :
    rewire p c ∈ signedOps (rewire p a) (rewire p b) := by
  simp only [signedOps,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
  rcases h with rfl|rfl|rfl|rfl
  · exact Or.inl (rewire_and ..)
  · exact Or.inr (Or.inl (rewire_or ..))
  · exact Or.inr (Or.inr (Or.inl (by rw [rewire_and,rewire_not])))
  · exact Or.inr (Or.inr (Or.inr (by rw [rewire_and,rewire_not])))

theorem rewire_live (p : Fin 12) {g : Word} {k : Nat} {s : Finset Word}
    (h : CoreSigned.live signedOps g k s) :
    CoreSigned.live signedOps (rewire p g) k (s.image (rewire p)) := by
  induction k generalizing s with
  | zero => change s = {g} at h; simpa [h,CoreSigned.live]
  | succ k ih =>
    rcases h with skip | ⟨a,ha,b,hb,ne,z,hz,nz,r,hs,tail⟩
    · exact Or.inl (ih skip)
    · refine Or.inr ⟨_,Finset.mem_image_of_mem _ ha,_,Finset.mem_image_of_mem _ hb,
        (rewire_inj p).ne ne,_,rewire_ops p hz,?_,r.image (rewire p),?_,?_⟩
      · intro hm
        obtain ⟨t, ht, eq⟩ := Finset.mem_image.mp hm
        exact nz (rewire_inj p eq ▸ ht)
      · simp [hs]
      · simpa only [Finset.image_insert] using ih tail

def same (s : Fin 3) : Word := match s.val with
  | 0 => 0x9999999999999999
  | 1 => 0xc3c3c3c3c3c3c3c3
  | _ => 0xffff00000000ffff
def more (s : Fin 3) : Word := match s.val with
  | 0 => 0x2222222222222222
  | 1 => 0xc0c0c0c0c0c0c0c
  | _ => 0xffff0000
def less (s : Fin 3) : Word := match s.val with
  | 0 => 0x4444444444444444
  | 1 => 0x3030303030303030
  | _ => 0xffff00000000
def delta (s : Fin 3) : Nat := match s.val with
  | 0 => 1
  | 1 => 2
  | _ => 16

def atSw (s : Fin 3) (i : Fin 64) : Fin 64 :=
  if (same s).getLsbD i.val then i else if (more s).getLsbD i.val then
    Fin.ofNat 64 (i.val + delta s) else Fin.ofNat 64 (i.val - delta s)

def swWord (s : Fin 3) (w : Word) : Word :=
  (w &&& same s) ||| ((w >>> (delta s)) &&& more s) ||| ((w <<< (delta s)) &&& less s)

theorem sw_masks : ∀ (s : Fin 3) (i : Fin 64),
  ((same s).getLsbD i.val = true ∧ (more s).getLsbD i.val = false ∧ (less s).getLsbD i.val = false ∧ (atSw s i).val = i.val) ∨
  ((same s).getLsbD i.val = false ∧ (more s).getLsbD i.val = true ∧ (less s).getLsbD i.val = false ∧ (atSw s i).val = delta s + i.val) ∨
  ((same s).getLsbD i.val = false ∧ (more s).getLsbD i.val = false ∧ (less s).getLsbD i.val = true ∧ ¬i.val < delta s ∧ (atSw s i).val = i.val - delta s) := by decide +kernel

theorem sw_bit (s : Fin 3) (w : Word) (i : Fin 64) :
    (swWord s w).getLsbD i.val = w.getLsbD (atSw s i).val := by
  simp only [swWord,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_ushiftRight]
  rcases sw_masks s i with ⟨a,b,c,e⟩|⟨a,b,c,e⟩|⟨a,b,c,lt,e⟩
  · simp only [a,b,c,e,Bool.and_true,Bool.and_false,Bool.true_and,Bool.false_and,Bool.true_or,Bool.false_or,Bool.or_false]
  · simp only [a,b,c,e,Bool.and_true,Bool.and_false,Bool.true_and,Bool.false_and,Bool.true_or,Bool.false_or,Bool.or_false]
  · simp only [a,b,c,e,decide_eq_true i.isLt, decide_eq_false lt, Bool.not_false,Bool.and_true,Bool.and_false,Bool.true_and,Bool.false_and,Bool.true_or,Bool.false_or,Bool.or_false]

def applySw : List (Fin 3) → Word → Word
  | [], w => w
  | s::ss, w => swWord s (applySw ss w)

def rowSw : List (Fin 3) → Fin 64 → Fin 64
  | [], i => i
  | s::ss, i => rowSw ss (atSw s i)

theorem applySw_bit (ss : List (Fin 3)) (w : Word) (i : Fin 64) :
    (applySw ss w).getLsbD i.val = w.getLsbD (rowSw ss i).val := by
  induction ss generalizing i with
  | nil => rfl
  | cons a as ih => exact (sw_bit a (applySw as w) i).trans (ih _)

def swaps (p : Fin 12) : List (Fin 3) := match p.val with
  | 0 => []
  | 1 => [1]
  | 2 => [0]
  | 3 => [0,1]
  | 4 => [1,0]
  | 5 => [0,1,0]
  | 6 => [2]
  | 7 => [1,2]
  | 8 => [0,2]
  | 9 => [0,1,2]
  | 10 => [1,0,2]
  | _ => [0,1,0,2]

theorem rowSw_eq : ∀ (p : Fin 12) (i : Fin 64), rowSw (swaps p) i = atRow p i := by decide +kernel

theorem fast_rewire (p : Fin 12) (w : Word) : applySw (swaps p) w = rewire p w := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  rw [rewire_bit,← BitVec.getLsbD_eq_getElem hi,← BitVec.getLsbD_eq_getElem]
  exact (applySw_bit (swaps p) w ⟨i,hi⟩).trans (congrArg (fun x : Fin 64 => w.getLsbD x.val) (rowSw_eq p ⟨i,hi⟩))

theorem sw_fun (p : Fin 12) : applySw (swaps p) = rewire p := funext (fast_rewire p)

def matchesNode (p : Fin 12) (g : Word) (ws target : List Word) : Bool :=
  applySw (swaps p) g == g && (ordered (ws.map (applySw (swaps p))) == target)

theorem matches_sound {p : Fin 12} {g : Word} {ws target : List Word} {k : Nat}
    (ok : matchesNode p g ws target = true) (h : ¬ CoreSigned.live signedOps g k target.toFinset) :
    ¬ CoreSigned.live signedOps g k ws.toFinset := by
  simp only [matchesNode,sw_fun,Bool.and_eq_true,beq_iff_eq] at ok
  intro run
  have t := rewire_live p run
  rw [ok.1] at t
  apply h
  rw [← ok.2,perm_set (ordered_perm _)]
  have eq : (ws.map (rewire p)).toFinset = ws.toFinset.image (rewire p) := by
    ext w
    simp
  exact eq.symm ▸ t

end SignedProjection.QFast.ANode
namespace SignedProjection.QFast
abbrev Table (α : Type) := Nat × (Nat → Option α)
def get {α : Type} (t : Table α) (i : Nat) : Option α := if i < t.1 then t.2 i else none

def checkHint (views : Table View) (nodes : Table Node) (vID : Nat) (g : Word)
    (k : Nat) (ws : List Word) (hint : Nat) : Bool :=
  let val := hint/4
  match hint % 4 with
  | 0 => mismatch g ws (val % 64) ((val/64)%64)
  | 1 => match (get nodes (val % 65536)) with
    | some a => (nv a == vID) && (nk a == k) &&
        (if val < 65536 then ns a == ws else ANode.matchesNode (Fin.ofNat 12 (val / 65536)) g ws (ns a))
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
    have rej := closed _ a ha ok.1.1 ok.1.2
    rcases ok with ⟨_, ht⟩
    split at ht
    · exact (beq_iff_eq.mp ht) ▸ rej
    · exact ANode.matches_sound ht rej
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
  ⟨[⟨.and,[0,1]⟩, ⟨.and,[2,3]⟩, ⟨.and,[4,5]⟩, ⟨.and,[6,7]⟩, ⟨.or,[0,1]⟩, ⟨.or,[2,6]⟩, ⟨.or,[8,9]⟩, ⟨.or,[4,5]⟩, ⟨.and,[3,13]⟩, ⟨.or,[7,10]⟩, ⟨.and,[11,12]⟩, ⟨.or,[14,16]⟩, ⟨.and,[15,17]⟩],18⟩

theorem size : witness.size = 13 := rfl

theorem monotone : Monotone2 witness := by
  simp [Monotone2,witness]

set_option maxRecDepth 16000 in
theorem correct : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) =
    Nat.testBit (4276682240 * 2 ^ 32 + 4261445632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel

end LowerSymSix

namespace Direct64
open PEqualNP.CircuitLowerBounds SignedProjection
abbrev W := BitVec 64
abbrev basicOps (a b : W) := signedOps a b
abbrev goal : W := ~~~0xfee8fe00fe008000
open CoreSigned (build)
def tableB (x : Fin 6 → Bool) :=
  Nat.testBit (4276682240 * 2 ^ 32 + 4261445632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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

theorem low (reject : ¬ build basicOps (0xfee8fe00fe008000 : W) 11 cols.toFinset)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = tableB x) : 11 < binaryCost gs := by
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
    (reject : ¬ CoreSigned.build SignedProjection.signedOps (0xfee8fe00fe008000 : BitVec 64) 11 Direct64.cols.toFinset) :
∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276682240 * 2 ^ 32 + 4261445632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276682240 * 2 ^ 32 + 4261445632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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



namespace SignedProjection.Grouped
abbrev getOp (a b : Word) : Fin 4 → Word := ![a &&& b, a ||| b, a &&& ~~~b, b &&& ~~~a]
abbrev getKeep (a b : Word) (r : List Word) : Fin 4 → List Word := ![r, a::r, b::r, a::b::r]
abbrev Cases := BitVec 16
def covers (m : Cases) (o h : Fin 4) := m.getLsbD (4*o.val + h.val)
def joinMasks (x y z t : BitVec 4) : Cases := t ++ (z ++ (y ++ x))
theorem covers_join (x y z t : BitVec 4) (o h : Fin 4) :
    covers (joinMasks x y z t) o h = (![x,y,z,t] o).getLsbD h.val := by
  unfold covers joinMasks
  rw [BitVec.getLsbD_append (x := t) (y := z ++ (y ++ x)),
      BitVec.getLsbD_append (x := z) (y := y ++ x),
      BitVec.getLsbD_append (x := y) (y := x)]
  fin_cases o <;> fin_cases h <;> rfl

theorem signedList_slots (a b z : Word) (hz : z ∈ signedList a b) : ∃ o, z = getOp a b o := by
  simp only [signedList,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩
  · exact ⟨3,rfl⟩

theorem keep_slots (a b : Word) (r ks : List Word) (hk : ks ∈ keepChoices a b r) :
    ∃ h, ks = getKeep a b r h := by
  simp only [keepChoices,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩
  · exact ⟨3,rfl⟩
end SignedProjection.Grouped


namespace SignedProjection.Grouped

def rowTable : Bool → Bool → Bool → Bool → Cases
  | false, false, false, false => 0xffff
  | false, false, false, true => 0x303
  | false, false, true, false => 0x5005
  | false, false, true, true => 0x1100
  | false, true, false, false => 0x303
  | false, true, false, true => 0xffff
  | false, true, true, false => 0x11
  | false, true, true, true => 0x550
  | true, false, false, false => 0x5005
  | true, false, false, true => 0x11
  | true, false, true, false => 0xffff
  | true, false, true, true => 0x3030
  | true, true, false, false => 0x1100
  | true, true, false, true => 0x550
  | true, true, true, false => 0x3030
  | true, true, true, true => 0xffff

def rowKilled (g a b : Word) (r : List Word) (p q : Nat) : Cases :=
  if g.getLsbD p != g.getLsbD q && r.all (fun w => w.getLsbD p == w.getLsbD q) then
    rowTable (a.getLsbD p) (b.getLsbD p) (a.getLsbD q) (b.getLsbD q)
  else 0

def rowOp (a b : Bool) : Fin 4 → Bool := ![a && b,a || b,a && !b,b && !a]

theorem rowTable_valid : ∀ (a b u v : Bool) (o h : Fin 4),
    covers (rowTable a b u v) o h = true →
      rowOp a b o = rowOp u v o ∧ (h=1 ∨ h=3 → a=u) ∧ (h=2 ∨ h=3 → b=v) := by
  decide +kernel

theorem rowOp_get (a b : Word) (o : Fin 4) {p : Nat} (hp : p < 64) :
    (getOp a b o).getLsbD p = rowOp (a.getLsbD p) (b.getLsbD p) o := by
  fin_cases o <;> simp [getOp,rowOp,hp]

theorem rowKilled_sound {g a b : Word} {r : List Word} {p q : Nat}
    (hp : p < 64) (hq : q < 64) {o h : Fin 4}
    (hit : covers (rowKilled g a b r p q) o h = true) (k : Nat) :
    ¬ CoreSigned.live signedOps g k (getOp a b o :: getKeep a b r h).toFinset := by
  unfold rowKilled at hit
  split at hit
  next good =>
    obtain ⟨hg,hr⟩ := Bool.and_eq_true_iff.mp good
    obtain ⟨ho,ha,hb⟩ := rowTable_valid _ _ _ _ _ _ hit
    have hz := (rowOp_get a b o hp).trans (ho.trans (rowOp_get a b o hq).symm)
    apply mismatch_sound hp hq _ k
    unfold mismatch bitAt
    apply Bool.and_eq_true_iff.mpr
    refine ⟨hg,?_⟩
    simp only [List.all_cons,beq_iff_eq.mpr hz,Bool.true_and]
    fin_cases h
    · exact hr
    · simpa [getKeep,ha (Or.inl rfl)] using hr
    · simpa [getKeep,hb (Or.inl rfl)] using hr
    · simpa [getKeep,ha (Or.inr rfl),hb (Or.inr rfl)] using hr
  next => simp [covers] at hit

end SignedProjection.Grouped

namespace SignedProjection.Grouped
open CoreSigned

def keepMask (len k : Nat) : BitVec 4 :=
  if len > k then 0 else if len = k then 1 else if len+1 = k then 7 else 15

theorem keepMask_iff (a b : Word) (r : List Word) (k : Nat) (h : Fin 4) :
    (keepMask r.length k).getLsbD h.val = true ↔ (getKeep a b r h).length ≤ k := by
  unfold keepMask
  split <;> (try split) <;> (try split) <;>
    fin_cases h <;> simp +decide [getKeep] <;> omega

def eligible (s : List Word) (a b : Word) (r : List Word) (k : Nat) : Cases :=
  let mask := keepMask r.length k
  let allow (w : Word) := if w ∈ s then 0 else mask
  joinMasks (allow (a &&& b)) (allow (a ||| b)) (allow (a &&& ~~~b)) (allow (b &&& ~~~a))

theorem eligible_iff (s : List Word) (a b : Word) (r : List Word) (k : Nat) (o h : Fin 4) :
    covers (eligible s a b r k) o h = true ↔
    getOp a b o ∉ s ∧ (getKeep a b r h).length ≤ k := by
  unfold eligible
  rw [covers_join]
  have each (w : Word) : ((if w ∈ s then 0 else keepMask r.length k : BitVec 4).getLsbD h.val = true)
      ↔ w ∉ s ∧ (getKeep a b r h).length ≤ k := by
    by_cases el : w ∈ s
    · simp [el]
    · simpa [el] using keepMask_iff a b r k h
  fin_cases o <;> exact each _

theorem pair_step (goal : Word) (n : Nat) (ws : List Word) (hn : ws.Nodup)
    (done_ : ws ≠ [goal])
    (children_ : ∀ a b r, (a,b,r) ∈ pairs ws → ∀ o h : Fin 4,
      covers (eligible ws a b r n) o h = true → (getOp a b o :: getKeep a b r h).Nodup →
      ¬ live signedOps goal n (getOp a b o :: getKeep a b r h).toFinset) :
    ¬ live signedOps goal (n+1) ws.toFinset := by
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
    obtain ⟨o,ho⟩ := signedList_slots a b z (List.mem_toFinset.mp hop)
    obtain ⟨j,hj⟩ := keep_slots a b r kept hkeep
    rw [ho,hj] at hnd hraw
    apply children_ a b r hmem o j _ hnd hraw
    apply (eligible_iff ..).mpr
    exact ⟨ho ▸ hzws, hj ▸ (show kept.length ≤ n by omega)⟩
  rcases hm with direct|swap
  · exact go hp direct hs hz
  · exact go (hp.trans (.swap _ _ _)) swap (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)
end SignedProjection.Grouped


namespace SignedProjection.RecipeCache

open QFast (Table get)

structure Entry where
  viewId : Nat
  code : Nat
  out : List Word
  cost : Nat

def entryOK (stock : List Word) (e : Entry) : Bool :=
  match recipeRun 12 e.code stock with
  | some (rs, ws) => ws == e.out && rs.length == e.cost
  | none => false

theorem entryOK_sound {stock : List Word} {e : Entry} (h : entryOK stock e = true) :
    ∃ rs, generated signedOps stock.toFinset rs e.out.toFinset ∧ rs.length = e.cost := by
  unfold entryOK at h
  split at h <;> try contradiction
  rename_i rs out hr
  obtain ⟨rfl, cost⟩ := Bool.and_eq_true_iff.mp h |>.imp (fun z => eq_of_beq z) (fun z => eq_of_beq z)
  exact ⟨rs, recipeRun_sound _ _ _ hr, cost⟩

def checkAt (stockAt : Nat → List Word) (entries : Table Entry) (i : Nat) : Bool :=
  match get entries i with
  | some e => entryOK (stockAt e.viewId) e
  | none => true

def stockAtOK (views : Table View) (stockAt : Nat → List Word) (i : Nat) : Bool :=
  match get views i with
  | some v => vs v == stockAt i
  | none => true

def ValidCache (views : Table View) (entries : Table Entry) : Prop :=
  ∀ (i : Nat) (e : Entry) (v : View), get entries i = some e → get views e.viewId = some v →
    ∃ rs, generated signedOps (vs v).toFinset rs e.out.toFinset ∧ rs.length = e.cost

theorem result {views : Table View} {entries : Table Entry} (h : ValidCache views entries)
    {i : Nat} {e : Entry} {v : View} (he : get entries i = some e) (hv : get views e.viewId = some v) :
    ∃ rs, generated signedOps (vs v).toFinset rs e.out.toFinset ∧ rs.length = e.cost :=
  h i e v he hv

theorem valid_of_blocks {views : Table View} {entries : Table Entry} {stockAt : Nat → List Word}
    (tab : QFast.passBlock (checkAt stockAt entries) 0 entries.1 = true)
    (stock : QFast.passBlock (stockAtOK views stockAt) 0 views.1 = true) : ValidCache views entries := by
  intro i e v he hv
  have ilt : i < entries.1 := by by_contra! b; simp [QFast.get, Nat.not_lt_of_ge b] at he
  have vlt : e.viewId < views.1 := by by_contra! b; simp [QFast.get, Nat.not_lt_of_ge b] at hv
  have a := QFast.block_at _ tab (i := i) (Nat.zero_le _) (by omega)
  have b := QFast.block_at _ stock (i := e.viewId) (Nat.zero_le _) (by omega)
  simp only [checkAt,he] at a
  simp only [stockAtOK,hv,beq_iff_eq] at b
  rw [b]
  exact entryOK_sound a

end SignedProjection.RecipeCache

namespace SignedProjection.Grouped
def nib (p q r s : Bool) : BitVec 4 :=
  (if p then 1 else 0) ||| (if q then 2 else 0) ||| (if r then 4 else 0) ||| (if s then 8 else 0)
theorem nib_at (p q r s : Bool) (i : Fin 4) : (nib p q r s).getLsbD i.val = (![p,q,r,s] i) := by
  fin_cases i <;> cases p <;> cases q <;> cases r <;> cases s <;> decide

def cls (p : Word → Word) (out : List Word) (w : Word) : Nat :=
  let x := p w
  if x == 0 then 2 else if out.contains x then 1 else 0

def zeros (q : Nat) := if q = 2 then 1 else 0

def cutNib (p : Word → Word) (out : List Word) (base cost ca cb : Nat) (z : Word) : BitVec 4 :=
  let c := cls p out z
  if c == 0 then 0 else
    let l := base + zeros c
    nib (decide (cost ≤ l))
       (ca != 0 && decide (cost ≤ l + zeros ca))
       (cb != 0 && decide (cost ≤ l + zeros cb))
       (ca != 0 && cb != 0 && decide (cost ≤ l + zeros ca + zeros cb))

def cutKilled (v : View) (g a b : Word) (r out : List Word) (cost k : Nat) : Cases :=
  let p := signedPin (vm v) (va v)
  if p g != vg v || p g == 0 || !(r.all fun w => cls p out w != 0) then 0 else
    let base := vk v + r.countP (fun w => p w = 0)
    let n := cutNib p out base (cost+k) (cls p out a) (cls p out b)
    joinMasks (n (a &&& b)) (n (a ||| b)) (n (a &&& ~~~b)) (n (b &&& ~~~a))

theorem nib_help (p : Word → Word) (out : List Word) (base cost : Nat) (a b : Word) (r : List Word)
    (hr : ∀ x ∈ r, cls p out x ≠ 0)
    (h : Fin 4) (z : Word)
    (ok : (cutNib p out (base + r.countP (fun w => p w = 0)) cost
       (cls p out a) (cls p out b) z).getLsbD h.val = true) :
    (∀ x ∈ z :: getKeep a b r h, cls p out x ≠ 0) ∧
      cost ≤ base + (z :: getKeep a b r h).countP (fun w => p w = 0) := by
  have zeros_eq (w : Word) : zeros (cls p out w) = if p w = 0 then 1 else 0 := by
    simp [zeros,cls]; split <;> simp_all
  simp only [cutNib] at ok
  split at ok
  · simp at ok
  rename_i hz
  have goodz : cls p out z ≠ 0 := by simpa using hz
  rw [nib_at] at ok
  fin_cases h <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
    Nat.succ_eq_add_one, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at ok
  all_goals
    simp only [getKeep, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
      Nat.succ_eq_add_one, List.forall_mem_cons, List.countP_cons, decide_eq_true_eq]
    simp_all [zeros_eq,List.countP_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem cutKilled_sound {v : View} {g a b : Word} {r out : List Word} {cost k : Nat}
    (hv : ViewOK v) (witness : ∃ rs, generated signedOps (vs v).toFinset rs out.toFinset ∧ rs.length = cost)
    {o h : Fin 4} (hit : covers (cutKilled v g a b r out cost k) o h = true)
    (nd : (getOp a b o :: getKeep a b r h).Nodup) :
    ¬ CoreSigned.live signedOps g k (getOp a b o :: getKeep a b r h).toFinset := by
  let p := signedPin (vm v) (va v)
  simp only [cutKilled] at hit
  split at hit
  · simp [covers] at hit
  rename_i passed
  have ok : (p g = vg v ∧ p g ≠ 0) ∧ (∀ x ∈ r, cls p out x ≠ 0) := by
    simpa [p, Bool.or_eq_false_iff, List.all_eq_true] using passed
  rw [covers_join] at hit
  have hn : (cutNib p out (vk v + r.countP (fun w => p w = 0)) (cost+k) (cls p out a) (cls p out b)
    (getOp a b o)).getLsbD h.val = true := by fin_cases o <;> exact hit
  have info := nib_help p out _ _ a b r ok.2 h _ hn
  obtain ⟨rs,built,eq⟩ := witness
  have bound : ¬ CoreSigned.build signedOps (p g) (vk v) (vs v).toFinset := by rw [ok.1.1]; exact hv
  apply exclude_cut (vm v) (va v) g k (vk v) _ (vs v).toFinset out.toFinset rs
    ok.1.2 bound built
  · intro y hy
    obtain ⟨nz,w,hw,rfl⟩ := (avail_mem p).mp hy
    have hgood := info.1 w (List.mem_toFinset.mp hw)
    by_contra no
    have no' : out.contains (p w) = false := by simpa using no
    change p w ≠ 0 at nz
    apply hgood
    unfold cls
    have nr : (p w == 0) = false := by simpa using nz
    dsimp only
    rw [nr,no']
    rfl
  · unfold lost
    rw [List.Nodup.card_eq_countP nd,eq]
    exact info.2
end SignedProjection.Grouped

namespace SignedProjection.Grouped
open QFast
abbrev Packets := Nat → Nat → List Nat

def oneCase (o h : Fin 4) : Cases := (1 : Cases) <<< (4*o.val + h.val)
theorem one_hit {o h i j : Fin 4} (eq : covers (oneCase o h) i j = true) : i=o ∧ j=h := by
  revert o h i j
  decide +kernel


def killedBy (views : Table View) (nodes : Table Node) (entries : Table RecipeCache.Entry)
    (owner k : Nat) (g a b : Word) (r : List Word) (tag : Nat) : Cases :=
  let arg := tag / 4
  match tag % 4 with
  | 0 => rowKilled g a b r (arg % 64) ((arg / 64) % 64)
  | 1 => match get entries arg with
    | none => 0
    | some e => if e.viewId < owner then match get views e.viewId with
      | some v => cutKilled v g a b r e.out e.cost k
      | none => 0
      else 0
  | _ =>
    let o := Fin.ofNat 4 (arg / 4)
    let h := Fin.ofNat 4 arg
    let ws := ordered (getOp a b o :: getKeep a b r h)
    if QFast.checkHint views nodes owner g k ws (4 * (arg / 16) + 1) then oneCase o h else 0

theorem killedBy_sound {views : Table View} {nodes : Table Node} {entries : Table RecipeCache.Entry}
    (cache : RecipeCache.ValidCache views entries) {owner k : Nat} {g a b : Word} {r : List Word} {tag : Nat}
    (known : ∀ i < owner, ∀ v, get views i = some v → ViewOK v)
    (closed : ∀ (i : Nat) (n : Node), get nodes i = some n → nv n = owner → nk n = k →
      ¬ CoreSigned.live signedOps g k (ns n).toFinset)
    {o h : Fin 4} (nd : (getOp a b o :: getKeep a b r h).Nodup)
    (hit : covers (killedBy views nodes entries owner k g a b r tag) o h = true) :
    ¬ CoreSigned.live signedOps g k (getOp a b o :: getKeep a b r h).toFinset := by
  simp only [killedBy] at hit
  split at hit
  · exact rowKilled_sound (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) hit k
  · split at hit
    · simp [covers] at hit
    rename_i e he
    split at hit
    · rename_i lt
      split at hit
      · rename_i v hv
        exact cutKilled_sound (known _ lt _ hv) (cache _ _ _ he hv) hit nd
      · simp [covers] at hit
    · simp [covers] at hit
  · split at hit
    · rename_i pass
      obtain ⟨rfl,rfl⟩ := one_hit hit
      have hh := QFast.checkHint_sound known closed pass
      rwa [perm_set (ordered_perm _)] at hh
    · simp [covers] at hit

def collected (f : Nat → Cases) : List Nat → Cases
  | [] => 0
  | n :: ns => f n ||| collected f ns

theorem collected_hit {f : Nat → Cases} {ns : List Nat} {o h : Fin 4}
    (hit : covers (collected f ns) o h = true) : ∃ n ∈ ns, covers (f n) o h = true := by
  induction ns with
  | nil => simp [covers,collected] at hit
  | cons n ns ih =>
    simp only [collected,covers,BitVec.getLsbD_or,Bool.or_eq_true] at hit
    rcases hit with hit|other
    · exact ⟨n,List.mem_cons_self,hit⟩
    · obtain ⟨j,hj,ok⟩ := ih other
      exact ⟨j,List.mem_cons_of_mem _ hj,ok⟩

def checkPair (ws : List Word) (k : Nat) (a b : Word) (r : List Word) (f : Nat → Cases) (ns : List Nat) :=
  eligible ws a b r k &&& ~~~collected f ns == 0

theorem checkPair_hit {ws : List Word} {k : Nat} {a b : Word} {r : List Word} {f : Nat → Cases} {ns : List Nat}
    (ok : checkPair ws k a b r f ns = true) {o h : Fin 4}
    (can : covers (eligible ws a b r k) o h = true) : ∃ n ∈ ns, covers (f n) o h = true := by
  have eq := beq_iff_eq.mp ok
  have bits := congrArg (fun m : Cases => m.getLsbD (4*o.val+h.val)) eq
  have lt : 4*o.val+h.val < 16 := by omega
  change (eligible ws a b r k &&& ~~~collected f ns).getLsbD _ = (0 : Cases).getLsbD _ at bits
  simp only [BitVec.getLsbD_and,BitVec.getLsbD_not,lt,decide_true,Bool.true_and,BitVec.getLsbD_zero] at bits
  change (eligible ws a b r k).getLsbD _ = true at can
  rw [can] at bits
  apply collected_hit
  simpa [covers] using bits

def evalNode (views : Table View) (nodes : Table Node) (entries : Table RecipeCache.Entry)
    (packet : Packets) (idx : Nat) (n : Node) : Bool :=
  match get views (nv n) with
  | none => false
  | some v => decide (ns n).Nodup && (ns n != [vg v]) &&
    match nk n with
    | 0 => true
    | k+1 => QFast.scanFrom (fun j (a,b,r) => checkPair (ns n) k a b r
          (killedBy views nodes entries (nv n) k (vg v) a b r) (packet idx j)) 0 (CoreSigned.pairs (ns n))

def nodeAt (views : Table View) (nodes : Table Node) (entries : Table RecipeCache.Entry)
    (packet : Packets) (i : Nat) : Bool :=
  match get nodes i with
  | some n => evalNode views nodes entries packet i n
  | none => true
end SignedProjection.Grouped

namespace SignedProjection.Grouped
open QFast (scanFrom Table get passBlock AliasTable symCheckRoot block_at viewAlias_sound)
theorem groupView (views : Table View) (nodes : Table Node) (entries : QFast.Table RecipeCache.Entry) (packets : Packets) (cache : RecipeCache.ValidCache views entries) (vID : Nat) (v : View)
    (hv : (get views vID) = some v)
    (earlier : ∀ i < vID, ∀ w, (get views i) = some w → ViewOK w)
    (hroots : QFast.evalRoot views nodes vID v = true)
    (hnodes : ∀ (i : Nat) (a : Node), (get nodes i) = some a → Grouped.evalNode views nodes entries packets i a = true) :
    ViewOK v := by
  have closed (k : Nat) : ∀ (i : Nat) (a : Node), (get nodes i) = some a → nv a = vID → nk a = k →
      ¬ CoreSigned.live signedOps (vg v) k (ns a).toFinset := by
    induction k with
    | zero =>
      intro i a found owner fuel h
      have ok := hnodes i a found
      simp only [Grouped.evalNode,owner,hv,fuel,Bool.and_true,Bool.and_eq_true,decide_eq_true_eq,bne_iff_ne] at ok
      exact ok.2 (singleton_list ok.1 h)
    | succ k ih =>
      intro i a found owner fuel
      have ok := hnodes i a found
      simp only [Grouped.evalNode,owner,hv,fuel,Bool.and_eq_true,decide_eq_true_eq,bne_iff_ne] at ok
      apply pair_step _ _ _ ok.1.1 ok.1.2
      intro a' b r hab o h can nd
      obtain ⟨j,good⟩ := QFast.scanFrom_sound _ ok.2 hab
      obtain ⟨tok,_,valid⟩ := checkPair_hit good can
      exact killedBy_sound cache earlier ih nd valid
  intro build_
  classical
  obtain ⟨S, sub, path⟩ := CoreSigned.compress build_
  let ws := (vs v).filter (· ∈ S)
  have eq : ws.toFinset = S := by
    ext w
    simp only [ws,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (sub hw)
  obtain ⟨q,hq⟩ := QFast.scanFrom_sound _ hroots (show ws ∈ (vs v).sublists from
    List.mem_sublists.mpr (List.filter_sublist ..))
  exact QFast.checkHint_sound earlier (closed _) hq (eq.symm ▸ path)

theorem certifiedGroup (aliases : AliasTable) (views : Table View) (nodes : Table Node)
    (entries : Table RecipeCache.Entry) (packets : Packets) (cache : RecipeCache.ValidCache views entries)
    (roots : passBlock (symCheckRoot aliases views nodes) 0 views.1 = true)
    (states : passBlock (Grouped.nodeAt views nodes entries packets) 0 nodes.1 = true)
    {i : Nat} {v : View} (hv : get views i = some v) : ViewOK v := by
  have allNodes (j : Nat) (a : Node) (ha : get nodes j = some a) : Grouped.evalNode views nodes entries packets j a = true := by
    have hj : j < nodes.1 := by by_contra! lo; simp [QFast.get, Nat.not_lt_of_ge lo] at ha
    have ok := block_at _ states (i := j) (Nat.zero_le _) (by omega)
    simpa [Grouped.nodeAt,ha] using ok
  induction i using Nat.strong_induction_on generalizing v with
  | ind i ih =>
    have hi : i < views.1 := by by_contra! lo; simp [QFast.get, Nat.not_lt_of_ge lo] at hv
    have ok := block_at _ roots (i := i) (Nat.zero_le _) (by omega)
    simp only [symCheckRoot,hv] at ok
    cases he : aliases i with
    | none =>
      exact groupView views nodes entries packets cache i v hv ih (by simpa only [he] using ok) allNodes
    | some x =>
      rcases x with ⟨j,m⟩
      simp only [he,Bool.and_eq_true,decide_eq_true_eq] at ok
      cases hh : get views j with
      | none => simp [hh] at ok
      | some w => exact viewAlias_sound (ih j ok.1 hh) (by simpa only [hh] using ok.2)


end SignedProjection.Grouped

namespace SignedProjection.RecipeCache.Data
def cw (i : Nat) : Word := BitVec.ofNat 64 (if i < 792 then (if i < 384 then (if i < 192 then (if i < 96 then (if i < 48 then (if i < 24 then (((0xa0aaaaa000000000a0aa0a0000000000a0aa000000000000a08a080000000000a02a020000000000a00a0a0000000000a00a0000000000009000900000000000500500000000000030030000000000000ff00000000000000f000000000000000aa00000000000000a500000000000000a0a000000000000099000000000000000f0000000000000000ff00000000000000f0f0000000000000f000000000000000ee00000000000000cc00000000000000aa000000000000009900 : Nat) >>> (64*(i-0))) % 18446744073709551616) else (((0x3000c00000000000230023000000000022228888000000002200880000000000210021000000000011001100000000000f0f0f00000000000f0f0000000000000f0c0000000000000f0a0000000000000f050000000000000f030000000000000f00ff00000000000f00f000000000000f000f00000000000f000c00000000000f000000000000000c0ccccc000000000c0cc0c0000000000c0cc000000000000c08c080000000000c04c040000000000c00c0c0000000000c00c000 : Nat) >>> (64*(i-24))) % 18446744073709551616)) else (if i < 72 then (((0x880088880000000088008800000000008484848400000000848484000000000084008484000000008400840000000000820082000000000080808080000000008080202000000000555555000000000055550000000000005500aa0000000000550055000000000055000000000000005050a0a0000000005000a0000000000044448888000000004400880000000000333333000000000033330000000000003300cc000000000033000000000000003030c0c0000000003000f000 : Nat) >>> (64*(i-48))) % 18446744073709551616) else (((0xa080a08000000000a020a02000000000a000a0a000000000a000a00000000000999999000000000099990000000000009990000000000000998800000000000099110000000000009900990000000000990000000000000090909090000000009090900000000000909000000000000090809080000000009010901000000000900090900000000090009000000000008c8c8c8c000000008c008c000000000088888888000000008888880000000000888800000000000088808880 : Nat) >>> (64*(i-72))) % 18446744073709551616))) else (if i < 144 then (if i < 120 then (((0xc300000000000000c000c00000000000bbbbbb0000000000bbbb000000000000bb00000000000000b0b0b0b000000000b000b00000000000afafaf0000000000afaf000000000000af00af0000000000af00000000000000aaaaaaaa00000000aaaaaa0000000000aaaa000000000000aa00aa0000000000aa00000000000000a5a5000000000000a584000000000000a521000000000000a500a50000000000a500000000000000a0a0a0a000000000a0a0a00000000000a0a00000 : Nat) >>> (64*(i-96))) % 18446744073709551616) else (((0xff00ff0000000000ff00cc0000000000ff00000000000000f5f5f50000000000f5f5000000000000f3f3f30000000000f3f3000000000000f0f0f0f000000000f0f0f00000000000f0f0000000000000f000f00000000000f000000000000000eeeeeeee00000000ee00ee0000000000e0e0e0e000000000dddddd0000000000dddd000000000000cfcfcf0000000000cfcf000000000000cccccccc00000000cccccc0000000000cccc000000000000cc00cc0000000000cc000000 : Nat) >>> (64*(i-120))) % 18446744073709551616)) else (if i < 168 then (((0x30300000303000002300000023000000222200002222000022000000aa000000210000002100000011000000110000000f0f0000000000000f000000f00000000f0000000f0000000f000000000000000c0c0000c0c000000c0c00000c0c00000c000000c00000000a0a0000a0a000000a0a00000a0a00000a0a0000000000000a000000a000000008080000808000000808000008080000030300000000000000ff00000000000000aa000000000000000f0000000000000000ffff0000 : Nat) >>> (64*(i-144))) % 18446744073709551616) else (((0xa0000000a0a00000a0000000a00000009999000000000000990000009900000099000000000000009090000090900000908000009080000090000000900000008c8c00008c8c00008c0000008c0000008a8a00008a8a0000888800008888000088000000880000008484000084840000840084008400000084000000848400008400000084000000808000008080000055550000000000005500000055000000505000005050000044440000444400003333000000000000330000003300 : Nat) >>> (64*(i-168))) % 18446744073709551616)))) else (if i < 288 then (if i < 240 then (if i < 216 then (((0xcccc000000000000cc000000cc000000cc00000000000000c0c00000c0c00000bbbb000000000000bb000000bb000000b0b00000b0b00000afaf000000000000af000000af000000af00000000000000aaaa0000aaaa0000aaaa000000000000aa000000aa000000aa00000000000000a5a5000000000000a584000000000000a521000000000000a5000000a5000000a500000000000000a2a20000a2a20000a0a00000a0a00000a0800000a0800000a0200000a0200000a000a000a000 : Nat) >>> (64*(i-192))) % 18446744073709551616) else (((0x500000050000000040004400040000003030000000000000300000300000000030000003000000000ffff000000000000ff000000ff000000ff00000000000000f5f5000000000000f5000000f5000000f3f3000000000000f3000000f3000000f0f00000f0f00000f0f0000000000000f0000000f0000000f000000000000000eeee0000eeee0000ee000000ee000000e0e00000e0e00000dddd000000000000dd000000dd000000cfcf000000000000cf000000cf000000cccc0000cccc : Nat) >>> (64*(i-216))) % 18446744073709551616)) else (if i < 264 then (((0xa00a0000a00a0000a00a000000000000a000aa000a000000a000a0a0a0a0a000a000a0a000a00000a000a0a000000000a000a000a000a000a000a00000000000a00080a000800000a00020a000200000a0000a0000000000a00000a0a0000000a00000a000a00000a00000a000000000a0000000a0000000990000000000000090000000900000008800000088000000808000080800000080080080080000008000880008000000800080080008000080000008000000005000005000000 : Nat) >>> (64*(i-240))) % 18446744073709551616) else (((0xc0c0000000000000c00c00c00c000000c00c000000000000c000cc000c000000c000c0c0c0c0c000c000c0c000c00000c000c0c000000000c000c000c000c000c000c00000000000c00080c000800000c0000c0000000000c00000c000c00000c00000c000000000c0000000c0000000b000b00000000000b0000b0000000000a0a0000a0a000000a0a00000a0a00000a0a00000a0000000a0a0000080800000a0a0000020200000a0a0000000a00000a0a0000000000000a00a00a00a000 : Nat) >>> (64*(i-264))) % 18446744073709551616))) else (if i < 336 then (if i < 312 then (((0xf0f0f00000000000f0f0000f00000000f0f0000000000000f00f000000000000f000f000f0000000f000f00000000000f000c00000000000f000a00000000000f000300000000000f0000f0000000000f00000f0f0000000f00000f000000000f000000f00000000f0000000f0000000f0000000c0000000f000000030000000f000000000000000e000e000e000e000e000e00000000000e0000e0000000000c0c0000c0c000000c0c00000c0c00000c0c00000c0000000c0c0000000c00 : Nat) >>> (64*(i-288))) % 18446744073709551616) else (((0x440044004400440033333300000000003333000000000000330033003300000033003300000000003300300033003000330000330000000033000000cc0000003300000033000000330000000000000030300000c0c0000030300000303000003000303000300000300030003000300023000023230000002222000088880000222200002222000022002222222222002200222200220000220022002200220022002200000000002200008800000000220000002200000020002080008000 : Nat) >>> (64*(i-312))) % 18446744073709551616)) else (if i < 360 then (((0x880088008800880088008800000000008800008888000000880000880000000088000000880000008800000000880000808080008080800080008080808080008000808000800000800080008000800055555500000000005500aa00000000005500550055000000550055000000000055005000550050005500005500000000550000005500000055000000000000005000a05000a00000500050500050000050005000500050004400884400880000440044444444440044004444004400 : Nat) >>> (64*(i-336))) % 18446744073709551616) else (((0xa00000a0a0000000a00000a000000000a000000000a00000999999000000000099990000000000009900900099009000990000009900000099000000000000009090900000000000909000009090000090009000900090009000900000000000900000909000000090000000900000008c8c8c008c8c8c008c008c8c8c8c8c008c00008c000000008c000000008c00008a008a008a008a00888800008888000088880000000000008880880088808800880088880088000088008800888888 : Nat) >>> (64*(i-360))) % 18446744073709551616))))) else (if i < 576 then (if i < 480 then (if i < 432 then (if i < 408 then (((0xaa22aa00aa22aa00aa00aaaaaaaaaa00aa00aaaa00aa0000aa00aaaa00000000aa00aa8800880000aa00aa22aa22aa00aa00aa00aa00aa00aa00aa00aa000000aa00aa0000000000aa00a000aa00a000aa0000aa00000000aa000000aa000000aa00000000aa0000aa0000000000aa00aa00000000000000a200a200a200a200a0a3a000a0a3a000a0a0a000a0a0a000a0a00000a0a00000a000a0a3a0a3a000a000a0a0a0a0a000a000a0a000a00000a000a000a000a000a000a000000000 : Nat) >>> (64*(i-384))) % 18446744073709551616) else (((0xc000c000c000c000bbbbbb0000000000bb00bb00bb000000bb00b000bb00b000bb000000bb000000bb00000000000000ba00ba00ba00b000b80088b8b8888800b000b000b000b000afafaf00af000000afafaf0000000000af00afafaf000000af00af00af000000af00af0000000000af0000afaf000000af000000af000000af0000008c000000af00000023000000af00000000000000aaaaaa00aaaaaa00aaaaaa0000000000aaaa0000aaaa0000aaaa0000aa000000aaaa0000000000 : Nat) >>> (64*(i-408))) % 18446744073709551616)) else (if i < 456 then (((0xee00000000000000e000e000e000e000dddddd0000000000dd00dd00dd000000dd000000dd000000dd00000000000000cfcfcf0000000000cf00cf00cf000000cf008a00cf008a00cf000000cf000000cf00000000000000cccccc0000000000cccc0000cccc0000cccc000000000000cc00cccc00cc0000cc00cc00cc00cc00cc00cc0000000000cc0000cc00000000cc000000cc000000cc00000000cc0000cc0000000000cc00cc00000000000000c0c00000c0c00000c000c0c000c000 : Nat) >>> (64*(i-432))) % 18446744073709551616) else (((0xf300f300f3000000f300a200f300a200f3000000f3000000f300000000000000f0f0f00000000000f0f00000f0f00000f0f0000000000000f000f0f000f00000f000f000f000f000f000f000f0000000f000f00000000000f00000f000000000f0000000f0000000f000000000f00000f00000000000f000f000000000000000eeee0000eeee0000eeee000000000000ee00eeee00ee0000ee00ee0000000000ee0000ee00000000ee000000eeee0000ee000000ee000000ee00000000ee00 : Nat) >>> (64*(i-456))) % 18446744073709551616))) else (if i < 528 then (if i < 504 then (((0x1010000010100000100040010004000010002001000200001000200040008000100020000000000010001001000100001000100010001000100000010000000010000000400000000ffff0000ff000000ffff000000000000fff00000fff00000ffaa0000ffaa0000ffaa000000000000ff00ffff00000000ff00ff0000000000ff0000ff00000000ff000000ff000000ff00000000000000f5f5f50000000000f500f500f5000000f5000000f5000000f500000000000000f3f3f300000000 : Nat) >>> (64*(i-480))) % 18446744073709551616) else (((0x20a020a020a020a02080208208020800208020802080208020802080000000002080000208000000208000010400000020222220202222202020202000000000202000020200000020200000202000002000200200020000200020010001000010801080000000001080000108000000108000000000000010402080000000001040104000000000104000010400000010400000104000001010404000000000101020200000000010101010000000001010000101000000101000004040000 : Nat) >>> (64*(i-504))) % 18446744073709551616)) else (if i < 552 then (((0x30c000030c00000030c000020800000030c0000030c0000030803080000000003080000030800000303333300000000030330300000000003030c0c000000000303030300000000030303000303030003030000030300000303000000000000030033000300330003003000030030000300200003002000030003003000300003000300200020000300030003000300030003000000000003000200030002000300000030000000030000000300000002220222022202220220022002200220 : Nat) >>> (64*(i-528))) % 18446744073709551616) else (((0x420000004200000040c040c00000000040c000040c00000040804084080408004080408040804080408040800000000040800000408000004044444040444440404040400000000040400004040000004040000040400000404000000004040040084000400840004000400840084000400040040004000040004000400040003330000033300000330033000000000033000000330000003200320000000000320000003200000030c208000000000030c030c00000000030c020800000000 : Nat) >>> (64*(i-552))) % 18446744073709551616)))) else (if i < 672 then (if i < 624 then (if i < 600 then (((0x555000005550000050f0000050f0000050f000000000000050a050a00000000050a000050a00000050a0000050a0000050555550000000005050505000000000505050005050500050500000505000005050000000000000500a500000000000500550005005500050050000500500005000f0005000f0005000500500050000500050005000500050005000000000005000000a500000005000000500000000500000005000000048004800480048004440444044404440420042000000000 : Nat) >>> (64*(i-576))) % 18446744073709551616) else (((0x80800002020000008080000080800000808000004040000080800000303000008080000020202020808000000008080080008008800880008000800800080000800080040004000080008002000200008000800080008000800080003000300080005000800050008000400080004000800030008000300080002008800220008000200080002000707000070700000070700000707000007070000000000000700070007000700070007000000000005a005a00000000005a0000005a00000 : Nat) >>> (64*(i-600))) % 18446744073709551616)) else (if i < 648 then (((0x8800880000000000880000008800000080a080a00000000080a040500000000080a0000080a000008088080080880800808080888888888080808088080808008080808080808080808080802020202080808080000000008080800080808000808050500000000080804040808040408080303000000000808020208080202080802020808000008080202000800020808020200000000080800080202000208080000a0a00000080800008888000008080000808000000808000040400000 : Nat) >>> (64*(i-624))) % 18446744073709551616) else (((0xa0a0000000008080a0a00000000000a0a0a0000000000000a080a08000000000a0800000a0800000a00aa000a00aa000a00a0000a00a0000a000f000a000f000a000a00a000a0000a000a000a000a000a000a00080008000a000a00000000000a0008000a0008000a0004000a0004000a000000a00000000a0000000500000009990000099900000909999900000000090909090000000009090000090900000900990009009900090009000900090009000900000000000900000099000000 : Nat) >>> (64*(i-648))) % 18446744073709551616))) else (if i < 720 then (if i < 696 then (((0xaaa0a0a0aaa0a0a0aaa00000aaa00000a0f00000a0f00000a0aaaaa000000000a0aa0a00a0aa0a00a0aa0a0000000000a0a0a0aaaaaaaaa0a0a0a0aa0a0a0a00a0a0a0a808080800a0a0a0a0a0a0a0a0a0a0a0a0a0a00000a0a0a0a000000000a0a0a000a0a0a000a0a0a00000000000a0a08080a0a08080a0a0808000000000a0a0404000000000a0a000a000000000a0a0000a0a000000a0a00000a0a00000a0a0000080800000a0a0000000a00000a0a00000000a0a00a0a000000000a0a : Nat) >>> (64*(i-672))) % 18446744073709551616) else (((0xc000c000f000f000c000c000c000c000c000c00000000000c0008000c0008000c0003000c0003000c0003000c0000000c000300000000000c000000030003000c000000030000000bbb0bbb0bbb00000bbb00000bbb00000b0bbbbb000000000b0b0b0b000000000b0b0b000b0b0b000b0b0000bbbb00000b0b00000b0b00000b0b0000000000000b0a0b0a0b0a0b000b00bb000b00bb000b000b00bbbb0b000b000b00bb00bb000b000b000b000b000aaa0aaa0aaa0aaa0aaa0aaa0aaa0000 : Nat) >>> (64*(i-696))) % 18446744073709551616)) else (if i < 744 then (((0xc0c2020000000000c0c0f0f000000000c0c0c0cc0c0c0c00c0c0c0c0c0c0c0c0c0c0c0c000000000c0c0c000c0c0c000c0c0c00000000000c0c08080c0c08080c0c0808000000000c0c0303000000000c0c000c000000000c0c0000c0c000000c0c0000404000000c0c00000c0c00000c0c0000030300000c0c0000000c00000c0c00000000c0c00c0c000000000c0c0c0c00000000000c0c0c0000000000000c0800000c0800000c00c0000c00c0000c0020000c0020000c000c00c000c000 : Nat) >>> (64*(i-720))) % 18446744073709551616) else (if i < 768 then (((0xf000f00000000000f000c000f000c000f000a000f000a000f000a00000000000f0005000f0005000f000000f00000000f0000000f0000000f0000000c0000000f0000000000f0000f00000000000f000f00000000000c000f000000000000000e0ee0e00e0ee0e00e0e0e0ee0e0e0e00e0e0e0e0e0e0e0e0e0e0000e0e000000e0e00000e0e00000e0e0000000000000e00e0000e00e0000e000e000e000e000c0f0c0f0c000c000c0f0c000c0f0c000c0cc0c00c0cc0c00c0cc0c000000000 : Nat) >>> (64*(i-744))) % 18446744073709551616) else (((0xf0f0a0a000000000f0f0000f0f000000f0f00000f0f00000f0f00000000c0c00f0f00000000a0a00f0f0000000000000f0cf0c00f0cf0c00f0c0f0c0f0c0f0c0f0c0000000000000f0a0f0a0f0a0f0a0f0a00000f0a00000f0a0000000000000f080f080f080f080f00ff00000000000f00f0000f00f0000f00f000000000000f000f0f0f0000000f000f0f000000000f000f00f000f0000f000f00f00000000f000f000f0f0f000f000f000f000f000f000f000f0000000f000f0000000f00 : Nat) >>> (64*(i-768))) % 18446744073709551616))))))) else (if i < 1176 then (if i < 984 then (if i < 888 then (if i < 840 then (if i < 816 then (((0x111011101110bbb01100440011004400110033004400cc0011003300110033001100110044004400110011001100bb00110011001100110010b010b010b0b0b01080108010801080102040801020408010201020102010201010404010104040101010101010b0b01010101000000000101000001010000010001000100010000f0ff0f0000000000f0f0f0f0f0f00000f0f0f0f0f0000000f0f0f0f000000000f0f0f000f0f0f000f0f0f00000000000f0f0c0c0f0f0c0c0f0f0c0c00000000 : Nat) >>> (64*(i-792))) % 18446744073709551616) else (((0x202020200202020220202020000000002020200020202000202003030000000020200202202002022020000020200000202000000303000020002000200020002000200003000300200020000200020020000300200003002000020020000200118811880000000011880000118800001133000044cc0000113300001133000011224488000000001122112200000000112200001122000011112222000000001111111100000000111111001111110011110000444400001111000011110000 : Nat) >>> (64*(i-816))) % 18446744073709551616)) else (if i < 864 then (((0x222200002200000022220000000022222200880022008800220033008800cc00220022008800880022002200220022002200220000000000220000002200000021212121000000002121202000000000212100002121000021210000202000002100210021002100210021002000200021002000210020002022202220222022202120210000000020210000202100002020a0a02020a0a0202080802020808020202020a0a0a0a0202020208080808020202020202020202020202020002000 : Nat) >>> (64*(i-840))) % 18446744073709551616) else (((0x23230000230000002300af002300af0023002300af00af0023002300230023002300230000002300230000002300230022aa22aa2200220022aa22aa000022aa22aa220022aa220022aa000022aa22aa2233000088cc000022330000223300002222aaaa2222aaaa2222888822228888222288880000000022222222aaaaaaaa22222222888888882222222222222222222222222222000022222222000000002222220022222200222222000000000022220000888800002222000022220000 : Nat) >>> (64*(i-864))) % 18446744073709551616))) else (if i < 936 then (if i < 912 then (((0x3300000000003300303330303033303030330000303300003030c0c03030c0c03030c0c000000000303033330000000030303030c0c0c0c03030303030303030303030300000000030303000303030003030030300000000303000003030000030300000000030303000c0003000c00030003300300033003000303030003030300030003000300030000300300003002323afaf232300002323afaf0000000023232323afaf0000232323230000000023230000afaf00002323000023230000 : Nat) >>> (64*(i-888))) % 18446744073709551616) else (((0x3333000033330000333300000000000033303330333033303330330033303300333000003330000033223322332233223322000033220000330333003303330033030000330300003300cc003300cc003300cc000000000033003333330000003300333300000000330033303300333033003300cc00cc00330033003333330033003300330033003300330033000000330033000000330033003300000000003300300033003000330011003300110033000300330003003300000033000000 : Nat) >>> (64*(i-912))) % 18446744073709551616)) else (if i < 960 then (((0x4444111100000000444400004444000044404440444044404400cc004400cc00440088005500aa004400880044008800440044005500550044004400440044004400110044001100404440444044404440408080404080804040404040404040404040400404040440401010404010103333cccc000000003333cc003333cc0033333333cccc000033333333333300003333333333000000333333330000000033333300333333003333330000000000333330303333303033330000cccc0000 : Nat) >>> (64*(i-936))) % 18446744073709551616) else (((0x50500000050500005000f0005000f0005000a0005000a00050005500500055005000500050005000500050000500050045cf45cf45cf000045cf000045cf00004545cfcf00000000454545004545450045450000454500004500cf004500cf0045004500cfcf4500450045004500450044cc000044cc000044cc0000000000004444cccc000000004444888844448888444488880000000044444444888888884444444444444444444444444444000044444444000000004444440044444400 : Nat) >>> (64*(i-960))) % 18446744073709551616)))) else (if i < 1080 then (if i < 1032 then (if i < 1008 then (((0x550055000000000055005000550050005500050055000500550000005500000055000000000055005500000000000000545454545454545451f351f351f3000051f3000051f300005151f3f300000000515151005151510051510000515100005100f3005100f30051005100f3f35100510051005100510050f0000050f0000050550000505500005050a0a05050a0a0505055550000000050505050a0a0a0a05050505050505050505050500000000050505000505050005050000050500000 : Nat) >>> (64*(i-984))) % 18446744073709551616) else (((0x555555005555550055555500000000005555505055555050555544445555444455550000aaaa0000555500005555000055550000000000005550555055505550555055005550550055500000555000005544554455445544550555005505550055050000550500005500ff00000000005500aa005500aa005500aa000000000055005555550000005500555500000000550055505500555055005500aa00aa005500550055555500550055005500550055005500550000005500550000005500 : Nat) >>> (64*(i-1008))) % 18446744073709551616)) else (if i < 1056 then (((0x804080408040804080208020802080208008800880088008800810010000000080080000800800008000840080008400800080008000800080008000080008008000100080001000800008008000080077770000000000007700770000000000770000000000770077000000000000007070000070700000707000000000000070007000700070005555aaaa000000005555aa005555aa0055558888555588885555555588888888555555555555000055555555550000005555555500000000 : Nat) >>> (64*(i-1032))) % 18446744073709551616) else (((0x880000000000880084848484848484848484848400000000848400008484000084218421000000008421000084210000840084008400840082828282828282828282828200000000828200008282000082418241000000008241000082410000820082008200820080a080a080a080a08080909000000000808080808080808080808080101010108080808000008080808080800000000080808000808080008080101080801010808008080000000080800000808000008080000008080000 : Nat) >>> (64*(i-1056))) % 18446744073709551616))) else (if i < 1128 then (if i < 1104 then (((0x8888aaaa0000000088888888bbbb88888888888888888888888888880000000088888800888888008888808088888080888811110000000088880000aaaa0000888800008888000088880000111100008888000000008888888800000000000088808800888088008844884488448844884488440000000088440000884400008822882288228822882288220000000088220000882200008800cc008800cc008800880088008800880088001100110088001100880011008800000088000000 : Nat) >>> (64*(i-1080))) % 18446744073709551616) else (((0x8c8c0000000000008c238c23000000008c2300008c2300008c008c008c008c008c008c0000008c008c0000008c008c008b888b888b888b888acf8acf8acf00008acf8a8a8acf8a8a8acf8a008acf8a008acf00008acf00008a8acfcf000000008a8a8a8a8a8a8a8a8a8a8a008a8a8a008a8a00008a8a00008a00cf008a00cf008a008a8a8a008a8a8a008a00cfcf8a008a008a008a008a0088cc000088cc000088cc00000000000088b888b888b888b888aa88aa0000000088aa000088aa0000 : Nat) >>> (64*(i-1104))) % 18446744073709551616)) else (if i < 1152 then (((0x909000000000000090809080908090809080000090800000900990099009000090099009000000009009900090099000900980089009800890090000900900009000900090009000900090000000000090000900000000009000000090000000900000000900000090000000000090008caf8caf8c008c008caf8c008caf8c008c8cafaf000000008c8c8c8c8c8c8c8c8c8c8c8c8c008c008c8c8c8c00008c8c8c8c8c8c000000008c8c8c008c8c8c008c8c00008c8c8c8c8c8c00008c8c0000 : Nat) >>> (64*(i-1128))) % 18446744073709551616) else (((0x999099009990990099900000999000009988998899889988990900009909000099009999990000009900990099009900990099009900000099009900000000009900090099000900990000009900000099000000000099009900000000000000909900009099000090909090909090909090909090900000909090909000000090909090000000009090900090909000909090000000000090908080909080809090800090908000909000009090808090900000909000009090000000009090 : Nat) >>> (64*(i-1152))) % 18446744073709551616))))) else (if i < 1368 then (if i < 1272 then (if i < 1224 then (if i < 1200 then (((0xa0a00000a0a00000a0a000000000a0a0a0a0000000000000a080a080a080a080a050a050a050a050a050a05000000000a0500000a0500000a020a020a020a020a00aa00aa00aa00aa00aa00a00000000a00a0000a00a0000a000f000a000f000a000aa00a000aa00a000a50000000000a000a0a0a000a0a0a000a000a000a000a0000000a00000009999999999990000999999990000000099999900999999009999909099999090999900009999000099990000000000009990999099909990 : Nat) >>> (64*(i-1176))) % 18446744073709551616) else (((0xa2a2f3f300000000a2a2a2a2a2a2a2a2a2a2a200a2a2a200a2a20000a2a20000a2a0a2a0a2a0a2a0a200f300a200f300a200a2a2a200a2a2a200a200f3f3a200a200a200a200a200a0f00000a0f00000a0aaa0a0a0aaa0a0a0aa0000a0aa0000a0a0aaaa00000000a0a0a0a0a0a0a0a0a0a0a0a0a0a00000a0a0a0a0a000a000a0a0a0a080808080a0a0a0a020202020a0a0a0a00000a0a0a0a0a0a000000000a0a0a000a0a0a000a0a08080a0a08080a0a02020a0a02020a0a00000a0a0a0a0 : Nat) >>> (64*(i-1200))) % 18446744073709551616)) else (if i < 1248 then (((0xaa00aa00aa000000aa00aa000000aa00aa00aa0000000000aa00a000aa00a000aa000a00aa000a00aa000000aa000000aa0000000000aa00aa00000000000000a5a5a5a5a5a50000a5a5a5a500000000a5a50000a5a50000a5a0a5a0a5a0a5a0a521a52100000000a5210000a5210000a500a500a500a500a500a500a5000000a500a50000000000a5000000a5000000a3a0a3a00000a3a0a3a00000a3a0a3a0a2f3a2f3a2f30000a2f3a2a2a2f3a2a2a2f3a200a2f3a200a2f30000a2f30000 : Nat) >>> (64*(i-1224))) % 18446744073709551616) else (((0xaaaa00000000aa00aaaa000000000000aaa0aaa0aaa0aaa0aaa0aaa0aaa00000aaa0aa00aaa0aa00aaa00000aaa00000aa88aa88aa88aa88aa88aa88aa880000aa88aa88aa00aa00aa888888aa888888aa55aa5500000000aa550000aa550000aa22aa22aa22aa22aa22aa22aa220000aa22aa2200000000aa220000aa220000aa0aaa00aa0aaa00aa0a0000aa0a0000aa00ff0000000000aa00aaaaaa000000aa00aaaa00000000aa00aaa0aa00aaa0aa00aa00aaaaaa00aa00aa00aa00aa00 : Nat) >>> (64*(i-1248))) % 18446744073709551616))) else (if i < 1320 then (if i < 1296 then (((0xaf00af0000000000af008c00af008c00af002300af002300af000000af00af00af000000af000000af00000000000000acac000000000000aaaaaaaaaaaaaaaaaaaaaaaaaaaa0000aaaaaaaaaa00aa00aaaaaaaaaa000000aaaaaaaa88888888aaaaaaaa22222222aaaaaaaa0000aaaaaaaaaaaa00000000aaaaaa00aaaaaa00aaaaaa0000000000aaaaa0a0aaaaa0a0aaaa8888aaaa8888aaaa2222aaaa2222aaaa0a0aaaaa0a0aaaaa0000aaaaaaaaaaaa0000aaaa0000aaaa00000000aaaa : Nat) >>> (64*(i-1272))) % 18446744073709551616) else (((0xafafaf00afafaf00afafaf0000000000afaf8c8c00000000afaf232300000000afaf0000afaf0000afaf0000af000000afaf00008c8c0000afaf000023230000afaf000000000000afa00000afa0a0a0af8caf8caf8c0000af8caf8c00000000af8c0000af8c0000af23af23af230000af23af2300000000af230000af230000af00afafaf000000af00afaf00000000af00af00afafaf00af00af00af00af00af00af00af000000af00af008c008c00af00af0023002300af00af000000af00 : Nat) >>> (64*(i-1296))) % 18446744073709551616)) else (if i < 1344 then (((0xbb00b000bb00b000bb000b00bb000b00bb000000bb000000babababababab0b0bab0bab0bab0b0b0baaabaaabaaab000ba00ba00ba00b000b8b88888b8b88888b0bbb0bbb0bb0000b0bbb0b0b0bbb0b0b0bbb000b0bbb000b0bb0000b0bb0000b0b0bbbb00000000b0b0b0b0b0b0b0b0b0b0b000b0b0b000b0b00000b0b00000b0a0b0a0b0a0b000b000bb00b000bb00b000b0b0b000b0b0b000b000bbbbb000b000b000b000b000afafafafafaf0000afafafafaf000000afafafaf00000000 : Nat) >>> (64*(i-1320))) % 18446744073709551616) else (((0xbbbb0000aaaa0000bbbb000000000000bbb0bbb0bbb0bbb0bbb0bbb0bbb00000bbb0bb00bbb0bb00bbb0bb00b0b00000bbb00000bbb00000bbaabbaabbaabb00bb88bb88bb888888bb88bb8888888888bb888b88bb888b88bb888888bb888888bb0bbb0bbb0b0000bb0bbb00bb0bbb00bb0bbb000b0b0000bb0b0000bb0b0000bb00bbbbbb000000bb00bbbb00000000bb00bbb0bb00bbb0bb00bb00bbbbbb00bb00bb00bb00bb00bb00bb00bb000000bb00bb000000bb00bb00bb0000000000 : Nat) >>> (64*(i-1344))) % 18446744073709551616)))) else (if i < 1464 then (if i < 1416 then (if i < 1392 then (((0xcc000c00cc000c00cc000000cc000000c4c4c4c4c4c4c4c4c3c3c3c300000000c3c30000c3c30000c300c300c300c300c0c0cccc00000000c0c0c0c0c0c0c0c0c0c0c0c000000000c0c0c000c0c0c000c0c00000c0c00000c0c000000000c0c0c00cc00cc00cc00cc00cc00c00000000c00c0000c00c0000c000c000f000f000c000c000c000c000bbbbbbbbbbbb0000bbbbbbbbbb000000bbbbbbbb00000000bbbbbb00bbbbbb00bbbbbb0000000000bbbbb0b0bbbbb0b0bbbb0000bbbb0000 : Nat) >>> (64*(i-1368))) % 18446744073709551616) else (((0xcf000000cf000000cccccccccccccccccccccccccccc0000cccccccccc000000cccccccc00000000cccccc00cccccc00cccccc0000000000ccccc0c0ccccc0c0cccc8800cccc8800cccc4400cccc4400cccc0000cccc0000cccc00000000cccccccc000000000000ccc0ccc0ccc0ccc0ccc00000ccc00000cc88cc88cc88cc88cc888888cc888888cc0ccc00cc0ccc00cc00cccccc000000cc00cccc00000000cc00cc00cc00cc00cc00cc00cc000000cc00cc0000000000cc004400cc004400 : Nat) >>> (64*(i-1392))) % 18446744073709551616)) else (if i < 1440 then (((0xcfcfcf00cfcfcf00cfcfcf0000000000cfcf8a8acfcf8a8acfcf0000cfcf0000cfcf000000000000cf8acf8acf8acf8acf8acf8acf8a0000cf8acf00cf8acf00cf8acf008a8a0000cf8a0000cf8a0000cf45cf45cf450000cf45cf00cf45cf00cf45cf0045450000cf450000cf450000cf00cfcfcf000000cf00cfcf00000000cf00cf8acf00cf8acf00cf00cfcfcf00cf00cf00cf00cf00cf00cf00cf000000cf00cf000000cf00cf00cf0000000000cf008a00cf008a00cf004500cf004500 : Nat) >>> (64*(i-1416))) % 18446744073709551616) else (((0xe0e0000000000000e000e000e000e000dddddddddddd0000dddddddddd000000dddddddd00000000dddddd00dddddd00dddddd0000000000dddd0000dddd0000dddd000000000000ddcc0000ddcc0000ddcc000000000000dd88dd88dd888888dd00dddddd000000dd00dddd00000000dd00dd00dddddd00dd00dd00dd00dd00dd00dd00dd000000dd00dd000000dd00dd00dd0000000000dd000000dd000000d0d0d0d0d0d0d0d0cfcfcfcfcfcf0000cfcfcfcfcf000000cfcfcfcf00000000 : Nat) >>> (64*(i-1440))) % 18446744073709551616))) else (if i < 1512 then (if i < 1488 then (((0xf000f000f000f000f000f000f0000000f000f0000000f000f000f00000000000f0005000f0005000f0000000f0000000f00000000000f000f000000000000000eeeeeeee00000000eeeecccc00000000eeee0000eeee0000eeee0000aaaa0000eeee00000000eeeeeeee000000000000eecc0000eecc0000eecc000000000000ee00eeee00000000ee00ee00ee00ee00ee00ee0000000000ee000000eeee0000ee0000000000ee00ee00000000000000e0e0e0e0e0e0e0e0e0e00000e0e00000 : Nat) >>> (64*(i-1464))) % 18446744073709551616) else (((0xf300a200f300a200f3005100f3005100f3000000f3000000f0ff000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0000000f0f0f0f000000000f0f0f000f0f0f000f0f0f00000000000f0f0c0c0f0f0c0c0f0f08080f0f08080f0f00000f0f00000f0f000000000f0f0f0f0000000000000f0c0f0c0f0c0f0c0f0a0f0a0f0a0f0a0f080f080f080f080f00ff00f00000000f00f0000f00f0000f000ff0000000000f000f0f0f0000000f000f0f000000000f000f000f0f0f000 : Nat) >>> (64*(i-1488))) % 18446744073709551616)) else (if i < 1536 then (((0xf3f3f3f300000000f3f3f300f3f3f300f3f3f30000000000f3f3a2a2f3f3a2a2f3f30000f3f30000f3f3000000000000f3c0d1c0f3c0d1c0f3a2f3a2f3a2f3a2f3a2f3a2f3a20000f3a2f300f3a2f300f3a2f300a2a20000f3a20000f3a20000f351f351f3510000f351f300f351f300f351f30051510000f3510000f3510000f300f3f3f3000000f300f3f300000000f300f3a2f300f3a2f300f300f3f3f300f300f300f300f300f300f300f3000000f300f3000000f300f300f30000000000 : Nat) >>> (64*(i-1512))) % 18446744073709551616) else (if i < 1560 then (((0xff00ff0000000000ff000000ff000000ff0000000000ff00ff00000000000000f8f80000f8f80000f8f8000000000000f5f5f5f5f5f50000f5f5f5f5f5000000f5f5f5f500000000f5f5f500f5f5f500f5f5f50000000000f5f50000f5f50000f5f5000000000000f5a0f5a0f5a0a0a0f500f5f5f5000000f500f5f500000000f500f500f5f5f500f500f500f500f500f500f500f5000000f500f5000000f500f500f50000000000f5000000f5000000f3f3f3f3f3f30000f3f3f3f3f3000000 : Nat) >>> (64*(i-1536))) % 18446744073709551616) else (((0xffffffff00000000ffff0000ffff0000ffff0000ff000000ffff000000000000fff0fff000000000fff0ff0000000000fff00000fff00000fff00000f0f00000fff0000000000000ffcc000000000000ffaaffaa00000000ffaaff0000000000ffaa0000ffaa0000ffaa000000000000ff88ff8800000000ff880000ff880000ff55ff0000000000ff0fff0000000000ff0f000000000000ff00ff00ff00ff00ff00ff00ff000000 : Nat) >>> (64*(i-1560))) % 18446744073709551616))))))))
def unpack : Nat → Nat → List Word
  | 0, _ => []
  | n+1, x => cw (x % 2048) :: unpack n (x >>> 11)
def stockAt (i : Nat) : List Word :=
  let r : Nat := (if i < 144 then (if i < 72 then (if i < 24 then (((0x1fb3f27d58000000009d93a270c0000000049c8f90960000000024e44c7d30000000011d2263d18000000008b9151e6c000000004187d0f46000000002003f479b000000000f81ee3d9800000000628be15ec000000002ec5c0b360000000013c26c4bb000000000770ec1058000000003185c084c00000000154270466000000000740e01b30000000003205e0b18000000000f818022c0000000085509a056000000003f67e0fa3000000001d0364625800000000002013e0800000000000f99f04000000000007ccf7a : Nat) >>> (69*(i-0))) % 0x200000000000000000) else (if i < 48 then (((0x670cb17c2da0000001682984a01100000004407c0c8128000000009191ca1bb0000000047f8eb0898000000023fc73840c00000001096104186000000008450860b30000000041c83705d8000000017a2d453ac00000000a754826d60000000050ea1932b0000000027d4e099d8000000013ea6f4ccc000000009f5372656000000004ea9b92fb000000002464888c58000000012023f460c000000008e91ca3060000000041882d02b0000000020c41481180000000101a023e4c00000000800ff1f56000000003f87e4fb3 : Nat) >>> (69*(i-24))) % 0x200000000000000000) else (((0x8891020a3ce000000320630c214700000018e318608af8000000c51802c431c000000630c517e2c20000001cc3886908d0000000da1a42e04c8000000670c2110054000000330640be0ae0000001943205e0850000000c818c2e8438000000590ac1200840000002c0560a20aa00000015c2b05008d0000000ac1542784780000002803805403c0000001382202803a0000000981101b01f00000004a0880d01180000002404406009c000001552a44f83e6000000aa15229340d0000004ea9c93003f800000125248470774 : Nat) >>> (69*(i-48))) % 0x200000000000000000))) else (if i < 96 then (((0x13ea724d21020000009f93ea6c4c90000004f69e9372638000002794f09b930c000001262434662fa00000091922a320b90000004588ad0b1f180000022a44a864fec00000114a2642e7fe0000008a112a143fb00000044888d0b1f180000019d31a5f8b7c000000ce98b2fa5ba000000600bf9600b90000002cc594b00468000001352424344f40000009a9292183b60000004d49411f21700000026a49c9010a80000013223240848c0000009892c1fe3b20000004c0961161e100000025e4b0898fe80000012c24e4507dc : Nat) >>> (69*(i-72))) % 0x200000000000000000) else (if i < 120 then (((0x1a7b4e692d02000000d1da334167f000000688d0da133d8000003125f8b7d26c000001892f45baa9a000000c497c2a3439000000624bd16c2a28000003125eaa7d0e4000001892f45aaa7a000000c3d7fa9c42b00000061ebe54da1280000030c5f2b4d21c00000173ada5a28d6000000b856d27c2250000005beb69662358000002de5949dc4a40000016f2d85929da000000b756cac74e90000005b2b516426b8000002ac546a5504400000153aa452481a000000a254426909d00000050aa0d3fa658000002845069e9314 : Nat) >>> (69*(i-96))) % 0x200000000000000000) else (((0x9a92b24643e0000004d49512221d0000002644b08d1038000000e81c235865c000000648c61862ca0000002f45e0ba1690000001422804e89a8000000670c818822c0000002d0560a812e0000000f41e03906f0000000680cc1882d8000003125f4b7152c000001562a452c9fe0000008a513a1841d0000002684b08f10880000013225c47082c000000468850f21a60000000a01101d02d000000a153da56c678000004a294127e0d4000001b235f6904ee000000d89b03452730000006aed51a91fa8000003566aad44fbc : Nat) >>> (69*(i-120))) % 0x200000000000000000)))) else (if i < 216 then (if i < 168 then (((0x1562a552ea02000000a354628a4ff0000004b296123a428000002544a69211e40000012a25248e8ee0000008b916a164210000004528950b20d8000001e53b26e8cc4000000f29d536e63e000000794ea1b631b0000003ca74cda98c8000001e53a46d0c5c000000f29d136662a000000764e99b130b0000003aa750d81828000001b736c6c0b4c000000cc18c30a5b200000063cc69822d30000002f65e4bb16c80000015c2b0554a94000000ad1582a8542000000534a414528100000029a51ca213f80000014b29250c9ec : Nat) >>> (69*(i-144))) % 0x200000000000000000) else (if i < 192 then (((0x1d3390708d82000000e99c7b836bd00000073ae41c135d80000038b708e09a64000001c3b846fed26000000e15c237e6870000006d2d81aeb4c8000003646c2d6da54000001b23606b4d26000000d5daab53693000000676ce994b2780000033766acb99340000019b335652c96000000c49842e8565000000624bfd71aac8000003125f2b69524000001892f75aea86000000c497b2d6541000000610be5692998000002ff5f4b414bc00000171adc5a0a02000000b8d6d2ce4ff0000005bcb6965a788000002b2548a65414 : Nat) >>> (69*(i-168))) % 0x200000000000000000) else (((0x25a4af9410a20000012aa54ca083f00000094d2965041d80000049991b20222c0000024848e8ef0ee00000121e40c778510000008f71e23bc1d80000044c88f0ee1440000022644687509e00000112623c398470000008831021dc1f80000043e87b0ee0f40000021ac348630a20000010ce1943183d00000085f0ba15c2880000042d8590ae0fc00000200bec7b0efa000000fe1f63d57750000007b4f61e9bb48000003da7aef49d9c000001e2bbe774ed6000000f05df3b876900000077eef9dbbb28000003a6728e1db24 : Nat) >>> (69*(i-192))) % 0x200000000000000000))) else (if i < 240 then (((0x1756ea5cfac729e800a033e6704ba89b40049d93524a4544da0018e31660ab95585000c718ab025c8aba8003d079cec1b932b4001e83cc75cdc191a0004808f1101f03650013a6744e09510ee800630c557f2a943b40013225a46c82021a00287d0b9c128232500134e694d19510c68008cd1963243f83d4004518a11361dc2aa001bd3786e8d99a4d000c5d8aafd5c093a80005008c0f01700b400000c29766bdcf68000005d9b93592574000002b3d65abf0a200000158ab0d5f83b0000009ed366574458000004cf99d28218c : Nat) >>> (69*(i-216))) % 0x200000000000000000) else (if i < 264 then (((0xa4948e86cfc9631a3523a3f4327d4b08d3a8e51ba293c656374d4668c5149d72a2326586b055dab15021cb1a2342658c19700dd800629c2f782c1d01a00314e15bb55f27c5001782eddcfad12ea800b075f6b9d6889b40056cad75aab4430a00276cec9c12ae21500135a6acd19750da80081d009fcbde78d400408806fd1ee3c4a002044027e4f6de1d000ec5d3b9e718daa800758ea1ccb896cf4003ac74ee5dc4366a0018fb15612ba559d0007b4f31da37666a8001d43a4718d819b400629c2d76ebecf9a0030be16b9f5ce705 : Nat) >>> (69*(i-240))) % 0x200000000000000000) else (((0xc598af0cde3b0d42360fc1981af1d6d975affdfbbd778eb44c6d6ced85a8b4761a26eb41672c6d86ad116f55cab150e9950889ba94523a294225d46ed4a2915069711b4d16a514868950496edeb528a4144681cb68d7a9451fa2140a5ac6ccdf1bc3766d6d345be6f4de5bab686961371a5340670c317119fa93523a012ce351a0d49691d0e9fb2c9bc6 : Nat) >>> (69*(i-264))) % 0x200000000000000000)))))
  unpack (r % 8) (r >>> 3)
def mk (vi code extra cost : Nat) : Entry := ⟨vi,code,stockAt vi ++ unpack cost extra,cost⟩
def rowAt (i : Nat) : Entry := (if i < 871 then (if i < 415 then (if i < 216 then (if i < 96 then (if i < 48 then (if i < 24 then (mk (((0xc8602e160a8502612088401e0e06830160a048200e06028080200 : Nat) >>> (9*(i-0))) % 512) (1+0) 0 0) else (mk (((0x1b0d4682f168b0562a148a04e26128904622108803e1e0e870361a : Nat) >>> (9*(i-24))) % 512) (1+0) 0 0)) else (if i < 72 then (mk (((0x2a950a652289409a4c249208c452210c8441200fc7c3d1e0e87037 : Nat) >>> (9*(i-48))) % 512) (1+0) 0 0) else (mk (((0x389c0de6e369b0d66a3499cca6331184c05f2f174b85b2d164b057 : Nat) >>> (9*(i-72))) % 512) (1+0) 0 0))) else (if i < 144 then (if i < 120 then (mk (((0x45a29128843a190a8441a0902803f9f4f87b3d1e4f0773b1d4e873 : Nat) >>> (9*(i-96))) % 512) (1+0) 0 0) else (mk (((0x5228d44a15027d3c9d4e26d34994c25d2c954a24d249047a391a8c : Nat) >>> (9*(i-120))) % 512) (1+0) 0 0)) else (if i < 168 then (mk (((0x5eaf176ba5cae16eb65aad166b258ac15eae56ab156aa54aa14ea6 : Nat) >>> (9*(i-144))) % 512) (1+0) 0 0) else (if i < 192 then (mk (((0x6bb59aad469b49a2d067b399acc65b2992c76331588c3613017ebe : Nat) >>> (9*(i-168))) % 512) (1+0) 0 0) else (mk (((0x7a3cde4f1783b9daec75ba9d2e873b99cae471381badc6db69b2d8 : Nat) >>> (9*(i-192))) % 512) (1+0) 0 0))))) else (if i < 295 then (if i < 247 then (if i < 240 then (mk (((0x87c3a1b0c85c2a130883c1a0b048140600ff7f3edf4f97c3ddecf5 : Nat) >>> (9*(i-216))) % 512) (1+0) 0 0) else (mk (((0x45a2b1489c4a2310 : Nat) >>> (9*(i-240))) % 512) (1+0) 0 0)) else (if i < 271 then (mk (((0x422110884421fcfe7f3f9fcfe7f3f9fcfe7d3c9e0ec75299147c3e : Nat) >>> (9*(i-247))) % 512) (1024+(((0x8c0320c02004332cc7308c531440320c43004110c431000c020c8210c821 : Nat) >>> (10*(i-247))) % 1024)) (((0xc0bd14ea914e207c1903a004238410840f01a023509680d019f33c3122f83185c : Nat) >>> (11*(i-247))) % 2048) 1) else (mk (((0x47a3d1e8f47a31188c46229148a45229128944a1d0e8743a110884 : Nat) >>> (9*(i-271))) % 512) (1024+(((0x809230c0230433244032043208c832084208c832083218c83208730c4232 : Nat) >>> (10*(i-271))) % 1024)) (((0x1de4d8849271ea2786f0e0166288000bb1702cc0209e12e0400005509c9351b084 : Nat) >>> (11*(i-271))) % 2048) 1))) else (if i < 343 then (if i < 319 then (mk (((0x4e271389c4ca6530974ba5d2e974b2592c964b2592c964b23d1e8f : Nat) >>> (9*(i-295))) % 512) (1024+(((0x440320c0108c0108c332c8e234c832c8e328c6234c92340c3208f238c212 : Nat) >>> (10*(i-295))) % 1024)) (((0x390740c49620b857c230ca016328cc9890d01a02e092328650c9989312030048eb : Nat) >>> (11*(i-295))) % 2048) 1) else (mk (((0x53a9d4ea753a9d4ea753a9d4ea75329948a050281409e4f279389c : Nat) >>> (9*(i-319))) % 512) (1024+(((0xc0b018c61380d3040c320c43004c03880200c2304c11004230440108ca30 : Nat) >>> (10*(i-319))) % 1024)) (((0x12c3c82e100410abd57a9d5289f54a27d12a9b91d0ca3d4738b586839659002001 : Nat) >>> (11*(i-319))) % 2048) 1)) else (if i < 367 then (mk (((0x57ab158ac562b158ab55aad56ab55aad56ab5529d4ea753a9d4ea7 : Nat) >>> (9*(i-343))) % 512) (1024+(((0x4330c8f038c1230c330c42318c0320c4300801008332cc723c8313c4303 : Nat) >>> (10*(i-343))) % 1024)) (((0x4d49184205c0b8c114a2374621d8202d459a9f538a684dc2608006040e17102840 : Nat) >>> (11*(i-343))) % 2048) 1) else (if i < 391 then (mk (((0x68341a0cc65ae572b85c2e170b55aad56ab158ac15eaf57abd5eaf : Nat) >>> (9*(i-367))) % 512) (1024+(((0xc412004012c071204b23c4e1304f1084810007320c332c8e1344d030c830 : Nat) >>> (10*(i-367))) % 1024)) (((0x4cb12a0cc382bc2cdac04908c4edac9f12c6c819012753a49c0221c628c4d7a29d : Nat) >>> (11*(i-367))) % 2048) 1) else (mk (((0x69349a4d269349a4d269349a4d269349a4d269349a2d168b45a2d1 : Nat) >>> (9*(i-391))) % 512) (1024+(((0x8c2218821384a034c921481100c83008c210801204003c42124c92044810 : Nat) >>> (10*(i-391))) % 1024)) (((0x802e0571742e4c8a44c869091fa3fc258ff1d210c74833095900f78f91e63d419 : Nat) >>> (11*(i-391))) % 2048) 1)))))) else (if i < 631 then (if i < 511 then (if i < 463 then (if i < 439 then (mk (((0x6eb75badd6eb75badd6eb75bad96cb65b2d96cb65b0d269349a4d2 : Nat) >>> (9*(i-415))) % 512) (1024+(((0xccb308c63080d314c1100c830043328c93248c3208c034cb23c8710c0a32 : Nat) >>> (10*(i-415))) % 1024)) (((0x5e8fa8d91897d588f0fdc2b91362221890033de7bcd89b1112680522e4c8057052 : Nat) >>> (11*(i-415))) % 2048) 1) else (mk (((0x753a5d2e974ba5d2e974ba1d0e8743a1d0e8743a1d0e872b95c6e0 : Nat) >>> (9*(i-439))) % 512) (1024+(((0xf43d073290c43104320c342d0332cc11010c42100320c01090c3108421 : Nat) >>> (10*(i-439))) % 1024)) (((0x31a24ca592a01a794db9d33180a01e82107620c468860d42143484b0503f25035a : Nat) >>> (11*(i-439))) % 2048) 1)) else (if i < 487 then (mk (((0x75badd6eb75badd6eb75badd6eb75badd4ea753a9d4ea753a9d4ea : Nat) >>> (9*(i-463))) % 512) (1024+(((0x4852044043108410c8310c0210801204002d0732cc2034d110104320c010 : Nat) >>> (10*(i-463))) % 1024)) (((0x620c3978b125feb8d7cada548b394b2ce4fea58a592c2b0560f49cd36e750c6969 : Nat) >>> (11*(i-463))) % 2048) 1) else (mk (((0x76bb5d8ec763b1d8eb75badd6eb75badd6eb75badd6eb75badd6eb : Nat) >>> (9*(i-487))) % 512) (1024+(((0xc831c0d100c41000f41ccb31cc321c8312c0a438ca3188e21881434c931 : Nat) >>> (10*(i-487))) % 1024)) (((0x91d2044d2f25b8a0152a1f2548752721648e4608082813e27095118202c798db19 : Nat) >>> (11*(i-487))) % 2048) 1))) else (if i < 559 then (if i < 535 then (mk (((0x773b9dcee773b9dcee773b9dcee773b9dcee773b9dced76bb5daed : Nat) >>> (9*(i-511))) % 512) (1024+(((0x80d434c9314c1214484310841100340c8310c02408c21083328c9324c502 : Nat) >>> (10*(i-511))) % 1024)) (((0x6c141e804fe9fb3d67acf69bb2d2264f69b52be23cdd9b52821d9791792724dc95 : Nat) >>> (11*(i-511))) % 2048) 1) else (mk (((0x78bc1e0f0783c1e0ee773b9dcee773b9dcee773b9dcee773b9dcee : Nat) >>> (9*(i-535))) % 512) (1024+(((0x43438c9434404304341d0332cc730c8720c4a438ca318c22488e2184e12 : Nat) >>> (10*(i-535))) % 1024)) (((0x88e3a070e18b7d8521daac6c86315236052cd68c086a19630c5a18f31860552296 : Nat) >>> (11*(i-535))) % 2048) 1)) else (if i < 583 then (mk (((0x793c9e4f2793c9e4f278bc5e2f178bc5e2f178bc5e2f178bc5e2f1 : Nat) >>> (9*(i-559))) % 512) (1024+(((0xccb3044043104320c010d0f41ccb308d2328c1434c9304410310c410c830 : Nat) >>> (10*(i-559))) % 1024)) (((0x13e2b06f8e81ae384658b43cae997cbec3ca74cc662ac4d882e2e20c295eee54da : Nat) >>> (11*(i-559))) % 2048) 1) else (if i < 607 then (mk (((0x7a3d1e8f47a3d1e8f379bcde6f379bcde6f379bcde6f379bcde6f2 : Nat) >>> (9*(i-583))) % 512) (1024+(((0x44910108410481000b41c0e438ca3088e144d1324c11040c3008c1404341 : Nat) >>> (10*(i-583))) % 1024)) (((0x622bcd842e85a4a094c94d196034708cb254534f71ec3d673cf598c3a66e8b60a9 : Nat) >>> (11*(i-583))) % 2048) 1) else (mk (((0x7abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf47a3d1e8f4 : Nat) >>> (9*(i-607))) % 512) (1024+(((0x84e12809434c93148d214811210c42104340c8310c02108341c0a3284a02 : Nat) >>> (10*(i-607))) % 1024)) (((0x43a85994bae756ea5d5ba5744e95d339470ee99c83846c0dfdad22120e3850d24a : Nat) >>> (11*(i-607))) % 2048) 1))))) else (if i < 751 then (if i < 679 then (if i < 655 then (mk (((0x7bbddeef77bbd9ecf67b3d9ecf57abd5eaf57abd5eaf57abd5eaf5 : Nat) >>> (9*(i-631))) % 512) (1024+(((0xc8e1448c4310740cd2034d03009341ccb31cc321c831290e328c62388620 : Nat) >>> (10*(i-631))) % 1024)) (((0x1ac881d83a6716ccc3d33175ed85ca21f28e875982166525081a0a814e51ca113c : Nat) >>> (11*(i-631))) % 2048) 1) else (mk (((0x7c3e1f0f87c3e1f0f87c3e1f0f87c3e1f0f87c3e1f0f87c3ddeef7 : Nat) >>> (9*(i-655))) % 512) (1024+(((0x8c2238862050d344c9314c1214811210c42104400c8310c02108341ccb30 : Nat) >>> (10*(i-655))) % 1024)) (((0x15455ca994f81502a03c05809001fec00802fbded3c17d8f61df3d3770880a3b30 : Nat) >>> (11*(i-655))) % 2048) 1)) else (if i < 703 then (mk (((0x7f3edf6fb7dbe9f4fa7d3e9f4f97cbe1f0f87c3e1f0f87c3e1f0f8 : Nat) >>> (9*(i-679))) % 512) (1024+(((0x81344481200b238120348d0310a0441341d0332cc730c8720c4a438ca31 : Nat) >>> (10*(i-679))) % 1024)) (((0x87735e6a4a086232d9a33081b031fc3338169419995749ccc123b292a60f4560ab : Nat) >>> (11*(i-679))) % 2048) 1) else (if i < 727 then (mk (((0x7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe : Nat) >>> (9*(i-703))) % 512) (1024+(((0xcc730c8720c4a438ca3188e21881434c9314852044843108410c8310c021 : Nat) >>> (10*(i-703))) % 1024)) (((0x5b4ef9673b835e1e86b0d436a6bcb3d85b05602bd578af55eeb8d67add59623d5f : Nat) >>> (11*(i-703))) % 2048) 1) else (mk (((0x7fbfdfeff7fbfdfeff7fbfdfeff7fbfdfeff7fbfdfeff7fbfdfcfe : Nat) >>> (9*(i-727))) % 512) (1024+(((0x90e328c6238862050d324c5214811010c42104320c43008c2108010d0732 : Nat) >>> (10*(i-727))) % 1024)) (((0x10c3846a1d335e606f15dfbbb762ebdb9bb3732b3dcaacb2bee555f9410a1719b5 : Nat) >>> (11*(i-727))) % 2048) 1)))) else (if i < 799 then (if i < 775 then (mk (((0x80c06030180c06030180c06010080402010080401feff7fbfdfeff : Nat) >>> (9*(i-751))) % 512) (1024+(((0x4c93044043108400c8310c010cd332cc110108320c010d0732cc730c8720 : Nat) >>> (10*(i-751))) % 1024)) (((0xc5188ae3e14bb33dae65719bb130032f67d770eecdc99b3115c39d3708f61bfbd3 : Nat) >>> (11*(i-751))) % 2048) 1) else (mk (((0x84c260d068341a0b058241205028140a050280c06030180c060301 : Nat) >>> (9*(i-775))) % 512) (1024+(((0x80501cc23414c3090d5490d54d07015505401001d0f42d0332cc2348ca30 : Nat) >>> (10*(i-775))) % 1024)) (((0x8c91c1b919da1718867d1d19f468a082e3486743684c3cac4a00aff7de794ea98f : Nat) >>> (11*(i-775))) % 2048) 1)) else (if i < 823 then (mk (((0x88c46231188c42211087c3a1b0d86c32190b85c2a150a8542a1509 : Nat) >>> (9*(i-799))) % 512) (1024+(((0x90d5450c5410f4180501d0f43d0f300c3305533055301915541500500750 : Nat) >>> (10*(i-799))) % 1024)) (((0x19f4aa93d1fa16dde3247133e678ceb738c6dd1beb746f6298681a633a3385b50f : Nat) >>> (11*(i-799))) % 2048) 1) else (if i < 847 then (mk (((0x89c4e271389c4e27128944a25128944a25128944a25128944a2311 : Nat) >>> (9*(i-823))) % 512) (1024+(((0x50d404c05410c400c343d0b329524390a3255143509321504310832d0e54 : Nat) >>> (10*(i-823))) % 1024)) (((0xb3f676cd59bb0f1662a9ab580ae83a0d21a269eaf55bab3556ab53da614acd006f : Nat) >>> (11*(i-823))) % 2048) 1) else (mk (((0x8ac562b158ac562b158ac5229148a452291489c4e271389c4e2713 : Nat) >>> (9*(i-847))) % 512) (1024+(((0x8c15450d404c05410c400c343952435514315043d0f40cc25490e408c154 : Nat) >>> (10*(i-847))) % 1024)) (((0x311806ff5fcbf17eaf2cc497e70c3f8dbb6b6cad7da437cf35e507d1b22d4b6da2 : Nat) >>> (11*(i-847))) % 2048) 1))))))) else (if i < 1316 then (if i < 1076 then (if i < 956 then (if i < 908 then (if i < 884 then (mk (((0x1168b45a2d168b45a2b158ac562b15 : Nat) >>> (9*(i-871))) % 512) (1024+(((0x343952435514315043d0f40cc25490e40 : Nat) >>> (10*(i-871))) % 1024)) (((0x1e211639b08e0ec17808eebe47c2224720c4 : Nat) >>> (11*(i-871))) % 2048) 1) else (mk (((0x69349a4d269349a4d2692bd5eac55a9d388f462290e8442210fe7f : Nat) >>> (9*(i-884))) % 512) (1048576+(((0x8d121891104d0214c8324923049010101210d12109110cd201cd010cd010cd010c9330d0d1009001900310c8210c821cd020c5230c5020d0931c9031 : Nat) >>> (20*(i-884))) % 1048576)) (((0xa72185cc7e9111d244c7f90410241c1984921a42c868fb1f95fa344b89a92d26847c9a139a08006720788f51483545d8b80aa1392aa915b61811ea9104023818078 : Nat) >>> (22*(i-884))) % 4194304) 2)) else (if i < 932 then (mk (((0x75badd6ea753a1cadd6eb75badd6eb75badd6eb75bad269349a4d2 : Nat) >>> (9*(i-908))) % 512) (1048576+(((0x951009501084204d1014d00110c3290c31cd01090c109081090730904308911049010453304503010d10109100d110cd320cd021c9013c123290021 : Nat) >>> (20*(i-908))) % 1048576)) (((0x5d8bc5762f159ca58f49cd3d25a4468850503f209444825112084448a6fa9e44d85dd70b09444b5afaae04d8b7570adbdc2b7570a14b212ef1d0b9c7684c148b0c74 : Nat) >>> (22*(i-908))) % 4194304) 2) else (mk (((0x75badd6eb75badd6eb75badd6eb75badd6eb75badd6eb75badd6eb : Nat) >>> (9*(i-932))) % 512) (1048576+(((0xc9730c9643c9630c9430c9410c14219153290f328951089501548105143250f3250c4349643149431453214143117321153210c320d5200d5100c320 : Nat) >>> (20*(i-932))) % 1048576)) (((0x530939800285f626524aa44b69fd07ace052c6c1412a24cbc4932f16169fd8eaf963c4a98f3126060a180b1e5c4c6d56b1e24e4a98d31b624be586b0e5debc552247 : Nat) >>> (22*(i-932))) % 4194304) 2))) else (if i < 1004 then (if i < 980 then (mk (((0x76bb5daed76bb5d8ec763b1d6eb75badd6eb75badd6eb75badd6eb : Nat) >>> (9*(i-956))) % 512) (1048576+(((0xc94319153250f320d5210c72104802cd4100d5100911009010d4943d4910d4532d1732d1731d1432d0c32cd720cd420cd410cca32cc421cc020c9741 : Nat) >>> (20*(i-956))) % 1048576)) (((0x5172042dc9c93c5e64b498902a2a3bc3b4bca01782f25febc97fa80266c78932f143cc6d8312a5cc8749baf9142be55aa474aca592ea7f25427d0eace49ca5967a1f : Nat) >>> (22*(i-956))) % 4194304) 2) else (mk (((0x773b9dcee773b9dcee773b9dcee773b9dcee76bb5daed76bb5daed : Nat) >>> (9*(i-980))) % 512) (1048576+(((0x496434963149431457324572014943149311453214132117321153210c320d5210d3230d0230c721d4931d1432d1431cd721cd621cd421cca32c9631 : Nat) >>> (20*(i-980))) % 1048576)) (((0x9c21aa710c39e72be5e98c986d6a6fd079b93fa59d00897400c498c9ff4027b4da9e53d67b0cb9ed36a57a962f526cbe48e51d20645a8a9285d547c772f22f2478ba : Nat) >>> (22*(i-980))) % 4194304) 2)) else (if i < 1028 then (mk (((0x773b9dcee773b9dcee773b9dcee773b9dcee773b9dcee773b9dcee : Nat) >>> (9*(i-1004))) % 512) (1048576+(((0xd1432d1431d0c32cd721cd621cd421cca32cc421c9731c9643c9631c9431c57329153290f328491254840540325143250f3250c434d2244d22349731 : Nat) >>> (20*(i-1004))) % 1048576)) (((0x3373695a4af19936a5e2969cc6055b4a031832d524a0946a926f06a9b630d4d4af94263035d000d46314b4f59df132774daa0b36a8398ca0f3da8398fa0e63273aa4 : Nat) >>> (22*(i-1004))) % 4194304) 2) else (if i < 1052 then (mk (((0x78bc5e2f178bc5e2f178bc5e2f178bc1e0f0783b9dcee773b9dcee : Nat) >>> (9*(i-1028))) % 512) (1048576+(((0x5404150f3250f3050d1050c3250c3050c104d410494104573045430417411511050d1050c104d7434d001d4943d4931d4532d4132d1732d1731d1730 : Nat) >>> (20*(i-1028))) % 1048576)) (((0xb895ef152f9c54fb3155c5c5572b154dac5511f0ec47c2711ed73ecb8336aabba6b857170c5bec310ef0c0e8c310ecc850731d3f955d006c74027198c976a9227b60 : Nat) >>> (22*(i-1028))) % 4194304) 2) else (mk (((0x7a3d1e8f379bcde6f379bcde6f379bc5e2f178bc5e2f178bc5e2f1 : Nat) >>> (9*(i-1052))) % 512) (1048576+(((0x8d0108c1008c01d4d10cd732c8d01c8c014d1014d00148d0148c010d1010d001d0f30d0d10d0c30d0c10c174195332950108d5108c1108951054843 : Nat) >>> (20*(i-1052))) % 1048576)) (((0x5f2bcd7ca825f2a086f1cf3a64a8709cf1c25b0f71cf3dc5b0f61cf3d85b0f29cf3ca5b0f2bec3cb714f2cda3cb11e243a6bc8be60ac47393714c65c55df71712e14 : Nat) >>> (22*(i-1052))) % 4194304) 2))))) else (if i < 1196 then (if i < 1124 then (if i < 1100 then (mk (((0x7abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57a3d1e8f4 : Nat) >>> (9*(i-1076))) % 512) (1048576+(((0x50c4349731496434963149431457321494314931145321414314132117321153210c32108320d5210d5020d3230c7210c320c8d10c8c100951008d10 : Nat) >>> (20*(i-1076))) % 1048576)) (((0x75ce99d021d7300d1cd0a7748e11c714772ceb9c9ba970ceadb2bae6c6eaca3147754eadd3390728e41d1ba5742e89d30a8708859b03291c2bcc70a825dabcd7caf3 : Nat) >>> (22*(i-1076))) % 4194304) 2) else (mk (((0x7abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf5 : Nat) >>> (9*(i-1100))) % 512) (1048576+(((0xcd721cd720cd621cd421cd420cca32cc421cc020c9731c9643c9631c9630c9431c9430c5732c17219404294031940219153290f32884205143250f32 : Nat) >>> (20*(i-1100))) % 1048576)) (((0x71a859b632973e50917b7f670d68a38a843adfd9835a702875ca83472229dc90a5436e119636070051da821627ce5104b84422dfc1abab06851ca135a75ae41d7147 : Nat) >>> (22*(i-1100))) % 4194304) 2)) else (if i < 1148 then (mk (((0x7c3e1f0f87c3e1f0f87bbd9ecf67b3d9ecf67abd5eaf57abd5eaf5 : Nat) >>> (9*(i-1124))) % 512) (1048576+(((0x14132117321153210c320d5210c7210953400d0100a01cd720cd420cc020c9730c94300c32000c02d4943d4931d4532d1732d1731d1432d1431d0c32 : Nat) >>> (20*(i-1124))) % 1048576)) (((0x78101cab15780d01e00bec7fd001ec2477e3029df3e96bac91b6b2b672d6d98b5b6b8cc596b616c2cadb0b5b298eb8a53a943ceadcd947714874a7390444e1054b90 : Nat) >>> (22*(i-1124))) % 4194304) 2) else (if i < 1172 then (mk (((0x7c3e1f0f87c3e1f0f87c3e1f0f87c3e1f0f87c3e1f0f87c3e1f0f8 : Nat) >>> (9*(i-1148))) % 512) (1048576+(((0xc9740c9731c9643c9631c9431c4c03c17219404294031940219153290f32884205143250f3250c434973149643496314943114943149311453214143 : Nat) >>> (20*(i-1148))) % 1048576)) (((0x772ccdea24e7e00f5f68ab496f6055bbe76c91ca8bef470f6120bd307d01c1e9572a6ee204bec81455e054017f8939f983d7ea2adffbd87e3029f74057b301de140a : Nat) >>> (22*(i-1148))) % 4194304) 2) else (mk (((0x7f3f9fcfe7f3f9f6fa7d3e9f0f87c3e1f0f87c3e1f0f87c3e1f0f8 : Nat) >>> (9*(i-1172))) % 512) (1048576+(((0x1494314532115320d5210c7210c32014543d0023c974010023d4943d4931d4532d4132d1732d1731d1432d1431d0c32cd721cd621cd421cca32cc421 : Nat) >>> (20*(i-1172))) % 1048576)) (((0xae5616b3582b0360abcd7aacab3a23bb897335d9a3ec776cd1e2bec2b7028acc0549f01d994077ec55deea4e2bafb128bd815afb1efa477f654d2bbd32ae2b1273d3 : Nat) >>> (22*(i-1172))) % 4194304) 2)))) else (if i < 1244 then (if i < 1220 then (mk (((0x7fbfdfeff7fbfdfcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe : Nat) >>> (9*(i-1196))) % 512) (1048576+(((0x117321153210c320d5100c32009510d4532d1732d1731d1432cd720cd420cc020c9730c9631c9630c943091532540325143250c434d7204d42049731 : Nat) >>> (20*(i-1196))) % 1048576)) (((0x3a074eef5dfbb372adc5b995ef4edb5b95c560aba1b5ad2b68de56e8a8ee1e4c3b77d0ee1e3beade352b80b477911c3dd82aef5bac256eb0b5eebf3b8aff0eebb2da : Nat) >>> (22*(i-1196))) % 4194304) 2) else (mk (((0x7fbfdfeff7fbfdfeff7fbfdfeff7fbfdfeff7fbfdfeff7fbfdfeff : Nat) >>> (9*(i-1220))) % 512) (1048576+(((0xcd720cd420cd410cca32cc020c9741c9730c9643c9630c9430c9410915329151090f328d510895105143250f3250c434d41049643494101494314532 : Nat) >>> (20*(i-1220))) % 1048576)) (((0x97cf4df04a08230a0e98e17b1282b0387948f62e6886b9630deb4af81f0a043ddf1036e4431d31bb6e4e35b9bc372af11d3bc5766ee428ba021aeb428b9d78ab35df : Nat) >>> (22*(i-1220))) % 4194304) 2)) else (if i < 1268 then (mk (((0x80c06030180c06030180c06030180c0601008040200ff7fbfdfeff : Nat) >>> (9*(i-1244))) % 512) (1048576+(((0x8d5108d1018d0018c1104d7424d7404d4424d4404d41045440115321151010b320d510cd410cd101cd001115100d510d4943d4532d1732d1432d0c32 : Nat) >>> (20*(i-1244))) % 1048576)) (((0x39971cf2dc73cb130c7dc7c36c4b0e401c4f76710cf6c3d132e34f6c498a2e15c7bb2bfededc7827114035c300d116e15c3b7770ceb5e270d77ee89d33b7728715ca : Nat) >>> (22*(i-1244))) % 4194304) 2) else (if i < 1292 then (mk (((0x8542a13098341a0d0682c12090281406030180c06030180c060301 : Nat) >>> (9*(i-1268))) % 512) (1048576+(((0xcd80149b01cda0189901c98305845345b3014c301895418d5418954cd80149b01d1632d1410d0d10d0c10d0832cd742cd740cd442cd440cd41094440 : Nat) >>> (20*(i-1268))) % 1048576)) (((0x32e2d8c38a66df191754706dd18a8f50b998dca85c629e147689d1a9d5468c904c3080bb0d1d582b130f2dc73cb131895ccba6c4a72c01615765fd4f6829131e3cf6 : Nat) >>> (22*(i-1268))) % 4194304) 2) else (mk (((0x8944a231188c46231188c46231188c46231188c462310884421b0d : Nat) >>> (9*(i-1292))) % 512) (1048576+(((0x10c3210b32d8d54d5b43d5843d5043d0e43cda5495943953435584355343550544da5418d5415b43159431504314c43d5b41cda0189901c983045b30 : Nat) >>> (20*(i-1292))) % 1048576)) (((0xa7b4ae982ba3474aa8b1a034b42c6850b34033e8806f0e149c379a0a5342e951a0a5547e8a86fa274a8ce9a0a4d49e8fd0ba1f42e37b776e319175c716e118e66b73 : Nat) >>> (22*(i-1292))) % 4194304) 2)))))) else (if i < 1525 then (if i < 1412 then (if i < 1364 then (if i < 1340 then (mk (((0x8944a25128944a25128944a25128944a25128944a25128944a2512 : Nat) >>> (9*(i-1316))) % 512) (1048576+(((0x4db424da544da424d84249b4341b3241a5441a3218d5418d421894318554185431853215b431594315332150431503214f4214c4314c421193210f32 : Nat) >>> (20*(i-1316))) % 1048576)) (((0xa94b02a2074a8a346a9d30a6c6ae30aba89c1d2291a7a8557a9fd59a6356e83d5ea0156e7ad553546aead55baacaeaab53daad4aea02c0a814f6a0530aa35569eaba : Nat) >>> (22*(i-1316))) % 4194304) 2) else (mk (((0x8944a25128944a25128944a25128944a25128944a25128944a2512 : Nat) >>> (9*(i-1340))) % 512) (1048576+(((0xcdb42cda54cda42cd842c9b43c5a42984329594395343953329503290f3290c3258043580425584355343553325523255132550545503250f3250c32 : Nat) >>> (20*(i-1340))) % 1048576)) (((0xa5cb02a0874a7c3455ed30a5a6ae7d8d15734ac3ad5b0e86ac3a2ba0e94ac692ba1a54aea653da714c2aed3dabc6aeaf2baabc69eaf555abd55aaf52bab6aeaadd2b : Nat) >>> (22*(i-1340))) % 4194304) 2)) else (if i < 1388 then (mk (((0x89c4e271389c4e27128944a25128944a25128944a25128944a2512 : Nat) >>> (9*(i-1364))) % 512) (1048576+(((0x14f4014c4314c401193010f3010c3010330d8d54d8d42d8943d8143d8142d5b43d5b42d5843d5842d5043d1b32d1a32d1832d0f32d0e43d0c32d0832 : Nat) >>> (20*(i-1364))) % 1048576)) (((0xb14f36c5587b15166cb59ab0ef2ac3c558b2f28d6d5e3595656155b75756dd4d59a8c6ae99ac035d4f5625301a74f69a2baa9069d62d2b356ae8d58d23574ad6052b : Nat) >>> (22*(i-1364))) % 4194304) 2) else (mk (((0x89c4e271389c4e271389c4e271389c4e271389c4e271389c4e2713 : Nat) >>> (9*(i-1388))) % 512) (1048576+(((0x90f3090c305584355343553305523055130550545503050f3050c304db404da544da404d84041b4318d5418d401814315b4315943153301504315030 : Nat) >>> (20*(i-1388))) % 1048576)) (((0x1b2f286cc55b4361ed11beb44f2ad116db4566ad159bb45156cfbcab3f156ca3cdb1c1f6c78b5b311662f9beb1968ac4d9d8b567cde9beb3d67ecdbcab3761ecdc55 : Nat) >>> (22*(i-1388))) % 4194304) 2))) else (if i < 1460 then (if i < 1436 then (mk (((0x89c4e271389c4e271389c4e271389c4e271389c4e271389c4e2713 : Nat) >>> (9*(i-1412))) % 512) (1048576+(((0xd8d54d8d40d8143d5b43d5b40d5843d5840d5043d1b30d1a30d1830d0f30d0e43d0c30d0030cdb40cda54cda40cd840c1b4395943953439533095030 : Nat) >>> (20*(i-1412))) % 1048576)) (((0x381688dfd9d79d67ec81be8b8f34e0d8779f1646d5878baf2ac916d7a1154df3ca37c364df45579b1562c3cdb161f6c40b57991662b9be0fd67c3e9be0faf283ec55 : Nat) >>> (22*(i-1412))) % 4194304) 2) else (mk (((0x8ac562b158ac562b148a45229148a45229148a45229148a4522914 : Nat) >>> (9*(i-1436))) % 512) (1048576+(((0x14f4014c4314c401193010f3010c3010330d8d54d5b43d5843d5043d0e43cda5495943953435584355343550544da5418d5415b43159431504314c43 : Nat) >>> (20*(i-1436))) % 1048576)) (((0xbd0f92f45e5bd1312fa5f8bcaf86f2cbf988f84e25b5b5470ce2da41b9690e18dbb4c1fc405b20fe70eda5a4b6a70edadafb521fed3db538470ed8db2b5f692d2da4 : Nat) >>> (22*(i-1436))) % 4194304) 2)) else (if i < 1484 then (mk (((0x8ac562b158ac562b158ac562b158ac562b158ac562b158ac562b15 : Nat) >>> (9*(i-1460))) % 512) (1048576+(((0x90f3090c305584355343553305523055130550545503050f3050c304db404da544da404d84041b4318d5418d401814315b4315943153301504315030 : Nat) >>> (20*(i-1460))) % 1048576)) (((0x1c8f84724bfc01797009ddc02f8700988c037e300dfac032feff3e1bfd2fef93e4bd8226f68c4bed312651ddbd5806f3dfc98b7f8ee1ddbfb7fafd3e1bf5796fd4bf : Nat) >>> (22*(i-1460))) % 4194304) 2) else (if i < 1508 then (mk (((0x8ac562b158ac562b158ac562b158ac562b158ac562b158ac562b15 : Nat) >>> (9*(i-1484))) % 512) (1048576+(((0xd8d54d8d40d8143d5b43d5b40d5843d5840d5043d1b30d1a30d1830d0f30d0e43d0c30d0030cdb40cda54cda40cd840c1b4395943953439533095030 : Nat) >>> (20*(i-1484))) % 1048576)) (((0x3bf804ef5fc7cb7faf71dd98ef90f05e57cd31072de5990f86f81887cf2fceebe13ba390eecbf7c92fe613e4bd2226f30c47c7312609dd1157f8449dd112f8444cbf : Nat) >>> (22*(i-1484))) % 4194304) 2) else (mk (((0x1168b45a2d168b45a2d168b45a2d168b45a2d16 : Nat) >>> (9*(i-1508))) % 512) (1048576+(((0xd8d54d5b43d5843d5043d0e43cda5495943953435584355343550544da5418d5415b43159431504314c43 : Nat) >>> (20*(i-1508))) % 1048576)) (((0xf1e11c10788f26021cf808f10e6c0822c4660e11678b08602c2278b08e0bc0e22f02e113c278b06e0ec1780b01e02 : Nat) >>> (22*(i-1508))) % 4194304) 2))))) else (if i < 1645 then (if i < 1573 then (if i < 1549 then (mk (((0x7f3f9f0f87c3e1eaf57abcde6f1773b9dced76bb5daed76badd6eb : Nat) >>> (9*(i-1525))) % 512) (1073741824+(((0x55b430c86250c4355b430c943117321894310c604842155b430c943117321894310f56d0d109974344356d0d1055b430c943117321894310e60c96319805250d56d0c3250c45cc86250c43181250c556d0c3250c45cc86250c43 : Nat) >>> (30*(i-1525))) % 1073741824)) (((0xaea35eb7572b0b5edfb8ad7d9028ab1577e302a00bbd800f4dce0a9720eb8a314772ceb9d31ca1d073ce50e839f6f0f2dc59c83326d5073126326fd079ec5aa478ba2d12464f49317b23a4f1782f32464f49988725e40b07142be58f127254c058f312 : Nat) >>> (33*(i-1525))) % 8589934592) 3) else (mk (((0x8944a25128944a25128944a25128944623118340602ff7fbfdfcfe : Nat) >>> (9*(i-1549))) % 512) (1073741824+(((0x1c543cc87150c321c5361085750f3215d430c8549843215106cc8535804314d60108439843210d06cc8371855409c6155167d504355056d0c735505414f260c356d0d101974344156d0c3250c45cc86250c43983258c66014943 : Nat) >>> (30*(i-1549))) % 1073741824)) (((0xa0156d5d500ab74ae79d53a6156aadabaab556e95d565734aeab461575502a653da814e29853d5734ae9ec6157537e83d5e97341eaf5171a142e9519d34144e9551fa16dba315bf3cb71ce39e5b8f748715cabc4740e9dcebc5764b556f1a85a2b9585 : Nat) >>> (33*(i-1549))) % 8589934592) 3)) else (if i < 1597 then (mk (((0x8944a25128944a25128944a25128944a25128944a25128944a2512 : Nat) >>> (9*(i-1573))) % 512) (1073741824+(((0x59e540c95710f3255c430c9549843255106cc95441a32550614c95415b4355054cc9541503250e610c94341b324dc61551271855441e54cc907950321d9544c873552321cd5415073550321c554cc871552321c5544c87155032 : Nat) >>> (30*(i-1573))) % 1073741824)) (((0xa581d295d5da7aaeaaed3da575795cd2babd1855d55e8a469eaf4f5aab578d51ababd5595d55eaad4aeadab9a5756e30abaaa141eaf53ca0f57a270745751383a52baa957aaad42abc69ea155eaad50aaf52ba0f5795d507abc69e83d5eaab41eaf52b : Nat) >>> (33*(i-1573))) % 8589934592) 3) else (if i < 1621 then (mk (((0x8944a25128944a25128944a25128944a25128944a25128944a2512 : Nat) >>> (9*(i-1597))) % 512) (1073741824+(((0xd0d06ccb3718554c9c6155271c9b4395d43cca5750c32952610ca5441b3290e610ca4341b328dc6155227185545d853d097614c425c3369097018d545c053d097014c425c043cc97010c325c042cc967d504359f430c96795332 : Nat) >>> (30*(i-1597))) % 1073741824)) (((0x3571855d32aa0f57991d07abcade969ab0eb56d5d075ab74ac3a2b9a561d230aba1a4ae6958d28c2ae8c8507abcab683d5ea9350160552a814c2a6d3e1a353ea155ea9d5016054ea814c2a653d5755329ed2ba714c15d5471a74f69a9aba56af03a2ba : Nat) >>> (33*(i-1597))) % 8589934592) 3) else (mk (((0x89c4e271389c4e271389c4e271389c4e25128944a25128944a2512 : Nat) >>> (9*(i-1621))) % 512) (1073741824+(((0x59f430c1679533059e540c15710f3055c430c15415b4355054cc154150301d9544c073552301cd54150735503015d43cc05750c30dd954ccb7655232dd9540cb7355032dc143ccb7050c32dc126d0f5710f32d5c430cb4398432 : Nat) >>> (30*(i-1621))) % 1073741824)) (((0x8bc6fa2abcb0faf2a2b07d8ab686c3bcab4361e2ada237a6fad159b79568acdc55b3368acd58cb445b6c65a2b37632d1455b3d67de559eb3f1569bd5e57552eaf1a758d57a959adabd4add5d5b574eaeadd2b71d4d8d59aea7aae8d753da566ad5cd2b : Nat) >>> (33*(i-1621))) % 8589934592) 3)))) else (if i < 1690 then (if i < 1669 then (mk (((0x8ac562b158ac562b158ac5229148a44e271389c4e271389c4e2713 : Nat) >>> (9*(i-1645))) % 512) (1073741824+(((0x55056d0d5415330550540c076551301cd548c073550541cd540c05750f3015d430c17018d5459f5410d5415b431cd541537655330dd9548c37655030dcd540c35710f30d5c430c25750f3095d430c17614f405d85310167d5043 : Nat) >>> (30*(i-1645))) % 1073741824)) (((0xc02770eee01bf4f8700dfa97f7df00df8bd5804c45eac037eaf560197f7f6ff3e1bfb7fa5fdacb4f6d6d58dcb496d4e11c3b4f6d6d7c60b44f2acada22daf46d145538168a2a9c1b0ef28e0d878aa1facfbca0fd67e2ad93b14f36cbd8a8b36446d587 : Nat) >>> (33*(i-1645))) % 8589934592) 3) else (mk (((0x1168b45a2d158ac562b158ac562b158ac562b158ac562b15 : Nat) >>> (9*(i-1669))) % 512) (1073741824+(((0x17018d5459f5410d5415b431cd541537655330dd9548c37655030dcd540c35710f30d5c430c25750f3095d430c17614f405d85310171cda4059f5410d67d0c3059e54cc1679503055c43cc15710c30 : Nat) >>> (30*(i-1669))) % 1073741824)) (((0x182b02e11c1239f016113c278b02e11c1732f00be1be7804c43e8c032fcefe0197e782f2be13c17965f88abfcf84455fe97f7c6f43e4beb7a2625f9bcc312f78e5bcb324eecbf7c4225f0cc01132ff005e57c3802f2cbf : Nat) >>> (33*(i-1669))) % 8589934592) 3)) else (if i < 1714 then (mk (((0x8944a25128944a25128944a25128944a25128944a25128944a2512 : Nat) >>> (9*(i-1690))) % 512) (1099511627776+(((0xe0d5498432e093718554da07155132d604398432d604341b32ca03718554a1c535804296143984329614341b328e127185545a0715503256043984325604341b3255054984325505441b324a0371855421d549843221d541853220d549843220d5415032209371855416143984321614341b320e12718554 : Nat) >>> (40*(i-1690))) % 1099511627776)) (((0x35b5795cd2b57d54283d5e65f41eaf55535d4f55cd2b35d4f630aba65137e83d5e3515029c5300eb56d5cd2b0eb56e30aba3534f283d5ea7541eaf52babb4f55cd2babb4f630abaabd5595cd2babd55a30abaa7737e83d5e5715795cd2b9e957a7ad55a855795cd2ba8557aab52ba5f54283d5eab556d5cd2bab556e30abaa734f283d5e : Nat) >>> (44*(i-1690))) % 17592186044416) 4) else (if i < 1716 then (mk (((0x22b13 : Nat) >>> (9*(i-1714))) % 512) (1099511627776+(((0x20d541503020d5415030 : Nat) >>> (40*(i-1714))) % 1099511627776)) (((0xbd5806fd4bfb1968acdc55 : Nat) >>> (44*(i-1714))) % 17592186044416) 4) else (mk (((0x112 : Nat) >>> (9*(i-1716))) % 512) (1125899906842624+(((0x935505498432 : Nat) >>> (50*(i-1716))) % 1125899906842624)) (((0x542abd5595cd2b : Nat) >>> (55*(i-1716))) % 36028797018963968) 5))))))))
def table : QFast.Table Entry := ⟨1717, fun i => some (rowAt i)⟩
end SignedProjection.RecipeCache.Data

namespace SignedProjection.RecipeCache.Data
private abbrev rc := checkAt stockAt table
private abbrev join {s a b : Nat} (x : QFast.passBlock rc s a = true) (y : QFast.passBlock rc (s+a) b = true) : QFast.passBlock rc s (a+b) = true := QFast.merge_blocks x y
set_option maxHeartbeats 0 in
theorem checked : QFast.passBlock (checkAt stockAt table) 0 table.1 = true := (@join 0 858 859 (@join 0 429 429 (@join 0 214 215 (@join 0 107 107 (@join 0 53 54 (@join 0 26 27 (by decide +kernel) (by decide +kernel)) (@join 53 27 27 (by decide +kernel) (by decide +kernel))) (@join 107 53 54 (@join 107 26 27 (by decide +kernel) (by decide +kernel)) (@join 160 27 27 (by decide +kernel) (by decide +kernel)))) (@join 214 107 108 (@join 214 53 54 (@join 214 26 27 (by decide +kernel) (by decide +kernel)) (@join 267 27 27 (by decide +kernel) (by decide +kernel))) (@join 321 54 54 (@join 321 27 27 (by decide +kernel) (by decide +kernel)) (@join 375 27 27 (by decide +kernel) (by decide +kernel))))) (@join 429 214 215 (@join 429 107 107 (@join 429 53 54 (@join 429 26 27 (by decide +kernel) (by decide +kernel)) (@join 482 27 27 (by decide +kernel) (by decide +kernel))) (@join 536 53 54 (@join 536 26 27 (by decide +kernel) (by decide +kernel)) (@join 589 27 27 (by decide +kernel) (by decide +kernel)))) (@join 643 107 108 (@join 643 53 54 (@join 643 26 27 (by decide +kernel) (by decide +kernel)) (@join 696 27 27 (by decide +kernel) (by decide +kernel))) (@join 750 54 54 (@join 750 27 27 (by decide +kernel) (by decide +kernel)) (@join 804 27 27 (by decide +kernel) (by decide +kernel)))))) (@join 858 429 430 (@join 858 214 215 (@join 858 107 107 (@join 858 53 54 (@join 858 26 27 (by decide +kernel) (by decide +kernel)) (@join 911 27 27 (by decide +kernel) (by decide +kernel))) (@join 965 53 54 (@join 965 26 27 (by decide +kernel) (by decide +kernel)) (@join 1018 27 27 (by decide +kernel) (by decide +kernel)))) (@join 1072 107 108 (@join 1072 53 54 (@join 1072 26 27 (by decide +kernel) (by decide +kernel)) (@join 1125 27 27 (by decide +kernel) (by decide +kernel))) (@join 1179 54 54 (@join 1179 27 27 (by decide +kernel) (by decide +kernel)) (@join 1233 27 27 (by decide +kernel) (by decide +kernel))))) (@join 1287 215 215 (@join 1287 107 108 (@join 1287 53 54 (@join 1287 26 27 (by decide +kernel) (by decide +kernel)) (@join 1340 27 27 (by decide +kernel) (by decide +kernel))) (@join 1394 54 54 (@join 1394 27 27 (by decide +kernel) (by decide +kernel)) (@join 1448 27 27 (by decide +kernel) (by decide +kernel)))) (@join 1502 107 108 (@join 1502 53 54 (@join 1502 26 27 (by decide +kernel) (by decide +kernel)) (@join 1555 27 27 (by decide +kernel) (by decide +kernel))) (@join 1609 54 54 (@join 1609 27 27 (by decide +kernel) (by decide +kernel)) (@join 1663 27 27 (by decide +kernel) (by decide +kernel)))))))
theorem valid {views : QFast.Table View} (stock : QFast.passBlock (stockAtOK views stockAt) 0 views.1 = true) : ValidCache views table := valid_of_blocks checked stock
end SignedProjection.RecipeCache.Data

namespace SignedProjection.Grouped
def packetField (w k i : Nat) : Nat := (w >>> (k*i)) % (1 <<< k)
def pgE0:Array Nat:=#[0x64a19246481914643173c58f143c4cf0f383cd0f303cb0f283c90f203c70f183c50f103c30f083c10f00,0x6c91b206c71b0c6981a586951a4c6921a4068e1a3068b1a286881a0c65819546531944650193464c192c,0x7171c587151c507131c4070e1c3470c1c207071c187041b606d71b546d31b446d01b386cd1b306cb1b28,0x7ce1f347cc1f2c7c71e5c7961e507921e3878c1e187581d5c7561d547541d4474d1d307491d1c7451c60,0xa4c292ca492920a1c277c9db273c99a263c959253c91c2468919243c8db233c7d81f5c7d61f547d41f4c,0xacd2b30acb2b28ac92b20ac32aa0aa32a88aa02a60a8e2a30a8b2a28a8829a0a632988a612980a582934,0xb672d94b642d84b4d2d30b282c9cb262c94b242c80b0e2c34b0c2c20ae82b9cae32b88ae12b80ad82b38,0xc69316cc593070c1a3064be82f9cbe62f94be42f8cbcd2f30bcb2f1cba72e98ba42e38b8c2e28b862da0,0xce73394ce4338cce23384ce03360cd73358cd53350cd33348cd03338ccb331ccc33308caa3270c9b3268,0xda4365cd963650d8e3618d7435c4d70359cd653590d573554d543544d4d3514d3334b0d1c33c8cf133c0,0xe1c386ce1a37d0df237c0de73798de53790de3375cdd63754dd4374cdc73718dc536d0db236c0da73698,0xeb83ac8eb03aa0ea23a58e7839c8e7139c0e613960e573958e553934e3338b0e2b38a8e29387ce1e3874,0xf783dd0f713d94f4d3ce0f343cc0f283c9cf243c60f173c30f043be0ef23bc4ef03ba0ee33b80ed83b2c,0xff83fd0ff03f9cfe33f80fd73f1cfb43ec8fa63e38,0x3281840ba05902a814409a049022810407a03901a80b405202501080740320150088034012005,0x62830417a0b905a82c415a0a9052828413a09904a824411a08904282040fa07903a81c40da069,0x92848423a11908a844421a10908284041fa0f907a83c41da0e907283841ba0d906a834419a0c9,0xc286042fa1790ba85c42da1690b285842ba1590aa854429a1490a2850427a13909a84c425a129,0xf287843ba1d90ea874439a1c90e2870437a1b90da86c435a1a90d2868433a1990ca864431a189,0x122890447a23911a88c445a229112888443a21910a884441a20910288043fa1f90fa87c43da1e9,0x1528a8453a29914a8a4451a2891428a044fa27913a89c44da26913289844ba25912a894449a249,0x1828c045fa2f917a8bc45da2e91728b845ba2d916a8b4459a2c91628b0457a2b915a8ac455a2a9,0x1b48d946c235d1ac8d546a234d1a48d1468233d19c8cd466232d1928c8463a31918a8c4461a309,0x1e48f147823bd1dc8ed47623ad1d48e9474239d1cc8e5472238d1c48e1470237d1bc8dd46e236d,0x214909484241d20c905482240d20490148023fd1fc8fd47e23ed1f48f947c23dd1ec8f547a23cd,0x244921490247d23c91d48e246d23491948c245d22c91548a244d224911488243d21c90d486242d,0x27493949c24dd26c93549a24cd26493149824bd25c92d49624ad254929494249d24c925492248d,0x2a49514a8253d29c94d4a6252d2949494a4251d28c9454a2250d2849414a024fd27c93d49e24ed,0x2d49694b4259d2cc9654b2258d2c49614b0257d2bc95d4ae256d2b49594ac255d2ac9554aa254d,0x3049814c025fd2fc97d4be25ed2f49794bc25dd2ec9754ba25cd2e49714b825bd2dc96d4b625ad,0x33699a4cca66132e9964ca264d3249914c8263d31c98d4c6262d3149894c4261d30c9854c2260d,0x3669b24d8a6c135e9ae4d6a6b13569aa4d4a6a134e9a64d2a6913469a24d0a68133e99e4cea671,0x3969ca4e4a72138e9c64e2a7113869c24e0a70137e9be4dea6f13769ba4dca6e136e9b64daa6d1,0x3c69e24f0a7813be9de4eea7713b69da4eca7613ae9d64eaa7513a69d24e8a74139e9ce4e6a731,0x3f69fa4fca7e13ee9f64faa7d13e69f24f8a7c13de9ee4f6a7b13d69ea4f4a7a13ce9e64f2a791,0x426a12508a84141ea0e506a831416a0a504a82140ea06502a811406a02500a8013fe9fe4fea7f1,0x456a2a514a8a144ea26512a891446a22510a88143ea1e50ea871436a1a50ca86142ea1650aa851,0x486a42520a90147ea3e51ea8f1476a3a51ca8e146ea3651aa8d1466a32518a8c145ea2e516a8b1,0x4b6a5a52ca9614aea5652aa9514a6a52528a94149ea4e526a931496a4a524a92148ea46522a911,0x4e6a72538a9c14dea6e536a9b14d6a6a534a9a14cea66532a9914c6a62530a9814bea5e52ea971,0x516a8a544aa2150ea86542aa11506a82540aa014fea7e53ea9f14f6a7a53ca9e14eea7653aa9d1,0x546aa2550aa8153ea9e54eaa71536a9a54caa6152ea9654aaa51526a92548aa4151ea8e546aa31,0x576aba55caae156eab655aaad1566ab2558aac155eaae556aab1556aaa554aaa154eaa6552aa91,0x5a6ad2568ab4159eace566ab31596aca564ab2158eac6562ab11586ac2560ab0157eabe55eaaf1,0x5d6aea574aba15ceae6572ab915c6ae2570ab815beade56eab715b6ada56cab615aead656aab51,0x606b02580ac015feafe57eabf15f6afa57cabe15eeaf657aabd15e6af2578abc15deaee576abb1,0x636b1a58cac6162eb1658aac51626b12588ac4161eb0e586ac31616b0a584ac2160eb06582ac11,0x666b32598acc165eb2e596acb1656b2a594aca164eb26592ac91646b22590ac8163eb1e58eac71,0x696b4a5a4ad2168eb465a2ad11686b425a0ad0167eb3e59eacf1676b3a59cace166eb3659aacd1,0x6c6b625b0ad816beb5e5aead716b6b5a5acad616aeb565aaad516a6b525a8ad4169eb4e5a6ad31,0x6f6b7a5bcade16eeb765baadd16e6b725b8adc16deb6e5b6adb16d6b6a5b4ada16ceb665b2ad91,0x72cb955ca2e4d724b915c7ae3971ab8c5c5ae25710b875c32e15708b825c0ae016feb7e5beadf1,0x75cbad5d62ead754ba95d42e9d74cba55d22e8d744ba15d02e7d73cb9d5ce2e6d734b995cc2e5d,0x78cbc55e22f0d784bc15e02efd77cbbd5de2eed774bb95dc2edd76cbb55da2ecd764bb15d82ebd,0x7bcbdd5ee2f6d7b4bd95ec2f5d7acbd55ea2f4d7a4bd15e82f3d79cbcd5e62f2d794bc95e42f1d,0x7ecbf55fa2fcd7e4bf15f82fbd7dcbed5f62fad7d4be95f42f9d7ccbe55f22f8d7c4be15f02f7d,0x81cc0d606302d814c09604301d80cc05602300d804c016002ffd7fcbfd5fe2fed7f4bf95fc2fdd,0x84cc25612308d844c21610307d83cc1d60e306d834c1960c305d82cc1560a304d824c11608303d,0x87cc3d61e30ed874c3961c30dd86cc3561a30cd864c3161830bd85cc2d61630ad854c29614309d,0x8acc5562a314d8a4c51628313d89cc4d626312d894c49624311d88cc45622310d884c4162030fd,0x8dcc6d63631ad8d4c69634319d8ccc65632318d8c4c61630317d8bcc5d62e316d8b4c5962c315d,0x90cc85642320d904c8164031fd8fcc7d63e31ed8f4c7963c31dd8ecc7563a31cd8e4c7163831bd,0x93cc9d64e326d934c9964c325d92cc9564a324d924c91648323d91cc8d646322d914c89644321d,0x96ccb565a32cd964cb165832bd95ccad65632ad954ca9654329d94cca5652328d944ca1650327d]
def pgE1:Array Nat:=#[0x99cccd666332d994cc9664331d98ccc5662330d984cc166032fd97ccbd65e32ed974cb965c32dd,0x9ccce5672338d9c4ce1670337d9bccdd66e336d9b4cd966c335d9accd566a334d9a4cd1668333d,0x9fccfd67e33ed9f4cf967c33dd9eccf567a33cd9e4cf167833bd9dcced67633ad9d4ce9674339d,0xa2cd1568a344da24d11688343da1cd0d686342da14d09684341da0cd05682340da04d0168033fd,0xa5cd2d69634ada54d29694349da4cd25692348da44d21690347da3cd1d68e346da34d1968c345d,0xa8cd456a2350da84d416a034fda7cd3d69e34eda74d3969c34dda6cd3569a34cda64d3169834bd,0xabcd5d6ae356dab4d596ac355daacd556aa354daa4d516a8353da9cd4d6a6352da94d496a4351d,0xaecd756ba35cdae4d716b835bdadcd6d6b635adad4d696b4359daccd656b2358dac4d616b0357d,0xb1cd8d6c6362db14d896c4361db0cd856c2360db04d816c035fdafcd7d6be35edaf4d796bc35dd,0xb4cda56d2368db44da16d0367db3cd9d6ce366db34d996cc365db2cd956ca364db24d916c8363d,0xb7cdbd6de36edb74db96dc36ddb6cdb56da36cdb64db16d836bdb5cdad6d636adb54da96d4369d,0xbacdd56ea374dba4dd16e8373db9cdcd6e6372db94dc96e4371db8cdc56e2370db84dc16e036fd,0xbdcded6f637adbd4de96f4379dbccde56f2378dbc4de16f0377dbbcddd6ee376dbb4dd96ec375d,0xc0ce05702380dc04e0170037fdbfcdfd6fe37edbf4df96fc37ddbecdf56fa37cdbe4df16f837bd,0xc3ce1d70e386dc34e1970c385dc2ce1570a384dc24e11708383dc1ce0d706382dc14e09704381d,0xc6ce3571a38cdc64e3171838bdc5ce2d71638adc54e29714389dc4ce25712388dc44e21710387d,0xc9ce4d726392dc94e49724391dc8ce45722390dc84e4172038fdc7ce3d71e38edc74e3971c38dd,0xccce65732398dcc4e61730397dcbce5d72e396dcb4e5972c395dcace5572a394dca4e51728393d,0xcfce7d73e39edcf4e7973c39ddcece7573a39cdce4e7173839bdcdce6d73639adcd4e69734399d,0xd2ce9574a3a4dd24e917483a3dd1ce8d7463a2dd14e897443a1dd0ce857423a0dd04e8174039fd,0xd5cead7563aadd54ea97543a9dd4cea57523a8dd44ea17503a7dd3ce9d74e3a6dd34e9974c3a5d,0x35a3acdd64eb17583abd,0x17080005aa000162800057200014680004fa000123800046a000112800042200010080003ca0000e0800036a0000d280003320000b680002ba000092800021200006f800016e00004780000ce,0x2818000a0200027880009c20002698000982000251800094200024c800090200022b800087a00020b80007e60001e9800077a0001ce80006ce0001aa8000686000191800062a00018280005e2,0x3f78000f820003dc8000f020003b38000eb200039c8000e1200037b8000db20003578000d0e0003348000cc200031b8000c0e0002f88000bae0002d38000b320002b38000a8a0002998000a42,0x5bc80016a6000593800160600057e800159a00055b800153a00053c80014aa000522800144e00050280013fa0004ec800132e0004b380012ae000494800117a00044c80010ca00041f800102e,0x7038001bd20006e28001b4a0006d08001b0a0006be8001aca0006af8001a7200068e80019f200067180019ba000662800197a00064780018ca00062f800187a0005ff80017ba0005dc800170e,0x863800217e00084e80020fe00082e800204e00080e8001ffa0007ee8001f4e0007cb8001ed20007a38001e520007828001dfa00076e8001d7a0007528001d0e0007338001cae0007238001c52,0x9b680026920009a2800264600098d800261200097e800254e00094b80024fa000923800247600090580023e60008eb80023660008d1800233a0008be800228e000899800224600088380021c6,0xaa08002a72000a908002a12000a7f80029ce000a64800296e000a53800291e000a4380028e2000a33800288e000a20800284a000a1080028320009f380027b20009e380027520009d38002712,0xb9f8002e4e000b8f8002e32000b7f8002dd2000b648002d5a000b418002cd2000b318002cba000b138002c2e000b038002bd2000ae78002b8e000ad28002b42000acc8002ace000aa48002a8e,0xc7f80031de000c6e8003182000c5c800313e000c4380030fe000c3480030c2000c24800307e000c048002ffe000bfb8002fbe000be78002f7e000bd88002f3e000bc08002efa000bb08002eb2,0xd518003542000d428003502000d3c80034ba000d23800344e000d128003406000d0080033de000cf180033c2000ce08003372000cd0800332e000cc380032da000caf800327e000c9b8003212,0xe7180039b2000e5e8003976000e4f80038fe000e3780038ba000e208003872000e0f800383a000df680037ae000dd98003742000dcc80036de000da88003642000d8080035ce000d67800358e,0xf518003d0a000f408003cfa000f378003cba000f2a8003c4e000f068003c06000efe8003bae000ed98003b52000ec48003ace000ea48003a86000e968003a3a000e8c8003a12000e8180039d2,0x106a80041a600105a8004166001052800411e0010368004086001014800404600100e800401a000ff68003fca000fef8003f7a000fc78003eea000fae8003e6e000f838003de2000f718003db2,0x113680044a6001124800447a001118800442200110280043d60010ee80043ae0010de80043660010d6800432e0010c280042e60010b680042ca0010a9800428200109b800422600108480041fe,0x124080048da0012358004896001220800487e00120c80047da0011e4800476e0011ca80047260011b680046a60011a68004666001191800462e0011738004592001159800452600114180044e6,0x135b8004d3a00134c8004cce0013278004c8e0013118004c4200130c8004bda0012e28004b5e0012d28004b0a0012c08004ac20012ad8004a4a0012918004a1200127780049aa0012568004956,0x14a6800524600148480051ce00146f800514e00144c80050e600142b800504e0014048004fda0013e18004f520013d18004f3a0013b38004e9a00139e8004e3a0013878004dfa0013718004d92,0x15e980057660015d4800573a0015c880056e20015b280056be00159c800563a00157b80055aa001569800555e00154880054c2001520800547200150180053c20014ef800534e0014c380052f2,0x17168005c3a0016f78005b8e0016d18005b0e0016bf8005a8e00169c8005a0600167d8005996001650800590e00163480058c2001623800588200161f800584200160380058020015fc80057c2,0x1851800614200184380060c6001830800608e00181c8005fde0017e18005f4e0017c58005efe0017ad8005e9a00179e8005e360017828005dee0017698005d8a00175a8005d660017468005cae,0x19a0800666e00198380065d2001960800654a001942800650200193480064c200192e800642e0018f980063860018d2800632a0018c080062e20018b080062a6001891800622e00187c800618e,0x1b4c8006d2e001b148006bc6001aed8006b7e001ac48006ace001aa18006a82001a9c8006a32001a80800699a001a5e80068de001a208006842001a0280067c20019e780067820019cb80066de,0x1c218007082001c138007042001c048006ff2001be38006f7e001bd38006f2e001bc38006efa001bb28006eb2001b9c8006e5e001b8c8006e02001b7c8006dc2001b6c8006d8e001b5f8006d72,0x1d2b800747e001d0e80073fe001cef800739e001cdc800733e001cc380072fe001caf80072ae001c94800721e001c8480071d2001c7380071be001c64800716e001c54800710e001c3780070ce,0x1e9f8007a1e001e76800795e001e4180078da001e20800787e001e0b80077ce001de8800776e001dc380076ce001daf8007676001d96800763a001d7d80075ca001d6f8007572001d4780074e2,0x1f888007e12001f748007dc2001f648007d8e001f5c8007d52001f448007cfa001f2f8007c4e001f0e8007bfa001ef38007bbe001eee8007b7a001ed38007b12001ebe8007aee001eae8007a9e,0x205c800814e002044800810e00203480080ce00202e800808a00201e8008012001ffb8007fd2001fe78007f92001fd48007f4e001fc48007f02001fbf8007ed2001fab8007e92001f978007e52,0x212c8008472002113800840e0020f480083ce0020f080083860020e0800837e0020d380083320020c480082ee0020b3800829e0020a38008262002093800820e00208080081f2002073800818e,0x22278008892002210800881e0021f780087820021dc800875e0021c280086f20021ac800869e002193800862e00218380085d2002164800858e002157800854e00214c800850600213180084c2,0x23148008c2e0023048008bde0022f48008ba20022e48008b520022d08008b120022c38008af20022b48008a9200229b8008a2e00228780089e600227080089b200226b800897200224e80088d2,0x23ec8008f7e0023d38008f3e0023cc8008efe0023b48008ebe0023a48008e7a0023928008e3a0023848008dfa0023648008d6e0023548008d1e0023448008cd20023338008c920023208008c7e,0x24bb80092be0024a4800925200248f800921e00247f80091f200246c800917e002453800913e002444800910200243f80090be00242b800907e002417800903e0024088008ffe0023f08008fbe,0x2604800980e0025fb80097ba0025d6800971a0025b4800969e00259d800960600257c800958e002553800951200253480094ba00251e800941a0024f480093920024e380093620024cf80092fe,0x270c8009c120027038009bce0026f28009bc60026e38009b7a0026d38009b320026c38009ad20026b38009a920026948009a4e00268f80099ce002664800995200264e80098fa0026268009852,0x2803800a0020027ff8009f920027d78009f320027b48009eae0027a38009e760027998009e4e0027878009e0e0027788009dce0027638009d8200275c8009d0200273c8009c8e00271e8009c4e,0x28a6800a272002883800a1d2002873800a1c2002863800a186002860800a17e002853800a13600284a800a10e00283d800a0da002833800a0ba002823800a076002813800a04a00280d800a012,0x298b800a60a002979800a5c2002967800a58a002951800a54200294f800a4de002923800a46e002913800a43a002903800a3da0028f3800a3920028d7800a34e0028cd800a30e0028b3800a2c6,0x2a88800a9e2002a74800a98a002a56800a942002a4f800a8ce002a24800a866002a10800a82a0029f8800a7c60029e2800a74e0029d2800a73e0029c2800a6d20029b0800a68e0029a2800a652,0x2b48800ace2002b30800aca2002b20800ac62002b13800ac22002b04800ac02002af8800abc2002aef800aba2002adb800ab62002ac8800ab1e002ab8800aaa2002aa0800aa62002a93800aa32,0x2c13800b042002c03800aff2002bf3800af92002be3800af62002bd3800af3a002bc2800aeda002bb2800ae8a002ba0800ae7a002b88800adee002b78800adb2002b68800ad62002b57800ad32,0x2cec800b34e002cd0800b312002cb3800b292002ca3800b282002c91800b242002c8f800b20e002c7c800b1d2002c6c800b182002c5b800b14e002c47800b10e002c38800b0ce002c23800b082]
def pgE2:Array Nat:=#[0x2de8800b75e002dd0800b732002db2800b6a2002d90800b61e002d80800b5c2002d63800b56e002d53800b512002d3c800b4ce002d27800b48e002d1c800b446002d01800b402002cf8800b3c6,0x2eec800bb92002edb800bb2e002ec7800bae6002eb0800baa6002ea8800ba6e002e90800ba12002e7c800b9ba002e5c800b932002e47800b8f2002e30800b8b2002e20800b85e002e07800b7c2,0x2fbb800beb2002f9c800be5e002f8c800be02002f7c800bdce002f6c800bd92002f60800bd7e002f5c800bd32002f4b800bcf2002f37800bcb2002f28800bc72002f10800bc32002f03800bbf2,0x308b800c1fe003077800c1be003068800c17e003050800c13e003040800c0fe003033800c0be00302c800c07e003014800c03e003008800bffa002ff2800bfba002fe8800bf7a002fcc800bef2,0x3170800c5a2003158800c54e003148800c4fe00312f800c4ae00311f800c472003104800c3fe0030f7800c3be0030e0800c3520030cc800c2fe0030b3800c2be0030a4800c28200309f800c23e,0x32e6800cb420032cc800caf20032b3800caae00329e800ca2a003278800c9aa003258800c91a00323c800c89e00321d800c8060031f0800c78e0031d3800c7120031b8800c6ba00319e800c61a,0x33e7800cf920033dc800cf1e0033c2800cf060033b7800cece0033ae800ce9e00339c800ce5e003387800ce12003378800cda2003363800cd7e003343800cce2003324800cc7a003308800cbfa,0x34d8800d31e0034b0800d2b200349c800d26a00348b800d21e00347d800d1e6003477800d19e003458800d15e003447800d10200343c800d082003410800d01e003403800cffa0033f7800cfb2,0x3581800d60200357f800d5de00356d800d5aa003567800d576003557800d55a00354e800d51e003538800d4b6003527800d48a00351d800d45e003514800d44200350c800d3f20034f4800d3be,0x36af800da6e00368c800da22003677800d9b2003650800d90e00363c800d89200361f800d82e0035fc800d7e20035e7800d7620035c0800d6ce0035a7800d68e003597800d652003590800d61e,0x37b4800deba00379f800de0e003777800ddae003767800dd7a003757800dd1e003746800dcf2003727800dc76003717800dc1e003701800dbea0036e8800db6a0036d6800db220036c4800dac2,0x38d4800e33e0038c4800e2d20038b3800e29200389f800e23e003877800e1be00385b800e11e00383c800e08e003819800e03a003802800dffe0037f2800df8e0037d4800df1a0037c2800def2,0x3a20800e872003a00800e7ce0039ec800e78e0039d4800e74e0039cf800e6fe0039a4800e65200398f800e61200397b800e592003957800e532003933800e4be003914800e4120038f3800e392,0x3ae7800eb8e003adc800eb46003ac1800eb02003abc800ea8e003a94800ea4e003a90800ea06003a80800e9fe003a73800e9b2003a64800e96e003a53800e91e003a43800e8e2003a33800e88e,0x3c3e800f09e003c17800f002003bff800efae003bdc800ef62003bc7800eef2003ba3800ee72003b82800edee003b69800ed82003b5c800ed1e003b30800ecbe003b13800ec2e003b03800ebd2,0x3d62800f57e003d5e800f53a003d43800f4d2003d2e800f47e003d03800f3ee003ceb800f39e003cd9800f342003ccb800f2de003cac800f26e003c84800f1de003c6c800f17e003c4e800f12a,0x3eaf800fa7e003e84800f9d2003e6f800f992003e5b800f912003e37800f8b2003e13800f83e003df4800f792003dd3800f712003db4800f6be003da4800f652003d93800f612003d7f800f5ba,0x3f87800fdf2003f6f800fd8e003f5f800fd52003f50800fd3e003f3f800fcee003f2f800fc9e003f1f800fc62003f0f800fc02003efc800fb82003edf800fb4e003ecf800fb32003ebf800fad2,0x40c180102ce0040a3801025200408f80101fa004064801014e00404480100fe00402f801005e00400e800fffa003fef800ffba003fde800ff4e003fc6800fefe003faf800feae003f94800fe3e,0x4223801087a00420c80107d20041ee80107b60041df801070e0041b480106be004194801063a00417e80105be00416e801055a00414b80104fa00412b801046600410780103da0040e78010376,0x433d8010cda00432e8010c760043128010c360043048010c020042ff8010b9e0042db8010b360042c98010ade0042a88010a4200428c80109c2004263801097a00424c801091200423280108c6,0x1026e38409b4e1026c38409ace1004b3840011e100033801106e00440e8010fda0043e78010f760043c18010eee0043a98010e5e0043838010dd20043708010d860043608010d7e00434d8010d2a,0x102913840a40e1028f3840a34e1028c3840a2ce102883840a1ce102863840a14e102843840a0ce102823840a04e1028038409e8e1027938409e0e1027738409d8e1027238409c4e1027038409bce,0x1036d6840d69e103597840d61e103577840d59e103557840d51e103527840d45e103487840d1de103467840d15e103447840d01e1033f7840cf9e1033c7840cede1033a7840ce5e103387840a48e,0x103b47840ecbe103a1c840e8021039cf840e5ee103957840e4ce10386f840e16e103847840e08e103811840dffe1037e3840de7e103783840ddde103767840dd5e103747840dc9e103717840dc1e,0x103fef840ff4e103efc840fb82103eaf840f96e103e37840f84e103d7f840f57e103d43840f47e103d03840f32e103cb7840f26e103c77840f17e103bff840efae103bc7840ee8e103b7b840eda6,0x20045e88010ca20041f880102e2003f78800ece20037f880087a20020b88007e62001b38800686200162880046a2000f288001be20005b8410ea61041af84105be10412b841041e10408f841014e,0x20326a88024fa2008f988023ae2008d9880228e200891880220e200871880204e2007d38801f0e2007a38801b8a2006c2880198a2005ee88016a6200593880160620055b880148a200513880132e,0x203ad1880eb06203aa3880ea4e203a81880e9ce203a53880e90e203a33880e88e203a13880e80e2039f3880e78e2039d3880e70e203973880e54e203933880e18e203853880e10e203834880db6a,0x203eef880fb7e203ecf880fafe203eaf880f97e203e3f880f87e203cfb880f3ae203cd9880f326203cb9880f26e203c7b880f16e203c27880f05e203b77880ed1e203b27880ec4e203b03880eb8e,0x3004cb8c001be30005b8810eee2043978810bfe2042e78810a32204270881077e20414b881039e2040b3880fefe203faf880fe3e203f6f880fd7e203f4f880fcfe203f2f880fc7e203f0f880fbfe,0x303a818c0e9ce303a538c0e90e303a338c0e88e303a138c0e80e3039f38c0e78e3039d38c0e70e3039b38c0e68e3039738c0e54e3039338c0e48e3039138c0e3ce3038e38c0e18e3038538c0e10e,0x303e0f8c0f7fe303ddf8c0f73e303cfb8c0f3ae303cd98c0f326303cb98c0f26e303c7b8c0f16e303c278c0f05e303b778c0ed1e303b278c0ec4e303b038c0eb8e303ad18c0eb06303aa38c0ea4e,0x30414b8c1039e3040b38c0fefe303faf8c0fe3e303f6f8c0fd7e303f4f8c0fcfe303f2f8c0fc7e303f0f8c0fbfe303eef8c0fb7e303ecf8c0fafe303eaf8c0fa7e303e8f8c0f97e303e3f8c0f87e,0x4020f3900838e4020d3900830e4020b3900828e402093900820e402063900814e402043900808e40201390012ce4004a3900011e4000338c10eee3043978c10bfe3042e78c10a323042708c1077e,0x4024039008fce4023d39008f0e4023b39008e4e4023739008a4e40228390089ce402253900890e40220390087ce4021e3900870e402193900860e402173900854e40214390084ce402123900840e,0x402633900988e4025f3900978e4025c3900968e402593900960e402563900954e402543900948e402513900940e4024c390092ce402493900920e402463900914e40244390090ce402423900904e,0x402823900a04e4028039009fce4027d39009e8e4027939009e0e4027739009d8e4027539009d0e4027239009c4e4027039009bce4026e39009b4e4026c39009ace40268390099ce402653900990e,0x402c77900b15e402c47900b0de402c27900b01e402bf7900af9e402bc7900aede402b97900a48e402913900a40e4028f3900a34e4028c3900a2ce402883900a1ce402863900a14e402843900a0ce,0x403027900c05e402ff7900bf5e402ed7900bb1e402eb7900b9de402e67900b85e402e07900b7de402db7900b59e402d57900b51e402d27900b45e402d07900b39e402cb7900b29e402c97900b21e,0x403254900c91e403227900c85e403207900c79e4031d7900c71e4031a7900c65e403187900c4de403127900c41e4030f7900c31e4030b7900c29e403097900c21e403077900c19e403057900c0de,0x403487900d1de403467900d15e403447900d0de403427900d01e4033f7900cf9e4033c7900cede4033a7900ce5e403387900cd5e403347900cc9e403317900cbde4032e7900ca9e403297900c99a,0x6005c3980164e60054e980148a60050298013fa403777900dd9e403757900dd1e403727900dc5e403707900d69e403597900d61e403577900d59e403557900d51e403527900d45e4034e7900d31e,0x600f019803b8e600ed19803b06600e7498037da600da89803642600ccb98032da600c9f980307e600bfb9802f9e600b939802d5a600b0f98029fe600a5b980291e6009f398026da6009a498017fe,0x6014c398050ae60141b9804ece6012f698049de601235980489660121f980476e6011a9980466660118b98045ee6010eb98043666010cb98042e66010a99803f1e600f979803e1e600f379803c4e,0x601eef9807b4e601daf9807676601d2b980747e601cbf98072ae601c6f980716e601bdf9806f2e601bbe9806d7e601b4b980699a6017bf9805eb660177b9805da660172f98056be60157b980555e,0x6023929808dfa60235f9808c7e60230b9808bde6022c3980893a6021c2980863e6020df98082ee6020a7980818e60202e980807a601fff9807efe601fab9807e5e601f639807cfa601f2e9807c7a,0x6029cf980a68e60291f980a17e60283d9809eae6027879809c8e6027119809bc66026949809a3e60267f98099be6025fb980969e602563980954e60253398092fe60243f98090ae6024179808f4e,0x602fde980befe602f5f980bd2e602f37980bc0e602e6e980b6ca602d5f980b23e602c5b980b11e602c03980af3a602b9e980adfe602aef980ab6e602ac7980aa4e602a62980a942602a42980a8ca,0x60376f980d5fe60355d980d22e603467980d00e6033f1980cf466033c1980cda260335f980cd3e60333f980caae603227980c78e6031d3980c6ce60312f980c27e60308b980c1de603033980bfca,0x603d1e980f43a603c9b980f1de603c3e980ee0a603b7b980ed1e603b0f980e9fe603a5b980e91e6039f3980e73e60397b980e55e603933980e03a6037fe980dfba6037de980deba60379e980de3a,0x6042b7981098e60425198108c66041df981073e60414b981039e6040b3981028e603faf980fd3e603f3b980fc9e603ed3980fabe603e5b980f8de603e13980f58a603d52980f50a603d32980f4ba,0x703eaf9c0f992703e5b9c0f8de703e139c0f80e703de39c0f652703c9b9c0f1de703b7b9c0ed1e7039cf9c0e61270397b9c0e55e7039339c0e48e7039039c0e2d260441f9810d7e60433d9810b6e,0x9041dfa41073e90414ba41039e9040b3a41028e904083a4101ce8041dfa01073e80416ea01052e8040e7a0102ce8040a3a01020e804073a00ff7a803d4ea00dfca8037e2a00164e]
def pgEL (i:Nat):Nat:=(if i<64 then pgE0.getD (i-0) 0 else (if i<128 then pgE1.getD (i-64) 0 else pgE2.getD (i-128) 0))
def packetEntry (i:Nat):Nat:=(if i<324 then packetField (pgEL (0+(i-0)/24)) 14 ((i-0)%24) else (if i<2034 then packetField (pgEL (14+(i-324)/24)) 13 ((i-324)%24) else packetField (pgEL (86+(i-2034)/24)) 26 ((i-2034)%24)))
def packetUnpack : Nat → Nat → List Nat
  | 0,_ => []
  | n+1,x => packetEntry (x % 8192) :: packetUnpack n (x >>> 13)
def pgP0:Array Nat:=#[0xb605ac2d41670b305902c61620b085742b61580ab85542a81530a8854029c14d0a5051c28c144,0xdb06d43681b20d886b43561a60d0867832a18d0c5862030e17f0bf05f42f21780bb85d82e8173,0xee076c3b01d70ea074c3a41d10e8073c39c1cd0e6072c3941c90e287103861c10de06e83721b8,0x109884842020e104881c4062000ff87f43f81fb0fd07e43ee1f60fa87b83d21e50f187843c01dd,0x13589784b824d125892448e246122890c484241119888c444221110087843821910b885842a214,0x1658b005782bb15c0ac455a2aa1510a705262911430a1450628213f89f44f827713b09cc4dc26d,0x1a60d246863421a08d0067c33d1920c6862c31017a8bd05e22ef1768bb05d62ea1748b9c5c82d8,0x1c68e307123881c20dfc6fa37b1bc0dd46e83721b88dbc6dc3671b30d906c035a1ac8d4069e34d,0x21b10d48464192000fd07e23f01f70f947b63da1ec0f5c7aa3c71e28ef473a3991cb0e4c72238e,0x26112e896a4b4243121490848224092008fe47e23e91f08f647a23c917489844422090f4874439,0x28a144ca24511288143ca1c50d2860038a1400d284803001600a004001c00a00400193d09c04d1,0x2d39684b4059e2ce966cb345982cb9654b2858c2c49614b045812be95c8a6c52328c145ca2c515,0x2eb1754ba85d32e8973cb9c5cc2e29708b7e5be2de96f0b765b72da96bcb5c5ad2d616acb545a8,0x3479a38d1268834099f0cf067733b19d4ce066f33719a8cd266733118d4c6662230f1780bbc5dd,0x15808403e01a3be1d9ce8c74239d1ce4e7073739b0048d4269f34e1a6cd3469934c1a4cd22690,0x4102000fc07d03c01dc0e006403101800b205602981480a004d024011807e03a01c80dc062030,0x6783381960ca063030017e0bd05c02d01600ac05402981460a104e826412e0950488234110083,0x8f847823211708b043420810308083f01f20f707a03a41d00e507103741b40d906c035c1a80d3,0x4dc26613209884a8250120,0x133054032a1500af85405a014e0b505382c814e12905344a214d0d905342cc14d165852837014a0b585282d414a0b2052829c14a0aa051c2a2147153851854a146151051854014614985183ae146,0xfe05843a01610b3058439c16014d057c53215f14a857c51e15f0d485782b815a0ae056454415814a8560526158149056051e15814705605181580e98560542157150055c3ae1570aa05442a6151,0xfa85dc5d017617385d856c1760bc85d83241740b885c02e416f0b985b522a16b0dc05ac36a16b12e05a837016a0da85a83781660db859837616514605885c616116c05845ae16116b05845a0161,0x17a86b45dc1ad17686b441c1ad10386b439a1ad0e506b43901ad0e186b44041a6115068836c1a10db067c36c197292064c3c61932f1064032218f163863858e18d0d5862c31e1890dd861834c17a,0xe606e83961ba0e506e88b61b90ff06e03f01b812686dc4961b70ff06d43f21b530486c4b8e1b11ab86c43a61b10ec06b889c1ad22586b48921ad22386b488a1ad22006b47201ad1ba86b46e61ad,0xe187004841bf0fd06f838a1be0e306ec7da1ba1f486e87a81ba1d086e86f81ba1bc86e86ec1ba1b806e86c61ba19706e86201ba17986e85e01ba17786e842a1ba10706e83e41ba0f586e83b81ba,0x3110728c3c1ca1c307287081ca1c087286fe1ca13007284941ca12287284821ca10b07284281ca1e8071c6ca1c719b071c3b81c62ae07107de1c411507103b81c42e4870c61c1c30e2870c4e21c0,0x20c87707081dc1bf87706aa1dc11087704021dc0f3077042e1d910b07644201d9146075cb901d4100874c3b01d30eb874c5c21d217007485b01d216787483f81d2298873c3f41cf0fa87384821cc,0xfd07a89dc1e70fd079c3f41e4161878c3ea1e30f2078c3ea1e223307748b41dd22907748a01dd20d07746aa1dd11387744421dd10287744001dd0f787743d01dd23407708c61dc23087708461dc,0x1f607e87d21fa1f207e87c41fa1f007e87ba1fa1eb07e87aa1fa1e987e877e1fa1dc07e87641fa1d407e874e1fa1d287e84381fa10c87e84b41f81ee07d87f41f520a87b07fc1eb14287ac3f41eb,0x1bb885842c215185085061221410e084cc2021030488404422101cb08386da20e1b5883862820e130883848a20e10a08389a220d11188345f020a106881c9d4206113880c6a01ff15d07f43fa1fb,0x2a1091499c245224091488c24517789148962442f08908bbe2422690908c7024126c89045d8241120888cb2422129a0884a0a22127708849c02211198880a4621c1198870be22192f40864440219,0x31089fcaca27f31709f0c4027c2b209f08be278158099455e2631778988a382611b009846a026117789807c825f1ed897c77a25f1d6897c57625a14f094852e251298092088a2461ba8918c72245,0x1ad0bbc6022ef26d8bb85fa2ee1f00bb07722ec17d8bb05902b92320ae055c29d1510a605262921498a4454a28e1558a34a362861808a18aee28517d8a14a862831430a0c50a2821768a00c5e27f,0x28c8c908463241ac0c906ae3242110c8c83e32020d0c70c0631a2d98c68aec31a20c8c6876c31a1da8c6875a31a2e80c54c583052268c14c603002218c00c542ff2210bfc6062f62848bbc8142ef,0x2dc0d507c03541ee8d449c035026f8d407b434f1ec8d3888834b1eb0d287aa3492e38d147a63452198cd87a03361b28cd885e3323020cbc85c32f2168cb8c3a3292140ca484e3283048c90bc8324,0x1c08dc070036f2b40db871036e1bf8db8e6a36a2948da8a3e36a1f78d947dc3642e50d887d83621f48d7c7d035e1c68d687c83592de0d54b723552228d548883551f10d546ea3551ba0d557aa354,0x1ea0e90b263972970e58b8638c1eb0e307723882af0e18aae3862a78e14ab43842a60e10ab83832ac8e0caa83812a70e00aba37f2a80dfc70c37c1c28decad23742058dd071a3741c20dd0706372,0x20b8f0882c3c154f0efc8283bf2f58ef88263be2088ef08203bb2068ee07fc3b42058ecc8143b22040ebc80a3ac2020eac87a3a92f70ea08043a82008e9c7f03a61eb8e987fe3a52f50e907fc3a4,0x2438fbc90c3ee3398fb090a3ec3390fa49083e92418fa09043e72408f909003e234f0f808fe3e034e8f7c8fc3df23e8f74b2a3dc23e0f68a5e3d623d8f588f43d523c8f4c9fa3cd1eb8f1d53a3c2,0x2421044906410345903c90440f2409034cda40b2bf902c90040b3361028afc40a23f90288fc40933590208fa40823e1014b204042ae10088f64022c790048f44013450ffcb1c3ff23c8ffca4a3ef,0x1c800c06e00300f000c1d000201c800803c002087800008600030693c8c104ed30313acc044e92f1139cbfe4e526912ec8c245028310a0a0a4232771064b24417243905c90c4162c8905090a414,0x3e80140b200502900140a2005023001403a0051228014c3450109e801021e00406800100fa00403900100c80040238010fe20043f70010fb8004099000c260003074000c168003050800c0c0003,0x3a0801cc5a0072ef001cb780072d4001cb040072bd001c4fa0070ee801c3b80070b5801c232006074801813c00602d00180a000602280180500063a28018b64006122801823e00507a00141b0005,0x6e80201b000809e801c26200708f001c23200708b801c1b600706d001c17a00705c001c14c00704e801c12a007032001c0b2007028001c08800701c801c06e007013801c03e00700e001ce8a007,0x67802c14200b024002cb2400b29a002c9be00b211802c83200b192002c63400b0f0002c2c200b07480281d000a06e802803e00a11c0028c3a50607a00241b2009015802405200907e80201f0008,0x3c30030eec00c3b78030eda00c3b60030eca00c3b20030ec600c3b10030eb800c3ac0030eac00c3aa80303f200c0fc003032400c0b580302d400c099002c26000b087002c1e600b074002c1ce00b,0x1d003006e00c3f68030fd800c3f58030fd200c3f38030fca00c3f20030fc600c3f08030fbe00c3ef0030fba00c3ed0030fb200c3eb8030f2400c3c80030f1e00c3c70030f1600c3c48030f0e00c,0x5f003411000d0158034f2e00d3cb0034ed400d3ac803451200d13e003448200d0fa803428c00d094003021a00c083003020800c08080301f800c07c80301b400c06c80301b000c068803012e00c,0x1f480387d000e1f380387c800e1f100387ba00e1ed00387a600e1af00386aa00e13e003849a00e120803843800e10980383ba00e0ac00382a800e08f803423a00d07a00341b200d06c00341a000d,0x3318038cc200e3300038bb400e2ec8038bac00e2e90038b9e00e2e70038b8600e2e08038b8000e2df8038b7c00e2de8038b7800e2dd8038b7400e2db0038b6a00e2cb0038b0400e29700387d800e,0x3bb8038ee600e3b88038ee000e3b48038ed000e3b30038ec200e3b00038ebc00e3ae8038d0e00e3430038d0a00e3420038cfe00e33f0038cfa00e33d8038cf400e33c8038cd000e3330038cc800e,0x3a814a8c605232de148cb6c51e3051464d3251608c803822c00e07480381b400e06080380fc00e3ed8038f3600e3cd003803e00e3c68038f1800e3c28038f0800e3bd8038ef400e3bc8038ef000e,0x33816f0cde5bb33716e8eac5b93aa96e4cd45b733496d8cce5b533116d0efa5b332f96ccc0a5b32fb968cbde58d2f69628bd85882dc95fcbcc57c39e152cbb05402e314ccb525302e194b8b8252c,0x34f9770d385da34d9764d345d834c975cd305d634b9754d2c5d434a974cd265d23489744d205cf3479738d1c5cd3469730d125c63441714d025c33401708cf85c133c1700cee5bf33b16f8cea5bd,0x1d80497a86920a0004007a0103a0188424600f087003c05a00f34f97e8d385f934d97e0d345f734717c8d125ef34097b4cf85ec33c17a4ce05e8337179ccd25e63311794cbe5e43509778d405dd,0x6a005809a01601f80580620160110058080015011805426a014093004cef87493b39d20ef87473b91d18ece7453af9cd4e987320a000482780120968048252012091804822a01203900480b6012,0x27007827601d093007423a01d04280740b001d08b80700c801c01b807015e01b032006c0b401b022806c1ae01a038806804a01a0a980682a601908e00601de01806900600aa0180178060202016,0xa880942a2024072008c098023018008c20202207280881a8022026808806202215b808830c022073008424e02008c807c20201f074807c1b401f060807c0fc01f2e8007c2a601f09a80780c001e,0x3bc00aced602b3b500acd0e02b34300acbde02b26880ac82202b0a880ac27402a09800a80ae02a02100a826c02809380a022c02804a00a00f402808f009c12a027032009c0a402606b8094096025,0x10380c43a00310e500c43740310b500c408202f08680b822e02c08080b01a802c05f80b00ac02c02680b007e02c08f80ac1e802b06c80ac11002b3f300acfc402b3c680acf1802b3c500acef202b,0x2200dc4be0370fd80dc21e03508b80c420203107e80c41ee03107800c41ca03106a00c418603105f80c40ac03102680c409203101f80c499803126380c498c03117780c45d803117380c4472031,0xdc00fc2d603f0a700fc28403d06e00ec25003a09200e820803a07f00e81b003a04b80e829c03a09d00e413803904b00e40c003909880dc23c03708b80dc17003704a80dc11203703d80dc0c8037,0x4e811011a04403201100b2044029011028204309f010c26004207781040bc04102a81041c804002f810009804008080fc1ee03f07280fc1a803f04a80fc09a03f0fd00fc3a403f0e500fc37403f,0x85813023c04908b812426404808701201e604807401201420480a1011c124047030811c27604608e81180fa04602c01180a404609b011424a04508b011409e045098811023c04405c011015c044]
def pgP1:Array Nat:=#[0x3e81480c4052098814023c05008b814014c05004a81400c80502bd0140394050057813c10e04f08081341fe04d07801341ca04d06e01341b404d06a01340ac04d2bd01345e004d0e5013437404d,0x31816823c059057016412a05904301640c805910701643940590dd016435a05908081581ca05606a015840e0560e501583740560860154186054067814c24c05208f014823a052056814810a052,0x53019013a06404a819010c06403d81904e606412f819048a064120819041c0640ee81903940640dd019035a0640a70190294064057818c16806004b01801e005e08b816c24e05a08b016814a05a,0x5c01e815e07a07201e420e07806781e01060780ed81e023207708401dc97e07707e01d419607505181d411a07506001c017a0700aa01c01b806b05f819c26206408f019022e06405c019015c064,0x77821020e083126820c21208207d820411808107e02001c4080065820011a08008c81f81d207e06d01f8bb007e2a001f853e07e12581f823a07d05681f412607d08f01ec22e07b05c01ec12a07b,0xd682342d608d0b502341dc08c08f82201e808806c8220fd40883ca0220f100883428220d08088268822097c088125822024e08708b021c14a08708f0218170086057021812a086053821413e085,0x6d825417a09505c025413a095097024814009207e02341f008d07682341c408d065823414608d04c8234c8408d31c8234c7008d22c823489c08d17502345ce08d15c023448a08d120823436c08d,0x76828c1c40a3065828cc880a322e028c2640a1074028423a09f056827c14a09e098827417009d0fd027426009c055826c14409a07e02641960990fd02642d4099094025c20809708f025422e095,0x2a582f4a940bd1b582f42a60bd09882e01b60b805e82e04280b810702e03940b80dd02e035a0b80b502e029c0b829b02b84280ae10702b83940ae0dd02b81f80ac07102b04840ac05c02981f80a3,0x129835048a0d40da83502940d40a2035020e0cf0af833c2b00cf0ab833c28c0cf08c83382100ce08483342100cc07e032c1ee0cb076832c1c40cb263832c5b00cb14e032c1ee0c50a883001800bd,0xa3036823e0d907a0364b3e0d92ce03647fc0d91d203645880d9160036448a0d90dc83642b00d90ab836428c0d909403602320d8082036028e0d708083501ca0d4261035096a0d416c03504ac0d4,0x3328368bbc0da2ee0368bae0da2e88368b8a0da2db8368b640da1f703687d60da1f303687c20da1ef03687b20da1b083686b80da1aa83686a40da12283684840da10e03684260da0ac036828e0da,0x8083949680e517983944920e512103944820e511c03942ee0e507e03881da0e207b83782860dd08103742320da0748368f320da3cc0368f280da3c98368eaa0da34a0368d240da3460368ce80da,0x11003d02020f012383c01f80ed12403b42320e93ee83a44fe0e912283a42640e807983a0c1c0e827e83a09e80e826f03a08460e820c83a07080e81bf83a06480e818d03a05380e812083a03680e8,0x2fc03d0bee0f42f903d0bda0f42f603d0bd20f42f403d0bce0f42f303d0bca0f42cc83d081e0f420683d08160f420503d08120f420403d080a0f420103d08020f41ff83d04fe0f413883d048a0f4,0x3bb83d0ee80f43b803d0ed20f43b403d0ecc0f43ae83d0eb40f43ac83d0e920f43a403d0d280f434903d0d180f433f03d0cfa0f433d83d0cf20f433a03d0ccc0f433203d0cc60f433003d0bf20f4,0x3a883dcc860f732083dc5de0f717603dc40e0f708f83d0fd00f43ed83d0f360f43cd03d0f320f43cc03d0f2c0f43ca83d0f260f43c883d0f0a0f43c203d0f060f43c103d0f000f43bf03d0ef60f4,0x25d84002480fe08683f8c720fc31c03f09ba0fc26e03f089c0fc22503f087c0fc18083f05f60fc17583f05d20fc16003f05380fc13983f04900fc12103f041a0fc10383f036c0fc0a703f02940fc,0x17a84045e610117804045de10117684045d810117484044a81011228404486101121040448210110b040440e1010e904043741010dc84043701010db040436a1010bb04042d41010a70404294101,0xb1846423c1171b5045c6d011710a045c544107146041c2501040fd04102c21040a704102941043220404c841012b58404ad41012b48404ad01012b38404acc10122e04048b21011c204046fe101,0x3ab847ccfe11f33d047ccd011f332847ccc211f2fd047cb2611f2ba847c82c11f20a047c53611f14a847c52611f149047c52011f147847c4fa11f098847840411e25f84644fe11910704643ae119,0x17a84e03a41320b084c857613113084c43941310dd04c42941310b204c03f81281768480fc011f3ec047cf2e11f3c0847cefe11f3bd047ceea11f3b8847cedc11f3af047ceb611f,0x45a87482d48a00e905a932e1b50b5257836a16a49506d42d41d20b585a83a416a0b4076c36e16215a899c2be86a0ee857c4ce1b20af875c36015f0ee86b82be2b213385604ce1b20ac21d82b01570ee855c2a49c30dc052936e1b80a5261c2c214a43a0a2428c2b30db85183b61b70a321a035c146,0x10e884c35a22110886b44422100d6974041c1ad67487dc35a2220e686b5b881c90d690f03921ad4f789c831050210085dc7fa1e40bba4203f416b47a87842d61fd0f085ac3f41e10b5a3883a416b45d07482d62d90e905ac3f81d20b587ec3a416b0fc86e02d68dd0fd05a83fa1e10b526043a416a,0x6b2084c366bb610b06c575a2150d8885842a1b1111883436220e0ff86c58aa2130d7b71489c1ad291911035a5d021f86b5a423ef0d6b5506f01ad6a88de035ad461ba86b4a582ef0d68d3c5de1ad6928bb435a3ac17606b46ca21e0d6b3a84381ad110086835a22010c86b489c2170d68e4042a1ad,0x2f988383745f010706e8b3020e0dd165c41c1ba2ca083837459310706e8a7020e0dd14dc41c1ba29b083837453510706e8a4620e0dd14e43941ba0fa87903728d50e906e11861d20dc22b83a41b8455874837089a0e906e0a062010db07d43c81b61fe870c36c8d70e906d52281b80dab3f04381b3,0x6a78bcc374d4d17986e9a722f00dd34dc5e01ba29b0bbc37435e17786e87762ec0dd14dc5061ba2cb8a0837435f10e06e844021b0dd08804321ba110886037440010a86e87d22150dd0d7c42a1ba1a4885437431610a86e86202150dd0fa44261ba1eb084c37440710906e87c62120dd08844201ba,0x11088403868ca0fd07084402190e088844201c141f87303803d01df86f1d0640c0dd34387da1ba6990fa4374cf51ee06e9a023d40dd16506f81ba29a8df03745f01bd86e8b2637b0dd148c6e81ba2cc0dc03745381b806e8be636f0dd364c6be1ba6bb0d58374d691a406e9b723160dd36986201ba,0x612084c394bad10987287d62130e50f984261ca1f1084c3943de10987287a42130e508844201ca30707703945fb0ee07288941cb0e510f83961ca0e6872c3942140f5872576e35f0e42fac68a1c85da884c390bd2109871ca0a2210e208804321c4304884038822110807104402190e1b15442c1c3,0x2938da83945a81b40728b4e3680e516146d01ca5d20d94394c071ac87297683550e52f7c68a1ca2110c8c39444d18b87288843110e50e1c4901ca1c1092039452d122872870e2420e50e084841ca1d2088039436110e07286b821c0e50d544381ca1a9087039441310c87287fc2190e508804321ca,0x110086439621c109872c4422100e5ae18bf61ca5a71648394b4c2c187299425340e5327ca4a1ca53313d0394b822700728bf64e00e5362c8941ca69390f8394c1d20b87289e83fc0e52b647841ca53f0f0839453d1c20728a763840e516806fe1ca2ce8dfc3945471b50728a8c36a0e514e86d41ca,0x30b09883ba5fd13107744c420d0eea90c3ea1dd51607883ba5392118770b344190ee16687021dc29e09843b859e12f87717fa2130ee285c3c61dc2c088383b2522107076441c2040eb0d946c41d41a2885c3a850510b07506a82100ea315441e1d42940da83985861b407304402190e608844201cc,0x11088403eca3d19987d44562260fa93b84421f311008643e422110807c84422100f708844201ec27e89803d622110807ac4422100f4885842a1e71f608403ce223106879c9dc2170f2b5904221e511088403ca55110787904422100f188383ec1e367e08443c053f1228778b442410ef296c6aa1dd,0x5dd89843fe35010e07fc8282190ff90344321ff61408583fec2410a87fd7fa2150ff885842a1ff21188403fe26110707fc44620d0ff96f46d01fa2c38da03f45841b407e8afa2fb0fd15e44be1fa2d289043f45a412087e957e2230fd085842a1fa11088403f4b0c10687e844620d0fd08844201f7,0x10e085042622110a084580cbfe1082f7975c21020c8efc4204191d8884044221410816f0a4620e5d10d7841cba11aa083973834a1072f0868a20e1a5087041c4381300835ba6216106947470820739d891440ec28109881985022110188804322035da8840406221108080d7e021510090507f61ff,0x2008c9043240a17788648122ef10caf486c42171af0bd442e3e8176885ca5c37710b377c4462156ee888c42a35f10b085469421610aaf2068a214110086842822010c88517f2bf010990647ba2131eb8e984263e21b7084c7a631a1098fa05da2131f00bb44263e7176084c7c02ec1098874428213,0x1a28c904423ba18d088474a31a11093884c022120c8ebc4403d71d30880b3e3821100ecc6dc2201d28c684403ba17608807642ec1100f805da21e2948da84384441af887071a34a10e0d2464821c1af0bd443835417a88706a82ef10e0d4c5de21c22210444324001f8086480438d10c97a46d4219,0x2a18fcc48a5421f98914bf23c912297e079224531c8e3448ac051ba09157f4374122b0086aa2455f88d5448a42319d8914e7630912298844fe2451c28dec484d5c1a60909672638120ab0076624155b8ecc4826381c4090558836e120aaf06dc24120c8ce448262013e0905894c25110afd97e0221,0x58b8ec45d8c492118a19602419142aaa46342855f08c905064231920a0c83231a141321ca7c27f63d0d384ff0881a509fe0ae57a13e2cacaf427c5fa14704c251c1fb8984bca3cf13094706ec2615c893884c0ced1eb892070036f1243228c72245656950c48ac732a1091593a532122950c89c245,0x5cf94cc614c761b20c1594a51f180b29c7083012118cec60273d3178c00b4244318014f888630062e8d245feb521bf8bec83233917db6308742f56b90d705ead221aa0bd5ae035217ab1946ba2ef5c78d745dec8f1aa0bbd8c2353177b4a486c2ed6850f985dad081ef0bb56363ba1762cf47642ec,0x5420ecc652a7a1d90ca180640d1922fb07083242118da8648c581a48c917723451922a0c7b43235d60d3c64658120c8c814ea3a8190340874831c2cb1070634ac21dc0c6961e3a718d2a2074a31a5590dfc6344191b40c6964e3c118bb1d470831362f0e10626b131d38c4564c37f187ac506fe30f,0x61510b86bec1c2168d79b2044a1aac19088835561390a06aacd21ba0d557283741aaaf4c9c035460d109c6a8bf32118d457ee3761a8b08c84434f637108469cc571c18d389c43d41a6b59879434d60a107c694c7b1c68d29ad841e1a443187a833a8690d20674d6a1df0cc950c3bc197a9f07d032e,0x2bb0e186f85191c30df158c3b81bcaaec75e37665d91106e8cb82220dd15503a51b8349487c36f5b210f46dcb6121e8db96d03b31b731c0a5236a5c294a46d4c592930da9ae84181b3b59c7a23676db90546ccc6f2118d921b04321b1b0e471e3626280e186c4c311c30d8989637c1b1337888835f,0x56b90b4776adf2140ecd5aa4271d92ae08323af56f1088758b212108ead5a041f1d413888063a66d08f5c74cab121b8e9561c3ab1ce2a5074a3945468e94728af11df8e3d5d23bf1c7acb07503882fb0f2c70e4341d18e1dada42f1c2b13c8463842100e6c704d0520d0e0160c4191bfac0877e37c,0x980030000a782c693c94e25c3276ae60a5c4ed54096209d6baa29613ad4ee57c272ae78a3c4e52e2162c9c0c2b2119051aee42f209b43c8343fe68610607e2da32000fc21984321f6b4ac87c3e268210787a8cff1f88f459fc3d81e52c888323c158390ec77eae320c8efd6e043d1de2b8485c3bc,0x5cc9500a0213100600101b600c002011001800401b8030008104003801029c0b400186540c00030a501800069c5005800c12a00b00180dc01600315c802c00697b003800d28c00700184c800e003074001c006048003800c04e00a00103a000e00207980180040da00180081d00050008364006001,0x1f1072800e2f50e5001c5da1ca00389cc39200731286e800e2f30dd001c5e01ba0038bbc37400722706b400e4470d6801c6f01ad0038dd435a00717a86b400e1f20d6801c2d614e00385ac2940070b5052800e5b208c80181b400700316c86f00061ec86e800c05000680141b2007002a9c8b46501,0x1b40bb000ec00122801cc722450039d144820073a0890400e638120801d99e21400391284280071bd885000e22310a001c42a21400396f041c007225083800e447107001c88a20e00390f841c0071bc083800e375107001c5e820e0038bc441c00710a081c00ebb10e5001c8941ca00390f8394007,0x3200dc00e33b01b801c67203700383680500074fc007c00eba7399001c202012003835002400739f152c00e5622a5801cac054a003aec09d20072ef10f800e5b221f001cbbc36f00396c86de0071bf0dac00e4441b5001c6e836a00397786d00072d40da000e43d1b4001c6dc3680038da85de007,0x58028c00e14d04a801d3f407a00383f00e000706581c000e0da032001c55a0640038ab00c8007155819000e2aa032001c48a06400388840c80070fe819000e1fa032001c3b006400387280c80070dd019000e15f032001c29c06400385280c80070a3019000e1ba02c801c3c8050003816c09a007,0x94002c01003a005802005600a004007c0120080a504f400e1ad098801c35a11e003849c23200707b837c00ea2106d001d41c0da00383dc18e00713082e000e25f05c001c48a0b8003890417000710a02e000e20e05c001c3940b800386e81700070d682e000e14e05c001c2940b800386b415c007,0x29207580143240ea00283fe1cf0050d7834400a17c86200141d606c802417207e004847c01600906c802c012088005802405600b004a0f401600927010480124e020680249be40d004938880600927010040125e7192002481a324004900464800928107d40123350fa8024362192004818006e008,0x8c802c0140da00580280fc00b005007c01600a2700d800144e01ac80289be359005138869a00a2700d2401453f1920028a7832400514e464800a29a8c900145271920028a4c324005148464800a1a48c9001421310800286481ff0050fb03ce00a279878c01431d0f18028a461dd0050d543ba00a,0x270072801640f0d8802c7fe1b10058a5036200b19186b0016a3a0d0802d42619f0058be831000b17005a80162d80b5002c3a416a0058b442d200b16f05a00162d40b4002c5c01640058ae82c800b0b585840164f307400289b40e80050be41d000a0ee83a00141dc07400282060da00503e019600a,0x4c50af00162c815e002d2ec2ba005b31444200b14e08400165fb107002c9c020e0058a6840200b18d07fc01631a0f5802c7d81e70058f7c3ce00b1ee879c0162ec0f3802c9f61e30058c743c600b51d8774016a350ee002c7dc1dc0058b343a400b20c873c0165fb0e6002c9c01cc00597ec39400b,0x2e60c680165be18d002cb7a31a00596e863400b2d10c6801659e18d002cb3a31a005966863400b2ca0c6801658518d002cb0831a005960063400b1f38c680163e418d002c7aa31a0058ee063400b1d38c6801636e18d002c9c42ef005908c5de00b1920bbc016419176002c6342ec005a7245b000b,0x2c3906401657920c802caec41900598587e200b3070fb80164191f7002c9e83e400590647ba00b3070f6c0164fd1ec002c9e83d5005985878600b3070f040164191e0802c9e83bd005906475e00b3070eb40164fd1d5002c9e83a7005981473200b1ba0c900165d718d002cba831a005974463400b,0x2c80a8016d3e3df002da807a1005845c03c00b018806801603100a002cc0a5b30059814aec00b2e2137801658b26f002d3364c8005a6ec98e00b2ee10640165d920c802cbaa419005973c83200b2e010640165b420c802cb66419005969c83200b2d310640165a420c802cb40419005966083200b,0x20c8284016324050802c6340a1005858414200b05882640160b904b802c26009500582d012a00b067823401608d03c002c20205c005874c0a600b0d88120016161024002c2a0048005836008600b02e00fc0160d501d002c0ca03a005819007200b03000dc0160d7018802cae203100595bc06200b,0x15c03a00162b6074002c4420e8005887c1d000b10803a001620b074002c3ce0e800587741d000b0ee03a00161d6074002c3440e800584081b000b06e83600160d706a002c2420cc005833c19600b07e02c40160b1051802cc1c0a1005981414200b2fd82840164f4050802c9c00a1005908c14200b,0x47584c00164df098002c400130005859026000b0a184a00160fc07c002c9c40f3005940c1d000b28103a00164fb074002c9cc0e800593881d000b21183a0016419074002c71a0e80058e201d000b19b03a0016335074002c6660e80058c901d000b19183a001631d074002c6340e80058be81d000b,0x30504c80165fb099002c9e8132005938026400b21184c8016419099002c6481320058c6826400b16c04c80162cc099002c5961320058b2826400b16484c8016201099002c3f6132005879c26400b0ee04c80161d2099002c39e13200585a026400b0b384c8016164099002c2c2132005a3b026000b,0x8c80340180e900680300fc00d006219401a00c00f80340187fd0068030ba040000617d47e000c2fa0fc00185f01f800308003f00060ef86b800c2cf8d300185751a600312e22c500607e83a400c48b05ac0181fa0b500302d616100605a82c200c666332c016cc9664002cc1c132005983026400b,0x4da83f00189b407e00302c20f9006075c1b400c09b836401813606c80302320d900603a41b200c0e9836401812b05c00301f80b200607e812e00c0b2025c01816104b803019608e00602f40d000c07e00e80188eb01b8030086037006035006400c02e80c40180d900f803023e00e00600ac01c00c]
def pgP2:Array Nat:=#[0x1e1072801a3c10e5003475a1ca0068e9c39400d1d2072801a40f0d880347fe1b100687d433000d52b864001a1580a3003457612800607e825000c0f084a001816809400302c8128006058425000c0b2049401810a08380303f810400607e820800c0fb841001816108200312aa101006255020200c,0x1c407e801a31a0fd003457e1fa00690f43d600d1f687ac01a3e70f580347c41eb0068bb03d600d20c879c01a2ec0f3803457c1e300690583b800d0f1875401a4120e6003480c1cc0068ffc39800d20b872801a4160e500348241ca006901839400d202872801a4010e500347fe1ca0068ff839400d,0x2f40dd001a5e61ba003481637400697c864800d2078c9001a3ff1920034bf42ef00697e05de00d2f90bbc01a5ec1778034bce2ef00690605de00d2080bbc01a40f17780348142ef00690245de00d2028bbc01a40317780347fc2ed0068e905da00d2fc8a0c01ad421100034580219006887043200d,0x2f7911001a5ed2220034bd0444006911082200d271103c01a625205803488840b00693bc7fe00d26f8ffc01a5db1ff00347fc3ed0068ff87b800d2ce0f5c01a5991eb8034b263d70068fc478600d1ec0ea801a3d71d30034b703a400696c474800d1f30e9001a3e31d200347a83a400697bc6e800d,0x2fb00ac01a5f50158034be802b00697cc05600d2f800ac01a5e30158034b3e02b006967005600d2cc80ac01a5930158034aea02b006905405600d20000ac01a3a6015803407401f006845c03a00d01b007001a04d00c003409a017006813402600d6339d2c01acd43a50034e9262f006934801c00d,0x1d2036401a22006c80343ee0d900687b81b200d0e7836401a19206c80342a40d900685181b200d0f1836001a19206c003417c0bd006904c11000d1ff022001a3be044003474808800687d411000d0f1822001a10903c003417a06c006827c0b200d032014801a058022003408e044006813408200d,0x2f4836401a5e806c8034bce0d900697981b200d2f2836401a5e406c803482e0d900690581b200d20a036401a41106c80348200d9006903c1b200d206836401a40b06c80348140d900690241b200d204036401a40506c80348040d900690041b200d200036401a3ff06c80347fc0d90068e981b200d,0xfd047c01a1f708f80343ac11f006869823e00d17b847401a2c008c80342ac119006842420e00d20683d001a39407a00344320f400688481e800d0f583d001a0fa07100342320d90069d241b200d3a4036401a5fa06c8034bf20d900697dc1b200d2f9036401a5ef06c8034bda0d900697b01b200d,0x1b0072801c35c0e500386aa1ca0070d4039400e1a7872801c3490e5003868a1ca0070bbc38800e17786c401c24d0af80383ba15f00709342b000e0ee856001c1dd0a80038aea11f006904c23e00d1ff047c01a3be08f803474811f0068e3c23e00d163847c01a2c608f803443211f006882023e00d,0x18d07e801c4470f9003876e1f20070bcc3e400e1b307b001c3e70f580387c41eb0070bc03ca00e178078c01c3640ee00385de1d400707743a600e0ff873c01c3600e600386a01cc0070d1439800e1f7872801c3ee0e500387cc1ca0070f8839400e1ed872801c3d50e500386ca1ca0070d9039400e,0x29f8bbc01c53a1778038a6c2ef00714b05de00e2938bbc01c5221778038a422ef0070d9c5de00e1af0bbc01c35d17780386a82ef0070d4c5de00e1a78bbc01c34d17780387cc2ed0070f9c5d800e28e8a1801c5431418038a6e2830070f7041c00e10e081c01c21310380388882030070e203f400e,0x1eb8dc401c4441af80389c435d00715e06b800e1d70d7001c6251aa803889435500711106aa00e1ba8d5401c3741aa80389de345007137c68a00e29d8c9001c53619200386ba3240070d1464800e1ae0bd401c3e617980387bc2f30070d705e000e1a90bc001c5461778038a8a2ef00715085de00e,0x34b14f001c69329d0038d205380071a3ca6e00e34694d401c6392968038cee52800719d8a4e00e33a949801c66f2910038cce51d007151c88800e29b911001c5332220038a5c44400714a088800e291911001c43e1f100387cc3b70070f846f000e2a38dd001c5331ba0038a4637400714786e800e,0x1a701f801c34c03f003853c07e00708700fc00e10981f801c1d303f00382a007e00703000dc00e05e81b801c80a03700380c805a007018c0b200e02b010001c05f01f80380be031007047805000e02b008c01c056010003828e01f0071cf8e7800e39e98bc01c73c2b10038d3053e0071a5ca7a00e,0x1a8836801c34f06d00386940da0070d241b400e1a2836801c29d06d00384380da007084c1b400e101836801c20106d00383fe0da00707dc1b400e0ea036801c1c406d00383620da00705401b400e08f025401c1080418038ba007e00714f80fc00e1f801f801c3d903f00387ae07e0070d980fc00e,0x296836801c52c06d0038a520da00714a01b400e293036801c52306d0038a440da00714841b400e28f836801c51e06d0038a3a0da00714701b400e28c836801c3e606d00387ae0da0070d941b400e1b2036801c35f06d00386bc0da0070d741b400e1ae036801c35506d00386a80da0070d4c1b400e,0x10e03a401c2130748038e780e10071cf41b400e39e036801c73b06d0038a8e0da00715141b400e2a1836801c54206d0038a800da00714f81b400e29e836801c53c06d0038a760da00714e81b400e29c836801c53806d0038a6e0da00714d81b400e29a836801c53306d0038a640da00714b81b400e,0x1b0846401c35c08c80386aa1190070d4823200e14c046401c29708c8038438119007084c23200e0fb846401c1f208c80383ca119007078c23200e0e2046401c1c308c80382c4119007042020e00e2a103a401c5290748038a3e0e900714701d200e1f803a401c3e707480387280e90070d641d200e,0x17a86b40241cb0d6804829c13f007ab34c345a35699834b1aacc30416295b86062c42b48bfe57c57295d8adeca439e152d82461a2a03060c1a5336089820a5cc2130314b182c5ff28f30b4ae25192a1846401c52308c80387d61190070f9823200e1f0846401c3de08c80387b21190070e3c23200e,0x1ea872802c2400cd805834219900b27a003e015011007c02a2600a0004839414000906e82800120a705000241ba09c804837412d009053825a012131048c02410105c004829c07200907280b60120a6816c02406401880485de2450090a0c48a012176090402428212080486f62140090bd4428012,0x27306e40341dc0c380680e006900c9670704018130873c0303fe0e500607481ba00c08643740180d305b80301ca06a00585da04d00b07ac09a0160e5013402c1ba026805835804d00b0bd407e0160e500fc02c1ba01f805870803100b07280620160b300c402c60e12f80587dc1dc00b1838394016,0x1ed873003e9eb0e1807c7d21ba00f8d3c35801f0f186b003e35e0d1007c34619400f89c830e01f08b83a003c1320280078c2c26200f1710b1601d2f48da803a3ff0d680740c801f00d809c03e01b0ee040403407103800680e006d00d051c04a01a27009840344f412f80684c21cf00d137837401a,0x2e68bb003e5c1176007cb7c2ec00f96ec5d801f2dd0bb003e3e8176007c7ce2ec00f8f805d801f1ef8bb003e3da176007ca5a2b800f96d450a01f4f189b403e21c103807c42620700f912840601f222080c03e411101807c7d21ec00f89003c601f291877403e3550ee807c7d41cc00f8fa439801f,0x4001d003e0ba038007c47606400f817c0ac01f027811003e040018807c06802500f80c004401f3a398b803e6382e2807cb7844700f948c88a01f2ef10f403e5ce21e807cb8c43d00f96fc87a01f2de10f403e43d1f4807c87a3e200f8f8c5e801f1ee0bc403e5dd176007cbb82ec00f97485d801f,0x10e03a403e203074807c3860e900f94901b401f1f7836803e3ee06d007c7d20da00f8d941b401f175836803e27206d007c4d80da00f884c1b401f101836803e1e306d007c3880da00f870c1b401f4f8834c03e9e5069807c1800ba00f823010001f2eb01f803e5cf03f007c7d207e00fa7f40e801f,0xc9046403e16108c807ce8c0e900f97601d201f2ea83a403e5d4074807cba60e900f97181d201f2e283a403e5c3074807cb800e900f96f41d201f2db03a403e5b4074807c7de0e900f8fb41d201f1f483a403e3e4074807c7ba0e900f8f601d201f1eb03a403e3d5074807c7a60e900f8d8c1d201f,0x1758ad80442030ee00883ba1dc0110e9c3940220ee071004451f0dc808869e1ac01109b0310022173861c0441a60bf0088ba211900f973023201f2d9846403e3f108c807c7dc11900f8fb023201f1ea846403e36308c807c6c211900f8b1823201f10e046403e20c08c807c3f411900f878c23201f,0x109881c0463d40dd008c4381ba01186843280230ee040404423b07e00884760e201104701b202208e022004411b043008870e0560110e080ac0221bd81580442f502b008840e05601107280ac0220dd015804417e02680882dc031011059806202206d00c004407e0118088a7a38401114b4570022,0x1de87300563ad0e600ac3c61ac015890033602b0d186640561660b080ac4c21ff01504781b40280d6816805011901b80a0b8858b01414a46d40281a286b40502c60d580a042805901386e80b202728f880804e050015809817a06f01281c00de02540501bc04a07003500901b20250121ff404a024,0x2bc0bc005640717800ac75c2f00158ff85da02b1d20bb40565a717600acb4c2ec015966c5d802b2cb0bb005658817600acb0a2ec01596045d802b2c00bb00563bb17600ac7742ec0158ec85d802b1d88bb00563ac17600acaf6285015904440602b21e87ac0562ec0f580ac5d81e70158bc03c602b,0x2cc94c00565a821e80acb2e43d015963487a02b2c310f405658221e80ac87a3bc01590f476602b2fb0e1c0565f51c380acb3e382015967070402b2fb0d980565f41b300acbe6366015978c6cc02b20a8d980565991a600ac8262f50158ef85ea02b2ca8bd005640c17980ac76e2f301597c45e202b,0x1d503d00563a807a00ac74e0f40158e941e802b10c83d00561ec07a00ac3ce0f40158f081b202b1e083640561e306c80ac2c20d901585741b202b05e82ec05680005d80acb42088015966011002b1de02200561f504400ac3d8088015822c0ea02b03f81d405604101880ace8662e01598e0b1802b,0x1e1847c0563c108f80ac77e11f0158e9c23e02b163847c05621908f80ac3ee11f015879c23e02b3a103d00565a307a00acb400f401596781e802b2ce83d005658d07a00acb180f401596281e802b2c383d005658407a00acaf80f401595e41e802b1e103d00563bc07a00ac7700f40158ebc1e802b,0x44a06e00624620d600c43461a1018877030603145805a80621dc0aa80c52ca14e018a54829c03148f85380622cd0a700c459414e0188b2029c03115e05380622ba0a700c42d614e01881f806203009200fc05cbd801880b174c0310162a8406202c04a80c405859a08f80acb2811f01595d823e02b,0x21e87ac0623640ee00c442a1cd01898383940312fd872806243e0e500c47cc1ca0188f883940311ef07280623d20e500c47481ca0188d543940310e607280622840e000c4c4a1ba01897103740312c586e80623ed0dd00c47c61ba0188f7037403117786e806221c0dd00c43981ba018a260370031,0x1b70a1406273f14180c4bb428201896945040313a28a000622ed14000c591027f01898bc4fe03131089fc062b3813e00c4e8a27c0189d044f803131709f006262013e00c4bac27c01896844f80312fd8984062dbd10b80c44462150188dd441c0311b788380622f110700c44c220e018887040e031,0x1ed0bb40625dc17600c4ba42ec01897045d80312df0bb00625ba17600c4b4c2ec018966c5d80312c40bb006258517600c4b002ec0188f9c5d80311f00bb00623da17600c47742ec0188ec85d80311d60bb00622e316980c48c22b801890e450c0311ba0a180625b514280c4af628501890d450a031,0x31c16240627502b680c4e8c5600189d08ac00311f80e1c0624231c200c47ae38201897546fe0312db8dfc0625a01bf80c4afa37f01890646fe0312220dd00625c61b780c4b6c36f01890f86de0312e30db80625b61b700c4b1a36e01895f06dc03121e8db80625c117680c4b702ed0188f805da031,0xe481340621ba02680c437204d01886b009a0310c4013406218702680c42dc04d018a840092031053012406210101f80c4ea003f0188a0c07e03112b00fc06225401f80c44a603f018872807e0310dc00fc06214e01f80c421a03a01882fc06e0313a018840625ea2e580c4c705c201898e0b18031,0x1ba013406236f02680c46dc04d0188bc809a03117781340622ed02680c45d804d0188ae009a03115b013406228602680c450a04d0188a1009a031141813406228202680c450004d01889fc09a03113e013406221602680c442a04d018881c09a0310ee01340621cd02680c439604d018872809a031,0x99017006275002b00c489c0560188df80ac03110b015806221502b00c440e05601887340ac0310e581580621ca02b00c43920560189d4009a0313a0013406273e02680c4c7204d01898e009a0312b1013406256002680c489c04d0188e1c09a0311c2013406238202680c46fe04d0188df809a031,0xe503940621ba07280c42dc0e50188bbc1a8031176035006226206a00c43940d401886e81a80310d0835006216006a00c429c0d4018845c17e0310a002e006213405300c4246095018b11411a0316100234062bdc04680c575208d018abf411a03156e0234062aa504680c550208d018a2cc11a031,0x13e040406226008080c4426101018881c2020310f584040621dc08080c439610101887282020310e484040621c308080c437410101886e02020310b5840406214e08080c43741000188bbc1fa03117603f40620fc07b80c46e80f70188db81ee03110a83dc06220707800c45da0e501887ac1ca031,0x306091406eac712080dc50221401b89f84280374c407ec06e60e0e500dc7dc1ca01b8f043940370ca854006e2ca0a700dd30414a01b8b60294037166852806e2cb0a500dc37014a01b89001ac0332a884040624cc08080c46261010188c3c20203117784040622ec08080c450410101889fc202031,0x1b4019006e24203200dc42806401b88380c80370fe819006e1ca03200dc37406401b86b40c80370a7019006e14a03200dd2da03f01b83a00720372fd8da806e4231b500dcb8036801b961c6d003720c8da006e8ea15d00dd7c628101bb0244fc0371f2097c06e3bd12f80dd81624501baffc48a037,0x1b4045c06e12508200dc24610101b8da81b2037092836006e0cb05e80dc4c20b801b897c1700370e502e006e1ab05c00dc6d409d01b982412a037285825406e2ba04a80dc48209501b872812a0370d6825406e14e04a80dc29409501b952c0c80372a5019006e4bb03200dc6d606401b8da80c8037,0x16384a00741fa09400e82c812801d058425003a0fd041007416108200e82c209701d026411403a06e81200741fa0dc00e82d616101d13801d003912282580725fd13100e484626101c98384be03920c897c0724df0e600e44c21cf01c2f9d7c80375d92ebc06eaad55500dc29413101b8da822e037,0x177871007e3610dd00fc6901ba01f888037403f10986e807e1f70dd00fdffa1b801fa46c37003f0fd06e007e1d20dc00fc5de1b101f87e82d403f0b585a807e90e0b080fc2d414f01f8b1c29c03f0fd053807e16b0a700fc2d014e01f859029c03f0b0853807e4e217780f80fa03f01e027407e03b,0x2960bbc07e52717780fca442ef01f94845de03f1aa0bbc07e35317780fc69e2ef01f947450c03f2a18a0c07e73d13f80fce7627f01f94f84fe03f28e098407e41113080fc80426101f90044c203f28f885807e2610ff80fc5de1d401f904c39403f1b2872807e3610e500fc6b81ca01f873039403f,0x17a815807e20702b00fc39405601f86e80ac03f0e5013407e08802080fce7c73c01f9cf0ac403f3a014f807e63929900fcc7252d01f94ec70803f28f8e1007e5471ba00fca6637401f94786e803f2220dd007e54417a80fc8262f501f95185de03f2a28bbc07e54217780fca7e2ef01f94e85de03f,0x17a83fc07e10407f00fc3940e501f86e81ca03f098837007e26106a00fc29c0d401f84b417003f096827407e94304c80fd23809901fa46413203f080826407e8d904c80fc21a09701fa51812a03f04c823407e10c04400fc13a06401f84a00ba03f092017407e10402e80fc1fc05d01f8dec0ac03f,0x163853808614a098010836219502106542a00420f5815408259d1bf8104be22f10209d0c4f80411d6897c0824130e5010477c1ba0208ed03740412e98dfc08074713e01007b625f0200a083860401f586e808055c08080fc99810101f8dd020203f0e5040407e1b808080fc2d410101f853820203f,0x1e9072808a1f70d681149be1310220da82620440e604c40881ca098811037413102206b42620440a704c408814a098811055211e022076023c0440a304780889f9046811029c06402205280c804410a01640881ba02c8110e7854b02214a06d404428f8da80882ed10a011099c1ca022058429c044,0x20c8bb009031a1760120c2c26202413f44c0048176079c09060e0e601209e81cc0240bbc3620480d886480901610a7012026210402387e829c0470b0853808e1fa0a5011c9be40d02317d44900462fa092008c3fe10a01187481ca02310303740461ff06e808c2a20af811835a05a022937c6b2045,0x1f507280983db0e501307b41ca0260d8c37404c27a072809607d026812941a04d024829809a0490f384c809016409901202c213202413c01d004821183a00901b107401202580e202403881c004805602a80900bc04a812013008d024020c1000482fe90600905fd1b381208462ef0240c905de048,0x3a409fc09a40813081345e820e0268f9c3d604d1f107ac09a4f40e501347fc1ca0268fac39404d1f3072809a1cc0e501349de1ba026903037404d20386e809a3fe0dd01347a81ba0268bc037404d0c7062c09a8260a28134b762ec0260f7c5d804c1f007ac0983ee0ee01307de1ca0260fb839404c,0xee040409a1ca080813439210102686e820204d17683fc09a20707801345d80e502687281ca04d0dd039409a1ac07281345de0d4026895c1a604d0a002e009a134053013421808802684540f604d03c01cc09a38402b01347083240268dfc63404d1920bbc09a5db17681346342ec0269d244fe04d,0x20987280a03ef0e501408261ba028102c37405020386e80a03ed0dd01407c61ba028088037405010e06e80a01f70dd0140b881ad02808082fc05015685480a02aa0a90140e8c54a02796fc6d004f2db8da009e19503001389fa2600270bbc20204d176040409a25f080813440e10102687ac20204d,0x2a581900a036b03201406d40640280ab00c805015581900a0245032014042806402808380c805010101900a01d8032014039406402806e80c80500d681900a015f03201401b20520282880c8c05051811780a05e513081408062600280f604c00502ed88500a041310a01405ea2140282824414050,0x1de87280aa3ad0e501547581ca02a904c37405506783080a411f032014828c06202917d84840522f189080a43be0e5014905214402907dc35a05115704780a026208b81404c0117028085022e0500dd045c0a0a0408b01402bc11602804d020205009a83a00a011606d01404c00b802806e8170050,0x39d89fc0ac53e13f81586a026102b0de041c05617a08380ac2f110701584c21ff02b11283940561ae07280ac3520e501586ac1ba02b084c3740560fb86e80ac1f60dd01583ca1ba02b0ef85ea0552ca8bd00aa58117601547622ec02a8bb03ce0551e087700aa3c20e501547821ca02a8ef8394055,0x10384040ac1ca080815839210102b06e820205610384000ac20707801583740f002b0bd41ca0560e503940ac74029f0158c7253202b14ec70805628f8e100ac5331bd8158a3c37b02b11286f60561c38d980ac3821a60158a582f502b14805ea0561aa0bd40ac34f17a8158a3a28602b1cf44fe056,0x10c86e80b22130dd01644061ba02c87d83740590f586e80b21e50dd01643861ba02c962c35a05929606b40b234f0d681644261ad02c87dc35a05915685400b22ac0a8016455415002c857c2a00593a115280b05861b40160afa36802c16704900582cc89200b055b08081585e810102b0bc4202056,0x28e09840b23aa130016469a26002c950848a05929988500b252010a0164a3c21402c90f84280591d208500b235410a01645da21402c90f841c05917688380b22f30f4816487c1ca02c8bd439405917687280b243e0dd01647481ba02c8d7c3740591aa86e80b234e0dd01646901ba02c8bcc374059]
def pgP3:Array Nat:=#[0x12404780b221408f016441c11e02c876023c0590e504780b21ba08f016435a11e02c851823c0590dd02e00b220e05701643940ae02c86e815c0590d682b80b21ca04e81646d606402c8da80c805910a01900b21d8032016437406402c83680b405939e152c0b25281b50164a4c36a02c947c6d4059,0x8c81900b415f0318168a6024802d0d9849005a1a609200b45b210701687d020e02d0fac39405a1f107280b43de0e501686c21ba02d0d4837405a10986e80b41e50dd01683c61ba02d0d5435a05a14c05180b4248098816442813102c88382620590e504c40b21ba098816435a13102c8aa423c059,0x10e081c0be34e0dd017c4261ba02f870c37405f1d207280bc3fe0dd01783c61ac02f058429c05d1920bbc0b831a17601701a806402d8da85de05b1b40bb00b6639122816c4fe24502d98e048205b13e09040b6214103816c89c1ad02d872435a05b0dc05b00b61b80a5016c23c0da02d06b415e05a,0x2ba89080c43be10a01888261ca03115e03740621d706e80c41e30dd01884041a603105282600600c682d00c014e05a01802940b403003a00c806019209840c04e213001809e825f0300c684be06027308080c04e20dd01802c814e030058429c06015e05280c01d20a501802c814a0300f705e205f,0xdc05280c81dd0a3019035a12703186b416e06307481900c60da032018c7b625f0318d7841c0631ef07a40c63610e5018c6aa1ca0318d483940630f287280c63eb0dd018c7bc1ba0318f5037406310e06e80c63e10d6818c2b014603183d00c806206c81900c457525d818875a25f031167c484062,0x17a87280c82ed0e5019199c1c9032189437406422506e80c83e90dd01907b81ba0320f503740641df06e80c83a40dd01905e01ba03208703740640f286e80c81c10dd01904041b9032170435a06427786b40c83da0d681904381ad032086435a0640ee857c0c816b0a701902c214e032059829a064,0x2db08500c83e010a01905ea2140320bc842806411188500c821610a01909c02130320bd441c06449387f40c82ab0ee81903ba1d80320d1439806427a07280c84d90e501908941ca0320fbc3940641f507280c83db0e501907aa1ca0320f083940641de87280c83ad0e5019074e1ca0320d94394064,0x26912ec0c84f41d801909c036a03211106d40641c20da80c85bd1b40190b0c36803216106d00642be8da00c843d1b401907c03680320dfc6d00641b50c900c836818d01905de2620320bbc4c00642da097c0c857912f81907ba25f032177c4840641c109080c85de10a0190b8c21403216e0428064,0x12102e00c824105c019041c0b803207281700640dd02e00c81ad05c01902d80b803205381700640a502e00c824205b81903740b7032052816006412102b80c81ba05701903940a60320da813a0640a702740c814a04e81902be095032053412a0640a502540c814604a81901f80700321d08a94064,0x1b504c40c836809881903fa13103205382620640a504c40c814e096819055c11e03206e823c0640a684780c814608f019048a117032090822e06410a045c0c81ba08b819035a117032053422e0640a3045c0c8140080819024e0da0320da817006413082e00c826005c01904be0b80320914170064,0x40f01e00ee2450e781d87481ad03b086435a0760d305e80ec24807101d44840e203a8598196075176828c0ea2ec05181d44900a303a87301460750d6828c0ea2f504c81d448409903a87301320750ba82340ea15504681d4c1c24103a86482e807540c83500e67f60a381c029c0b8035b309982064,0xf482980f636a04a81ec29a09503d836814c07a04301f80f45dd1b401e83ba10703c07741f807808803500f01d806781e03600cf03c036411e0780b3020c0f04e012281e09e824103c091439e07827306d80f04de0d681e10bc16603c07742be0780ee85400f008303f01dd04407803ba0800f0077,0x2a087d40fc3e20f581f87bc1e903f0f7c3ce07e17807940fc5230ee01f86bc1dc03f0d543b807e20487500fc2ef0ea01f87bc1ca03f079439407e50c87100fc1e30d601f86bc1a203f078c33607e0a905400fc11806d01f42260cf03e844819c07d40f83080fa41813101f41b407d03e092026207b,0x20c0d9c0fc5f31b301f882a36603f103c6ba07e2058d540fc4031a681f869c31603f0f6462007e1ef0bcc0fc35217801f8bba2ec03f17645d807e2eb8bb00fc5cd17601f87d02ec03f0f7c5d807e2e70a080fc5d613e01f87e024803f0f5c49007e1b309080fc34c12101f844021303f0f8c41c07e,0x2a083680fc52d06d01f8a480da03f0d941b407e1af03680fc28e06d01f851a0da03f084c1b407e0f183680fc1d306d01f83780da03f05401b407e0a803380fc0d904b81f812808603f023010007e2f80fc00fc4001f801f87e037d03f16f06f007e2918dd40fc5de1b701f8b7836e03f0f886dc07e,0xac04640fc15008c81f8e8e0e903f17601d207e2eb03a40fc5d207481f8b9e0e903f170c1d207e2e103a40fc5c007481f8b7e0e903f16f41d207e1f803a40fc3ef07481f87d00e903f0f901d207e1ee83a40fc3d607481f87aa0e903f0f4c1d207e1b303a40fc21c07481f83f40e903f150c1b407e,0xd682b010017705182002f408d040055411a08028f86d81001a60bb82002cc161040174423207e2e604640fc5b308c81f87dc11903f0fb023207e1b184640fc36108c81f843811903f083023207e0fd04640fc1e308c81f83a611903f064823207e0b104640fc16108c81f82be11903f057023207e,0x10702b810c1ca05702183740ae04306b415c0862a30da810c5a71b402143ba107041854020e0830ee833c10628e0ee820c51a1dd04187743a60830e9859810624807102044900a304089201320812cc892010221c0d682043ba0fc040059819608022502b01002f505602004840ac040081c158080,0x2d10bb011059617602207762ec0440ec45d80882cb8a081105a113e02206c61f504410243a8088163062c1101f50bb82202cc16104405482a008808f036810e2ae14e821c6ce2620438a7829a08714b853410e1d30a6821c51c1460438ab823c086154847810c1d808f021828c11e043085015c086,0x2c203d01103c207a02207760f40440ee01e80881d783d01103a807a022074e0f40440e941e808810c83d01101eb07a02203ce0f4044078c1b20880b0836411015d06c82202380d404403501a408808f027c1105a81b70220b0436e0440ecc6dc0882098d581103be1a40220b4e2ec04416905d8088,0x166852811a2c80a5023457814a0468ae829408d2cd047c11059408f8220aec11f0440f0423e0881df847c1102c708f822055011f0440a8823e08810c847c1101e708f82203ae11f0441d0c1e80882d183d01105a107a0220b360f404416601e80882c503d011058907a0220b0e0f404416181e8088,0x1f4873011a3d20e602347481cc046888c39608d21f072811a2f50e502345da1ca046891439408d0e6072811afeb0da82353fc1b5046971035a08d2c586b411a3ef0d682347c61ad0468f7035a08d1bc06b411a3750d682343941ad046914435808d0ee068811a1a30d082342d616a04687702aa08d,0x2db8bec11a57d17d8234b702ed0468fa05da08d1f30bb411a3e017682347bc2ed04696985d808d2cd8bb011a3bb17602347582ec04695ec50a08d2220a0c11a43d141023450c27f0468a144f808d2fd891411a44510702345da20e046891441c08d178078c11a8490ed02345de1d4046983839808d,0x180828c11a2fb05182345de0a30468bb414608d176028c11a286051823450a0a3046888c14608d106828c11a20705182343980a304686d814608d0d6828c11a1ac05182343440a304685e814608d3a8026411a14a04c8234ea04bd046971887c08d2e190f811a58621e823487c3e904690f477808d,0x21e838811a1ad07102342400d40468bbc19608d176032c11a24506582342ea0cb04685d019608d0b3032c11a15506582342940cb046845c17a08d3a802b011a2f505602345e60ac0468bc015808d17682b011a223056023441a0ac046881c15808d3a8028c11a444051823487c0a304690f414608d,0x21e83f011a2f507e02345e80fc0468bcc1f808d17903f011a2f107e02345e00fc0468bbc1f808d17683f011a2ec07e023448a0fc046888c1f808d10983f011a20707e02343d80fc04686d41f808d0d683f011a1a207e02342d80fc04685281f808d08083dc11a24807682343d80ed04686b41da08d,0xa502e012a0e804b025484636a04a969c6d009520c8da012a36a17782546d02ec04a8b685ae0952fe898812a60a130825484624504a90644820950d5862c12a1ae0af82542ae14d04a827412e09261eb0ec11ac3561982355eaaf3046abb55d608d090040411a62807e02348880fc04690f81f808d,0x6e828412e0b504e825c16409904b85a82c20970fd052812e1d808f02542be11a04a898822e0950ec045c12a15f08b82542020dc04a849c1b4095091034412a10105f82541a80bf04a891417009512082e012a21405c025441c0b804a87281700950dd02e012a1ad05c02542d80b804a8538170095,0x1a98bbc13234f1778264a3a28604c950848a0991a6090813254310a0264a3e20d04c911040609912287fc1324130e602646c21cc04c8bd43940990e607281322ef0e202652241b504c8d8435a0990fb86b41322c70a502643f414a04c87482940990b205281321610a502643f412804b8584250097,0x467a33413244a05602645ea0ac04c881c158099463231013253e28d0264a8e44404c94dc888099299911013252e2220264a5044404c91106be09928f8c0413254417a8264a8c2ef04c95145de09929d0bbc1325361778264a4e2ef04c94885de0992908bbc13235e17782646ba2ef04c8d505de099,0x17986e813a1fa0a702742d414e04e859029c09d0b0853813a1fa0a5027429413004e0b1c29c09c2ba89081363ad120826c7681ad04d8f5c49009a1ed89041343eb0d6826825410104c98c01f809922203f01321b507e02642d80fc04c85ac1f80990a503f013210407c82644840e204c8914196099,0xb085381403be0e5027c7fc1ba04f937c26209d1b504c413a248098827435a13104e852826209d080837013a16c05c027429c0b804e852817009d10a02b813a20e057027435a0ae04e841014009d2938da813a53c1308274a8624504e94fc48a09d299091413a52d12282746cc24204e8bb442809d,0xf384c81424f007402848460e805086c41d00a12fc108c1425e42118284a8442305094f48460a129c108c1425192118284bf6416050908c82c0a12fd8d901424231b20284a7e32405094ec6480a129c8c9014253519202846923240508b2858e0a130707281424f40e502843f414e05005a029c0a0,0xd603f01461ad076828c5d80e205189201c40a3120832c146240065828cbe22f1051976c5da0a320409141463660f6028c5e01e50518ff83980a31f587301462f50e5028c5da1ca05189043940a30e607281462ef0d8828c9de1ad051903035a0a320386b41463fe0d6828c31a18a051970c87a0a2,0x178883814c40c0f482985e61e9053103c3740a617806e814c2020bb829848411705296f86d00a52ea097c14a3f01240294bb4241052975c4820a52e2890414a5c212082948880fc0518bcc1f80a317903f01462f007e028c5de0fc0518bb01f80a312083f014622307e028c40e0fc05186b41f80a3,0x12287fc15844a0e502b05ea1ca0560bc83880ac1b286b41582130d682b03ee1ad05607d835a0ac0e506b415858a21e82acbc62420558dbc4280a9121045c14c36a05c02984c20b805309141700a610a02e014c20e05c02983740b805306b41700a606c829c14c5f91228298bf024505317c441c0a6,0x2c4890415a2ed10a02b4c5a0fc05611281f80ac17a83f015824207e02b04460fc056081c1f80ac0d683f015820707682b0a6644a05614b88940ac2250d7c15851f18082b0a402f50560d785ea0ac1ae0bd415835417a82b06a42f50560d4048a0ac22388381582f510702b05e820e0560bc441c0ac,0x2a1091415c53f12282b8a6424505714b448a0ae269090815c34c12102b86de21405708504260ae10a081c15c3b70dd02b86ba1ba0570d703740ae17986e815c2130dd02b86f01ad0570d9435a0ae1ad06b415c2ed0d682b84261ad05716146d00ad2cf097c15a5a512082b4b4424105696304820ad,0xa504c416a10405c02d429c13005a03a01700b4192091416831a12082d02d014e05a059c29c0b40b205381681610a702d0bb020e057970c41c0af1f3072815e35c0dd02bc49011e05708381b60ae107030015c21405c02b835a0b805715d49760ae2938da815c53c13082b8a38261057150c48a0ae,0x22f870c1703d60dd02e05e01ba05c0bbc3740b810106d81703ef0d682e07ca1ad05c0dd435a0b810386b417016a0a702e02d414a05c03681700b71eb892016e54010702dca5c20e05b8d2841c0b71ae072816e3e60dd02dc4381ba05b87c83740b710e06b416e0d905c02d85ea21405b0edc3740b6,0x1b40c6817036a18082e06d02fb05c0da85de0b81b40bb01704e213002e0b3c25f05c0bbc48a0b82ec89041705a512082e0b4824105c16884820b82c6090417058912082e05d824105c08704280b82ca88381703e310702e07b820e05c0bd041c0b8143883817021410682e1b7820705c085040e0b8,0xee05d818c24507e03144820fc06298bc1ee0c531703dc18a2ed07b831448a0f706289041ee0c50d683dc18a4b9065831448a0cb0628b9c2ec0c41b788501862ed10a030c35a0db06007282620b80a704c417014a09882e027a0fc05c05381b60b810702f41705851b402e09e033f05c0da86480b8,0x17603f019624807e032c48a0fc06589081f80cb12083f019622307e032c40e0fc06586b41f80cb0bc83f019616b07e032c2940fc065a6e81a80cb45783501962ef130032cc1824506597ec3980cb0ca85d01961b80a5032c29c14a065950c36c0ca13605e41942eb0bb03282940cb064a0241ae0c8,0x27786b419e2b60bb033c362174067a0e02cc0cf41a059819e8300b3033c3a414a06785402320ce40e033c19c81a06783390300cf06718941f80cb2a583f019654a07e032c8940fc065911c1f80cb22283f019644407e032c87c0fc06590f41f80cb1b583f01962f307e032c5de0fc0658bb41f80cb,0x21189841a85b412f8350af225f06a10644be0d417789141a826112283505d824106a097c4820d4130873c1a85fb0e503509781b206a05382940d428e09841a611f06a0348bca26106905381a80d13ff83641a0117088833c3ba107067859820e0cf156835019e2b10ee833c3ba1d8067940c36c0cf,0x13e04041a8245080835048210106a08542020d410a04041a820708083503e410106a072c2020d40e504041a81ba080835037010106a06b42020d40b504041a814e08083508462ef06a0da85de0d42d10bb01a841917603506d02ec06a218055e0d430b09881a83f1131035078626206a18284c20d4,0xb205281b0423177835c8322ec06b93bc3740d73fd05501ae1610a7035c70810106a0dfc2020d41bc04041a837508083506e810106a0dbc2020d41b704041a836a08083506d010106a0bd42020d417a04041a82f108083505de10106a0bb42020d417604041a8283080835050410106a09fc2020d4,0x20606e81b240b0dd036480e1ba06c8ffc3740d91db86e81b22200dd03644321ba06c87dc3740d920606b41b23ff0d683644401ad06c886435a0d90fb86b41b22a70af836500c15306c87e82500d80b084a01b01fa08203602640dd06c04641b20d807483641b08eb16283602c814e06c0b1c2940d8,0x20409841b23aa130036475a25f06c9d2048a0d92fc89141b2d4310c836443821906c90204020d91b187dc1b24690fa83648ce1f506c8b083ea0d916087d41b22bf0fa836457a1f506c87d43e80d91f807b81b23660f603648181e906c8f743ce0d942987481b21f50e703643c61ce06c95e03740d9,0x21190581b242320a036484640906c97ec8100d921190201b25fb2030364ba040006c90307d60d91ff0fac1b240c1ef03647fc3de06c8fbc7840d91f70f041b23ea1de83647c83bd06c983875a0d91ed8eb41b23da1d603647aa3a706c8f5c74c0d91f30e901b23d21d203647e436a06c8f0c4c40d9,0x9404641b254b07e03648260f406c90301e80d920383d01b23fe07a03647840f406c8edc1e80d91d703d01b23a407a03643c60f406c95e01de0d907f83941b20fa07103641ea0de06ca0b01b40d92e2162c1b283741b036506683206c97e88460d92f4908c1b25e52118364bfa41806c97ec82c0d9,0x10e06e81b42130dd0368a3e1b906d170435a0da29606b41b43ef0d683687ca1ad06d0f8c35a0da1ed06b41b43650d683686b41ad06d0d3c35a0da1a286b41b421c0d683684261ad06d0b1c31a0da2a085dc1b42a90ac036878211f06c886423e0d90f1847c1b219b08f83642c211f06c857423e0d9,0x29008501b451e10a03687c021406d0d504280da10e08501b4a1e109836842821306d283c4060da21187fc1b42610ff83687681f606d0f743ce0da1df07941b4a1e0f183688461d406d0fa43740da1f186e81b43dc0dd03687ac1ba06d0f503740da1af86e81b43550dd03686901ba06d0d143740da,0x50e8d3c1b4a2e1a20368a3e30106d0aac51a0da1f889881b453c13083686a026106d0f604c00da1ed897c1b453012403687ae24806d0d304900da39d89141b45431228368a7e24506d14c848a0da29689141b45df121036869824206d17784280da2e308501b45b810a0368b6c21406d14cc4280da,0x28e108c1b45951f18368c1c3db06d164c7ae0da2900ef81b453d1c20368a7638406d14747080da2a38da81b45461b50368a7436a06d14a06d40da2938da81b45261b50368bfa36706d29306ca0da50d0d941b45fb1b2036884636406d0ef86b80da5118d541b44231a9836884635106d17ec6a00da,0xdd03a41b41ad0748368ee473c06d172cb600da2ef95d41b473c2a58368d4254706d1a80a8c0da30615081b469529d8368d2253906d1a20a640da34014b41b45fb2948368cd451f06d1828a380da2ba92ec1b45462118368a8a42306d14f48460da29c908c1b45382118368a5242306d14888460da,0x1ee03a41b43da07483687ae0e906d0f581d20da1ea03a41b43d207483686cc0e906d0d941d20da1b083a41b435f07483686bc0e906d0d701d20da1ad03a41b435607483686aa0e906d0d501d20da1a903a41b434f07483686980e906d0d281d20da1a403a41b421c07483684260e906d07941d20da,0x2e083a41b45b80748368b6c0e906d16c81d20da2a203a41b45400748368a660e906d14c01d20da29703a41b452c0748368a400e906d14781d20da25d83a41b43ef07483687da0e906d0fac1d20da1f483a41b43e807483687cc0e906d0f941d20da1f183a41b43e207483687c00e906d0f781d20da,0x17384641b429608c836851a11906d08702320da10984641b420308c83683f411906d078c2320da0e984641b41c408c836832811906d05942320da0ae04641b411708b03682000f006d03ec1da0da3a283a41b45e10748368bbe0e906d17781d20da2ed83a41b45d80748368b8c0e906d170c1d20da,0x28105dc1c42e50bb83882fc17707105e82dc0e217683dc1bc1ad07b83783100f706f05d81ee0de11c83881bc1610a1837426412806e8b803f40dd516a87c1b412808f8368a8611906d14902320da29184641b451f08c83687dc11906d0d942320da1b184641b436108c83686aa11906d0d3c2320da,0x2c586b41c654b07e03888940fc071111c1f80e222283f01c444407e038887c0fc0710dac1f80e217783f01c42b807e03884460fc071081c1f80e20ee83f01c41b607e038835a0fc071061c1f80e20bc83f01c417607e0388704248071103448a0e225d89081c438212103887d21ec07119342ee0e2,0x17a84041ca2ef08083945da1010728a0c2020e513f84041ca261080839448a10107288542020e510a04041ca20708083943e410107287702020e50e584041ca1ca080839437410107286b42020e52f88bc41ca40d13083947c01eb0728fbc3940e50dd06b41ca59c124038cb3e2420718ef44820e3,0x1b508001d04190ff83a09f61f50740cd43ea0e819987d41d03df0f383a06c81dc0740c6839e0e827106e81d04e60dc83a09de1ad07407703180e82f214641ce5dd20c839cba241907390647d80e71de897c1cc58b0dd03987081010728de02020e51ba84041ca37408083946de1010728da82020e5,0x2b790641d056e20c83a0a0e41907410647be0e82118e101d04191bf83a084636a07410646d00e85250cd81d0a3719b03a07083240740da86480e82e98c681d05cd18d03a07ce31a0740f4c6340e81bf8c681d036818d03a08462610740c904c20e820c897c1d031a12f83a198821007410204020e8]
def pgP4:Array Nat:=#[0x1f686e81d23dc0dd03a46ac1ba07488703740e92e206b41d24f009903a084613207410642640e819204c81d031a09903a03ce13207406c42640e827803cc1d042307983a06480f3074079c1e60e82f215c41d05b32b783a0ae842307415c48460e82b8108c1d050821183a0b7641907415cc8320e8,0x1f809201d236612403a46b224507497844840e91b309081d274512083a4bb424107497644820e92e289041d25c212083a47c8241074976c4280e92a208501d222010983a48461ff07490343fe0e919207fc1d23630fb83a47e01ee074904c3ca0e920087501d23240ea03a45de1c407497103740e9,0x2df8da01d25be1b403a482e36507490586c80e92098d841d24e01b003a482436007490346b20e92098d481d24081a803a480c350074901469e0e92700d241d24011a483a47fe3450748f906340e91ea8c681d25b717d83a47e22620748d644c20e91ec09801d25d412f83a4b6825f0748f904be0e9,0x1ef84641d23dd08c83a47b41190748f582320e91ea84641d23d308c83a46cc1190748d8c2320e910e04641d20fb07683a4bc65e10749d18a940e92a2104c1d24f41f503a4be23dc07493f47b00e927a0f541d25d51bf83a4ba637f07496d46fe0e92ef0da01d25dd1b403a4ba436807497006d00e9,0x2ea84641d25d308c83a4ba211907497382320e92e684641d25cc08c83a4b8211907496fc2320e92de04641d25bb08c83a4b7411907496dc2320e92db04641d25b508c83a4b661190748fc02320e91f784641d23ee08c83a47da1190748fb02320e91f384641d23e408c83a47c41190748f802320e9,0x109881c1e03550e503c04261ba0780dd435a0f010386b41e01ba0d683c06d60fc076888c1f80ed10383f01da1ad07e03b4a4644507691286aa0ed17a87941da2f00dd03b4be82480760a1035a0eb12303f01d424307e03a835a0f7075091c1da0ea3a284641d25de08c83a4bb811907497682320e9,0x2c586b41e85762b783ccae251907996048320f320c8ec41e659d18d03ccb2c31a0798ee86340f31d28c681e65a720c83c8b34419079106477e0f2109881c1e23d90dd03c442a10107808502020f010384041e01cb08083c037410107806b42020f02918dd41e035e17a83c0a7c27f078085040e0f0,0x2be8bec1e83c313103d081a26107a0fd44c20f41d509801e859e12f83d0af225f07a0ef44be0f41f909141e874112083d0b4a24107a16904820f42c609041e858912083d06d421207a10343fe0f434187e81e86820fd03d0ce21fa07a101c3ca0f420087501e84070dd03d075c1ba07a08643740f4,0x1d3847c1e83a508f83d043211f07a07ac23e0f40f3847c1e87422a503d09c041207a13808020f427a0ef41e84fd1d503d09e83a707a16806fe0f42ce8dfc1e857b1bf83d0b5036807a169c6d00f42cd8da01e85871b403d0b0c36807a16146d00f42038d841e84071a903d077031a07a0e9c6340f4,0x2cb047c1e859408f83d0b1011f07a161823e0f42c1047c1e858108f83d0b0011f07a15f423e0f42be047c1e857b08f83d0aec11f07a104c23e0f41e1047c1e83c108f83d077e11f07a0ef823e0f41dd047c1e83b808f83d076611f07a0ec823e0f41d8847c1e83af08f83d075811f07a0ea023e0f4,0xbb03f01ee14a07e03dce8662e07b9588a960f72b015281ee37e1b583dc6d42ef07b8da05d80f714189141ee74112083dc50424107b885040e0f70e586b41ee1880bc83dc56c17607b9d145da0f63a0847c1e85a808f83d0b4c11f07a169423e0f42d0047c1e859d08f83d0b3411f07a165c23e0f4,0xfb06b41f81ba0d683f037016c07e274429c0fc0dc05281f81610a503f029c14a07e177887c0fb2d910f81f643e1f103ec7bc2ed07d97d44900fa2fb09081f414a07e03e49b423b07c137c3980f80ee06b01f02fa0c383e17b00fc07bae981f80f755083f01ee25407e03dc48a0fc07b89041f80f7,0x1f809081f83d712103f070e24207e16944820fc12f89041f822310a03f042820707e14ac4060fc17987c81f843d0f583f05d81eb07e0bcc3d20fc176079c1f84f40e603f09c01cc07e18943740fc17986e81f82230dd03f05cc1b607e09c036c0fc4ca06d41f89390da83f12581b507e07f436a0fc,0x2c690f41f858a21e83f0b0443d07e10f47660fc2220da81f843d1b403f0b2a2f407e13885de0fc1b50bbc1f85a717603f0b2c2ec07e16205d80fc2c28bb01f858117603f0b002ec07e0ee85d80fc1d90bb01f83b117603f06d02ec07e0bbc4c40fc22209841f843d12f83f070e24807e098448a0fc,0x54c2a541f8a9154783f14f2a7607e29cd4e20fc62204041f8c1f08083f17b410107e2ea02020fc57e04041f8adb08083f154610107e2a002020fc4e004041f89be08083f137810107e23602020fc45884041f88a645183f113c89c07e1d08a940fc30f94ac1f85bc22383f0b5043d07e165c87a0fc,0xda85a82021fe0a7040436a14e08085a829c1010b085382021b80a5040429c14a08097786de1002d90dbc2003e317a04007d02ed0800f883941000a704041fc1fa0a703f82c214e07f137c3940fd60bb0541f8c1260803f179abca07e2f197880fc5cfae741f8b9a5cb83f15a8ad107e2b395980fc,0x130891420258c1208404b122410808db8482101176090420225f120840442a214080938842610117987a42022ec0f384049e81ca080938039410114106f82022f00dd04045de1ba08088703741010fb06e82028c00dc04044a81b80808de035a10110a86b42022070d684043741ad08094a8320101,0x2c10db82023b31b704046e836a080966c6d01011b70da020259517a0404b4e2ec08096905d81012cb0bb020258117604047762ec0808ec45d81012cb8a0820256513f8404e8627c08096844f81012b209f020232413084049fa26008096784be1011f4897c20231a12f84046e82450808bbc48a101,0x15405882322a20af846436215d08c84d426411730b098822e387121045c7fe34508b05d42a01142cc892020a1fa09404102c212808224243f410447b07e820890f0a704102c214e08205842941040f18770206131096840421a104080987ca541011d30e0820257b1bf8404b7837808096a06dc101,0x1eb8d302325ce1410464ba825f08c97684821192eb89042322201098464b7820e08c948c41c11950408302324140ff84646c61f508c8d843ea1191f6079c2321f50f18464a481d608ca8043a61191f507282324020e204647b21c108c887037411910986e82325430db04643c619b08c8664328119,0x154058823e1b10ae847c49013108f085026211e0dd04c423c382124047834c17a08eb34c23e119416847c23212708f0464fac52308c9ee0a4611930b0fc423260e1f704648323ee08c90647d81192060fac23260e1ed84647ac38808c97846cc1191f80d982324161b2046480e36108c977c698119,0x20c8f0423e4191df847ca403be08f983875a11f1d40e2023e3f2141847cb2e28208f96784be11f2d2890423e5a2120847cbe220e08f965441c11f106082023e4140ff847c7681f608f8ef83ca11f0fa878c23e1ff0e7847c8261ca08f8ff839411f1df072823e3bd0e5047c8041c408f866432811f,0xb085382602c70a504c02c814a0980b2c29c12f0b3853825e53a1b504b459614a0960b2858e12846f07e82508cb0fd04a116c1fa09422843f412816787e82501fc0b084a058e14e0940da82801231b405002462140a0048c87c1ba0903ee426411f3e417c423e544209847cc2c3c308f983878211f,0x19207502641ff0e784c83ce1cf099183839413227a07282641610a704c8a4c36a09890286d413128e098426240d13084c481026109893f44c01311c3892026254212284c46cc2420988da8440131291885426254410a04c49c01ca09890303741311ab06e82628f80a504c437014a098a3a4262130,0x10a050026860a2f204c8c1451909915c48461322a3108c26454521184c8a52423099148884613228e108c26456f20c84c8846353099108c6a213229e0c9026453619204c8a4e32409914986481322908c9026442319204c86ba32409910646341321668b1c2644230ff84c86481ff099108c3a8132,0x166c6d014017a88382801b80a505007fc1ca09d8e9037413b10a05002722ed10704e48941ba09c0da8280134,0x9904a00180033a29cc800e0032ef141800e0032d913a400e003779083800e003778883800e0036c236085ea21468e34645da21463531a4a6c20e66c335ca4620e58e965841c1fa5b4960841c1fa110086441c1f1110884041c1f15c02df83fe1ba5a58f083941ad64f0d943941ad238915033017c4d487f03a414e48807f02c214e4d887f03a414a47e87f03a414a48087f02c214a47fa3f829c14a,0x4b085a807e007080819006200765c8bbc0620075b10bb00620076ef081c06200750b07700620074f3062004400706d019003e007098836401a00706c829801a007074025401600766e33646e80075b6ada86dc0076f3379442a0072c1097c41c00752e88a83ba0074c1a5e82940073a29d0400e0052ef16a000e0052d9160800e005753083800e005752883800e00506582d011a0030fd84c806e003,0x5560da01d00075ec89141d000755109041d000777288501d000777086b41d000727486b41d000769708501b400769306b41b40072d40da81b200774c88501b200774a86b41b20072c106b41b200710a04041700070a703f017000707e02e014600709883f013200707b82e013200707e02e011a007845111011a0070a503f00e00070fe87840c800710a06f40c800706a019009a007098840407e007,0x2180ccc39400b2178cc839400b2160cb439400b2140ca439400b2130c9c39400b20d8c7439400b20d0c7039400b13d870037600b13d06f837600b26407482d600b16787842c200b100836801600a0eb047c0160090e7836401600909884a020800747c85282080071ba09142020071b7090420200710a86b42020071720ae01f800722209841f800721e897c1f800711186e81f80075f30da81d0007,0x2138ec865000b2128f7064c00b2120dd464a00b2118dd064800b2110f6864600b2110eb064600b20f8f5864000b20f8ea064000b20f0f5063e00b20c8db863400b2148ca85e600b2120c945e000b2118cec5de00b2118c905de00b20d0c705da00b20c8ce45d800b20c8c685d800b110887042000b110886442000b110885442000b110884440e00b110884040e00b52e07fc3ba00b2198cd839400b,0x304170c9da00b30416289da00b30396249d800b30317049d600b30316209d600b30216189d400b30116f09d200b30116089d200b30096e09d000b30015f49cc00b2ff96d89ca00b2ff95f09ca00b2ff15ec9c800b2198fbc66c00b2198f0866c00b2190fb466a00b2170fa465e00b2170ef065e00b2168fa065c00b2168eec65c00b2150f8c65600b2148de065400b2140ecc65200b2138f8065000b,0x74015804400b506075803400b3a71d0ce6800b3a69d08e6600b3a61d04e6400b06d012001c00b074036401a00b06c828401a00b06c812001a00b07400ac01a00b09904a001800b050825c01800b30e96a0a0c00b30e176ca0800b30d9694a0600b30d1760a0200b30d168ca0200b30c9684a0000b30a966c9f800b308965c9ee00b30816549ec00b30697189e400b30696349e400b30596309e200b,0x2118bbc0b800b20c8bb00b800b09083e409000b080835009000b07e032c09000b07e023409000b145028407e00b312938807e00b14585a807e00b26584c807400b07f012007400b5de908c07200b5de080407200b074019006e00b5df908c06e00b545106406e00b08003cc06200b08083a006200b0ee035c06200b079813406200b074013406200b09900fc06200b02400fc06200b099015804400b,0x8b83a014c00b09403f814200b09203f814200b07e032c14200b07b831414200b16d074814200b07402e012a00b09903f011a00b09902b011a00b074028c11a00b056028411a00b099026411a00b81107580f000b099028c0ea00b0cf062c0ea00b6180c900c800b5740c680c800b27a0c1c0c800b2700c1c0c800b5730c680c000b50587580c000b4fb86c40c000b49305840c000b49205840c000b,0x7dd165423e00b71096f023200b09904a020800b09904a01fc00b2718bc01e000b2158cb01d000b2100c841d000b20e8c781d000b11088401d000b10087501d000b100874c1d000b10086c41d000b0ea06c41d000b0e986c41d000b09904101b000b2698c681ae00b1920bbc1ae00b18d0bb01ae00b09904041a800b08083a01a800b09903f019600b07e03a019600b07b83a018a00b6170c9016800b,0x48885ac1f800c0b583f013200c0b5040407e00c0fd025c07e00c15d04a006e00c0fd03a401a00c4898b642d600c4d007e82d600c48987e82d400c2118c9026400b20c8c6826400b110884026400b265874826400b265074826400b262074826400b16f074826400b16d874826400b16d074826400b0fe074826400b16e058426400b168858426400b167858426400b679872826200b26504c825000b,0x2038eb86ea00d1ff0e905da00d2c98c2044000d2cb8a0c44000d74097c843200d74117a043200d2f80c3043200d110087043200d110086442a00d110086840e00d110086440e00d7400a983ba00d4438a943ba00d0fa878c3ba00d4388a803a200d20b8f0839400d2098ef839400d2058ecc39400d1ff0e9039400d13c870037c00d0fa879035800d0fa878c34400d0eb85602ae00d0fd078425000c,0x4f4862004400d06d036403e00d06c835c03400d06c80c402c00d01880ac02c00d2fb9760b4600d2f79718b1a00d2f6970cb1400d2f61704b1000d2f416f0b0400d2f316d8af800d08f846401c00d07a03a401c00d077839001c00d015807c01c00d3a2073c01c00d438056001c00d20b8fbc78400d2088fa477800d2080fa077600d2050f8076400d2028f6875800d2010f5875000d2060edc6f000d,0x6c828c11a00d080839411000d08f841c10600d083836410600d06c82540f600d25f83640f000d06c82f40e000d86e8e980c400d2c98c200c400d86d90000a400d2f80c300a400d06c81900a000d51287d40a000d080836409a00d07e836409a00d06c835009a00d08f815809a00d06c815809a00d079836409000d2f98c3008c00d06c82e008800d08b836406e00d06c813406200d406855004a00d,0x7b83781b200d2070ee41b200d2cc08801b200d2ca08801b200d2c088801b200d0fd07941b200d0fd07901b200d0fd078c1b200d0f2878c1b200d0f2078c1b200d0d486681b200d25f855c1b200d150855c1b200d72f05501ae00d0ab847c19e00d083836419e00d73d877419e00d0ee851819e00d31a97cc16600d31997c016600d06c82e014c00d07e036414600d06c832c14600d08b836412a00d,0x6d01900b200e678884c0b200e0e985980ac00e06d02e008800e06d015806200e3ff054405600e06d00e405400e018808803e00e63414d843800e66b148c43800e10e085442600e10e884c40e00e10e084c40e00e4480a543ba00e10e086423e00d0fa878823e00d0eb86c023e00d0eb855c23e00d66a96f023200d22090001f400d2208e981c600d07983a01b200d08083941b200d07e03881b200d,0x4b705381a800f433874c23e00e1eb8dc41e200e10e081c1e200e10a84001c800e08083c01b400e07e03b41b400e1f28d681b400e40705501ae00e442077419e00e406054418000e06d02e015c00e07e036815800e2e80c1814a00e06d02b011a00e0a8042010600e09903cc0fc00e07983a00fc00e6af0f5c0c800e6b108700c800e6a588700c600e109881c0be00e675884c0b400e439874c0b400e,0x401054418001f07e036815801f06d032c10001f06d023410001f07b836405601f06d036405601f3ff054404a01f4f9870c04401f10e084c40e01f06b832c14601a06b82f40e001a72d854c05601a06c835011001606a032c0ea0160a704041700121c20da80c80121bf8da00c801210b08500c801210b06b40c80120a701900620126420bbc06201259a0bb00620126e1081c0620120dd01900ac011,0x2f79634a6602b2f69628a5c02b2088ef06be02b110086440e02b2098ef837402b1ff0e9037402b08f032c11a02708f032c10002740585441b402540785500e002508584140ec0231c10dc41e00222a68e1c1ca02242286c41b40220990394142022427059812a02208f035010c02206a032c10002206d03500fc02209902840ac0221c38df40ac0221c28dec0ac02210386e80ac0224f927c0310022,0x6a025406e0312ec15847000312c20dfc6ec0311f78e006de03157210646dc0311e10dfc5d80311d38bb04be03111f08f0474031674087042a0316160dd03fe031116878c3b80311df8df03740310d386902fc03116985ac2d403142207702ba031473078429c03122610541d802b40085441b402b72e054c17a02b07e036414602b06c832c0ea02b06c82340ea02b06c81900a002b86e105408c02b,0x6a02d00c803106a02740c803106a02d00c003106d01f80ac03110b081c0ac03107f82980a003106c822009a0311c00dbc09a0311c20bbc09a0311bf8bb009a0311ba885809a03110b081c09a0310dc868409a0310ff03f007e031094025c07e03112f05a807e03112e85a807e03112e05a807e03112d05a807e0310da85a807e0310b5053807e0310e5027407603108082580720312b6040406e031,0x8083f014603107403941420310990390142031098840413a0313a78a0c1320310b585a813203108083f011a03107e039411a03107f838811a03107e035011a031080832c11a03106a032c11a03165e0bbc11a0315b30bb011a0311b78a2011a0311ba0a1811a0311b70a1411a0311bd088c11a0316f0081c11a03110a873411a03164e072811a03108f035010c03108082e00c803106a02e00c8031,0x2ae897c2020312a8897c2020311bd0858202031179885820203110b073420203110386e82020310ee05f02020310dc05a82020310b505382020311c20a181f80311bf8a141f80310e686e81f8031617908c1d003157390641d00312af8e1c1ca0311c38df41ca0311f78e001b403167908701b4031513078c1b20311c083a01a80310b505381a80310e50500170031098840417003108f0404170031,0x4e807e829c03a5df0c901d003907e025811a03921189141d003720c89041d003747685281b00371c20da817e0371bf8da017e03708b83f011a03708b832c11a037065825411a03710706b40c803707e825409a03763931c48460375922c8c8320375348f044be0375328ee04be0372cd0c2c4940372d30da03940372ce89283940371d288383740374be25e82940372b10e102020312b00dfc202031,0x2940e106f403f2948e106f203f2930e106ec03f1c20d945de03f1bb0d444c203f1b20bbc4c203f5cb085442603f1bc89843fe03f1b80d1437403f1be07fc37403f461074837003f0dc05ac2d403f4aca55c29c03f48287e829c03f4c0058429c03f145853807e03e0a702e007e03b4b3053820203a09403f013203a08203f013203a094026411a03a07f026411a03a0b5826411a03a7ff05ac11a03a,0xb0853825e03f0b0853821a03f0fd053820803f2ae098420203f0dc05a820203f5ca86e81f803f49085381f803f5c806e81d003f0b205381b003f4b8053819603f4a6853819603f4a4853819603f45f85a817003f08083f013203f082040412e03f08083f011a03f0b585a811a03f08c83500fc03f08082e00c803f1c28dec0ac03f10386e80ac03f08c81f809a03f06a01f408c03f2b1150070803f,0x128077429a04d126074429a04d050826411a0483a69cf0e6604830694cc9e404830594c89e204830414b89da0482170d7c65e048222108c64804821e9064634048110884040e0482178cc837404820d0c7037404816f874829c04808c83680fa046432074c2320454fe06482320444fd86541a80441ca840417004409883f011a04407402540900441af89843980442998da8390044145853825e03f,0xce85fc20204d1c20a181f804d1bf8a141f804d12705341a804d12605341a804d0ee853419e04d0a6846c12a04d08b835012a04d08083f011a04d07e832c11a04d06c835011004d083835010604d06a033c10604d08b83500f604d08383500f004d25c03500f004d06a033c0f004d12805340ac04d5dd0dd064804d5448db863404d12f88543f404d11587d43b804d12787743b604d69d0bc037404d,0x2a68e1c1ca0561c28d941b40566b0884c1b40560e985341b405613386c81a80561bd8a1c15805608b83c014c05608083881460560a6846c12a05607e03c011a05607e039411a05608f035010c056083835010605606a033c1060562b1950070a0561c28dec6ca0566ad885442605608b838811a05008f83640c805010706b40c805012f88383b80501bd085820204d179885820204d10386e820204d,0x52791443580644ca87f42d606449d07f42d606449787f42d606444987f42c20646a5084c1b406310a03a014806006582d011a06042d858823205a0a304781b405a67608701b405a10b06b418605909883f011a05908f033c10605908c83680c805910706b40c80596dab6c8426059697b4b03940592ac0e082020561bd08582020560e686e81f80561c38df41e00561c10dc41e00561c588541e0056,0x6ce365c438064536a97c4320641dd897c41c0646f4b7a040e0646eb083c40e06412108383dc06410a08383d606410a08383ce0644440aac3ba06413088383b806413088383a80641de097c398064130880c39606412f87b03960642c00da03940642be0da03940641d90da03940642d009103940642c4090439406412407b03920642c68da03900641df88383740641d887283740641d9872835a064,0x8b83f011a06407e02e011a06407e02d011a06407e025411a064845911011a06482c90f411a0648448bbc11a06482c0bb011a06485f881c11a06485f081c11a06449c05ac11a06408f033c1060644448774106064671337c8880645ba2dc887a06462db168648064588ac406340646560c4c5de0645ab0c3c5d80645318ebc4be0645340e9c4be0642bb0c1c4880646cc8f5c4840645360eb0482064,0x18183a011a07540a051c1b4070730051c1b2070120873037c070809052819606609884a02080640a7050020206484791101f806482e90f41f80646548bbc1f80645a98bb01f8064861888c1f80646ea081c1f806481707741f8064099045c1d00642b889141d00642b789041d0064260045c19e06410a03a016806408b838814606407e02e01320644c985ac13206449585ac13206409883f011a064,0x8c836812a086433874c2320834378a581b4083439874c1b40830a8046412008343c8acc2ae0837f286c41b40801810a1c15808014386b41580801f80df421607e1be8d981c807e42707701a807e6af8fc014a07e6778d9813c07e0b0836412e07e06d036411007e422858410e07e06d025410c07e08f836412a07b06c825411007b73a075c23e078431856023207843907743a207822089081c4075,0x2ec0bf051008d2db0bf051008d31b166049408d31a165048808d31215d848808d11f88f447008d84a088c43808d83c91103fe08d116078c3ba08d268091439408d2258efc35a08d1eb0a2035a08d0d406942f408d0da85ac2d408d49b09582ce08d7f207742ba08d42885542a808d7fc078429408d73707701a80882fb968ca800882080eec6bc0882098ef85ea088110086440e08810707c415c086,0x12284041ee08d12084041ee08d10384041ee08d0d684041ee08d2220dd01ee08d21e8db81ee08d22609201da08d18183f01d008d83d108c1d008d82490641d008d84b0f501b408d2ec0bf01b408d2db0bf01b408d84c08701b408d1eb06b41b408d812878c1b208d17e83a019608d17e0a2014608d14406b414608d0da840413208d0da85ac13208d82410f483208d8498fb45da08d8490f505da08d,0x631b1885de09558cac605d809510a08383a809544b07f42d409544b85a820208d12a85a820208d12a04041f808d0ff04041f808d31a8c601f808d3198c601f808d2220c4c1f808d21e8c3c1f808d1808a181f808d17d8a141f808d26809141f808d14309141f808d26c09041f808d14289041f808d11188341f808d10687341f808d17986b41f808d17806b41f808d0e686b41f808d0da85ac1f808d,0x31d94f048a099313147048a0992230d4448a0991b28bbc48a0992a00a1848a09931a14d4488099312146448809929e8a18488099832888c42609922409143fe09914308343880997f9074836a09931614a435a099315149835a0992200d1435a0991a50a1835a09922587fc35a0990da85ac2d40994cb06d42c209949806d42c20997fe07e829409980a858429409910706e817009507402e0142095]
def pgP5:Array Nat:=#[0x9203f817009d10707c415c09d39e952461a09d29f0db461a09d28e8da461209d2a00db441c09d1a5098441c09d2a0091441c09d29d892839409d1b2891439409d1ae872837409d494858429c09d0fd05282080990da85ac1f80990b205281b00991810a1c15809914386b41580998318d905de0998310d245de09928f0c0450c0994918b1c4ac09931b94e449409931b14e049409929d8a18494099,0x120888c3f40a326988343f40a314288343f40a311207d43ba0a326b88343b80a326c09043940a309884781d00a121a0cdc1d00a108083a01a80a13a71cf4e680a130d1500a020a130c94f8a000a130a94e89f80a130917cc9f00a130394b49d80a12168d7865c0a12178cc85ea0a12148ca85e60a12120c945e00a1110884040e0a12178cc83940a120d0c703940a126287482d40a149405381f809d,0x14386b41f80ac0e686b41f80ac8568d581d20ac8560d201b40ac2a00c081b40ac28f0c081b40ac857084c1b40ac85587941b40ac1a506b41b40ac8548d585ea0ac8540d205ea0ac2a00c0850e0ac28f0c0850e0ac855088c4260ac143883835a0ac10706e81700a612f88383f40a610687341f80a317986b41f80a317806b41f80a30e686b41f80a3189088c1c40a383591106480a381d10f46340a3,0x44a85a82020b80b505382020b83a1952061a0b82d08db461a0b82bd8da46120b8635b1985de0b858f2c705d80b82d18db441c0b82cb0db041c0b82c5097c41c0b81d4097c41c0b82d1890441c0b86d836b040e0b81e109043940b886f0e983740b81dd07283740b810a08383620b8101070c2ee0b846087f42d40b84c9058429c0b81b786b42720ae0dd04041860ae6d536a440e0ae10687341f80ac,0x82090f48320cb1b50c4c6020cb1b40c3c5f60cb63a108c5de0cb59290645d80cb8198f045d80cb31b96684940cb31197ec48a0cb21c898448a0cb31918384820cb21a897c4820cb122888c4020cb12c857c19e0c612c057c19e0c613089141a80c512f89041a80c5409851c1b20c040a051c1ae0c01bd86b42800b86590dd02020b85ad8db82020b86ec88542020b86ed881c2020b852907702020b8,0x13088544020d425b09a02ae0d425b8ad028c0d442e05181b40cf43d876c29a0cf0af851819e0cd80505282420cb80405282420cb80385282420cb809852820e0cb2208bf81f80cb31589201f80cb17789141f80cb31889081f80cb31489081f80cb31389081f80cb22089081f80cb17609041f80cb11188341f80cb10386b41f80cb2260c101da0cb21189141d00cb20c89041d00cb83911108460cb,0x2b18e142020d42ab0e142020d42b10e102020d42ac0e082020d42b08e002020d42a98e002020d42b00dfc2020d41c28dec2020d41c18dc82020d42ae09842020d42aa89842020d42a609842020d41ba09842020d42a9097c2020d41b7097c2020d41bf08582020d41bb86e82020d410a86e82020d412b85601b40d412b85181b40d45fa908c6e80d455c90646dc0d41c68e106d40d41c40dfc6d00d4,0x2d00e104400d92ce8e104400d92d40da84400d92d38da84400d92c30da84400d92c28da84400d92c20da84400d92be8c044400d92cf09844400d92d109144400d911008704320d92070ee44280d92020eac3740d92098ef835a0d92058ecc35a0d91ff0e9035a0d942187582ba0d90eb85602ae0d943d0a8429a0d90f184641b20d84a705382480d44a505382480d44a385382480d44b7853821c0d4,0x4310a7423e0da432074c23e0da08f046422e0da2ec0e002000da2e18e002000da0dd06b42000da84a8f501f60da0dd06b41f60da2a00e141e00da2970e141e00da1c28d281e00da0dd06b41da0da1f28d681d20da07983a41d00da1f28d684280da512084c3c60da08f847822e0d92070ee41e80d969d86e81e00d907a03cc1d00d90fa85dc1c40d908f84641b40d907a03a41b40d90ac05181b40d9,0x2b08e002020e52a98e002020e51c28dec2020e51c18dc82020e51bf08582020e51bb86e82020e510a86e82020e520a8e1c6fa0e52a68e1c3dc0e52208bf81f80e231589201f80e231489081f80e210386b41f80e22260c101da0e284b8fb41d20e22208f5c4840e226b08343ee0e252387d43ba0e217608343740e217a86e835a0e217686e835a0e20d0065c2f00e231d1858a140e0297098441c0db,0x8360c901f00e881d8c681f00e82b889141f00e82b789041f00e871d06e81e00e830997409f20e830817c49ec0e821a0fc066e0e82100f5c6420e820e900063c0e830b93f84900e830c13fc4840e82158cb04280e811088704200e82180ccc3740e82160cb43740e82130c9c3740e82108c883740e820d0c703740e82178cc835a0e82140ca435a0e820d0c7035a0e82b18e142020e52ab0e142020e5,0x2178cc83740f32160cb43740f32130c9c3740f32108c883740f320d0c703740f32140ca435a0f31c18dc82020f01bf08582020f01bb86e82020f010a86e82020f01d30e086e20f069e88544260f01ba885835a0f010386b41f80ed2260d984900ed852088c4260ed6db084c40e0ed2260c103740ed17986e835a0ed0dd06b41e00ea21a0cdc2640e85c606b42620e85e00c901fa0e85458c681fa0e8,0x7f606d42c20fc4c806d429c0fc48b86d429c0fc7fdbfe82940fc4d5a6a82940fc4d705382940fc80705281f80f94dc05281f80f90da85382020f71c186b41f80f72f41608a460f411008644260f42020eac3740f42058ecc35a0f471686e82620f3307964c9ea0f3301148c9d20f320e8e9863c0f330b93f84900f330a13e84900f330c13fc4840f32fe13844840f3110884c4200f32180ccc3740f3,0x21a897c4820fc852888c4380fc81a088c4320fc224885041a0fc6e5b72840e0fc6ce887040e0fc83991103fe0fc122888c3fe0fc26a88343d60fc120888c3ce0fc26908343ca0fc26788343b80fc26a08343a80fc2208bf83740fc17788343740fc10787343740fc10687343740fc316161c35a0fc315161035a0fc2200e9435a0fc1d40a1435a0fc17a86e835a0fc17806e835a0fc17686e835a0fc,0x82110f46340fc1b50c4c6020fc1b40c3c5f60fc64ab2485de0fc62e0c905de0fc5a1ad005d80fc8190e9c5d80fc5890c685d80fc22d8b905700fc1c20c0450c0fc2be0bec50a0fc1bf8bec50a0fc2ce8a144940fc311938048a0fc21c898448a0fc2d00a144880fc2208fc04840fc31d96784820fc31315e44820fc31913d04820fc2240ee04820fc2230ebc4820fc1e10bb04820fc2d18a144820fc,0x1898a0c48a1011878a084821016a4887042a101538086442a1011bd08584281016020dd03fe10113088543fe10112f88543ce1011d28dc0374101179885835a101107872c35a10144c86e02c21014ad06e02020fe4b105382020fe4ae85382020fe4ae05382020fe4ac05382020fe65309142020fc13089142020fc5a809042020fc12f89042020fc6e906b42020fc0dd06b42020fc0a705282020fc,0xd306302f411742d13002c41174330a8823e10741205702321070fd05282841040b0853821a1040fd078429c1044dc87e82941044d807e829410464c8bbc2801015a40bb02801016e7081c2801012d195806fe1012c30dfc6f41012c38dfc6f21011c68e106d41011c40dfc6d01015618db86341012c515484be1011dc0de44be1011d78dd84be1011de0db84be1011d40db84be1011e08bb04be101,0x20a8f0062c11f2000e9862011f110086442e11f110086442611f2098ef841c11f2020eac41c11f2010ea041c11f6f188383da11f20b8f0839411f2058ecc39411f1ff0e9037411f2010ea035a11f73807582aa11f10e085c4261191ec8d3841c119503a8184181191eb0d2835a11942806c42aa1197390aa023e117739875c23e1176cd0fc04841176d210003741172f80c303741172e80c1835a117,0x5c18d244c21316d98d984901315c48d3c48a13128c8c1c4881315c72e2c4261311af098441c13145f07f43a41312a28da83941312908da839413128f0da83941311b50d50394131296091439413129e8910394131872905437413110707fc3741311a987283741311aa872835a13148105842941314cd07e829c1282f61620a5811f2f315f0a3c11f20b8f086ca11f2050ec86a811f2028eb069e11f,0x110885c420132110884c4201322178cc841c1322108c8841c13220f8c8041c13272c08383e01326d708383ce13217087e83a41322198cd83941322180ccc3941322178cc83941322160cb43941322140ca43941322130c9c39413220d0c703941322178cc837413220d0c7037413220f8c8035a13216e874829c132169074829c13216a87482941320b085282841315c38d904c21315be0d444c2131,0x30314b09d613230214a09d4132301148c9d213230094809d0132300147c9cc1322ff94789ca1322ff14749c813221a0d9866e1322198d9466c1322190d5866a132218905466813221490306541322140d546521322138d50650132212101c64a1322118e346481322110d3c64613220f8d2864013220f0d2063e13220c8e206341322188cd062c13220e8c7862013230a13e84901322fe1384484132,0x64c0e345de1405a38e205d81406e6885c40e1403a61cece6413230e951ca0c13230e1510a0813230d950ca0613230894dc9ee13230797c09ea132,0x51898fc1b200d003a8444720d9006801d818be5074002c00ec0a5f103a00160075642aac1d000b003a4f42ce037005801d902c7f63e111071ab325982cb887a3886c0b6008263be17ab93dc9c42f1990bd5922c902118c905ded1868b8ff87482ed71bb8d883431c176acfd67c41918d0bb1b80dbf6df088c42eec276088804322076e4b720438213103bc51e26221108081d71ab7a1a28838374d7c6bd112841c1ad68ab44c87c1ba0d6a6a134e9a60fd05392d696a4b486d429c9a24d0a67c29c14a,0x15105982b004d006a5dd27c2c509400313162c70b384a001891d48c03f012e00c48523dc26206400623311444c4099002d2f29720e904c801616109904a020800b0b084c82080d8005a53d2900b804a802d31897803200dc01693749a019006e00b41f20f003e00e005b9a5cd002b006802d1be8b7099003001616409904a001800b0b084c825000c0058584264097006002d38e9c616c87480162ab134893c1a800712283f017008d00389041f80b8046801c35a0fc05c023400e9e14ea070c0c8007,0xdd040415c05901885b81ca0a602800c536c9b307c80fc06226106a02e006e031130840412a037018897c20209501b80c439410104a80dc06214e080825406e031130835012a03701885381a809501b80c5cc4e5d0a983640569ee4f683f01b401f40b201c2a20da00fa04900e15406b8068ff07f70aa035c03433f1980c6423200e1d10e604260da0070cf067021306d003867e33118d847c01a3c81e308801b200d1e60e684400d9006a044ff615306c80350087f70a9836401a2a5127856009a00d,0x1b28d1842a101018885c42a1ca08080c49a625f08083f00622070dd04041da031176097c1f80d40188f3879821606a00c50948470ee03500624d413083501960310e504c420209d018853826210104e80c53b82eb07e02340622ef07e035011a0310b3035019608d018b28cea073e04680c44c210105c019006225f08082e00c80310dd040417006401885382020b803200c44c20d405c019006225f06a02e00c80310a70350170064018a75c4e80b803200c429c0d405a01800621ba08082e00b2031,0x176097c2020cb026859820e0d4041813439410105c019009a25f07282980a004d40ea06c20e07d0230730394131046811029413107e02340883651a3085420203f411a08420e0d401fa5592a60fe04680fc4c210105c019007e14e08082e00c803f0b0853820805d01fbffd2880fe07e00e848a0fc04a823406e24107e025411a0370e603f012a08d01b85281f809504680dc48a0cb04a823406e14a065825411a037130840417004d01b897c2020b802680dc5c21680a704c80623f91fb0858202031,0x121045c1c40a303209081f80b805181902f40fc05c028c0c81cc0e502e01460640a503f0170099032090822e0fc046819048a0fc05c02340c824107e02e011a0640d683f017008d03240784d80b804681904840fc05302340c817b065825411a06450a867c30017803205281960b4046818049013107682340b21ad07e02b811a05910386e81f80f002b06e81e00b803201584820e2053028c0a017a071029811a05010b885439410102692e04d426406a01350ba4c106a033c09a2ef130840419604d,0x16c8b382d60fc04c876037a1b206a02544ca1660af835012a26312585181a809517085a4294132046a7585d410107e02347903c611083f011a22310787301f808d4eda7643860fc046a7553a61c307e02343081830bc83f011a9744b9894c19608d49fa4d44a60cb046bf9dfcc1dd06582345ba16a0a5028411a2ce0fc85ac13208d404201428e0bd0381ff0ff214705e81c13be9da0e1845c0c89dd13a84041700640a705282020b803240804de0fc05c019029c14a07e02e00c874f1e20850170064,0x270829c14a08083f08dc46d0bb03f01c485442386c42320da1fe0e7c4380e906d39c5cd81d608f83647603a01cf03d01b216108f84641b40d916c05ac29c13206a0df839a1ad08082e044620f0e603f014635b1a3888c1f8099,0xb5058429c13201f802d1a08a5264812007400b462a26c99004801d002d1c88bb16f812007400b4cca6443f8132018802d3824c70b504c806200b26189702d4132018802c98825a0b504c806200b5c42e10394101018802c99225d0b5012006200b7c0077c3a0132006802d9f4cf911088403c000b5bcade04422100e6002d3ce1820bc85d82020076410a184c20fc05c001d8f228613083f01700075998a144be0fc05c001db821cd0dd03f017000710106842ec0fc05c001d2c095f0a703f01700074cc05ac29c0fc05c001d8ac4d4130832c17000750027fc2f60d4032001db4024210706d00c8007,0x6b435949a40fc065802d726b9217783f019600b729b94840e0fc065802dc8ce450e683f019600b42009e84820e805e802dd921c60d683a017a00b80a059029413204c802d18e89d266828412e00b46a22a45ba0a104b802e0310160fe04c811a00b80b8b48294132046802da00cfd26883f011a00b843420450c0fc046802e10b08014303f011a00b82ac14050a0fc046802e0a904f14283f011a00b87743a839a0fc046802e0c30600e603f011a00b863b4349aa0a3046802da0cd03176828c11a00b874395839a0a3046802dca2e500e6828c11a00b4cf13202d608d024002d2ea1640a704c807e00b,0x151893829a0d9026803454024c0a6836409a00d4f5061430204d0158035cbe1540a9836403400d804859029412804c803133a99c0b583f013200c48f24682c209904b80312981640a704a007e00c12d85a82d010401f803137e9bd0b500fc06200c4e60b603a416b099002d1b48b226384c825000b4d2a690988132094002d19c8a426184c825000b470a2e05b0132094002d1a48a716b84c825000b46e22d05aa132094002d19289f16904c825000b472a2f43f8132094002dbda1c60e183cc1b400b78d89ec4f20e806c802de381c60e283a01b200b46b22b05c413206c002c5b016b0a504c819600b,0x73f8a8c36015208f80350d62a614a847c23200d4368a9052011f08c80350dc1d70e9847c23200d4348a8c2a011f08c803549022d11488a020200d81608c045e22c07e00350821c50e183d01d200d6d2b68840e0fc0710035ab4d590e683f01c400d73b87603ae11706c8035cea2a20af845c1b200d4408a882cc10706c80353d81850bc03881b200d735071435a0d905e8035cc21530a3836417a00d873438439a0fc05180361bedb40e6828c11a00d6cdb66039a0a304680350ee87515003640f000d73f39f03ae0d903c0035cec2ab15283640a000d4f206142ee0d90280035cf01d70d9036409a00d,0x4a8249429c12801f80c51d01610a7041007e031673b39839a0fc07100ad9e0cee17683b414602b87036e040e0ed05180adac0d5d17a82b013202b86d05982c20d903a80ad09e1660b081f806202211d06a42bc0500188089fd01660b0836810001f401854c2a20da015807d02e1540a3835c0e001a535299c3940a10268059cde1660b082200620164460a3c3a215008c80390f01d80e984781b400e421070c35a0da060003902a1510a3836818000e85e42e039a0fc05600391168860e9836810600e43e074c3640da02b003852a2500a683680ac00e127054029a0da02b00390201540a8836804a00e,0x55e897c48210107e00c5aac1ba0d684041f80316a386e835a10107e00c530a14e0a504041f803147d853829410107e00c54a246c0dc86841f803171db8e437410107400c540a23a11c03941c403150505f82f40e507100c47983921c50c1c1a8031600898448a0d406580c531a14e0a503501960314bf05382940d406580c51dc14e0a5035019603142aa1482cc0d404a80c4ac22fc144040411a0312b10a1848a10104680c4ac0285120840411a0315c5073039410104680c448a1cc0e5040411a03165a32c05de0fc04680c56bab5a17603f011a0316ed376040e0fc04680c47603921c50c1c09a031,0x5752a304be0e803200dd890bdd12283a00c80376232f6c48a0e803200dddf0ecf12103a00c803777bbb384840e803200dddececd12103a00c80375802a984820e803200dd5fcaa412083a00c8037783bb784280e803200dde0cedd10a03a00c8037782bb704280e803200dde06eda10a03a00c8037786bb9c3740e803200dde10edf0dd03a00c803777d3b443740e803200dde16ee30d683a00c80377853b8835a0e803200ddd94e380d683a00c80374830b842c814a03200dd81a26112284041f80315fd898448a10107e00c57e426112284041f8031564897c48210107e00c558225f12084041f8031,0x86a35e05ea0e20400121c90e4717a82b01000486b735ac5ea0ac04001220630300e6028c0ea048485853829410107e00fd2ba95b0a702e00c803f80025142c210404c80e98ee2ef130845c1960375940bb04be11706580dd09a84c42406f012a0377f53fa42cc0cb04680dd4c8a620e604c80c80376202f386d40e803200dd87cbcc1b503a00c803761e2f2c6d40e803200dd874bc91b503a00c803757c2a646d00e803200dd5eca971b403a00c803757a2a586d00e803200dd8a6bed13083a00c80376212f404c20e803200dd614ab312f83a00c80375842ac04be0e803200dd5f4a9b12f83a00c8037,0x758ba384280d90320141d76e9b0dd03640c805075b3a4c3740d90320141d54e870dd03640c805075cba5c35a0d90320141d70e960d683640c805074234d835a0d90320141484a2b0be83640c805055b097c4820e50710135a78d380dd04041b204d44006dc2cc15f06a01350ae24b0db85181a804d5358730394101051813504a1450a203500fa04d4368abc4960d403c01351241db0d903500f004d415a0a828a0d403c0135c54e290e683f019604816f86d42d61320468121c58e2b17683b411a048874b95c40e0ed0468122190d10176838811a048537a9b85d80e204681221a6d7526b0388100048,0x722390c4fa13208f0165d64e8f10a04c41e8059756ba2837413107a0165e08edb10a04781e605977fbb5837411e0798165b742070dd04781da059765b90037411e0740165d0ad4c0dd04c41b20596c3b4744280da0320165b0ad1b10a03680c80596c1b4684280da0320165b2ad330dd03680c80596c4b47c3740da0320165b1ed2a0d683680c80596c6b4a035a0da032016470a30214384041f80563188e1c4840fc07281590508270a2033c0fa0525792a4c6d0117074014145e64031f064c1b205011c06a82bc0a60468141d6ae9210a03640c805075a3a444280d90320141d66e9010a03640c8050,0x5ac2d505d824107e0235baedd510386b41f808d867c33835a0fc0740235406a020bd835019608d805c00c29412804c8235ff21610a5041013208d806c01429409904b82350ac1d80d8051822e06448623e82941310820191b4e2070dd045c1f806465a8a184c210105c01916bc28512f8404170064636933c4c20fc05c01918be2ef13083f0170064590135c4be0fc05c019161a4d312f83f017006458a8bb04be0fc05c019165428512f83f017006449724b429c0fc05c019112288f0ec033c12a06443621a428c0cf04a81910fe1d80e8857c12a064483a3cc29413006c0181aa6d5213e84c423e059,0x77ebb504901170740299df2ed0121045c1d00a652028a44040d905c0299d60e8d0dd03641700a67573a2c3740d905c0299d6ee940d683641700a6757ba3035a0d905c029a1470a20d683f01b20a3806401029410407e02658a2bea13083a017009561c2f1c4c20e805c0255868bc313083a01700956192f044c20e805c02555e0a9212f83a01700955762a384be0e805c0255886bd612283a017009561b2f1448a0e805c02555f6a9f12083a01700955772a404820e805c0255e04ed90dd03a01700957803b5c3740e805c0255e12ee00d683a0170095780bb6035a0e805c025595ecaa17789141f808d,0x78c3c5c44221010704c9caae54110884041c132530a9804422100e604c9d8cec5110086441c11f6d7b6b4440219107047dbc8de210e084c41c11977f3b5449013108b83a1b3ed9e11088403680e867d934441a1e007e03890968460b084782320da736b9ac2c211f08b8365aa0d4e0dd04041ca0d9853c29835a0fc0710365c84e410dd04041d00d4868c34035a0fc074032d1ce1610a704c42080b86bfb4583740da05c02b9af6d120dd03681700ae6c5348c35a0da05c02b9afad140d683681700ae,0x445220d1041dd0a8036801c7f53fa05240ac03100f80394aca550cb06402320d9006b9f5cf4e7915187741b200d7623b0c4402190d6836401aa4d52587d43c617606c80350fc87d42c0a882be0d9006b969cb214802680c405600d3f99fc829402b00f803801a96449005a829c104080803201f0010b585282080fc006240d1e48f00b205281b000c47a23c51de2cf0b084c0016ca2650108c648245074002d69eb4d20c8c684820e8005bc59e2a22110806b41d000b4a8a52c5b816105a0254016ec8763851c09a048018802dbd8deb0a5812003e00e005bc69e3214c02400ac01a00b4e7273535a16b0a5019000ed5569688383740da0038019d4ee9810706e81b2007002bbcddc820e0dd03a000e003,0x447223449c1db0de85341a8b3b59a8db84be10107e0235918c851ba0a184c20fc046b719b862150e686e81f808d52829388d81a10bb03f011a93349907842d414e05c019110a88344105982be095032408603e1c307e02e011a06451fa89c8b045606c81900a0a45519115c8aa0d9032014148ca3411308941b206402828514241780bb83640c80504b3a58c2d414e07e023407e9e24f0080c2020fc04680c53bc9d80e20404170064018b745ba021c10986b41b400e,0x7e7bda894848e074036401a00b7dbbd5094648d074036401a00b7cc3cd494448c074036401a00b7ee3ddc94248b074036401a00b7e53d9494048a074036401a00b7da3d4493e489074036401a00b7ca3cc493c488074036401a00b7f1bdf846c234074036401a00b7e4bd90e326d1050822001a00b7e83dace286cc050822001a00b7df3d64e226c9050822001a00b7d33d0ce106c0050822001a00b7c43c94e0e6bf050822001a00b7e8bdb0950492050822001a00b7d23d04f987ae02400ac01a00b7c33c8cf967ad02400ac01a00b7c93cbcf887a702400ac01a00b7d03cf4f867a602400ac01a00b7e73da4e186c402400ac01a00b7d6bd28e146c202400ac01a00b7c9bcc0e126c102400ac01a00b7f13df495249302400ac01a00b52d29654b019c08c83680c8007668b34199acca10a08380c8007,0x7ddbd58e1e6c7074036401a00b7e1bd78e0c6be074036401a00b7ce3ce4e066bb074036401a00b7cbbcd0e046ba074036401a00b7edbdd8e026b9074036401a00b7c8bcb8e006b8074036401a00b7c3bc90dfc6b6074036401a00b7debd60dfa6b5074036401a00b7f03decdf86b4074036401a00b7dc3d54df66b3074036401a00b7d7bd30df46b2074036401a00b7eebde0df06b0074036401a00b7dabd48dee6af074036401a00b7e5bd98dec6ae074036401a00b7e6bda0de86ac074036401a00b7e3bd88de46aa074036401a00b7c6bca8de26a9074036401a00b7e33d84dde6a7074036401a00b7d9bd40ddc6a6074036401a00b7cabcc8dda6a5074036401a00b7c23c84dd66a3074036401a00b7de3d5c94e491074036401a00b7cebce894c490074036401a00b7efbde894a48f074036401a00b,0x7d2bd08dfe6b7099047c01a00b7d4bd18de66ab099047c01a00b7d13cfcdd86a4099047c01a00b7cfbcf0dd46a2099047c01a00b7d73d2c954494099047c01a00b7c5bca0fe07ef074036401a00b7d53d1cfa47b4074036401a00b7cd3cdcfa27b3074036401a00b7e03d6cf947ac074036401a00b7d93d3cf927ab074036401a00b7e43d8cf8e7aa074036401a00b7c4bc98f8c7a9074036401a00b7c13c7cf847a5074036401a00b7c63ca4f7e7a2074036401a00b7cb3cccf7c7a1074036401a00b7cdbce0f7a7a0074036401a00b7ed3dd4f7879f074036401a00b7c7bcb0f7679e074036401a00b7c2bc88f7279c074036401a00b7eb3dc4e3a6d5074036401a00b7dfbd68e386d4074036401a00b7cf3cece306d0074036401a00b7ccbcd8e2e6cf074036401a00b7f0bdf0e206c8074036401a00b,0x70d37f4e6065d079836801c00b7133820e58659079836801c00b705b7b8e52656079836801c00b70fb808e4e654079836801c00b712b81ce4c653079836801c00b7113810e4a652079836801c00b709b7d8e46650079836801c00b707b7c8e4464f079836801c00b70737c4e4264e079836801c00b7123818960475079836801c00b70ab7e095e474079836801c00b710380c95c473079836801c00b70937d495a472079836801c00b714382846e232079836801c00b708b7d0e5c65b05081f801c00b70b37e4e5a65a05081f801c00b70bb7e896247605081f801c00b70a37dce56658024007c01c00b713b824964477024007c01c00b7d63d24f8a7a8099047c01a00b7d43d14f807a3099047c01a00b7d1bd00f7479d099047c01a00b7d83d34e1c6c6099047c01a00b7d5bd20e086bc099047c01a00b,0x71fb8f9c7ae3c11088401d000b663b319986cc011088401d000b77e3bc1dd6ed307402e012a00b877c3b61d90eb07e03a011a00b843c21210708207e03a011a00b82b414e0a505107e03a011a00b866c32e1950c9074028c11a00b718b8c1c5ee2e08f03a00b200b7873bd5ddaee8074019006e00b7863bd1dd8ee6074019006e00b77dbbbddd4ed2074019006e00b62a303d7f8bef074019006e00b62730397f6be8074019006e00b62630217f0be0074019006e00b585ab2d57cab5074019006e00b582ab2957aaae074019006e00b4c7a62530c97f0fe018006e00b4c726112fa2d80a5018006e00b7893c45e20f0f08083a006200b63c31b18c8c6008083a006200b594ac7d634b1608083a006200b71ab8d1c66e32074013406200b70837ccfaa754079836801c00b70f3804fa6752079836801c00b,0x6572d5cdd069c07a03a401c00d670adccdc868f07a03a401c00d63eacb4dc268107a03a401c00d65ead94dbe67c07a03a401c00d6702dc4dbc67707a03a401c00d66d2dacdba67007a03a401c00d649ad04db666907a03a401c00d6432cd8db466707a03a401c00d641acccdb266407a03a401c00d66eadb893448007a03a401c00d64b2d1093247f07a03a401c00d65fad9c93047c07a03a401c00d6472cf092e47b07a03a401c00d672addc46a23307a03a401c00d645ace8dcc69804401f801c00d64bad18dca69304401f801c00d64d2d2493648304401f801c00d64a2d08dc6689015807c01c00d671add4938484015807c01c00d4e5a7293909400fd05ac20800c808c04200d00208203f013200c486a4112008fc09884100c800c4b625a1262922082040407e00c5c0adfd6fab7b0e604c41d000b,0x5ebaf4579ebc7080825406e0315d2ae8d740b9b080825406e0315502a71534a92080825406e03185942c61610af08f82b013202b7ec3dcce166c307a03cc09002b726b931c96e4a09902840ac02270e37fce5465707483a009001f659ad70dc468806d036405601f85ec2ee1750b907e036815800e6cb3561a90d3506d01900b200e6c9355da8ed3006d01900b200e6ddb6c5b56da808083680ac00e6a2b511a82d3f11008641b200d7563a91d3ee8906c82e014c00d873c3921c70e207e036414600d84e426e13509906c828c11a00d67c33dd9eccf409883640b200d75e3aa5d42e9c06c81900a000d75d3aa1d40e9a06c81900a000d755ba8dd3ce8806c81900a000d7603afdd7cebd080836409a00d688b42da12d0706c813406200d644acdcf6e77c07a03a401c00d65d2d8cf6a76707a03a401c00d,0x82fadd96deb6708083f011a0318272c25608aff08083f011a031823ab895c0add08083f011a0318202ad155eaa608083f011a03181caa1d50aa8208083f011a03180ea74939e9c408083f011a0317f8a2f11728b408083f011a03151e28e4c9264208083f011a031519a8ac8d445908083f011a03152f295045c22708083f011a0316ee373db98dc708082e00c803165bb26d92cc8d08082e00c8031621b10587ec3708082e00c803160f306d832c1308082e00c80315b02d2968ab3c08082e00c803157dabe55eeaef08082e00c803156d2b615acacf08082e00c803153fa9f54f6a7408082e00c80314d926bd3589a308082e00c8031456a2a915089f08082e00c803151c28d8c8e64508082e00c8031529a92445622a08082e00c80316923481a3cd1608082b80b203151528a08c045e08082980a0031,0x812408cc9863d07e0298146050813c0988e044f07e029811a0507513a75d0cd6308f83640c80505112870c9464408083f014604d52229048d645c08083f014604d52028f88ca45d08082e00c804d50da860c9064608082980a004d86cc35e1ad0d509902b01000487fb3fd5fe8ff309883f013204446b234d1a28c8098840413a03f7fba38d1c08db08083f013203f6bcb5cdae2d6f08f82200ac03f83841be0dd06d07e025411a037834c1a20cf06607e025411a03781fc0fa07b03c07e025411a0377773ba5d98e4909903a00c80374fb27d53e81820bc04041f8031862b7a9bcede108083f011a031850b4d1a62d2a08083f011a031848b3919bacbe08083f011a03183fb14989ac4708083f011a03183c30a584cc2208083f011a031838afb97d2bdd08083f011a0318352ee1766bab08083f011a031,0x65b2d7c93a48707a03a41b40d94a1250527893b0da85a81f808d7d0bcf8f9c7b007a03cc142088430a17d0b28580ee851819e07841da0e907283508f04641b4064733b999ccae6408f845c1b206485b42d61690b307e02e0158064815c0a88de45307e02e0146064862430a1830c007e02e011a064848423a11b08c07e02e011a06483f41f60f907b07e02e011a06483bc1da0eb07407e02e011a06482f41720b705a07e02e011a064826c13209704a07e02e011a064823411608904307e02e011a06481c40de06d03507e02e011a06480e406e03501907e02e011a0647f83fbdfdcfed07e02e011a064814c0a0c9663c07e02e011a064817c0b446222407e02e011a064850427e13d09d07e02b811a05985bb651b22d8e08083f01580566c53621b0cd7e08082e00c8056581ab15574aa7099045c1d0050,0x70eb80096647807983a41d00da7c73cacfa07b207a03cc1d00d97c83cb4f9e7b107a03cc1d00d97c1bc80f9a7af07a03cc1d00d97ea3dbcf827a407a03cc1d00d97ef3de4e406d807a03cc1d00d97db3d4ce3e6d707a03cc1d00d97e2bd80e366d307a03cc1d00d97e23d7ce366d307a03cc1d00d97bfbc74e2c6ce07a03cc1d00d97d3bd10e2a6cd07a03cc1d00d97c53c9ce266cb07a03cc1d00d97e9bdb8e1a6c507a03cc1d00d97ebbdc8e0a6bd07a03cc1d00d97e93db4df26b107a03cc1d00d97eabdc0dea6ad07a03cc1d00d97ecbdd095849607a03cc1d00d9731a0c505e82e08f84641b40d96542d44f6c77207a03a41b40d966dadb0dd26a107a03a41b40d96402cc4dce69a07a03a41b40d963f2cbcdce69a07a03a41b40d9658ad64dc068007a03a41b40d9655ad54db866a07a03a41b40d9,0x7e63d9ce3c6d6099047c1e80f37d8bd38e346d2099047c1e80f37c0bc78e246ca099047c1e80f37e0bd70de06a8099047c1e80f37e13d74956495099047c1e80f370c37ecfa875307983a41d00da711b814e6265e07983a41d00da706b7c0e5e65c07983a41d00da70637bce5e65c07983a41d00da70db7f8e5065507983a41d00da70cb7f0e4865107983a41d00da]
def pgPL (i:Nat):Nat:=(if i<192 then (if i<64 then pgP0.getD (i-0) 0 else (if i<128 then pgP1.getD (i-64) 0 else pgP2.getD (i-128) 0)) else (if i<256 then pgP3.getD (i-192) 0 else (if i<320 then pgP4.getD (i-256) 0 else pgP5.getD (i-320) 0)))
def packetBody (i:Nat):List Nat:=packetUnpack (if i<8159 then (if i<2045 then (if i<439 then 1 else 2) else (if i<6734 then 3 else 4)) else (if i<8646 then (if i<8338 then 5 else 6) else (if i<8686 then 7 else 8))) (if i<8159 then (if i<2045 then (if i<439 then packetField (pgPL (0+(i-0)/24)) 13 ((i-0)%24) else packetField (pgPL (19+(i-439)/24)) 26 ((i-439)%24)) else (if i<6734 then packetField (pgPL (86+(i-2045)/24)) 39 ((i-2045)%24) else packetField (pgPL (282+(i-6734)/24)) 52 ((i-6734)%24))) else (if i<8646 then (if i<8338 then packetField (pgPL (342+(i-8159)/24)) 65 ((i-8159)%24) else packetField (pgPL (350+(i-8338)/24)) 78 ((i-8338)%24)) else (if i<8686 then packetField (pgPL (363+(i-8646)/24)) 91 ((i-8646)%24) else packetField (pgPL (365+(i-8686)/24)) 104 ((i-8686)%24))))
def pgR0:Array Nat:=#[0x1c0b,0x1ea27aa1e9f,0x1a3064314ac5ac0644544,0x1090ed71090e271090003166042403f00fe,0x10905961090c53109016734b04240594003,0x109046c2b08e29109046c05a442411b00fe,0x109046c1090d2e109046c05d042411b0165,0x87321d6872a1dc872e1d5,0x14e046e11b84c4131054c,0x37a8c6a11b0d3512fcbd04b7c19a067019d,0x18fcee011b0e3212fcbd018fc16411b04bf,0x64053914e457e15f8539153454d158054d,0x14e447111c44c5131454d,0x14e457e14e454d158054d05e565003f00fe,0x3a3cde214d4bdd1574535,0x3a4463f3a34e2b066854934d04750670475,0x14e453715b853734a856e,0x14e4edf14e46f714e40fc05e45391524d2a,0x6fcdc1b6fc9bfd6fdc1cf81d6018001c008,0x3a4463f14dcd3512fc4bf18fc53703f04bf,0x5e4560158047111c447113144c5131457e,0x14e447111c44c5131454d,0x158047111c44c5131457e06401645978165,0x11c446c157846c34a855e,0x3a4047111c46f70590471064047511c4d2a,0x31a8e920670d352f3c55e37a853614d819d,0x15f8d332f546e515f81650640e8e1578de9,0x7031b976e19bdb0741bc881d80078040009,0x14e4c7214e46c714e419c1534560315854d,0x37ac640066847111c447113144c5131457e,0x14dc537585053703f06c814dc6c303f86c3,0x11b15dd11b016411b06c818f846c059463e,0x7911e456e0c1bd7035c1c001e0198044002,0x158047111c4640389857e190056015f819d,0x6f9d636ea1d646f75bf80024002807201a,0x83fa0e2835a0f883ca0ff,0x5e141585c5,0x17152e005f05c51b506d4,0x17145c54c445c505b817a,0x5c541585e1,0x6650564c40647191c5e1,0x1784647178416d1784196,0x813a052729c00d72b1cc7,0x192864a1b6864b05c017219180004c38000,0x1819602177c5f4443c5c3,0x17d118817d017b446c17c580c5c3177c719,0x17d131217d1604170d31305ec5f405c81dd,0x17d12f4170c606443c5df,0x44d01970664606443d1824bd45c319705df,0x4c1060618192f619705df065c17018181dc,0x85661708571f724db5768,0x18e46d917506d9182c1b1,0x18e46d917886d917719dc1b64639067019d,0x18e46d917506d9182c1af1b6462106b56a5,0x18e85ff1b486211b4d77f,0x18086d917886d9188577f581c63906701ad,0x18286d217486d918286f5,0x18746d318806d21825659,0x180c61e1bd463a1b486d3,0x18746d217646d948786f558201785a881ad,0x18e46d2182c6d917506f5,0x18086d117746d2182c6e7,0x18e46d2182c6d318646f5,0x582463906b86d25a8c60b1b6419d48706f5]
def pgR1:Array Nat:=#[0x18746d217646d9676c6f51b641781bd419d,0x18e46d2182c6d94b286f51b641ae1bd41ad,0x58456118b616118b662e4,0xfec46c0f64e250fe846c05903fb2b080f8,0xfe84170fe84120fe0ab1,0xfec46c315055528a8ab22d603fb2b04165,0x7d9b8107ddbc607e1b7700601f68006002,0x3c693e73f50ea037299e537d8e895da99b5,0x5e2952f454538339ec20d4dfce6b4918ca9,0x5a110a042811c847210a04c613184292f4c63f1c9842811c84c6,0x5fa1ca05f415fc5cc15fc54e172454e1d0025f17e824203f00fe05e45fa03e4243091c888,0xff682f563e090c243090ce4242f4e420921d6265e1aa500d4037,0x186d5738fa15738fa1831420e091824609180353c9daa66d6802a,0x3fba0bc58d60e35ec20c483e5883831a0ea,0x7011c0e7015bfb700deb37065bf17a95ea0,0x68c159069815f852b194865e3c34566196868c066469819e065a,0x68c1590e8315f86781bd468c05a4e9d1bd466139dc16a195d34a,0x1c52703dc483b853bf5ad5d77702000e678dd86707c02b7a359b2,0x68c158c69815f852b193c550155466f1bd468c066416a1bd419d,0x161052e193c54b4d1867816705aa15f854b,0x68c4ffc169158c6981a6057e19e06f5193c550197065c19bc6f5,0x1c52703dc483b893c05ad8e5b4dbc1e55ada07980e000f5ad803f,0x68c07b4fd316b0f81061057e14ac1e3151055015557693a6c6f5,0x55716b05571600e841511345155c65a196868c155c1841bd465a,0x68c155016a15f864f3a153454d18e774d1c68c51f858d585c198,0x143c50f1c063a7d3aa5ad937e0791d6d75bd43c003e1485ad8013,0x557158c55715f8678193c550155c6981bd465d155c6981bd419d,0x70b5bf175a9c0375b1d6e7149c837061bfa,0x13e550ec00a7614f17011d2e3760dd6b7e0538175c9d7d7df1ea0,0x19785643a0c54d14a856715f852a150d659,0x68c158c69815f852b193c65d15546981bd468c155469859c01ad,0x143c50f01ef4bb4dd075ad38939e5d7d7a8143c00cc013823608f,0x80ca147844e10383f21bb840210286f208b,0x1cdf4ac92b206f01bc597c1e1078404006f0808202804007841bc,0x64b180851a198c67a178864619705dc1f6c6d9089c63903f00fe1b6417018e46701958073,0x1cdf4abd2af06e800c46181d607592522fec1b81ff92af1ba46f8,0x17b17d05f417fc63414682fb1b5800c17881d81b5c00b17707d802146d617d0639067019d,0x5f4584c5f411c447111c44c513144c52f5130217d017811c44c5,0x5f418745f411d05f317644c817cc1ab2f5017b44e461d11d04c8,0x193145c651173467a18245ca19706202f51134192063911d04c8,0x20587551ce000413da7decd8e4dc1d1566d01ec2035f7467919b4,0x63419285e04bdc5db19c464a17fc0fc03f85f414685cc17245f4,0x5f418e45f41b5800c17886d7002c5dc1f646d617d063903f00fe05ed62918e42fa0764084,0x61218e861219145c517644c513144c5066c197184863a1f484c5,0x1cdd47f539e06e400c4361d684db004206e5e6a79c9d1401081b9,0x5c518d051a05fc5c518d017a17146341f3cbf317145e42f90be9,0x1cf94ac92b27dcd3d9439c0424db92b266cccba32ed21b01099b3,0x5f400445f418d051a17fc01017d001017fc011184801117ec7ce,0x5f41b5440005ec2e706106d517d05e006dc6d818485db077c7d61b545f417fc7fd03f00fe,0x5f418d051a11d047431a04c81320d322f51303586863911d04c8,0x5f41b605f41b545cc1a5c6d817246981f686d817d069703f00fe05ec5f405e01b7078080b,0x1134065c19918d051718e4649173067a1788649172465c17707d74be81ee07b863903f00fe,0x215b861608375a53d67de9d7c4dc9cc609a22da857a1920108044,0x612187461219945c51f34196184866e1c6466534bcd440670719,0x1cf87441cfa07481d20749d7b002d773074880479b01d21ba81d2,0x1cde4b593a16e61ce34600d4f353d3a77ad404081642fd6ea82fd,0x1ce248153a06e6800c436804279cd6bb7a78cb832e40426dd56bb,0x5f4186c5f4192c612186cc6b3194c6731d464b184866f00046f6,0x5f418745f431acc65319c19717d061d067064b17cc6f61bd86f6192c5f4061046720000fe,0x5f418e840011c447111c44c513144c511d064b17d063a11c44c5,0x612187460d4c045f3174c64b17cd1f11bd464b17cc17807440fe065c5f318740fc0750805,0x1ce9480539f837a0d84365d7a74082697ad1d6773500426d7c045,0xef18e513511c447111c41971b8863911c44c817cc62013204c8,0x1c72a6dcfd074c1c75198d97002d3a4074dd78071d46600102db]
def pgR2:Array Nat:=#[0x1c84ac5ce76e9c1c84c28d3a07213a534e80040b712b16ef02dc,0x1c64b352b16ea41c64b34d3707193a334dde6901092b17a2c02c,0x1cf94b4ca8806e81ba4b30d98366120c06e82fc1ffd2af118c1ba,0x61218e8400199400c18e4d4334c061e1bac17b18486341bac1ad1f2400c18d00fc076c087,0x1ce2519d4836e6db8d520c1e2078804007881e220300402024040,0x66518e863411d047417fcd8d11ec61e2f5817b08a06341bd417d199017018d06f511ec074,0x5f418d05f43294c65181418017d069706707c834c061e2f441d505ec5f418d01d109b019d,0xa8b4e540486e391674e541cc4715bd60731e4800181df79a0048,0x5f418b040006002e8061047111c44711bd447734c0d31075cbd6065c5f408801d711c419d,0x14836e3148307814860781e495219e68012139649a139607812f9,0x2055879e084839600e83993906f2dbce6f90042857e184875c013,0x1306498d2af06ec1bb46182f979ad2af01213934d3d3a206ec1bb,0x13944a2ca940be1d0101216126e391706ef53924d396f95be5772,0xa954e540486e391714e55348471dd79581560f00192f86e90cb7,0x13967505ffb4e5a00f83713914d2d76c5db0042735dd2d6d84cd1,0x1ce17509a7f6e9800c6e481d7075c1d7075c1d7201c1d76d5c476,0x8a0018a9302201ce0738c7631d914f4ea4d4535151c634d9314,0x6022408b31d91504ea4d4547213494c516102a581ce31d8d45,0x1cea5838a8e01161ed01221da836516b83c61dd83cd1f383ee0ed,0x13944e51ce6584800c6e781da07681da07681da20181da7a30048,0x1ce858394846e95cdc5211bdc83d148783c0045735528a6d89bc0,0x4601180464994dbc4b3530007141c54b3530007141c54b520ef,0x856a18682160dd836a0e783da0f583ea0ee,0x1c577531c47099c267099dc9170dc04a099ddae71b8041099c04a,0x690101069417ac42a1a505b711846921b98690066415a1ea07c7,0x6901a4148207ccfe805e05eb1aa46931aa45b71a646911f1c71b,0x67c06901991010f081b080151658015143c5b716585b716ec71b,0x1d88770400f7531dc278f401507a01e807a104f07a148966a9783,0x6901a406e418e051e18d05eb1aa46a916c45b91a6869a179471b,0x690101051844085e71a5104d16d05b541306901b9069403e40fa,0x5a1179c694172146552306e41a500f906a45a118e05e716d0690,0x6901010dbf650816905e05eb1aa46941aa45b91a686a31a697821a406e41a5084b03e40fa,0x5a116b85a117ac59616b85b916585ae5e0869016845a72eccbf8,0x69018ec51c17ac596169c5b9165863b5e086900a545a703e47f3,0x69018ec40017ac596169c5b9165863b5e0869007c85a703e40fa,0x51d16585a716205a3413059f169c0f903e859f10305eb16e4690,0x19431a401a718ec18f36ec5eb098c596169c5b9682459618ed7821a4081307c45a703e40fa,0x69018ed2cb179c6a9169c5b41a6863b52306901b905a703e40fa1a40169063c6a91a681ca,0x5a118e051e17ac5a118d05b717206351b9869016846342ec07c7,0x6901010fd017ac5961a505b516586a359686d03c7069403e41a91a401a705e02631ba084c,0x69016845a118e05a714785eb17ac5a1169c5b716dc5c818ec71b,0x16b85eb16b85b916b840e1b3c3fb10b0462,0x1a4100063b16585eb169c59616e463b5e08f181b405a703e40fa,0xfc506981a718e051718ec5eb16585eb169c5b916585b918ed7824fccf1d21345a703e40fa,0x15e816a85aa17ac6a916b85b91a685ae10386d01b905a710b0462,0x5c818e05c817ac6a9169c5b917204005e086d01b90a3803dcbf2,0x18205a5944100063818e026317ac6a9169da0a16e469a18ed78220506d01b905a703e40fa,0x69018e051e17ac5e7169c5b916d05b541306901b9063417ac5b9,0x144818e063817ac5e7169c5b916d05a341301f31b905a703e40fa069816918e05eb16e481c,0x22a78b3229a07981e60799051523565c681df157d49d19106c055,0x1c577309c5a09902640991dae71b8053099105352399ab0991a08,0x69010106a316f416905e042c10b0b6d10b05b611606a3428442c,0x5c810105c81a785c805e042c10b0b6d10b05b717215931f1c42c,0x1d8872b40537531e2b72c40152bc8af209990502f0d06166ac266,0x5c81a785c8101051c1b0842c10b042c2db45b9172069a1b0842c,0x69e101c63d1a28b7f2db504d16d05b52d8869e07d06c105bc0fa,0x5ba2dfc69317214652dbc5c81a8c18806a45c8175868a16d069e,0x69e10094e452e016d06cc68a2dfc693098c5b91a686a31a68ba01a799731a8c84e06d00fa,0x69018ec51c2db05962d8069e165863b2ecc5b9165863b2e80bfa,0x69e17690ac1a285962d805b9165863b2e8069e165863b06d00fa,0x69e176840b1a285962d805b9165863b2e8069e165863b06d00fa,0x51b16585a616205a32d88596175016f03e85c7176868a16e469e,0x14bc1a781a7176818742c068a098c5962d805b9682c59618ecba01a7888b165863b06d00fa,0x69e17699a31a28b7f2d805b41a6863b2dbc68a072863b06200fa1a7816d061cb011a681ca]
def pgR3:Array Nat:=#[0x69e17690ac2df45962db85b716585e52e0469016586c22ec07c7,0x69e10090ac2df45961a4c5b516586a32e0469e16586a306d01a91a781a706cc2631ba084f,0x1519f059618e063b145c015005442c2d805b716dc59618ec42c,0x1b2102c5da1658b7d2d8059616e463b2e8059607c063b06d00fa,0x10a706981a71768516176868a16582632d805b916585b918ecba01a28596211c63b06d00fa,0x5c818e05c82df4b7f2d8069e17204002eac5b9172063b1188462,0x5c817685c81a745c52ad45b9172063b1fcc69e1720a3b06d01a9,0x18605b5945102c5da1a902632df4b7f2d81a0c16e469a18ecba0205c1f007c463b06d00fa,0x5c818ec5c81a28424169c5b916d05b5109068a172063810905b9,0x14c617685d61a28b7f16985b916d05a32d8868a07d05d405bc0fa069816d176826316e481d,0x22bb8af62bc098c263098d053523965d098ddd2726df9f1fec055,0x1dcc07287a14b654d26fa801577dc1ca4071c9200141ca4b65b3b,0x69017690ac10b042c1fd068a42cd0f210b069008a418f10b01b11a401691fe442c0230229,0x16145cf1a8445911643bf16a85850f2c459,0x171442b10ac69d1714b6516a85aa10ac455,0x18205a46db10ac42b10ad657577961510ad01316a85aa10ac0fa,0x8450ba12e85de772d4aed40bd02f2bb4005,0x15e250e96195241059684949041641c02bb53e13c3c0122bb4003,0x15e2432d4ce506cf8302353e23c41238000d3e33c442ff2c4cb13,0x5a117685a117ac6a9685445f117c3d010b0690168440b10b045f,0x5c817685c810b042c2e9069e17210f22e0043110c017810b0430,0x18f3001400310b042c10b18ff65810f210b0a9929f8a8f28b40f4,0x18205a479f685c5da1a9042c10b042c2e959a863fd9601f0c42c20801c2072817810b00fa,0x211d81420356d01b408746194842004a8019d84707800f6a8c003,0x51252bc4af16062ead2375248bf943bcbc5,0x64212bc49914493fa501b524906443bcbf9,0x2a7941b51d548853b8be164192bc3f9d05c,0x19067c49a4e4af12bc1fd54493f9da50406d49241707c643bcbf9,0x50e902a40a94902e9d2365240bf65950ba7,0x50e94902e854902fd0ba140a902a48d9654,0x1906436d4e557a962f7e514c042d5fa87ff9449659800f693c04a,0x1d8807280534af55a34af401520381ca407105000141ca43c59ab,0x15e24909242524d05d59554934175a13000d3e43c4d00068c1a30,0x5c818e05c810b042c2d8069e1720400098c45f117c45f10b045f,0x5c818e051417ac5c5169c69e17203d11b9869e17201b310b01b1,0x18605b479f100063818e042c17ac6a9169d9a963fd9601f0c42c20841c207281b310b00fa,0x214d81aa04b820a040849dde972edf71596ddc9726004a7ed8003,0x1f16a101f100541f12bb905007c59ab5e05d88014c8162bd0030,0x42b8a9f42b8bf741694ed2ea505a5638ba9,0x5c810105c810b042c2db44601180be310b018217206382df41a9,0x5c818e05c810b042c2d8069e1720a3b10b069e1720400098c1a9,0x53c3905b291926742d481b57ac0164071b4f6d550b54b65aeb,0x4001090b601708a39109018218e0b7d060c16918e0b7f05b07a3,0x10a918e063810b042c2d8069c1708a3b10b01a641986382bc418552581a718e0aef05b0846,0x10a418e063810b04252d8148a118451310b069e069c400164c1a9,0x4001090b6017085d410901691000b7f06945c218e042403e87a3,0x10aa18e040010b042c2d8148a429863b10b022505a44002bc01a9069906518e042c03e8225,0x1a410105d810945e71a50457115d48b109416d1e8c6381094457,0x52a292bd6c1db224071b52802d2b46ba8f1465a92bd58bc015,0x1cb74af52bd6d05cbd40720d372f12d97ff5f13003d2bd69499a7,0x59c18943c716e45b416d442c109016a1090182167062516e442c,0x1de13f4905d490d4cd36c90540015a064330bb153c4f12400da0d,0x5a106094e44ab84001a8842c10b042c10945b71e714dd175042c,0xfe777d8fe776b8fe7014db1e3f9d4d16c81050657d4d300159ab,0x5a118d440010b04242d805b71a645b7109069e42e863510b07c7,0x4001a6c18f1090b6010b05b416dc5b910905a14ab818210b045c,0x190e168416d4ab928c100018220401f1063c42c109442c2d8042c16dc0fa66885d41f1c42c,0x1c2168416d57286a3168442c10944242db45b703e8f8216dc42406081c2168417810b05b7,0x5a14ab84001a790ba063c42c10b0b6010b05b71a645d41f1c42c,0x1c58753da7c2bb00166c3904a413904f2d9c00f7081d1a2bb0bc2,0x1dca71b505f861ddea80b4ba62dc4ba66c3d04f0015f7066a8ba6,0x10b52a7d0b577a10b50129b1e58bd4756d11c9242d404a0015b3b,0x69010106ba1a281f105e001510b0b6d10b05b7427c7c71f1c42c1a401a71ae805610b0076,0x19517145c516a85aa16a842410b042c05d85b916e45c540e042c]
def pgR4:Array Nat:=#[0x19517145c5189462517145b916e45c5174442410b042c05a842c,0x5c71000400061867c063442410b0b6010b0bdc171c5d41f1c42c,0x5c81a405c81a40ffb063c42c10b0b6010905b717205d41f1c42c,0x157269cad746dd4372ac80f4f98016800c8187239caf7581b3b,0x1a607c467c18e040418e0015005442c2db45b716dd09f179842c00b867c069c63810b0185,0x5c516a85aa10b042c03cc5b9171503810b018205a42a810b00fa,0x106053050b600540167fc54c142d9a9f6cec67d162881f2068bc4,0x1a619f01f110106c218e0015005442c2db45b716dd09f179842c19f001605a463810b00fa,0x40010903c617083fd10905c21000424060c5c2101042405b07a3,0x10ab101040010b042c0f194bf42cc40b10b022505a440010b01850608229101042c05b0229,0x16a83c80f205b817103c8574c5aa0f200fa,0x18242945aa109442506390a016e14801094f861b785aa10940fa,0x1cb240ad02b2e9d059563105207256562e9e07a004902b2e9c005,0x1820f243c93c305b8174042510941841094f881b7c6250614425,0x1cb328d924372440145648ba868400122ea1d87004958d0014ba8,0x4041a410a210b0b6d10945b61a8d0a110b06901a8c1a710b01aa,0x10104242db41821010b6311783d2109045e,0x10104242db416d16d842411783d21040183,0x2a7db0851d604d4b79b0376f92de6c28005,0x182101040410944252db509e16d86a31094f871ebc51e10940fa,0xa9f72646286c7947572f9c90538905c6ce9dbf5388f156cac005,0x12d7005501c72412d76c901ca1ae41ca0729dc065a56300015c31,0x6901a410ba101063818e042c10b04242db45b7427c7c7176042c,0x7881e2040006081ca063c42c10b03c610b05b71f103fd1f1c42c643c1a7100081110b00fa,0x7881e210ad10b04242db45b716cc5b710901c205a46c210900fa06081ca03d842c16dc1c2,0xa9916f818f1094a2e10945b61e750a010958f729f8f8b10940fa,0x569f5a886c1401580150618125df56c8dc3265b1e3c58c0005,0x4041094b6d16d85b6109068a415442500c068a145c42400c01a7,0x12bd734d01c72410d66c0dd9a4af5b0a00140157255c964170f16,0x21e1825a14c6d0a0a9873614b812a1b6801e2dc003e1e86d08005,0x3f9d2bd3710b6743cd2392fa922d4334b67,0xf3c38f0e499d2673710aec2bb001648e4bc22f0922d53b0ba6,0x499163251d19084af1449412d4cf2f85488,0xfe74370dc4442964f6850bdf48b54ec2e99fe016f12d9689c7c5,0x574c5aa16a851003cc51011884571188462,0x1823e186de40685aa16a85c117a80f905d846211884571164462,0x17145aa16a85eb171417611884621164462,0x18205a45c50a9c5aa16a80f917ac5c505d8bc611884621164462,0x5c516a85aa17ac5c505d84621158459115819517145aa17ac462,0x207b72d001240ad02b40ad10b00141c948e8bf62f810595958bf6,0x17145aa144442c10b0a302f78bd92f6842c,0x5c516a85aa10b042c05d869d1714bdb10b069d17142a82c481b1,0x5c516a85aa2dc0b6403cc5b917150382ad069d17142a706d0462,0x5788005000dd616f95a667995e876d45a65,0xee000c6db000c5aa000c3cc0f303cc0f30462118846211883cc,0x5000c1bf71e102a40aa0087991e86023e00d7999e887221aeb,0x845604380760bb82a805483560d28749fff,0x1d8872b400f752946d417801507a41e907a4bef5224bc12fbcbf5,0x5c816a85aa2df4b7f0f185b7172103b1c6869e17203fb2eb845f,0x18f316a80031b406e41690a9929f85a403cc45f117c4621188a37,0x18205a479f40085aa16a82631b406e4071081507041f105e00f9117c45f117c45f118845f,0x211e811601f07981e60799dc8725c055000cbef2fbcbef2fd4bef,0x50e902a40a94902e9d2365240bf65950ba7,0x190640a902a641d968079948f41619a52e99449659805520059a5,0x16705aa167042c10b03c516e45960f0040d,0x5c518945c51a745c5289069d17143c706c442c10b016a10b0b14,0x5000c1bf28d1242490a00c799de894914bb26839a113ffcbb2,0x845a06180a219584261832eb8bae4020bae,0xf3c38f0e29192673f9c1ea07a80164998bc22f0995e43c0ba6,0xfd24af4fd207981e64999f1401552bd1fe8bef66990f02dc59a6,0xfe72a7cfe776b81cb003c1e7593d58b0014bef65794d02fd4bf5,0x59f1000400060869b0634426167c5a717ac456117c45f1188462,0x5a11a785a11a790ba063c5eb16845a717ac45f117c45f117c462,0xf3d4dc587471d50711c1eb07ac01607ad04a2f08bef2fbcbf5]
def pgR5:Array Nat:=#[0x59c1a78595101059c18e05eb16545eb16ac45f117c45f117c462,0x59c2a6440006181f1063c5eb3f103fb17ac45f117c3d0118846264401a7100081203e445f,0x1c61825602a07981e60798bef2fbcbef2fd5dcb0155e2a0014bef,0x10b52a7cdc16c7962f51d5c9342d55cc6cf9de842d55cc6d20005,0x1a74407101c45611583d41090424100440e,0x10a8101051810900162db442e2fb4a3a10901a665c84042d481a9,0x690101c63d10905e7440cbe22fb8a3a109018608a86c110901a9,0x68c10105182db06e428c81a61b9040405bc45f117c45f2acc45f,0x65aca9f36fa0ab58bd4758351f4d57260a7,0x5c8101051e10b042c2db405217203d010b00521720404098c1a9,0x30000c1c22914a9e659daa4070801651d1b4e0709f51572daeb,0x488163251d90b7538e0ba64292be51294c2,0x1f462a7dbef7f7c00318a20b758bd4757eaa1a97d394e27e4e0c8,0x69018ec51c17ac596169c5b9165863b5e086900b745a703e40fa,0x69e17690ac1a285962d805b9165863b2e8069e165863b06d00fa,0x51252d84acd449828901b5301c334b620cd,0x14494b612b35125af8406d4c070cd2d880254c070cd2d86d1c003,0x53010db565141b70d903e5248bf143bcbf9,0x51252b04ac16062ead23753020d14b60bab,0x513590d2a4144d828d020530dc344b6a0cc,0x4ae60a0406dc3543560a85124ab051254c0,0x1f1164187a04b606b96fa9449694cf8340714c07f84f834b660ca,0x1c24af12bc0708016406c1c207292d86bac005000ca45206481e,0x1f464b65d5f81e162f40721937d3d2d982e5f10000c6b97eadf6f,0x19082a79a165124f8451d141b3e115cb6cbd4493e115cb6d0c003,0x578ca9e3ff9491418d237506cf845384bab,0x19082a79a4b57a8f8451d14c03e114e1830d4491e946276945f6d,0x10004242d801691000b7e11743d6109045d,0x10004242d8016d175042411743d6103c16c,0x2a25af7406e0244355b0b70e10d56c24003,0x8024af121f506cf84406d41b3e112d86ced41b3e112d86d18003,0x6c840b102c46211883d510b042c0fec40e,0x1b2100063b10b00152d8042d2faca3b10b016908984002d441a9,0x1a4102c5da10b05eb16b8bd82fb0a3b10b016d089863b10b01a9,0x1b0100063b16506d028c416d1b3040006d045f117c45f2ad045f,0x5ca894b620a457a901b8341f0e4b620ce,0x8031e1c7a54af121f4b6141b3e11fa9406d41b3e11f6e4b620c9,0x17145aa16a869d1714a241a745c50f1419b,0x5c516a85aa10b042c28cc69d1714a3b10b069d17143fb010419e,0x5c5102c40b1a745c5102c69d17143fb06c442c10b03fb10b0055,0x1cb07545cab6ca5b2b8011b546d4e00a800208672e5a817ff0016,0x18605b55e9102c40b102c46211884620f5442c10b042c0fec40e,0x18605b5946100063818e042c00540162d8042e10b842d28ec42c014c1f307c44002c541a9,0x18205a5947102c5da1a9042c005401616b842e10b842d28ec42c07d41f307c463b10b01a9,0x18205a5948100063818e02651b406e428c40901b2c6e010001b4117c45f117c45f2ad045f,0x19066a09966001400300555ea58bda6d6d15f0f7d41a9e6d59aeb,0x75000c79f07083ec1e7c003070800305e042c10b001628bc42c117c45f117ca37118842c,0x5000e091872607081ca0cf830a08a895226a874e1d486460cb,0x10b52a7d0b56c6962f51d5c8f42d55cc6c1207742d52bd6d24005,0x30000c1c329112bc5688af300541f14005b4d07081f14b60bb4,0x1f0d4af52bd855d62f4071d9972510d6829990900b92bd7321c8d,0x8aa22cd8a6e0b8829625589a626789a20c7,0x1a63fad46018e063818e022110a042810a028811c447111c4ac4,0x9418e063810a042810a047111c44712b1018205a40f610a0471,0x1a4188862210a042810a047111c44712b1068401f018f10a0471,0x208175340366c71b2a6c01b9d6eddb926bbe07d00d80366cc5bad,0x9518e051e10a042810a047111c447110a01a6069c1ac10a0471,0xfe30608feb18e051e18e042810a026a10a047111c428b11c4ac4,0x182101040410a042810a047111c447110a007b1e4817810a0471,0x20346a100366ca1af96c7dbb66e1dba16bbe07e00d80366cd1bb0,0x791024c7b050e41783f444282c3442810a0471306847111c4ac4,0x590164059819602981d1b1c6be5b336c01b9d6e1dbaf6e49aef,0x922a64a7e1a0c59005e042810a0a2c2be447111c4a3e3048ac4,0x5901640597fde07181cdb306ca1b2a6c01bac6ed9bb76e49aef]
def pgR6:Array Nat:=#[0x87821e6877db326cc9b326eb9bae6eb9bae,0x5591534dc81064419106457e15484701064192156453c1064561,0x5a11534e2510a042803e16a7166054d10a0190168454d10a116601e0598382042803f0178,0x54f106441915f854f2ac817929f8a2928f8079153c55311b0178,0x18f41534e3310a042805cc57e11b046c2b081791e8854d28b0a3e01e4169153420011b0178,0x5f510644191c78c52106471e39e05530598192158841928fc400,0x5f71534dc910a042803e071e314c54d10a071e05a454d08001670648400153442828fc400,0x5591534dc81064419106457e154847010641921000dee1064e93,0x5a11534e2510a042803e16a7166054d10a0190100054d10a05ff069859837ec42803f05ff,0x16801e81941064419106446c11c44712ac840010001901064471,0x1a4106441911b04712ac8400100041911c40770594ae5327c400,0x2ba9bf92ba8e8763f8e8638a8aea705ce87,0x54f106441915f854f2ac81a6153c55311b0179153c41915f8400,0x1bfe806c0352ba4ac82b21bb66e15b842ba402269dda762ba5b92,0x18e739b55e03e415ec0074f905e50e3a6bb01fa0088e3a6c01b92,0x8242bd401d5e18e3b2e3401d37d58fb5e5402138ecb8d705c022,0x7a41534e3410a042805cc57e11b046c2b081a605a454d080046c05e4400153442815f8400,0x22b538d5bf62e1cb8700720e4835ce352e1c0358270e352e1e0db,0x143e0018a350734b6640119ad4dad0c92d992e46e0914b2d98025,0x17544010fe446f11bc3d3109042428ac424,0x68c435c1701004409102447011c0c660f4c197109042428ac424,0x143d5791cc450f5ca800ad2e131cc1f9006560a2da10ca2da0ab6,0xff45c5100445a0f4045a10904011830424,0x68c100440538b454b2a0047111c43de03e842410904011090424,0x68c1004a7d4fc817005e05501970a9a197047111c43de08040fa065c42410044241090424,0x68c18e522a152c65c175047111c447103e868c05c00f6197047105ec4242d804241090424,0x5c518d040015405c5100045a116845a11681971090b602da4424,0x18205c06dc100063410019bd154065c175047111c447111c40fa10901971090b601090424,0x144218d0400154054b38a047111c447103e819505c0400154020505ec424169c4241090424,0x2196818e09339713717314c7731dcc7710bc0422da1b1043d0ab6,0x18205a472007786011804427109c427105847311cc47311cc411,0x846a16d8405d9070982ad32a0ca832a0ca8,0x17895e24fda4e08e7a00a141d3e381ff07fd2f037719de32a4ca9,0x5581804558154055845e84191064419106447411d01773298419,0x1784180458f154065c45e842810a0b5903e03e10f843e10f84a26,0x18205a471f457460118059c4154065c45ec42810a042810a00f811d047411d017711d0428,0x2119816e025397d3757df9d897085f75007ccad32b405b67c0cad,0x1bf04911244080c2045af4f004f6c03d32c1506447003d0090cb0,0x1b176fd002640cd46840cce6100a42023a5ccaf4eb0caf008ccaf,0x1ced81b1ced39793745db9b196bd1b110080cac32b003d32a9aa1,0x17b03c3149c57e17b43c310184090f0c3df,0x1a444386021064419106455615f8603106455615346031064470,0x5a2153455510a0b5703e16a6165d65910a0aa9165caaa28b00f5,0x1b03e34602155454d45dc42810a042803e05985a9d1665964428166020905e16dd10a00fc,0x1a4100063a155454d15a042810a04282b8c413104c4131c64413,0x1b5100063a14a055015a042810a042806d85985a9d2505964428166020a05c47192bd80fc,0x1fb39d0e3c2e2cb8b0068fa46e48e3c2e2d8e607f55df582d793,0x2107f0047574577439b15dc2e10de300697857fd4f8f5dd0b84,0x5969e206239cce385dbcb842e10b840070f987ae21e25dbcb84,0x3ff55173ff4ea1372d6b738053155db59b6,0x113b547113b37e13175db58fc37597c96690ea248b96b85ae08e1,0xf1938d8e702e10b840075bab3e6176b2e1207c00d976b2e11bab,0x6af18091791064419106457d19e0603106454b196860310644701abc170062841919e065a,0x6af1abd1371064419106457e1558668106454d155864e10644701abc1a705c44191bd4719,0x6ab06981a7180510d18084191064419106457e155857e180c419153455615346031064470,0x55918045591064419106447111c43dc106454d15643fe1064471,0x78618046010f0c3c3152057e19e06030f0c40610184090f0c3df,0x18905c07c2459460118044191064419106428a15f8678180c4195b5c54d19686031064470,0x22c28b162bf2bacaeb2bacee34f056b82b40e374d3176d2b40c74,0x1c5573d1c4039753735db4b9b2e6cb9b013cc6c304004f31b0b067a8404b59bd9bf5f499ec,0x1a4060245e454b196865a10a042810a00f81a2d6a8459865a10a068b092c1784c6042803f069005a418a1968428098024b,0x1a406903f3c54d155530910a042810a01a85a9c59854e165910a0690166018f5c1042803f0690069c1711c6442859e40de,0x1a181a6069c6013e306021534555153517710a042810a042803e068b1661677459965910a068b166020b05e16fc10a00fc,0x5a118045a1153455945dc42810a042806a047111c43dc59644281a405a10ff96df10a0471]
def pgR7:Array Nat:=#[0x55918e051e153465a2a5c41910644192b996a75aa05ff3278419,0x5591804559153455945dc4191064419106465f15611665964419198055905e178010640fc,0x784180459a153465a45dc42810a0b5903e16a75aa116659644282a64a7e2a18aab28b00f5,0x6081691ee516418046015bec54d196917710a042810a042803e02875a9d6a8459965910a08e80a1827a05e170010a00fc,0x22a58b1229638dd34c5db4b8f2e3cb8f2b3dd9e718d66e7a28b057635c230141ea62c14050,0x69018e92cb152c65a15a042810a04282b8c413104c4132b184131a40169063c65a10a0413,0x6901010fd0153455519ac42810a04281c64413104c41359644131a401a705e071910a0413,0x68906981a718e051718e854d155454d15a042810a042810a0ae3104c413104c4131c64413,0x18205a47c1100063818e0208153465a15a042810a042810a0ae3104c413104c4131c64413,0x22a68b2e29939053525df4b832e0cb832b30ac72b1cac766f8ac7,0x1abc63a4b2c54b197056810a042810a018b1a2d6a8494065a10a068b092c1711968b0303f06af05c018f19704281bbc24b,0x1abc40444e054d155866b10a042810a01a85a9c598565d65910a06af166018a1c657e303f06af069c1781c6442859e004c,0x1aa81a6069c638145c63a1540528154056810a042810a042806d868b1661676494165910a068b166020b05c47192bdc0fc,0x5fa18e05fa153465a15a042810a042806a06af17e84001c6442811c447111c565910a0471,0x6241701ee840018e0638081c550197056810a042810a042806d82895a9d6a8494165910a08e90a1027905c47192c100fc,0x22c18b5a2c039893775ddcb922e48b92013d67a59ed67567057d07829cd80a4d9c1240c464,0x178b5e35c5e5af13544d5178c2e70b9c006c04f2089e2c5af08234eacedb07f93242ae13ab,0x1c6f6951c6f398d3785de0b932e4cb93013cc6d2ff5b914eb8ab77af004c24099c25f44047,0x13e8512c20c37dd31e4d40b822e08b822b2541e5ec61e54d40b82512c03600d93162e09b58,0x68c1004fce153455519a4413104c413596442810a04281c644131a3019905a8719104c428,0x1a404043f4054d155466b10a042810a01a81abc5981ac07195f916a716606b0596442803f0690069c1781c644280131678,0x6af100d1371064419106457e15586b0106454d15586b010644701abc1a005c44191bd4719,0x1a404043f4054d155466b10a042810a01a85a9c5981ac165910a069016606b05c1442803f069006801711c644281bb004f,0x22b56a126e4e00e6f3a512fc379123c00c54213e4916c5decb9a1e247a61f4d6ca5f2c850,0x191219fc84864442e956b15e14d559b75df960d2e7484a2e7402f5e5db872125ba15df8b9d,0x6823d49a9a39d4e0a4d4cb8c2e30b8c0244fa55e6dba14d4cb8c0bf9f3d011d3532e31bb7,0x211c825c24c38f53515de4b942e50b94006a09070e61af5de4b9487a4036009d7792e521d8,0x2aa01640594fa4f1b7474df939b8df95dd4af82be0af82e4001e507cf916d661625dd4b90,0x55918e0559154055910004191064419106447411d0a3f329c4191980559100019d0ee819c,0x559102840a1540559100041910643c2106465f15603fe5ad04191980559100019d10640fc,0x559102840a15345590ff841910643c1106447111c43dc11c4419,0x559102840a19805592a0591d65b417806b44191064a29106420611c447128f84712ff0419,0x559102840a15405592ab44191064a29106447111c4a3e11c4419198055905e019d1064471,0x55918e055919805594b284191064419106447411d047111c4419198055903d81ad1064471,0xe724e28e880a0427387bcae72b9cae82ba17985ec616e876cae8,0x78510a04280fb83ed011d30537b004705ac54d1968ae31c6471911c44712b10a3e11d0474,0x2850a0c2780a0c3b70120e004c7d77c5df0b842e10b856abcace5e617b17fd9bbe5df0b85,0x59016428069b9d5878f88ed37fd31d5dd8b852e10b842e14acd6d817985ec61e45dd8b85,0x22a48b2a29838e534d5dc0b882e20b882b4e0eb83b21e35dc0b88,0x190b5e597a84afd2bf019144c3fa882a40752f1377566149a4cae4e2ce8a5afd26a3658c1d,0x448d2c137193fd3cc500743dcdcd401c0393a8d18b49fd68d67e4dfc444d2835c499d35a3150c450c0cd03c9a293008cc8,0x448d2c137190f644412883a9118c4a018bc37f91144a1183f5a3d91765e928800e58bc60fd50c450c0c668a19e766f08c6,0x648151858752c34b0c5a54b88dcf1ccd045532d0c45a0924e2cd14c842f96f44978b3c5a31520451c2df0334bbe0b782e0,0x648102e40b92fe379d23e5e957c4403cb36604981d4040b3e5a39520451c0c62ee82df0b8552065fc6301cc58a560742de,0x1c547531c4676ce10a4aacbba2ee9b142ee9c1a70fdcf38230bba6ff1c42743e08e2ee9e9f,0x376d2c1376cb7753bd2887cc91274a200393c04e7149f8b3262e8e6437312822ce983c5a288b237440c953bc8cc3004cc7,0x450d0343718b7a53c10073c0d18e4014b3839991154018b405a408b3450c0cf53c0c03332de4c373500700e59fd675c89c,0x97803904f128736f52870b30dd80b302550b3118a0b3025563182cc44482cc095584a5a2d50d3e542cc03308b40954255,0x215d81ae054853a0fd8518eff4f616b96308e604dd9771611167e822205a01961c35ae5771,0x3fcd17e371c0fd43e514a0e0598a68847323bb18a847acb3362ece4960811612ced83d30f0927032d17643e48fc5a0d6f5,0x3f5d17f3701eb743e8df23c1162662acb39399d6276088b4130f48ea034548543e96855be00fd58a19b003f59fe67608ec,0xfea45f0dc5854cfea45f0ee862551d46308e4460051546110c1d7aec06545a486859996cc,0x69010105181c787261b0042810a042810a047211c847211c842813184c613184c610a4bd3,0x5a11c9865010a042810a05ce194047219e45cb19344c6196cbd316846381c7842811c84c6,0x1a4040436fd95105a41781c78726194026f10a042810a031710a047211c847211d047210a04c613184c613204c610a4bd3,0x69018e44001c7852b18e442810a042810a047211c847211c842813184c613184c610a4bd3,0x51d14ac53f10a042810a046c11c846c10a04bf13184bf10a4bd0167c40c1c7842811c84c6,0x6548690069c639063cdbb1c7829e14ac63910a031710a042810a04720a6047211c847210a04c60a784c613184c610a4bd3,0x1a406394b2c6411c9863910a042810a042811b447211c846d10a04c313184c6130c4292f4869005a418f08f842811c84c6,0x1a404043f4071e14ac65010a042810a042811c847211c84721cd04c613184c613187342f4c690069c178094842811c84c6,0x1a4100063914ac71e18e442810a042810a047211c847211c842813184c613184c610a4bd3,0x3f181a6069c638145c639190452b0ab063910a042810a042810a047211c847211c847210a04c613184c613184c610a4bd3,0x608169652440018e0638098471e1c9863910a042810a042810a047211c847211c847210a04c613184c613184c610a4bd3,0x512063818e06411c9853f10a042810a042815fc46c14fc46c10a054e12fc53b12fc4292f401a605a4638098431711b04bf]
def pgR8:Array Nat:=#[0x22a98b3a29c24189090a60b8e2e38b8e0a602980a60298306c2980a7829e0a78cdc0a79b50,0x73adc8502f0b8e44c4b8e3be10c7637d88f39590c0618d7e013d9f392301c7a2c981060419f3a02780bc5f718b860e88c0,0x7391c847204b722c6c0d43c1d3e06378b2539a937d6188b2d13d1e4f2395c7c2c941511c29e570279c8968c588a5f188e6,0x16846af1c985aa16845a81a405a109b50191abc7bb09b417803e457f14cc78015087340db854e157073915947340e14770,0x1a4069018f06901b914731abc7bb063c0f91a8066615fc57f136069f193054e15384d01db86af1c986950ef4a2203f00fe,0x16106e451cc5fa063c188173864f19e44da172d308196c4d31ddc726193c3d728f419c06745a116a86901abc57f15386af,0x1a4069051fd95305a416a1a406e451cc3141abc7bb063c31403e457f19e464f1e007340db454e196c6691ce47340cb87581abc726193ca000c649ba03f00fe,0x17e854017e864214b4df41ab452d05c41b415fc5cc1e007340a6c54e17247391cd02a21de46af17e85ac0adc29b11a8d86,0x1a405ac161069016610191abc59805e00f915fc59816b0734135454e16645ad1cd04cb1da06af16605ac0ee4a1e03f00fe,0x167c598406459805e00f915f453e15fc4d9152cded15384d215e459814f83be288c0fc03f859f16a46901abc57f15386af,0x6550690069c5ac0610f811a4031416610191abc0c4166017803e457f0da459816b07340dcc54e0cac59916b47340cd475d1abca0116605ac0c849c303f00fe,0x1a405ac40e868b1b910191a2c34b05e00f915f467916b06790ddc54b196c5ad196c34119cc68b1c985ac0c909c503f00fe1a4016906103140d2c679196c23a,0x1a40634146869016605ab1b405981890b9515fc598178c7801cd054e16645de1ce47341dbc6af16605ff0a5825003f00fe,0x1a406903f386d016614731abc598063c0f915fc598193c7340df854e16646691cd03461d8871e166064f0ca88c4067019d1a401a705a97ed0dfc7801ce425a,0x5871b245822ab058203cc57f16087340fd854e160c7340fdc77e1c70582147c3f603f00fe,0x690f0916b05981b41019166030005e00f9166057f16b0734135c59915385ad1cd04cf1db05981c785ac0ef0a2003f00fe,0x3f1c1a6069c5aa3c205ac1a2c5980c510191a2c5980c0017803e457f166057f16b07340dc454e166454e16b47340cc475b1a2c5980c0c5ac0c689bd03f00fe,0x1674540167468d1674df40bc429005c41b415fc6791e0073411c854e196c7391cd04c62f4c71e1c985ac0adc28f11c84c6,0x17e85aa16a842810a03c615fc67916b0734153865b16b47341dec71e1c985ac10a019c06746af17e83fb10a02960a5c296,0x63e05aa16a86d01b910192a64a7e2a080f315fc67916b07340fc454e196c5ad1cd03f31da471e1c985ac0eec3f103f00fe,0x16186d01b90a9c2a140f315fc5ce1cd03f215385cb1cd03f41de871e1c984150fd019c06745aa161901905e05ac16b45ac,0x608169652903f16a85aa0c506d01b9101926442f10bc417803e436915fc67916b07340dd032b153865b16b47340ce875e27b871e1c985ac0c889c403f00fe,0x16845aa168469016850191abc35705e00f915fc53314f857f0a3854e152c54e15382a515d06af1c985ac0adc28e11a454e,0x17e863414685e81b905a71a2c5fa18d05e815fc57d15fc57f15fc54e152c54e153854e15dc68b17e85ff0c9829603f00fe,0x51205aa16a868b1b910191a2c34a05e016f15fc57d14f857f0de054e152cded153834215c868b1c9853e0c949c603f00fe069816916a831426d057f1538a03,0x8aaa2b78a4dee47b997cd7839cda0c4841d3ba53c5630d88c2570e464d658475f7493a0e09f1a7d55c7925889b5037c47f,0x6241701c843fe180460110b05eb1aa4547098457f19e45e310b02a1153865b177842c59602611c7872617fc42c119447a,0x21618172053443150468a8ee64f098c02eb4e4a4d7184b2c216717c91f564a68b0830516d9,0x7919f2d03512c64b192c62edd6215f610443bc5622629929b2d0ce4f588d81e4a70b4b1379f33588890d4a6cb430400100,0x16746cd1b8c60116741ac17ac59d0684df315fc6790a3c5e310b054e196c2a3177842c2f4c71e1c9828f17fc42c11c84c6,0x57686d001b063818e040010b042c10b03c615fc6790a585e310b054e196c297177842c1dac71e1c9829617fc42c03f00fe,0x6081691eac9691b406e4100063818e016a10b042c10b01a12d8437215fc6790dd05e310b0334153865b0ce85de10b075f27c471e1c9896c17fc42c03f00fe,0x8485e5579c206780bc09e2edcbb71cb8b003bb53c825818c72cd4e4a4d7093d612cb3d0e21f307d84a0974e8b35038c481,0x5fa18e05fa10b042c2d8047211c84722b144c613184c62b904721abc5fa1000b8911c84c6,0x6081691eac40018e063810b042c10b0b600a7057f19e525110b02a4153865b498042c1db490a0b282bd18e442c119447a,0x2122819e02f2ed4bb52c3029c0a7029c0a702a40a902a40a9189a7835cd90a902a4306ccdc,0x7d25e4b0278aa740d50352ed59875f5d23d3be58a767d55682c9ce57607d9ca54b0b2e13ddf3466248e356f8b27041c107,0x63d46d001b04010fec3fb10b042c10b03fb15fc6791e0040810b054e196c739102842c1df071e1c98296102042c03f00fe,0x167454016745eb16759b115fc6791e0042c153865b1ce442c2f4c71e1c985ac10b0472131868d167417106847801ce428f,0x63d45aa01b03cc0f303cc15fc67916b03cc153865b16b43cc1da871e1c985ac0f300fc03f8a9929f817806847801ce43f1,0x6081691ead00b16a85aa10b042c10b0b600dd857f19e45ac10b033f153865b16b442c1d809f21c7872616b042c03f00fe25a86d01b9017806847801ce496d,0x848e0478084bb52ed4b0c3bb93c9632cb1d392d35d613cb1f0e39f317d89c7d2c74057120df457d903111ca98ae60949b7,0x690101051810a042810a0ed915f457f2b08e31152c54e2b8457b1abc7261ac042815fc54e,0x5a110a042814cc65419e455c196c65b19dc7261ac042819e465b168463810a057d152c6af,0x1a4040436fd95505a417810a042810a03b4160067a195067a10a0550197066d19704291f986af1c986b023d84281e00739,0x69018ec40010a042810a058014ac54510a0550155456910a47f01abc59817fc4281e00739,0x51d10a042814ac5412b0854b1538ae115f059817fc42815fc54e167c40c10a058015406af,0x6558690069c63b063cdbb10a03b410a0428160029d14ac54510a05500a9855515a44291fa46af0a7459817fc4281e00739,0x1a4063b4b2c42810a042815f467a1514ac3152c65c15a4ae219d468b1c985ff10a0679196c69005a418f10a067a1970238,0x1a404043f4042810a042815fc52b1950734153855519b47341dd871e16606b010a07801ce4690069c17810a07801ce4887,0x1a4100063b10a042810a052b160054510a0555154056910a47f1166071e17fc4281e00739,0x3f201a6069c638145c63b10a042810a0428160052b160054510a0550155455015a44291f9c68b16602ac17fc4281e00739,0x608169652c40018e063810a042810a04280a3058019e854510a02a6154065c15a44291fac28c1c7872617fc4281e00739,0x512063818e042810a0428160057d1504ac2154054b1538ae115e068b1c985ff10a057f15381a605a46380a34580154028c,0x22ab8b3e29d2e18b862e18efd4f5d8c02e18e654de58512b4439423dc8f923e0b0a63019c0,0x71add4c02f1f3a03500bc2e5cf712e5d7e73be8f7363818b92d18e583dd586460ecb4e13e1f363dcdd242304b460420108,0x1c527459c4375944db745cf054f798d20c54e684ded8560c584dd2de4b310278b562d54b56,0x7151d4b7115ee20351d553c153de634989339a137b61597f31371d9127d1d3836b00ff03fcb742d7409e68ecb422d28b42,0x1684641167463814786361a405a10b19241160053319e86081cd0550157065c187c7341fb4690168490105a80f91e00739,0x1a4040414606901b915913b6057d15fc57f38b054b153854e15d86411c986b00ef40fc03f86901efc18403e457f1538daf,0x16846e456445ce19e4679172c65b196c6761c986b00f5c19c06745a1061018819e465b36c45a118e069015f454b1904690,0x1a4040436fd46105a41781a406e45644314160067a1a9867a1cd055019706a519707341f846411c986b027f831903f00fe1a407bf061031403e47801ce4a06,0x14bc60414bc64214b5178160052a178c734154052a17787341fbc64114ac5ff0adc46b367464214b41ac06d07801ce429b,0x1a4063b10006901661241160052b178c734154055517787341fa064114ac5ff0ee40fc03f8690166016a03e47801ce4dad]
def pgR9:Array Nat:=#[0x1474598490452b15fc57f14a454e153857a14ac5ff0ef80fc03f859805a80f915fc54e36c059f103069016005501904690,0x5188690069c63b063cdbb1a403141661241160037b14ac5e31cd05500d0c55517787341f9064127fc52b17fc32103f00fe1a4037c166016a03e47801ce4a0a,0x1a4063b4b2c68b1b9124115f467a178c679152c65c177865b19d06411c985ff0c900fc03f868b0d2c16a03e4679196ca0c1a40169063c31419e865c08f434b,0x1a404043f406d0166159115fc52b1a9873415385551a947341d8c71e14ac6b00ca819c0674690166018403e47801ce48c51a401a705e17ec1e0073909700c4,0x6c040018ec5981b4124114ac580178c73414a455017787341fa852b1c785ff0ef00fc03f85980c0016a03e47801ce4dae,0x3f241a6069c638145c63b1a2c5985fa9241160052b16005e31cd055014a455017787341f8c64114ac30917fc31a03f00fe1a2c5980c0016a03e47801ce4a08,0x16846381684690168440010a042810a042815fc679178c78010a054e196c5de1ce44291df471e1c985ff0a5842803f00fe,0x1674601167468d1675178160059d178c734154059e17787342f5068d16745ff0adc474132068d16741ac06d07801ce428f,0x608169653040018e06380c506d01b912410dec58019e85e31cd0343154065c17787341f949f51c7872617fc32203f00fe26482f10bc416a03e47801ce4a0b,0x168463816845e816845a7160052b17805e91540555176c5e81fb064114ac5ff0aac0fc03f868b168463817a07801ce4296,0x168463814786901685241160053415fc57f154054b153854e15d464116746360adc5801540690168416a03e457f153828e,0x518063818e068b1b91241160057d15fc57f154054b153854e15cc6411c985ff0c940fc03f868b0d2816a05bc57f1538a0d069816918e0314160055028409f6,0x8ab22d08a79da471a17d33c093dc6339889399537961457c50e4dd8b7089d2024c0057121dd9870a409e107d9fb6754a0f,0x5a118d840010b042c2d8057f14bc5ff10b054e156461910b077f1abc52f18d842c1e00739,0x16852ae10001820d5818f0ab852f14fc9071094b5f2d80425109457f14bc5ff1e00468109454e15646191ce47391094766,0x203c862a02f78302997854b726cb9b120a642990a64299306c2990a7d3560a7ccdc0a7d89b,0x7151e5379b92db6fb409e2ed4bb55f6d29f3bcd3cc243d2a52c88e514d849114a9cb2a139df1b70ac90f4a94b220518490,0x715dd4e02f0b722e38b8e3c193df636cb2439a537c617cb2c13c1d9222048582c90103040ddba02f009e2e398db617c858,0x58792c356d82cb44b958f0b2d3b45598b280b2d33054a4b2f13e82cb58b15b92ca01541c2c09e58792c302599f367208ee,0x167071e14ac63816705ff1094b5f0adc5a71a401a70910638068457f14ac78017fc4251e0054e155473917f04251ce4771,0x16706d03fe463b100040010b042c10b0a3115fc52b15fc5e310b054e155454e177842c1dd071e14ac29617fc42c03f00fe,0x16712ae10001820d2818f1094b5f28c44251b401a710009ad068457f14ac5e01e004251e0054e15545db1ce44251ce47591c7852b17fc9af1094a0203f00fe,0x80ea18980acb726cb1b157cf831374f40963ba93c66310b1c62b4e474d698482c798240e0df3f709dd392c709b602800a0,0x113e546913e43e0b075fe8ea646458c05fd4e0c446584c5f3c38a646197b74b8b09304d321,0x45214534521521452009643f162b5ff57fd3ac5193635d8d76244e11446985b616d7ee139592f664c8e023809bb051048e,0x3fdd92a51b8b172c5d4703add3b64e5d88b385d3324c1d7c713fd93366594712d2410b042d92a58a80965f958b560dc8ba,0x514d1481645453771114843f041f59497fd3ab13b146498c86240e0c4cb511961317e90e2592b2651991747c92f02880a2,0xff0514cff02c58b0b2e38c153280ca02c2cce5335cd872c80c17646912974bcb0b3054cd7,0x3f6192a58a8a6c57000962c58b165f6d5c43ac8f5b62c55692c8ce123d8183354b4b2b13a19303d6c8b9571cb23051c491,0x16846af1c9840416846b01a405a1019017817a05a11cd55911cd457f14c07801a987801cd054e15687391a947391cd0773,0x3fdd4533fdd4533fdc09643ed22b5fed7fb3ad13b363718dc6238e144cbd86061817df13c59326651e35696c9b80410104,0x3f615213f610fb48ad7fb3ab8f56633188d3838f5961417de0e3d92d3d59e2e258c0e812115210311e37031095b24dc996,0x16852ae100018209d018f1094b5f2d8042515f853114fc6f5109454d156c5621c644251bd471e17e85ff09c04251bd0718,0xfef862cfef09d9afb09d8ee446416ba09d8e3f445d77a09d96907824dce73c4b0209d8276,0x715df437d9503c72180d42edcbb75f950143bd13ce62cd0152d10e524d8d8354058b4c13a9f1c7d9c9104054b440524493,0x7395c8502f0b972e5cb9776e80bc0350b973b753d14f44b454f44e2f4d993662d3536613cdd9321f085a2d1485a0540497,0x66012c336e00d466012c30b2cb1751a40960b2d3b556e98a12d1c2cb4cc55bc6054b4f13f02cb66555ba242cb47055849a,0x17e86d03fe463910005a710b042c10b0a3115fc5cc1e005e010b054e1724739176c42c1dd471e17e824f17fc42c03f00fe,0x17e86cd17e85ab147853e1094b6a09c85a716005cc160053e1094550172455014f44251fb86d005a4272169c1a11e00739,0x17e90370fec1820d281ac1094b6a28c442516005cc14f85801094550172453a15404251f886cd17e853e26c8425067019d1b40169169c9ae06847801ce4a07,0x815a1498104b746c31afe3c0d3dd633cb37399937a614cb3f0e55e507d79c7e2cdc0eb1c19e510311c7f02599fc6758a11,0x168471e17c92ae10005fe06087bd23cc18f10a042810a042810b057f14cc780461c78010a054e1570739487073910a4767,0x1c74782c29a862202f0a6a0b271d090884e429a0a68c1c0a6829a0a802a033742a00a8189c,0x145c51700bc5171e78868d5434f40ef53bd55054d94e53394c4ed64edf6378d1adc052c495,0x1c7679fe19f4f513d44f513694da536913edf6978c9ae5042810a844206776d0efb3965f2e,0xbd02f402082f47815dc60bd13d44f513d40bd13694da536913ec2f47da5e366b9410a04280ba0bd02f40bd02f40bd02f4,0x1f407d01f41821ef418f1e6016905e034c10a042828b042c10b057f19e43f01e0078010a054e196c7391ce473910a475a1c787260fc098a262442803f00fe,0x1f54050208f4d3d342f5509964d6c7cfa23aa98b7634cf4e634ce0960e58573d3d857137d409667de393d39ad1050048b,0xf4001f42ec5760ff46c7ced643153d54f54e2442fd36a4da852363c998e78edaf3057415d,0x1f4f3f0badb217718f9c3b793d33cf53d338c13683cf936813e49a678e8f3d6b9015312642ea6630f4358f13af4cad98d,0x87b209902f1fef0d840b182cde778691fc23bad3c763159f86314e484d6d84967498490e11f197d7de3327f5abe02840a1,0x114554691454bacdd985bcea743218c16304e0d446184d613438c64697aa4a888fb3054302,0xfd8514cfd82c58b162e38eb03d698d62c84e103d7d85a2ca44e464b8f5a749cb21050c48d,0xfe45100fe43ad8f5e6388e163d8d86613f940d3d79c7b056070c2c5cb172e5cb482d40b48,0x1c4d76e0f4c76e0faa84fcef23da58d46350e503dad85861604e07cecf697499ad2050448c,0xfe13eaa1403da8ef73bdcf6c3954e5513bcf6a7485adf04081023da145c5170ed1387993c,0x7d014531ec54530c040bc514dfe93e9a1413ab495a3d558c96324e0d24d8f58613584d0e2d92c2654f557495ac5028c0a3,0x48a14286810eb562d13d238558364d9c4f55031a4d6b8c15212618ed025964662d1836666545302f0fa63d74f623d740bc,0x514d4537dad428590213a3abd3b24f293ca383d32e4d7935e0e4140b6649d336b280a4029145302f00bc6ad53b24cb886e,0xfed4b04dc676d4fed407cee5463d2815ab8e4044592855d3d69178217a9456c89d3010ccc,0x1ab440344dc42810a042815fc5cc1a9873415385c91a947341de071e16606b010a07801ce46ad068017110a07801ce4329,0x1a404043f4069016606941b405981a500f915fc5981a987801cd054e16646a51ce47341d7071e16606b0233c32a067019d1a401a705e00c45fac7801ce4254,0x1a404043f4071e14ac65010a042810a042311c847211c84721cd04c613184c613187342f4c690069c1780b2442811c84c6,0x1a404043f406d016606941abc5981a500f915fc5981a987340ecc54e16646a51cd03461d8471e16606b00ca88d0067019d1a4019905a872c03507801ce4259]
def pgR10:Array Nat:=#[0xa7a3ecd0283de51c43bf0f7a4538e5a1488f794ab5af2057015c63c06c557fd8bf6105941,0x268d5c24a8542b3eb9024504cf7247098d55050f74453185913854133dc92a46b501421c207931edc7cb26898ac608c90e,0x63a86807d7008036dd2c357c0f9f25a147c6288f4967d156763858163d299c954a986513f59213d2490c56edae7055c49b,0x1a1ca672a94fb50b3547c3df02cd55913cf3df82cd549d36413b0f7c0b355b76b6c101040496e7d2862e58e989f604d982,0x2a942cd51f02cd5594ef60b3552839504ee0b355b86b7814c1c25dac01f563a6281814660c79a4894fb53b54e233df496b,0x8431ff97f75e5c70f21a03bc13cb63418d0393935f61518540e59f2f70a1e306b3c0a5029619902f0096873d8d06151a56,0x7d259d2245755a933e718a329a0f41639181729a4f4261a052163aca683d05af1056c15b,0x78269e9d5b3e995f484c8f5c3acd8da6368f61384d85e61784eb3d71931748dad90528494,0x71400d60359d466fa1d3b50a0fa66ada1333aacf543aad8c66318e0b3d5ce0b612984a0e1940a3d5083374d9ac00388480,0xf345110fdd5110fdd8b18ea84f0d8c16304e1a4c8d84e6138c16646d128225c8fb3064cd6,0x1f471e1c9807d01f43f1517cffc044417810a042810a0a2c10b057f19e44660fc478010a054e196c47c1ce473910a4772,0x27ada986a7192766040b157e56487fc9b4b3b3d3ba63618d86360e1c4cf985c617185c139993a6671a6f6969ad6051448f,0x3da0a6f29b95f95921a953b4d3bb29c18e3388133f29c5867140193e6674a706ba41591c3593766600b126cd8b660e08bb,0x3580d627b1a717575e416af15f959222562574ecd4ee58ca632893b386933d613984e0e349ea64e599b7479ac70398482,0x144e513a02f5139c7584ecee73b68ee73b9ce0238b8e4c39303925e3998874a08fd3b9ce02,0x3599377d952a36fb40da50b5afc26cd0243b413cd62c91c36364e1d4d89834453585d13a54177da08d74a99ad80520492,0x501c08002f140702f00da517163e6c0098e3b493b063759f66374e1f4cb1861672d86113c993d664085921b1ae2053c496,0x76a1d48863942d79de13c3b38edc3bbceef386ce2e3930e4c0e454157d81d2a6b300e912180b10dbdd3f7330ece386ca0e,0x22ad8b4629f8982251895cee84f118c26308e444d5d84461102c27cadf5a74d1ab3017805e,0x3ca10df3fb55e5586c8ca2bfcafd2bf40394fd0fed02a80f12bf4c0e3024c095a5d6973024cce3304cc15bf56fd330582a,0x41b50df42e0afe2bf0afc4fd0fed02b4afc303cc0a3028ac03028ccf3310cc42b80cc460b991665e5a1a00e433362f982f,0xf2863f595d4380f95108502d3fb50434a24c0d3018c443034c0d3334cbe3404ccd3335826,0x649543f587c2b20ac42e45010f3c01702b25004f360b900aa2c3d51444ad6840ac96990ac955146896f60ac96fd0ac982b,0x210e2e8cba3811a0202e8cca43290abe3290d853614ade361582d43894e900ec33243b90e5,0x64942b20ac52ff37a02b25004f3602acb0e5e457ab0ac8abf0ac981a60842b22b7c2b260b545266107f801702e362a9821,0x1c547539c44796e1184a38b760439b132dd9ba06e1db928048b766f65bc96f360162dd9b79,0x3f590df3f58b762bf0afc7ce1979686803922c8fd60298afc232cc81301cc072af18bd301cd5132fccbf2b7182832fd827,0x1c5743854e82e88ba25f51c8570b80582e89b9d6e1da1d2e890396f5dbc90160ba20161b79,0x450d0df450cb782bf4afd22cd14302b8afd3234c0b302d4fa302cd5c3314cc553e0cc560c5e4e3cc08d100e489b5a75703,0x97403904ed0ce70c10ce0b54f950b542564fd4f850b540a922d02d530202d50958c8309582d533002d50958d530959829,0x210f814603682c20a1899a07f80f405f8274c7b31ecc7b31ecc7b3534d4d3534d4d353580f,0x190b5831651542912200a966359a4c4531156c05b34d0234099ae40b102c5f2926c37bce98,0x190b43754e657b56337ba1662599d66231ed6be5b2d6be35359c7513196e017c82a59896be,0xa4d415d23b3c80fd55f30c2754c4c4808d0ceb55c8d0a08d133954895a900c9976309cceb,0x1cae7531cab820197d6a00b992e64b992e65bb66eddb92804cb996f7dbe06f360152e79b79,0x579d29d4b1cb1a0b8923f64d42e256fc098579c0a84b1c9612610c230b891622af4a050b88ce70b891ea2b749ce0b89337,0x64a529e52143080b9904764a40b052148eb30a42e64c3d1000b98ced0b993a643fc2e64cf00fb0b9946c02608eb5a79706,0x3229412796c196014078f2664552c058ccc47311d159321d66b341cd074760d575b3d338,0x1cb84b012c08301cb64079f1f017d2c021a0c7b41a515531ed6673535068474cd4d5b2d326,0x6901a4063c1a406a817a047111c447111c44c513144c5131444d1abc2be1a585e811c44c5,0x5841aa069311c447111c44c513144c511485fa1a4c6a811c44c516845aa17a047113146af,0x1a4069051fd95705a416a17a06a81a4c73511c447111c439911c44c513144c50cb04c510d06af09b869309b873511c44c5,0x69016b058417a059816b847111c447111c44c513144c513144471abc59816b873511c44c5,0x59f16605a611c447111c44c513144c5114059816985e811c44c5167c5a917a047113146af,0x6560690069c5ac0610f8117a032016605ae11c439911c447111c44c50cb04c513144c510f06af237059816b873511c44c5,0x1a405ac40e85e71aa05ae11c447111c447113144c513144c5110068b08cc5ae1aa0471131469005a41841aa04711314233,0x1a406903f385e8166069311c447111c447113144c513144c511146af16606931cd44711314690069c16a1cd44711314251,0x58717a058211c452611c44c515444c50f3caac1608a2c0f803ea,0x1a43c285ac16605e816b847111c447111c44c513144c5131444c16602ac16b873511c44c5,0x3f281a6069c5aa3c205ac17a059817a05ae11c447111c447111c44c513144c513144c510d468b16602ac16b873511c44c5,0x5fa16a85aa10a04280f1847111c447111c44c513144c5131444a1abc5fa0fec42811c44c5,0x18f916a85aa17a06a816b847111c454411c44c5131456813143cd2a64a7e16b8a2c0f803ea,0x58617a06a811c447111c44c513144c50f38a9c2a14a2c0f803ea16a858616b84711314a84,0x608169653504016a85aa08905e81aa05ae11c447111c447111c44c513144c513144c510f48420ab82bd16b873511c44c5,0x5fa18d05fa17a06a8189047111c447111c44c513144c51314bd71a2c5fa18d073511c44c5,0x51205aa16a85e8179c5a611c447111c447113144c513144c5110468b0af45a617a047113141a605a45aa17a0399088c843,0x22ae8ae2294441d5015fe4c7f31fcc7f2ff8d463518d46351839a21008410888afa2ff8d46,0x73b1c8502fcb9144c8b91777909177b54f56ed91336e217f604d0d7646c4d76340011b5c8df3c027c0bf5f888c27a7170e,0x1c57722dc2f2ea8baa0989d9d71890492ea8c7831e0c786a80c786f5dbc96f1cbaa00f9b76,0x649543f587104841200574bf4de6015c0575271073247091368ad2f33780c784109aa067ad54c46796db3a78aca00f8cd0,0x7391c847204b732cc00d5778085121454f46e7db8f6e20b7304ccd7435d0d742b641195c89e58027dc8a68cc8e75fdd718,0x172069017206901b914731abc5c8063c0f911c447111c447111c44c513144c513144c511d069e17210310ae089011d04c8,0x1a4069018f06901b914731abc7bc063c0f91a783590ad03bd288447111c447111c4471068c4c513144c513144c506884b6,0x16106e451cc5fa063c18817202b50f5ca3c11c447111c4471068c4c513144c513141a21c505a116a86901abc69e11c44c5]
def pgR11:Array Nat:=#[0x1a4069051fd95905a416a1a406e451cc31d1abc7bc063c31d03e469e0d382b024a431924a847111c44710da447111c41a313144c5131432b13144c5068849c,0x1a405ac3e0469016610191abc59805e00f91a7859640c02b7236847111c447111c4471328c4c513144c513144c512b84ae,0x1a405ac161069016610191abc59805e00f91a785960aec3b9287447111c447111c4471068c4c513144c513144c506884ac,0x167c598406459805e00f916582bc0ef89ac11c447111c4471059c4c513144c5131416512f459f16a46901abc69e11c44c5,0x6568690069c5ac0610f811a4031d16610191abc0c5166017803e469e25045960ac032124ac4710da447111c447111c41a3131432b13144c513144c506884a2,0x1a405ac40e868b1b910191a2c35105e00f91a2823a08c832424b047111c447111c447106044c513144c513144c505f44a81a40169061031d0c7423211c44c5,0x69018d051a17a0598189069016605ab1cd447111c447111c447413144c513144c51320474,0x1a40634146869016605ab1b405981890b961a7859618ec893094047111c44710afc471068c4c513144c50ae84c506884ba,0x1a406903f386d016614731abc598063c0f91a78596094c32a22e047111c447111c4471068c4c513144c513144c506887111a401a705a97f2145425311c44c5,0x5871b245822ab058203cc304160451f29fc471314447128f81a31314d2b1314a4206884c2,0x690f0b16b05981b41019166030505e00f91658215083c3bc287c47111c447111c4471068c4c513144c513144c506884b3,0x3f2c1a6069c5aa3c205ac1a2c5980c750191a2c5980c1417803e468a1658215084031a26f047111c447111c447111c41a313144c513144c513144c506884a0,0x5fa18e051e5140ff22a446d01b905a72e2047111c4471328847113144c51314d84131444e,0x17205aa16a86d01b910191a785c805e00f91a785c840282b724c447111c447111c447111c44c513144c513144c51314436,0x17e85aa16a842810a03c61a785c8095c32311c447111c4471068c4c513144c513141a21c5c6af17e83fb10a08a311c44c5,0x5c81b406e4102c40b03cc47111c447128f84c513144c5290847316a85aa406440b11cc4c7,0x63e85aa16a86d01b910192a64a7e2a0c0f3086823a40483bb29e447111c4c5511c4a3e068c4c51314d2d1314a4206884b0,0x16186d01b90a9c2a140f31a785c81054a5711c447111c4a3e068c4c513144c529081a21c585aa161901905e025311c44c5,0x608169653904116a85aa0c746d01b9101926402f20bc817803e48b5086822c084032222d847111c447111c447111c41a313144c513144c513144c506884a4,0x17205aa16a868b1b914731a2c5c8063c0f91a285c816a82b7248047111c447111c447111b04c513144c513144c512fc46c,0x17e863414685e81b905a71a2c5fa18d05e81a285c817505e8225047111c447111c4471059c4c513144c513144c505944b8,0x51205aa16a868b1b910191a2c35005e016f1a2834e083c325225847111c447111c4471059c4c513144c513144c505944aa069816916a831d27048950da432b,0x8abe2b98a55ee57b9dc8c783dcdb0c6c41e773dc9d7f9096426f8c7f31fcc7f30bcc2f1d08d503540d5033f4cfd037c398,0x5c818e05c810b042c0f186d01b904002e2847111c44712b10ca113144c51314ae31ce0449,0x6081691eb840018e063810b042c10b0b6124786d01b9063b10b047111c447111c4ac41bb44c513144c51314ae31bf04b5,0x212481a20302ebcbaf6c05e4a79b5a225f54c843210c8459f567d352cd4b352daa2352c3a2,0x10af2aa10af2ef162551adb9d42bd53e2ef0d6141e157e5c74d8976cc2e54b20bbc62a42e5,0x791df3703552c84b212c82ee16245f6904677709852621a2468f0c905858986458d69f1d34d61586098747b171404fc502,0x5c8102c40b10b042c0fec47111c43dc2b104c513143e82b8c4531a785c8100042811c44c5,0x17206d01b90638172016a10b042c0684b611a785c825944000adc47111c447111c4ac411c44c513144c51314ae31314437,0x5c5101040010b042c0f1847111c43dc2b104c513143e82b8c4721b406e4100042c11c84c6,0x576c6d001bc63818e040010b042c10b03c60b4c23b24f863b10b047111c42bf11c4ac4068c4c513142ba1314ae306884b2,0x6081691eb89761b406e4100063818e016a10b042c10b01a12d849d20b4c23b25d063b10b047111c447111c44712b101a313144c513144c51314ae306884a5,0x8495e5679c606880c009f2ee0bb81cbdb02776dca1274dfa668e4c84321169832116981d18d5435516fe35516fe038c3a1,0x5c516a851a10b042c0fec6d01b903fb2e2047111c44712b1047113144c51314ae31314be5,0x15d216a806f0f303cc0f30a9929f8a840f3047111c4c5528943d813144c534b4a270f88472,0x6081691b7500d16a85aa10b042c10b0b6024586d01b905ae10b047111c447111c4ac41cfc4c513144c51314ae31cd8472,0x2117811201e2ed8bb6015df267d5da2368b8c883220c882ae989d3528d4a3528ad2603180d,0x7d2de4d027caa840d90362ed998b5f6524077748e423914db68e1ba05edde9554f8bb604d4d775bdd6f755fcada0470d24,0x63d86d001bc4010fec3fb10b042c10b03fb0b5022f238825610b047111c44710f64ac4068c4c513144c50f94ae306884c0,0x5c818e05c810a042810a069e1720a9110a047111c447110a047113144c5131442913146f4,0x17205aa16a842c10b0b601a785c840242b711c447111c4ac411c44c513144c52b8c4c510e06d01b9017806849320ea033d,0x5c80f2c3cb11c447128944c51314a2711cc40b102c1a1102c40b16a85aa0f2c473131c40b,0x63d85aa01bc3cc0f303cc0b5023c40443cc11c44713154a25068c4c51314d2d289c1a212c4a9929f81780684a6b0fc43f3,0x6081691eb900e16a85aa10b042c10b0b6022dc2d408b025610b047111c447111c4ac4068c4c513144c51314ae306884a625dc6d01b9017806849750dd033a,0x849a0488088bb62ed80577751c9e695da2e3220c883220aba1d28d4a3528d4a2b480e70ea9f277d602a91cac9c2246491b,0x69010105181b406a817a06900af86c117a047111c447111c446c13144c513144c512fc46c,0x5a11aa06a816846a31aa067819e047119e065a19684c5196865a168463817a069011c44c5,0x1a4040436fd95b05a417817a06a856447351a402bd1a8c8db1cd447111c447111d047111d04c513144c513204c51320474,0x69018ec40017a05984904690166063b1cd447111c447111c447413144c513144c51320474,0x51d16605e816605d417a046c11c446c11b04bf13144bf12fc46c167c40c17a069011c44c5,0x6570690069c63b063cdbb17a03b516612411a40949166063b1cd44710ec047111c447111d04c50d104c513144c51320474,0x1a4063b4b2c5e71aa12411a2c23318ec6a811b447111c446d11b44c313144c5130c4c311b469005a418f1aa023311c44c5,0x1a404043f405e816615911a405981a8c73511c447111c44711bd44c513144c513147191bd4690069c1781cd48dd11c44c5,0x1a4100063b16605e849045980ab063b1cd447111c447111c447413144c513144c51320474,0x3f301a6069c638145c63b17a059817a12411a2c5980ab063b1cd447111c447111c447111d04c513144c513144c51320474,0x5a118e05a110a042810a0690168440010a047111c447110a047113144c513144291314be6,0x608169653c40018e06380ed45e81aa1241245c2ae0af463b1cd447111c447111c447111d04c513144c513144c51320474,0x5a110105a117a06a816ac68b16846381cd447111c447111c447413144c513144c51320474,0x512063818e05e8179c5e81a2c2bd17505e815f846c15f846c11b054d12fc54d12fc4bf11b01a605a463817a091811b04bf,0x22b08b4a2a04421502015c912245491d68bcc8c3230c8c5a6d9ef3528d4a35296dc60399c3,0x71b1d4c02fdf3c03540bf2e60f772e617e877588c37e648c353f5bb63749b927a74b9804d8d7839d8d785c3d7190474d25,0x1c52699dc45323cc8f323cd603580d605f20bbc2ef009f690da4276984ca754c31f0c79a42,0x7151d4b7115ee30355d56775c9f37e88da5323cc8f323d7f403fcd603580d6062480ff1404b752d7809f69054fb53fd4fb]
def pgR12:Array Nat:=#[0x172040414706901b9159111c447111c447113144c513144c511d06901f0018403e4474132068a17206c20b1c4741320892,0x1a4040414606901b915911a2835f1b043bd11c447111c4471059c4c513144c5131416512dc6901f0018403e4da813604d0,0x16846e456445c81a8c3d711c447111c418113144c5131417d1c545a1061018836a84da134c5a118e06901a284711314690,0x1a4040436fd46305a41781a406e4564431d1a283551a8c9df0c6447111c44710dec47106bc4c513144c50d0c4c506b449d1a407c0061031d03e49cc0db432e,0x1a4063b147069016612411a2859618ec2c511c447111c447132c44c513144c513144af12bc690166016a03e49d50e94336,0x1a4063b100069016612411a2859618ec3b911c447111c447106bc4c513144c513141ad12b4690166016a03e4da613544cb,0x1474598490459617503be11c447111c416713144c5131416512f859805a80f936a44d9134859f10306901a284711314690,0x5190690069c63b063cdbb1a4031d16612411a289e1165863b0c844710dec47111c447106bc4c50d0c4c513144c506b44a31a40337166016a03e49d40dcc335,0x1a4063b4b2c68b1b912411a2823d18ec32411c447111c447106044c513144c5131417d12a468b0d4416a03e49db0ddc3411a40169063c31d08f44711314351,0x1a404043f406d016615911a785961a8c32a11c447111c4471068c4c513144c513141a21c48690166018403e48c70df83461a401a705e17f1097047113140c5,0x6c040018ec5981b41241165830918ec3bc11c447111c447106bc4c513144c513141ad12d05980c1416a03e4da7135c4cf,0x3f341a6069c638145c63b1a2c5985fbd2411a285960c2463b0c6847111c447111c447106bc4c513144c513144c506b44a11a2c5980c1416a03e49d10dc4331,0x16846381684690168440010a042810a04280b4425818ec8a40ed847111c447111c4428068c4c513144c5131442906884c1,0x5a118e05a11a405a1169c69e17204002e2847111c447111c447113144c513144c513146f5,0x172063817206d01b912411a785c810002b711c447111c447111c44c513144c513144c510e42f20bc816a03e49660ea033d,0x608169654040018e06380c746d01b91241277821e08f463b0c8847111c447111c447106bc4c513144c513144c506b44a7264c2f20bc816a03e49d80dd033a,0x168463816845e816845a71a2836017505e811c447111c447106bc4c513144c513141ad12e468b168463817a09230afc2ba,0x1720404172068b1b915911a285c818e02b715f846c15f846c11b054d12fc54d12fc4bf11b068b0d7018403e492211b04bf,0x518063818e068b1b912411a28355175032511c447111c4471059c4c513144c5131416512ac68b0d4016a05bc9dc0de0342069816918e031d278037b0d0c9f9,0x8ac62d38a85da571a40577735c9c7e5c9143230c8c323169b1f70d4a3528d4a5b700ea0ebdd8e709009f0aa4a1b246891b,0x59c102c3fb10b042c0fec47111c43d92b104c513143e52b8c4721b40596100042c11c84c6,0x1670a980fec1820d7418f10b042c0fec42c11c44710f6439c2b104c513143e509acae311c86d01658400236442c11c84c6,0x203782520232ed80436c98c813204c812ae4d483520d482b2d8087c8507574ada2c6261807,0x1c544b712b52ee4bb94aa9e5b80e52aa2ee5ba06e1d1722ee43496f65bc947d4bb90d24520,0x7151e5479bd2dc6fb809f2ed8bb65f852a07741ca3279da2668d5ba06e1de9745c8bb604acd6835a170747b8ad60518d1c,0x715dd4e02fcb732e44b917760880214d4f36e75b826e48b7304c0d7035c0d702b601153481dbb02fc09f2e448536ec8d70,0x58812c556f42d244c15900b4908653654f60b4913a54f4b7304242d233d157b2b6c109132409f58812c502608ef7a516ee,0x167063b10004252d7ca311b401a710001a111c447111c44250e7c4c513144c5109424a11d069e0af463b109488d11d04c8,0x16706d03fe863b100040010b042c10b0a310c2c35a20f863b10b047111c42bf11c4ac4068c4c513142ba1314ae306884bb,0x16712ae10001820d4018f1094b5f28c44251b401a710009b0068430a0d3c5d42690425273c47111c44710db04250dc01a313144c5131432d1094330068849e,0x80ce18c80b0b736cb5b167d0431c74f8098778c8647e954f226fcc813204c812ae494c1d0cd513544d512b50955038039b,0x1149515514943f80435ff93fe41c9dc368b4c253094c855a693ad3348cd235216d64c6d31c,0x45254554525522452409843f962e5ff97fe52a5082237c8df68f55224525b996ec57f704a4cef33bcd6635997150440d1b,0x3fe193451bcb192c6547252b908922f9a405e717bb4c2d7f704e0cf733dd3985c6c11f5c9593458b40985f988be7a6970b,0x51551491649455771514943f8420594d7fe529099a41fdf9668e8c252528c25321569a1d1cce92544ce935556ff03903a3,0xfd95154fd943d50625fe550b4189e2d2becc27309cc892ffcbff32f0cbc3518d4632f03ac,0x3f6593458b4a6d57040982c60b185f855c552a908322f14dc68d95223ea1e9854fcb9104b0cf033c17085600ad70448d1d,0x52f101051c17a06a8564455017206c21cd447111c447111c41a313144c513144c5068815f,0x15644041564660156417517a06e45644735154065c1a8c7d01cd447111c44713140471068c4c513146b804344c5068848a,0x1c5d6a1dc5f44255035ffdba06eddba15fe1bd96f81bda5fe1b7a76ce03e57197ff8052017,0x1684404168469016841b317a06e4564473511c447111c447411c44c513144c513204c511d069016846a3017c73511d04c8,0x3fe14553fe14553fe009843f522c5ff17fc52ac8702151a5d68dcc2c30b0c986da4c311d50cf233c8d716f14cff053850a,0x3f655223f650fd48b17fc529899c77ada32309cc273224c301d2cceb33acd5933f80e80ead5220315e38031499d309cceb,0x17e92ae100018209d418f10b042c28c442c1b405c8169c27110b047111c447111d0ac411c44c513144c51320ae31314474,0x1144863514409dcbac09ddf223ccdd2c5f38c8d3044c8d09dc2773570cd3357027709dd9cf,0x1c5340f50322eecbbb4061db380fc3482eedb9d6e1d03d2eed89e35a8d6a3a6571f0d20d8b,0x715df447d9903d721c0d52ee0bb85f990177745ca427a49e868f8c94325094d37c16a01d44d6a35a89583a657160524506,0x7395c8502fcb982e60b9876ec0bf0354b98777c87b21594fc2159b9d6e41b882e61bb304c8d7335ccd735c5cd730460d22,0x14bd4b48a925798bbd40314bd6e1d16f2ef54a135ed1e95c90d8c0b59c714b14bbd62902d6,0x66152c536e80d566152c50b48b1951a80980b49087687c97f53f82d230b553625e55001d582d233d557c25ed4fe055850c,0x17e86d03fe863910005a710b042c10b0a310c3c5c8093c5d410b047111c447111c4ac4068c4c513144c51314ae306884bc,0x17e85ae0fec4252da8a3111c447111c442513144c513144251bd46d005a45a70684471131469d17205ae10946f51c64272,0x17e90370fec1820d401ac1094b6a28c44250c385c816989ab109447111c44710df442506bc4c513144c50d1442506b470e1b40169169c9b106849d011c44c5,0x815e14a8108b756c35aff7791ca07e9d4f73234c8d32354f91f74d5c3570d5c53dc0eb0ec5e520315c8002609e35a71702,0x1720a990ff4182093818f10a042828b042c11c44710ff44742b104c513143fd1320ae311d02ae17203fd093842c11d04c8,0x1cba826803682d1e7c8694c823208c823208d47351cd47351d9bb774d0760e7888f6798d90,0x145e51780bf5179e7b86994b32519eb6733cc4b3258c9632587533458d6d35b4d6d052c508,0x1c777a0e1a17299dee780cc993264c991d54d7a35e8d7a055450b844606876d9dd93264d7a,0xbd82f6020c2f67815dc60bd9ca677c1e030bd8c993264c9904282f635e8d7a35e810a142c0bb0bd82f60bd82f60bd82f6,0x1fc07f01fc1821ef818f1e6416905e035310a042828b042c10b030c0d3c2b0262c98c10b047111c4a3e0db43702b101a313144c5290832e0cc0ae3068849f,0x1fd406020cf513d442f7509d64e6c7cfa3528892577c507d7f3d4275f09ba13e8daef049cce45c34d624698d620500d1a,0x1a853e005126c9da733ee14b76a250946cadbb569d0fb86bbdb9c35e4d7946ccd793504d41,0xf4501fc2ef5764ff56c7c9a741eddf37810c4e44b4c9d327476534a11a53604d81058c525,0x1fcf440bb9b217718f9d2695df241e5e026ed5ba13e75aee04dcd7935e51a335e411e34982ed663cf4658f498d5ee187e]
def pgR13:Array Nat:=#[0x87ae09b02fdff00d000b582d5e79869dfc6773894277bc9cb7f10c823208c822538c821d10d523548d522558d52038439d,0x145551540365154fa8850949741b1a25223cc263098c86321830732f4cbd351cd4760183a6,0xfd95154fd92c60b182e454a84205f9d68d0c2a30a8c922aec74f33b8cee3594ad5050c504,0xfe55104fe552b50887e78c2e30b8c9b1f80cf633d8d7d056050e2c64b192e61a3f5a8571a,0x1c4e76e4f5076e4fac850dde24235f9c7f40c9130ccc91324474e358cd0d358cd630504503,0xfe23eb21444239cbf7344c35325cc9715c4d0f35bcd6f05345093dc145e51794b43130d17,0x7d094551ecd4550c180bf5155fec3ea2145529499b4201f9b7f20c26252cc263218c861d20cea2548cea3558d5603943a4,0x48a542a68154ac683de0150a9a456bb810533cd70a35d411a348d8ee026164722f57bd5c2945502fcfa84214fa833cc0bf,0x51554557db142a590a13d529c86f7e81dfe30a0c283228c8a0290cec33b0d5a35680a40eb545502fc0bf6ae086f30a0cec,0x141a50c1cc15071cc36c294306e25aed6edd4386f29af06f81b781338f7b3ee4f8a3ee4fc3,0x1c492a895cd76dcf9551e5d8c41c127d2274c8e3030c0c3238c0c3574cc63318d5d3319832,0x1a404043f405e816606941a405981a5073511c447111c44711bd44c513144c513147191bd4690069c1781cd432811c44c5,0x1a404043f4069016606941b405981a500f91a785961a8c8cd0ca847111c44710df8471068c4c513144c50e5c4c5068870f1a401a705e00c55fc025411c44c5,0x1a404013f385e8166069411c447111c447113144c513144c511086af166069410884711314690066416a1cd447113142c8,0x1a404043f406d016606941abc5981a500f91a785961a8c32a233847111c447111c4471068c4c513144c513144c506887101a4019905a872d035425b11c44c5,0xa7c3edd02942584d46ca0fb745d1aef5accd2947c0d801350d82,0x20314b252c96c71af9409549e41d03476cd5b9d6e1d1726bbd6863590d6447b4d640d1cd8a,0xa7b3ed102942550d27348fb445d1bb80584d2747c0d80058172a63c46c65800dab5e8d727,0x26a55c34aa142c3ec102552c10904341fd150b0fb045c9bb804a155746c11ed359010f5c787941ee07cc26a09aa7a596fa,0x1c590204f4b6ca0fa06c01bb63e81b926bbcd7c338cd7c35f0da4527cf8981bdb4a67dc2f3,0x63b06817d7408136e52c557c8fa025cd47d25f507c26014da7f61680308097a54dcc9a1d5d6ef338c97c55f4d7c055c50d,0x1a20a6a2a98fb60b5d47d42482d7535ddff3ed82d754f5bb804b8d1f0b5d57935b01135c809817d3062f58ec8af5ed96ec,0x2a982d751f42d75361cd00b5d53d6e2c12f0b5d57a35b81145c85dad01fd63b25f97b65bb479b489cfb6424cfb646c8978,0x8435ffa7f79e6170f61a27769ca277b1fcd3238c8e3238c8e0294d5d3574d5d35740a50eca19a02fc0988741a553238d5d,0x7f25c52265759a943e7492425c907a7f6d6815a0512c32707645bc16f04690d7f0588524,0x78369edd5c3ea15f684dd08420d9f9a7f54c2b30acc95325475233c4cf135acd6b0528507,0x71440d80361d476fa5d3c50a8fa86ae6138528d07e20d5fa37f14c243090c24320cc831d14ce833a0ce8354cd5303883a0,0x1720638172042c10b0a311a785c81000b101b406e4169c1a101a047111c44712b1047113584c513144c52b8c7131388432,0x5c818e05c81b406e4169c78f17204001ca447111c447111c447113144c513144c51314446,0x5c80f283ca1a785c80f2847111c447111c44c513144c5131444f18e05c80f2840011c44c5,0x1720638172033b0ce12dd1b406e4169c0f91a785c8100005d1ca447111c44710d4847111c44c513144c50ce04c5131443a,0x5c516a85aa11c447111c44c513144c52fa06ca10b03fb105041a1a3c5a00fec4711314086,0x17145aa16a842c10b0a311a745c50fecb1111c447111c4ac411c44c513144c52b8c4c510f86d01b905a7068405d11c44c5,0x172040b102c69d17143fb1a785c810017d611c44710f7047111c44c513143e813144c5110c69e172040003e406811c44c5,0x5c816c05b010a042810a069e17203fc10a047111c447110a047113144c51314429131444b,0x5c8102c40b1a785c80fec47111c43d911c44c513143e5131445110a04280f1842810a0429,0x172040b102c42810a0a2c1a785c8294442865019a105e0bbf018047111c4a3e10a047113584c51314a4210a44c5138c433,0x5c818e05c810a042810a078e172063110a047111c447110a047113144c513144291314448,0x5c516a85aa1a745c50f1447111c447111c44c513144c5131445410a042810a042810a0429,0x172033b0ce063817200f610a04282f004281a785c800e063110a047111c435211c442811c44c513143381314429131443b,0x5c810a042811c447111c44c513144c52f9c78e102ca2c0f843eb18e05c810a0471131407a,0x172040b102c42810a0a2c1a785c8299842811c447128f847111c44c51314a4213144c510fc69e172017810a003811c44c5,0x1720638172042c10b04281a785c849e842811c447111c4ac411c44c513144c52b8c4c5111069e17200f610a006011c44c5,0x108c53110b957ed64a896033b0ce21ee8990c4630c8c87321c3523414d03355cd570ce03a9,0x5c8102c40b10a042828b0550172040b10b047111c43db2b101a313144c50f9cae3068815e,0x1fc07f01fd56246fc17510a042828b042c154065c1f407d110b047111c4a3e313cac4068c4c513143f50430ae30688489,0x1cb06a19a7e6ca1b2a7fcdbb66edda756bbcd67359cd67359cda3821e04f6871b4a6efcda3,0x1fc07f01fd4c542ec1b310a042828b042c11c447128f84742b104c51314a421320ae311d030d0d6c4cd043042c1d04737,0x27bda996a7592866180b557ed64a7fd1b4c20f087d2149a5c7f4cc4a30d0c936da0c931d40d143438d676f10d670514505,0x3dc0a7329c95fb5929a9652d908f22fdfda5e7d7bf6a35bb804e4d19344170c35f81205c9993866680b527008bf7a6d70c,0x3600d827c1a727579e426b095fb592a259275c9d92759f957f24c323118c32321cc871d24d033414d03355cd5703983a7,0x596a0e04c50bde7a86a149d41ddd29247cc49322cc8b322cea93378d4c3530d4c3810e03,0x3619387d992a96fb80dc50bdafc270102552c9ca523610d17f5142f6e41e9945c9aef04b4d1535a570947bcd690520d1e,0x502008102fd40802fc0dc517963f6c0098f52d486d215486d7f5d5265ee5b926da9aef04c4d183388d723388d72045cd21,0x76a5d49863d42f79e613e52c49437301cce3124c8b322cc8b15bcd0b356cd5b356c0e90eb80b50cbdd4073349dd2540957,0x22b28b522a289862528969dd5727dfa17ef0c7b31ecc7b31ec73e3534d4d3534d4d01ac2c4,0x5e49204677d2ef3ebd2045e9cde14704c5d1e348b04811f031bc94c93dd95a05d08c405bc979203299df27e0ec922c16f2,0x649920b68815f33ec530d6404ecb43b4c636070f7854ad3602f359260341a2027ececb607012522c520b7b6c12560708b1,0x1c6a47fd1fc8560f9347fe1073e4d2078bb0d4e3c7d59a5cbd72f7c7406547f086821a96cc,0x190b487521d4e10e7c3a71494419d0e332ad54646611c93524bf0,0x190b5115877487521d01954203e4d72b3a714203e4d72b439a09f4e2ce8a20c526a3658d96,0x138f48115864e39afd481138d6f842da6f5538c31711c03170c5c5bcc4d148697555bcced4,0x546520456192ea6be920466b0c5c4700c5c1ce89824811f021d3132934300a734f8c3f260d6f103292185cc8ec35bc59cc,0x511d20b539d447716d9e261b8c6243b0c624ca934202bcd402f3181b03412195cf8ec76740124260920b7efc1244ca981b]
def pgR14:Array Nat:=#[0xfe647fcfe68558f9347fe1063e4d2078bf8d393c7d27134e4d397aa806547e572c5cb19b9,0x642d2fb37957a45f0cb534fc0f242d4c02a60018052d516a43a693f13c94b5437c4a1c00a90dd539873062511cd6001152,0x3ca10df3fb54223e55b3f4fe8f2a43a96ab4fd0f95185daa700c93fb3cad0e45cfd68722793f43fb45fd6aa08ac22b0032,0x190b47e11f857b563347fd4ca43040500dd5545465d1d10a516da6431974474490467b8032,0x642d4435ea11f847e07f65080f937b4d1ff541d11f1bc50e832d13ed3c858035b4d74431053ed3c8488349d9ac43104032,0x642d0dd53995ed58cdf074bc8dde6924cb25b156d45b5174830dd3ee3c891566b24c3700c944c65b86167be46f05b5085e,0x448d1fa450d2e93761200544512669296af5441125485574d5a5150c426062b6ab48a600c950c3e547f77ebc03222888a2,0x167463a14706603dfc63310a442910a41a11c7859d18dc05d107046d0124c6811b4ac311b576515700495ca44291c6046d,0x17185d7171842910a44291c7859d18dc41c11b40491a98ac311b46b2157004910a471811b471e1674637068406830e4718,0x16746371674428167466a0abc59d18dc42811b459d1a9842815c184315706261c6071811b419f167463710a00f019c8718,0x5a118e051e19805c818cc42910a4429109047211c847211b44245d957661864d4e10a4472,0x167463a1470b6c1090b60069859d18dc1a1197459d18dc42423c046d314cc68109036811b465d157061910907181c6046d,0x167463a1470b7c10905af1c7859d19b042411b4598181c42411b5765157063a109071811b41820d6063a068427f11b4718,0xfdb4b54dc282d8f93407a1bd08fd2b78278c6e377927331b83667abce8b495574000c8c36,0x17e861c17e869017e861a10a442910a442911c847211c8472109068e17e11f10ae842911c869017e8178211442911c80fe,0x17dc61d17dcb6b109056b06245f718701a111b4c5331a44240d9c68c05a461c0c609b9067065d170d1f1109071811b47181a305f705e0424272446d28480fe,0x17dc61b17dcb6b1090b5c11b4c53194c4241a401691a60282067069017dc61b10902bf09f0662170c66f109046d1c64718,0x17d061d17d042910a44291abc5f4187042911c447111c442411c46ae170d1f110a471811d06af17d017810a427b11c40fe,0x17dc61d17dcb7b109056b11b5136199c4241abc19919b031806706ae170d3a8109046d1c606af17dc184109046d284c1ad060834d18741a111b49f71c60a14,0x44f11ff44f20ae375d1ff31b8dde4768c6e7c5858b47e5ef9025dda344796d15d00c365b45d9644792756af4c362208032,0x11bb47711bb57d56344800eb930159e95abd9024c692135d156924fd8f2c49ec89d301531a,0x5438fed17c11dc47dcfed50a5df83fb52003ae4032377d9e95abd40e227cf2c484d7455a493f6265cfed18adaa92298032,0xfdc2948fdc50a4f9551e4c213000c0031f0ce63328cca357cc384fd8f2e49ec89d3000cca,0x44f51dc44f5434376139b3ae123043a96ab5041124562174a5a213f644f46bd6aac8ac00c93f616311fa6a9c0322284998,0x16706021670b7b109054611b45324ef04241abc59c1f3427f11b4550184866e109046d1c641821670602068446d09fc739,0x23045f0fea82bc23045f0291447d1d00a45f2509051d023ecc183934230455d8520a44032,0x16705d916705e810a056c11c46781a9cac41ac86124ea071859606ad167018410a047106b46ad167061d10a04710ae827e,0x16705d91671105109056a11b53bd199c4241ac86124ea042411b46ad16701ac109046d06b46ad05c07d4109019c1c60a18060859c1f501a111b47182858a19,0x3fa90de3faa1543fa99e031c122f53a8c707afcf23601174e3109d973c8d1576b38c4200c9eb917bd2077b4c0976010885,0x145d478558450b9e80561142e7b3158588a54187ac55895d7575d50603631af9add6df8495,0x11fb7a0539c7b354df8bc9eb2562975f5d7dc2c1af9ae66e0065984491fb7671d9c7689d95,0x7d1c23278a1fe200a8616766d63308c9fad766d7ae08c9f838825d9f5b4823221817415d05d8a0d895ab2181abf6dbc032,0xfde47894d550a4fa7480cc2130851e431f14123d996e75d6cc3a5048f664a55ad530e8060,0x1140433d5634bb0dda678551544bd8115d8151544bd1606ba00603088c2243acc7e310cc43,0x1c4f480d5d07670fab480dd9c3ead20a888dda13db96e65d6975a7650f6e4a51ad36dec060,0x15413eace963ead0d487d8f6f5ba175e5d78f6f4a59ae06dfc0603db51e550b942e5065419,0x69794541ec91e21add5cf50a5fea3e9d20350a5feb3e9d20a885d40f24e0f655b897465d1940f2564f654a4dac66dc4060,0x51511e0691d429590520250a57ba48261f95045962485974b5d2d411251c62d6b2db72121540203080c26addb6c24e4947,0x14584a440365160fa940895243ea516e88a9549093424d223c891093424d093424d0934060,0x513144c78a55ed70f93995e59c3e537a2ea5b1dc655b1d74f5d3d3ef70a95a76b41b7400a944c03080b27b41e8e5b1c83a,0xf47575cf9e5e20f9e88c18e53d217645d902f00bc1a6469b03e4,0x7f220d11fe3e9c21447f8fa7085120688a0f6708516c95d7175c3d9c21449b5ada6df402a,0x26640d7035d1f855ad1fe0850fa708511fe0850fa7085120688342143d902145b117435d0c2143d9021449adac16dc002a,0xf2f4778fed57e9634480179e5ebd2088bd0d133324a545d1d7474fe0f2d295489d2294cc9,0x9ed4784f3857e9649480979e5ef9209889190465912175d6575929dca752975a6269a83e3,0xf6d57e96495e797be8bcd90565957615d84a7829d9a6369ac0604795576480d20a5ba5297,0xc858c2321d0c47791fa6a9d5fa58d12006d6d79e5ebd20888608a0640d96148517475d1ca15226489818adaaa6d70032,0xf1e4adcdc35088f9308b94223e4c22e87d4dfd37e822e3930e3e4ff02404adc8d52358032,0x68091db47e542e58cce9550b97ae434e1f150596d55b5574c5d3141621992776b35b7300c8795162d1f97325c102184884,0x22b38b26297897e250897a2868a0228587fdda07191d135cbd72f763dc25017dab46d98479,0x642d51b61dd2bf4afc6164ba0dd77bf901e5421120625d66a5ac149541ac7004848d9c62c1508448085f4561fc700c99ce,0xfea544823549c8dc508d545608d48f44078ebb013003245616b033542354c8120f3649899,0x548cfea17c586f21c588249c953037146165159dfb08d5efb4078ebb00c8235625d1585ac0cf84ccc2351bf521136658af,0x113c500023549c913c08d545608d48f24078ea508d4032491d6aa3350235335120e3644d91,0x111d293911d50d4dd751e0ebc59b52495aa4cf908d5571366cd09515997756a9b3900c8cf9,0x44f186f7358a4e44f06b450d42357bf14783ae823562592485ab0cf908d46ff561cd9b34214561ed087256a9aba00c8cf9,0x1eea7c5c05f4b012c04b01db07b848684079e127a8c86a45a620a365587a5b2d2103654d95,0x7251c740ec100c3fe0ff847211c84710f644c813204c80f9847210a042810a03c42b10429,0x61ac73b01b863818e040010a042810a042811c84723078a3f10a071e1eb40671000b5b06704c813204c80fa042911c833e,0x6e11b380ed16a85aa0fec57e19e0413151055019704c80f944c810a042810a0428104c429,0x61b02d90b6079001c006418e06380b6440010a04282d6842810a057e19e00fc1bb85ff10a04c8132033c13203e810a44c8,0x623100c3fe10a44290f104c813203e6106057e17e43fe10a04c811c84720f74428116c08e,0x61a473b01c4404100040010a442910a03c615f867859fc3fe10a04c813204c80fa0429132073b1cf0067100042803f04c8,0x1c8c71d01c860118043fe17a06a810a054811c8472307ca3f10a055019704c80f984c811c871e1c8c06417fc42806704c8]
def pgR15:Array Nat:=#[0x21b086c02a4afd5a5086021b592e265407421b5f0228945a2227086cd040ce520d3668d9a,0x4fac02a086c83761cd87929252bf56946156b0c21b592def84075b6d086d7c07c211688868d04086cd041bf920d3668d9a,0x211f7bb9ef2819a02e0196197846deff84a21aa8581f0a858e2033654d951be5bcf3654d95,0x1f477bac0652a851fc47f1db158cc86851e1e135eb886a54ea21f36599755b312543658d96,0x190b498526157b56334989660599518131e954646611c93650d945571eb018a572b5980828,0x642d1f847e15ed58cd1ff599166c59b16b1531d0bc495cda25a555094485a197f28032675151d65b862a7b5d66c1c14886,0xfea646597c477d53208d945908d88fa4c30ebf013567254cd6b133e82364c8925c367d693,0x5494fea1c911d55350fea57dddfc08d91ff3afc03208d90e95ac4cfa4cd02364958d9f5a4d91421ccfea18a9ed559b0702,0x231293cdc2516423151e0ebe08c55955ab4cd908d9599364ccda647023608d88ff00c8cd9,0x44f11d544f143608d939a3af823655cd6ad33ec236566cda1344991444f06bc7b596681c114591ed55706aec03233ec874,0x21c087002a2a74a47087021c58d88ff2ab821c5ec89002abe22e0870d93336ca47364cd93,0x1f871e1c9861c166c1b310a042810a056d160067a06707d510a03eb0fac4cc0faca280fac3ef0fbc3f105e0a2c0fc419d,0x1f85da17d842810a0735160067a1f544280fac3eb0faca280fac71e1c9817510a019c0fac3ef0fbc17128b03f106743f1,0x21c087002a087164c860421c5f06182889821c2904a43290ca43292ca4a085da906a28707,0x4fb002a087083947e156e6b2021c59311fe6db821c5f05206886cd110870d11494cda0368083861cd97118a5ed17a3c703,0x2120817e02686de1b885ee1b986ea17a881cd963659bd13658d967cb1f5b017ded87a4c6fa,0x5e3d2d14a612ee3a050235e98eca4934c5e1e308ad4b11f011bcd78f029d29827e095e22b54a046ad5775cc8bc85ba96ea,0x64892d166bd5f13a095406400ecc4614c6464880af66bc9fb27f181846b14d64d60ec8606012622b92d17b6812622b9818,0x1d094b3d2c082f8e7c407a0e842651698881f1d017d2c021a086a353519955bd72e5cb96cb,0x17904ab15780b383b8409c2ce0ee15816f502ce0ee124f32d8c4d0b3879e4ae17505c7171c,0x52f92d14aed2e670090235330c5a4930c5a1ac49704aedf001f796eb029d2995d897285bad3270b3d57734ecbc725bd9cd,0x557d2d154b9386700952e5508c5f4610c5f60640af606576361093280b41a1e34f4ec5674412125c12d17ef81216065328,0x11b64b3dbe68540e7c407a104426516988c9eae017d2ba5cb172c34e1199474cd3834e19b8,0x41b52c137192e5375101f526d07149296b2526906f496d73c60c149842606177ed08a700c949842685fd7ecc03222ac8a7,0x5fa18e05fa1a405fa100042910a442910a447211c847211c8ac51acc6141864d4d10a4472,0x17dc63817dcb7d1090b6006985f718e01a11a3061318e042423d447411d0636109037a11d065e184c61910907181c60474,0x17dc63417dcb9f10905af1abc5f31a6042411d05f3194c42411d06b317cc621109071811d01950d78634068427f11d0718,0x113c4b0113c8304dd74079f23465927023d0cb3013127432cd9ed7879196473d72d00c96d8,0x17206381720660172040017a4424169c5e911b45c818d86791090660172125f0ae842411b46601720175211042411b40fe,0x1718638171910110905a706305c618e01b411b509718d84240de465e05d06380c9c9c706bc65e171925f109071811b471819785c605d4424272046d27340fe,0x171863417185eb14b05b211b5097194c42c1acc1991a6027d067067b170c66f10b046d1c646b3170c63410b046d09f4718,0x171463417145e910905a71acc5c518e05e911d05c518e442411d06b3171525f109071859606b31714175109027b1bd40fe,0x1718634171910410905af11b50a3194c4241acc19918d032706bc6b3170d481109046d1c606b3170c1ae109046d27941ad05f835418d01b411b49fa1c609ca,0x42c52c042c614f374d01e31bd0c249d0c6f7c6060f4b01efd026de2241a96ce5cc13b75b39e1b41a91d67f0d3b721dc032,0xfed49f0dc6516cfed407cec2013115c5ac950f46ed1dd22759ea61c1319496172d6025319,0x52651bb170127c4ad8dc64e1ddf939f501f3b08032430d15c634555222a119b496573460b154a26791bb185dfb067a8032,0x11b4294d1b450dce7d51e4ec146354eb6334cfc330ccc33560bc94fdd19c477489d67a0cc3,0x42c8a5342c938737514793b0518d460d8cd555106e56717395c0554a42606b57ec99e800c954a18412c16ab003222a89a0,0x18486021849105109054616005c519544241540612177042411d071e184869710904741c6417e184860206845801ce427f,0x11b945f11758548e7c45f0efe419d15332ace454444051611580b7af4239454c90559f0032,0x184860018005eb10b054811d067a1800ac51ac8612520471859606b218481ae1cd46f506b46b2184863410b04740ae827e,0x18486021469106109054611b53be194c4241ac86125d9c42411b46b218481ae109046d06b46b205b469710901af1c609e605f861218081b411b47182788a1a,0x46e517c371615139f117c31c51894568c71788d19a60097374ee1e1c4669a187f313b800c9eba16fd1697eb809b6008878,0x156129815c84e21e8451e94bb7b3953b87d15597ab159e5d5175455643641ad9ccf7050488,0x12c27a1547a7b3d53b8b6dead567d7575d5dcf71ad9e03760865885c92c275d9de67885e1a,0x7894aa356c1fe300a80b875d5e7e51e9fbb7795ecb54edf8988cde1d7aad59d24a17315cc5e170ad86b624a1fb97e1c02a,0x11b54a48db54e1ce7f4088ec1465524b32cd55646a56e45d4971055591a9479dfd267e8060,0x10b445795964b9cdd545f54af422d8105d614af422da1b7f640603b0908a457ccb561019ff,0x1d004b40a6475d8e804089de6427516e88e1e2046b96e35d4575178651ae4799fd07e44060,0xdb63a01022427516e87dd1af5b957565d591af47a1cd1705406046b4a654e214bb556955a,0x697d5601ed92921afcdb54e1dfed39fd02252e9fee427116e88d5553254d1a85b857355cd5553267d1a8478dfc87e3c060,0x558128d6931387591502152e97bc45b61fa555587f497573a5ce9555252061877f9d8111f954f03000c077f5d802550948,0x5570aa0790d5ed70014775e59caa54e62eb5b0dd045b0d73d5cf554873d956d7f35f9000a955c03000b87b49e905b0c832,0x7fc29212ce39fc216407509c085916888e51aa08596c85d4d75346a82164731fd57e4802a,0x26840d903652bf36d12ce0858e7f085901d085909c085916888d0216469c2165b057335ccc216469c216472dfc57e3802a,0x119d4a191bb57f9634407d7a25ebd16a88bd54b3ca4a5622748a53418cc233097365cd8cc2,0x3640d92324a8d4a192c16ab15fe58d101f6d757a25ebd16a88d88a961c587b49697365cd89da2268898185dfb17e1047d,0x5900e91b94e2022d40794bb08b516988e8e0508b51d2390ce3800e822d00e891f2484032,0x69192784b0138858cd01e52ed7ae45a61f255616d05b4173b5ced55821951d97339c1300c8796183d2c07329c1121ac879,0x22c88b5e2c78afa2908ada2928aea2c388c5e1f740dd185cb972e7861cf50195fbc7e28478,0x144c61cdef14b39beb019544c70ec82a407551d70ec82f45a22134e2cd965afd26a3658d96,0x73f9d5202f5b186bd9b000488c5b6e54c5b0d9487e215df061f7cd3e3578d5e34f8c3e5c45e1002f40ca6cddb6b215cd5e,0x73edd4d0305b1d701dd576e88c606e4cc6035013604d813602f2ddbc03040d07ba5b674d8012221fdf777f5813d4d1085b,0x11b94b3d1b982b0e7c407a0df426516988dcd393a2925434e4d397c791b9019485d21a56cc]
def pgR16:Array Nat:=#[0x18784afd5a40848fdf51dc21244fd5398bfc2123cd559834e4d3901958784afc82b20c005a,0x1850638185064415646321b406e4169c0f91abc614100005d1c9c47111c447115f847111c44c500b44c519684c5131457e,0x18504030ffc6ac18483fb1abc614100072711c44710f6847111c44c500b43e913144c511b06af185040003e406811c44c5,0x1850638185042c10b04281abc722091442811c446c11c4ac211c44c313144c52b886fb11b06af1eb00f610a006d11c46fb,0x1d0b81b5d0b7979e8284d1923668209286f8c7d31f4c7d31f436a3578d5e3578d5e0da9689,0x741e06e741dd66702a1356ee4c576e58c570dadef378bdf04036cd3e6f8dbd334f8c3b24f1ebe0e01d377b7495f28100b3,0x21718191d057981c0984d8c7931e4c7931e59247b15d3023f9674362004e615585559d180a,0x73f009c73fdb286bd5b253200c803200c800271d06034db363200d4204e9bd83508bce350883b0c41f767b8169620a454a,0x74220697421e5d70061b06ee8c586e50c583501d7475c4d402f29f3502bdf797b7894f02e40c7219df787b700db4d0ca17,0x11b600c823700d0a8c49bde5f39f08894079ec2426488a45a622c367803466e8a403678d9e,0x46d809c2a3003221880db798ce7c4079fc07b1109945a5f8c882cd3f621ca404cd4d3f34fdf201e9ca8c21d5ed47a44701,0x205e864205d82fdbff84ae0e972a61668800d396f89bd234e4d397ca005f74d5ed87a4c05a,0xff1513cff1513cff1016944f3fc5d7e696151e4519df46966211381987c5dc17705cb972e,0xff1647957457b96374e757995ecd4e08bbccdf337d5755cb972e647987d016892e24fd6de,0x155d3fc4611513de273fc544f77e8ff1896d51e75fd1468a0a204381847862217705cb972e,0xfdf647987d29615ad016944f3e6492e51ed51e3e6493f54f22143380ce05b815b53538d84,0x46f55165eb0a59467d5345534f370458099515d6437b7d47a2378ebd431805c54d59f26800e1848d583e56c8ce15d1183e,0x14bc40414645eb157c69416005891ac1a01153465a56847181c606901b9069403e42c11c606af1c986b00ae40fc1c602c1,0x46f8a5a468154e44a809a516964451e9fb73b0119456d19f16cf4e19658d5b34c957485c4d936665d5b10e1dae10171713,0x11bc513d1bc55751bc016944f58dddc7871151e5ecde16870621d381d2345dc57715cbd72f,0x11b7513d1b7508ce7e898d423426e2888820e0748d17715cbd72f513c06678c5ab06d8c066,0x144c5131f5447f9d12017d44c71c882a47f951d73bc82f481a216551cd955af91ca3654d95,0x7159d110305b1b7171e076e8cc616e28c6134f53584d613583b19dbd03040af7818c614d6012321e885c780013e4cec85c,0xfea47fcfea82b4f9347fe0e03e4d20787ecd3848c91d334e0d387c78fea017c85d21a56cb,0x196f4afd5a4084963751dc2125ecd539888405f65bd2bf20ac8300848e8c55a8d3834e005a,0x14465119c675119c6786c4ee70a482920a48cd84d618466118292544c29274888fd59cc292,0x719a0607199da7719a1bf7074c597058c5934f5d7375c0d3d3b11eef0341fa47f38ec402e40c87b19f987f2c0dd4ce89e4,0xfea00c824900d4a8c4739e623fa888c4079ec3450488e45a622d363d231363d1ce363cd8f,0x3fa809d2a1c032218c0dd7964fea3a55fc17b01141434df8d8bf4d3c48cd1d74cd8d3c34f1eec03491f221d9efa7c240d2,0x203b85f20278555c7085f610573ba17f8bf0d386f41bcc34e0d387bb40667435eff7c2805a,0x2bd2a902bd6ce02bd51edbb40af553c7a91bde0af55837aa5ea47ca997e0185ed97a49ea7,0x145151440635145e75867551f7b221ad887155e7bd61b4892e27b,0x208979da19b7b261ab8bb5ef686ca2f88b81daf8199daf7845e24,0x2114afc03c0845e7651dc2117b255398bb82117bd95828be62e101882114afc2110844211,0x7c30038084c67e08646bb0acc02a02d082d57b5e7d084dfac7ee97967b282137e09f8888318737bdc2137df5f7f8916275,0x612a8003c209c827018421158c54773e5c2115eb55393e5e20e08458815608fbd891a276,0x21d00e021d0874fec51dc21d450953988ac21d46e9582893e27f,0x38209522157514773e5178754e4f9487f586a5608fba88fe26f19f8aa020996315eb5881,0x21ea82600637fa0f3b01860b179d219e7ef60e17b1e1ae7e2e20183ddef486d5f808906271,0xfdf513cfdf513cf9984b951e3e661698840ce03380d4e3538d84,0x11b8556d1b84e14e7e85f94b9426e1808c00cdf337cd4d3534d83,0x1c4a76c8f3276c8f9a84bde143e6a16a883de263efe177891e277,0xfe03e6a1303e6a16b87ccfbf85e223c89b0f3a5145451547d55e,0x1f29513c7a9513d5ae018d44f7f94f9984c551e7f9cf9985b22055575fe63efa179890e273,0x1223508da03508da4487f1431692223e89b98e901696385ed1885513c03c3e64f993ef803c,0x144f513df6a508d63784b14235ece16787e1431621217588f626d513c063018dab06d8dbc1,0x4fa8aa071815ed09502105e5825408422e75510fbb55b1fb57e156c209502105ce173800a944c02f80be08402100338210,0x4fa8aa071815ed09502105e5825408422e95b1825408417495d253ea3eed5a66ab9b5e00a944c030c0c3084021008400ac,0xa743eb50263eb51738bc4fc147da2fb8b8d8ef1b115f85e75876,0x92656bd28f5090f9b40894243e6d16e8b994323f011f48bda2de1e2c7aa1f289332500935,0x18e819f9f5300e8db34afd5ed3e5882b51dd7963e5883054e622261ccfbc20b1582893627d,0x6852930aa03ec821f51dcfb2087d5398ba0fc2087d5828bde2df20f5f4818a56315eb5881,0xaa0087d477087d5398a4421f560a28f8a39daa00e16315eb58811e5d2223ec8fb23f0882e,0x210b7fe1fdc7969c3a8671ec170ea1ac8b95ef071061b38bd62dd8660063016a1ce87661de,0x38084805a0849a913e502126a2cf9488942126a38fba893a27e,0x78169e5d593e655ee84a4f995e661648864fbe61d2173892a27a,0x1c4b01a40697511be774c54233e65ab184a94233e65b64859620250c4fbe6f0a174890a272,0xe18726200a5e296c92d500cf3904a80b657f164b7c15a6020fd7a05f01f0b69a08f16bbce214d0005c67159c567699d9,0x172040b102c42810a0a2c160060e102c42815405ee102c429677471e1c9840b10a00fc0b0c73b1cf440b10a42c003f82c0,0xe0a5f297155046840b757f564c6985fb85e857c169a5f866bbce224d04a616719b3c6eed93f6678a610431ad76df005c,0x9446a5da9b644d97001855ef58e61c6871579a5ed61c7870a21261d588687221c08922278,0xf3a298ca6257bd6396a4979a5ed5a8c8bc18756219a8f8bea2e2647d97e018492e24fc934,0x6901a494569c1d5a7901ab257bd6398971b655e697b58a0e2066f0d875621a28b8912274,0x1c4c647df594a41bec01a942571cc92e408942573c093f45ba21550cdd0a24d11f48926279]
def pgR17:Array Nat:=#[0x13f900e80634fe406301a945158d5c82234951f5ec1cf2235221e557988374388d3893227c,0x1dab7515e3f508d63784b54235ece16887c1431621217688ee26b1e2858e74c9ccb7049bf5,0x22b48b562a3898a25389762878a0628487fa28d8a2a28c8902270]
def pgRL (i:Nat):Nat:=(if i<576 then (if i<256 then (if i<128 then (if i<64 then pgR0.getD (i-0) 0 else pgR1.getD (i-64) 0) else (if i<192 then pgR2.getD (i-128) 0 else pgR3.getD (i-192) 0)) else (if i<384 then (if i<320 then pgR4.getD (i-256) 0 else pgR5.getD (i-320) 0) else (if i<448 then pgR6.getD (i-384) 0 else (if i<512 then pgR7.getD (i-448) 0 else pgR8.getD (i-512) 0)))) else (if i<832 then (if i<704 then (if i<640 then pgR9.getD (i-576) 0 else pgR10.getD (i-640) 0) else (if i<768 then pgR11.getD (i-704) 0 else pgR12.getD (i-768) 0)) else (if i<960 then (if i<896 then pgR13.getD (i-832) 0 else pgR14.getD (i-896) 0) else (if i<1024 then pgR15.getD (i-960) 0 else (if i<1088 then pgR16.getD (i-1024) 0 else pgR17.getD (i-1088) 0)))))
def packet (globalNode pairIndex : Nat) : List Nat := packetBody (packetField (pgRL globalNode) 14 pairIndex)
end SignedProjection.Grouped

namespace SignedProjection
namespace GroupMetadata
def r0:Array Nat:=#[1,5,9,0x1d,0x8d,0xc9,0x109,0x119,0x11d,0x121,0x135,0x181,0x259,0x5cd,0x601,0x645,0x675,0x691,0x69d,0x6c1,0x6c9,0x6cd,0x799,0xf0c,0xf1c,0xf28,0xf2c,0xf30,0xf34,0xf38,0xf9c,0x1002,0x1006,0x101a,0x1026,0x103a,0x1042,0x1082,0x1086,0x1109,0x11fe,0x1276,0x12de,0x132a,0x1332,0x1356,0x1362,0x1376]
def r1:Array Nat:=#[0x139a,0x1924,0x1934,0x1944,0x1960,0x1a28,0x1a2c,0x1a48,0x1a60,0x1b2c,0x1b4c,0x1c30,0x1c50,0x1c58,0x1d34,0x1d54,0x2924,0x292c,0x2934,0x29a0,0x2a28,0x2b2c,0x2c30,0x334c,0x335c,0x338c,0x33c4,0x33c8,0x35c4]
def rAt (i:Nat):Nat:=(if i<48 then r0.getD (i-0) 0 else r1.getD (i-48) 0)
def hint (w i : Nat) : Nat := rAt ((w >>> (7*i)) % 128)
def al0:Array Nat:=#[0,0x7000000000000000000000148000000000000000000003800000000000000000000068000000000000000001,0x70000000000000000000001980000000000000000000038000000000000000000000b8000000000000000001,0,0,0,0xdb4cb079c69800000000000000000000000000000000000000000000000000000000000000000000000004,0xeb8cb079c59400000000000000000000000000000000000000000000000000000000000000000000000004,0xf38d3079a59200000000000000000000000000000000000000000000000000000000000000000000000004,0xfb8db079859000000000000000000000000000000000000000000000000000000000000000000000000004,0xfbad3079a51000000000000000000000000000000000000000000000000000000000000000000000000004,0xfbccb079c49000000000000000000000000000000000000000000000000000000000000000000000000004,0x15d54d079c69800000000000000000000000000000000000000000000000000000000000000000000000004,0x17d95d079859000000000000000000000000000000000000000000000000000000000000000000000000004,0x17db55079a51000000000000000000000000000000000000000000000000000000000000000000000000004,0x17d99e07989a000000000000000000000000000000000000000000000000000000000000000000000000004,0x10c78e669eebe00000000000000000000000000000000000000000000000000000000000000000000000004,0x12cf8e669ecb600000000000000000000000000000000000000000000000000000000000000000000000004,0x114796671ef3e00000000000000000000000000000000000000000000000000000000000000000000000004,0x134f96671ed3600000000000000000000000000000000000000000000000000000000000000000000000004,0x1863966c32d3600000000000000000000000000000000000000000000000000000000000000000000000004,0x186396745355600000000000000000000000000000000000000000000000000000000000000000000000004,0x10cb8ea59edbe00000000000000000000000000000000000000000000000000000000000000000000000004,0x7000000000006000000000148000000000108000000003800000000002800000000068000000000028000005,0x7000000000006000000000150000000000110000000003800000000002800000000070000000000030000005,0x7000000000006400000000148000000000118000000003800000000002c00000000068000000000038000005,0x70000000000050000000001980000000001180000000038000000000018000000000b8000000000038000005,0x1ce74c6e2c60c00000000000000000000000000000000000000000000000000000000000000000000000004,0x1ce74c6eae68e00000000000000000000000000000000000000000000000000000000000000000000000004,0x1d67546d2650600000000000000000000000000000000000000000000000000000000000000000000000004,0x1d6b54ad2a50a00000000000000000000000000000000000000000000000000000000000000000000000004,0x1d70000000000000000000001550000000000000000f3800000000000000000000071800000000000000000006,0x1de74c2da648200000000000000000000000000000000000000000000000000000000000000000000000004,0x1de75c6da658600000000000000000000000000000000000000000000000000000000000000000000000004,0x1de75c6eaa68a00000000000000000000000000000000000000000000000000000000000000000000000004,0x1de75c6f2c70c00000000000000000000000000000000000000000000000000000000000000000000000004,0x1def5cedae58e00000000000000000000000000000000000000000000000000000000000000000000000004,0x1df39e2d3092000000000000000000000000000000000000000000000000000000000000000000000000004,0x1df5cf19e58e000000000000000000000000000000000000000000000000000000000000000000000000004,0x1fe7640fa660000000000000000000000000000000000000000000000000000000000000000000000000004,0x1fef5c6fae58600000000000000000000000000000000000000000000000000000000000000000000000004,0x1fef7ceda658600000000000000000000000000000000000000000000000000000000000000000000000004,0x1ff9be8db09a000000000000000000000000000000000000000000000000000000000000000000000000004,0x1ff9be95d11c000000000000000000000000000000000000000000000000000000000000000000000000004,0x1ff9df079859000000000000000000000000000000000000000000000000000000000000000000000000004,0,0,0]
def al1:Array Nat:=#[0,0,0,0,0xdb479c000000000000cb06980000008a02880000002e,0xdb279a000000000000d307180000009203080000002e,0xd8003278001a98002238000ad000307000180000000000002f,0xd8003478001c98002438000cc800306800180000000000002f,0xd80034c8003098002488002078001c6800180000000000002f,0xfb8db00000000000007985900000003881800000002e,0xfb6796000000000000e30610000000a202000000002e,0xf80036780016b80026380006e000306000100000000000002f,0xf80038780018b80028380008d800305800100000000000002f,0xfbad3000000000000079a51000000038a1000000002e,0xfb4794000000000000eb0690000000aa02800000002e,0xf80034780014b80024380004e800306800100000000000002f,0xf8003ad00030b8002a90002078001a5000100000000000002f,0xf80e80db4cb000000000000000000000000000000000000078068059449000000000000030,0xf80d80eb8cb000000000000000000000000000000000000078058069849000000000000030,0x17db55000000000000079a51000000038a1000000002e,0x6bb6800000000000000000007bf78043140000000000000000000053550000000000000000000031,0x17d47940000000000016d06900000012c02800000002e,0x17800547800153800443800056800506800100000000000002f,0xf80000000000780000000000001980000000001180e00000e8000060000068000000180000188000100000108032,0xd80034c800305800144800119800658800600000000000002f,0xdb59e4000000000000cb18e00000004910c00000002e,0xd80033980062580013180042d000319000600000000000002f,0xd80035980064580015180044c800318800600000000000002f,0xdb4cb00000000000019e58e00000011c50c00000002e,0x15800554800505800144800119800658800600000000000002f,0x15d59e40000000000014d18e00000004908a00000002e,0x15800559800645800149800254800518800600000000000002f,0x15d54d00000000000019e58e00000009a48a00000002e,0x180380000000580780000001181380000000000000000000980b80000000d80f80000001981b8000000000000034,0x280380000000680780000001281380000000000000000000a80b80000000e80f80000001a81b8000000000000034,0x1bea79a0000000000019e25920000019605100000002e,0x1864c340000000000018e6cb6000001aeeebe0000002e,0x1c80052c80013c00050c000119800469800060000000000002f,0x1c80066c80027c00064c000254800464800060000000000002f,0x1c80067480047c00065400044e8002e68000e0000000000002f,0x1c80066c80027c00064c0002568004e68000e0000000000002f,0x1c80052c80013c00050c00011a8004aa8000a0000000000002f,0x401400000000501500000000680000000000780000000000c01c00000000d01d00000000e80000000000f8000033,0x400c00000000500d00000000680000000000780000000001401c00000001501d0000000168000000000178000033,0x1de6da60000000000014c24820000014404000000002e,0x1de6da60000000000015445040000014404000000002e,0x1de75c6000000000000ca2482000000c204000000002e,0x180380000000580780000001180000000001580000000000980b80000000d80f80000001980000000001d8000033]
def al2:Array Nat:=#[0x1dd4d940000000000019c49840000018c08800000002e,0x1dd6d960000000000019c69860000018c28820000002e,0x401400000000581580000000600000000000780000000000c01c00000000d81d80000000e00000000000f8000033,0x1d81c80000001981880000001500000000001100000000000d80c8000000098088000000050000000000010000033,0x1d81c80000001981880000000d8000000000098000000000158148000000118108000000058000000000018000033,0x1df59e4000000000000cb08a00000004900800000002e,0x1df4cb00000000000019e48a00000011c40800000002e,0x1df54d00000000000019e50c00000009a40800000002e,0x1d80d80000001980980000001480000000001080000000001d00d0000000190090000000140000000000100000033,0x1d81d00000001981900000001580000000001180000000000d80d0000000098090000000058000000000018000033,0x1d81d00000001981900000001581500000000000000000000d80d0000000098090000000058050000000000000034,0x1d81d00000001981900000001680000000001280000000000d80d0000000098090000000068000000000028000033,0x1d80d80000001980980000001d00d00000000000000000001c80c80000001880880000001c00c0000000000000034,0x1d80d80000001980980000001c80c80000000000000000001d00d00000001900900000001c00c0000000000000034,0x1d81580000001981180000001c81480000000000000000001d01500000001901100000001c0140000000000000034,0x1df5cf00000000000019e58e00000001840800000002e,0x1d80075980064580014180005c800718800600000000000002f,0x1df5cf00000000000019e58e00000009a48a00000002e,0x1d80d80000001980980000001c80000000001880000000001d00d00000001900900000001c0000000000180000033,0x1df5cf00000000000019e58e00000011c50c00000002e,0x1d81580000001981180000001d00000000001900000000001c81480000001881080000001c0000000000180000033,0x1eeaeaa0000000000014c24820000014404000000002e,0x1eeb6ca000000000000ca2482000000c204000000002e,0x1edae9a000000000001acaa8a0000018408000000002e,0x1e8006ae8002bc00060c0002168004a68000a0000000000002f,0x1e8006b68004bc00061400040e8002a68000a0000000000002f,0x1e81c80000001a81880000001681480000000000000000000e80c80000000a8088000000068048000000000000034,0x1e81c80000001a81880000000e80c8000000000000000000168148000000128108000000068048000000000000034,0x41545400000000000069f6de000000ebfefe0000002e,0x1865c740000000000018e7cf6000001aefefe0000002e,0,0,0,0,0,0,0,0xeb8cb0000000aa88a079c59400000038c1840000007f,0xf38d30000000b2892079a59200000038a1820000007f,0xfb8db0000000ba89a07985900000003881800000007f,0xfbad30000000baa92079a51000000038a1000000007f,0x15d54d00000011c50c079c69800000038c2880000007f,0x17d95d00000013c91c07985900000003881800000007f,0x17db5500000013cb14079a51000000038a1000000007f,0x17dd6d95d54d000000000000079c69859449000000000000080,0xdb4cb00000005944919e58e00000011c50c00000007f,0x15d54d00000005944919e58e00000009a48a00000007f,0x79c698000000000000bacaa80000000000015d54d00000000000019e58e000000000000000000082]
def al3:Array Nat:=#[0xeb8cb0000000698491ae98e00000012c90c00000007f,0x16d94d0000000698491ae98e0000000aa88a00000007f,0x79c594000000000000bac9a40000000000016d94d0000000000001ae98e000000000000000000082,0xf38d30000000718511b699600000013491400000007f,0x1b699600000000000013cb1c2000000000000f38d3000000000000079a59200000000000000000082,0x796ba6000000000000000000610a217d7be6000000000000000001651a6000000000000000000081,0xfbadb3beb9e200000000000079a5933cb1c200000000000080,0x17db5d3beb9e200000000000079a592baa9a200000000000080,0xfbcdb5bed9e400000000000079c5953cd1c400000000000080,0xfbceb9bedae800000000000079c6993cd2c800000000000080,0x17dd6d9bedae800000000000079c698bacaa800000000000080,0x1bedae800000038c2899e58e00000001840800000007f,0x79c698000000000000594490000000000001bedae80000000000019e58e000000000000000000082,0x1bedae8000000bacaa99e58e00000009a48a00000007f,0xc32d36000000000000e3af3e000000000001863966000000000001a6bb6e00000000000000000082,0x1bedae80000013cd2c99e58e00000011c50c00000007f,0x145355600000000000165b75e000000000001863966000000000001a6bb6e00000000000000000082,0x1ce74c6000001c65444ca6486000000c244040000007f,0x1ceb4ca000001c69448caa48a000000c284080000007f,0x1d67546000001c63442d26506000000c224020000007f,0x1d700000019e20000000000015500000011c2000000f38000000baa00000000000071800000038a00000000083,0x1d70000001550000000000000d30000000510000001bea0000013ca000000000000baa00000038a00000000083,0x1de75c6000001c61440da6586000000c204000000007f,0x1df35d2fba79a0000000000019e31c2baa38a00000000000080,0x1df37dadb279a0000000000019e33ca9a238a00000000000080,0x14d04900000000000000000010c0081df4db40000000000000000019e49a400000000000000000081,0x1d81d00000001981900000001581500000001181100000000d80d0000000098090000000058050000000018010084,0x1df55d4fbc79c0000000000019e51c4bac38c00000000000080,0x6380000006ba00000000000073c0000007be0000014700000014f20000000000015740000015f600000000083,0x6580000006da00000000000075c0000007de000000c70000000cf2000000000000d74000000df600000000083,0x1df5cf00000005944919e58e00000001840800000007f,0x79c69800000000000038c288000000000001df5cf00000000000019e58e000000000000000000082,0x1d80d80000001980980000001d00d00000001900900000001c80c80000001880880000001c00c0000000180080084,0x1d81580000001981180000001d01500000001901100000001c81480000001881080000001c0140000000180100084,0x1df5cf00000019e58e00000000000000000000000017dd6d80000013cd2c800000000000000000000000000000085,0x1e6b64a000001c63442e2a60a000000c224020000007f,0x1e70000001ae2000000000000e30000000aa20000017540000013c600000000000071400000038600000000083,0x1e70000001650000000000000e30000000610000001be60000013c6000000000000ba600000038600000000083,0x1eeb6ca000001c61440eaa68a000000c204000000007f,0x1e81c80000001a81880000001681480000001281080000000e80c80000000a8088000000068048000000028008084,0x1ef36d2fb6796000000000001ae32c2ba638600000000000080,0x1ef37d6eb2796000000000001ae33c6aa238600000000000080,0x14d04900000000000000000010c0081ef8eb8000000000000000001ae8aa800000000000000000081,0x1e81e00000001a81a00000001681600000001281200000000e80e00000000a80a0000000068060000000028020084,0x1ef97dceb879c000000000001ae93ccaa838c00000000000080,0x5540000005d600000000000075c0000007de000000c70000000cf2000000000000e78000000efa00000000083,0x1ef9cf0000000698491ae98e00000002880800000007f,0x1e80e80000001a80a80000001e00e00000001a00a00000001c80c80000001880880000001c00c0000000180080084]
def al4:Array Nat:=#[0x1e81680000001a81280000001e01600000001a01200000001c81480000001881080000001c0140000000180100084,0x1650610000000000000000001240201f74f34000000000000000001b64b2400000000000000000081,0x1f01d00000001b01900000001701500000001301100000000f00d00000000b0090000000070050000000030010084,0x1f757d6f34796000000000001b653c6b2438600000000000080,0xd30510000000000000000000920101f79758000000000000000001b6934800000000000000000081,0x1f01e00000001b01a00000001701600000001301200000000f00e00000000b00a0000000070060000000030020084,0x4d20000005d60000000000006da0000007de000000c70000000d74000000000000e78000000f7c00000000083,0x1f00f00000001b00b00000001e00e00000001a00a00000001d00d00000001900900000001c00c0000000180080084,0x1ff37d2fb2792000000000001b61340b2030000000000000080,0x1ff37d2fb2792000000000001be33c2ba238200000000000080,0x1ff57d4fb4794000000000001ae12c0aa028000000000000080,0x1ff57d4fb4794000000000001be53c4ba438400000000000080,0x1ff77d6fb6796000000000001ae32c2aa228200000000000080,0x1ff77d6fb6796000000000001b65344b2430400000000000080,0x1f81d80000001601400000001b81980000001201000000000f80d80000000600400000000b8098000000020000084,0x1f81d80000000e00c00000001b81980000000a0080000000178158000000060040000000138118000000020000084,0x180380000000580780000000980b80000000d80f80000001181380000001581780000001981b80000001d81f8084,0x1ff97d8fb87980000000000019e11c09a018000000000000080,0x1ff97d8fb8798000000000001be93c8ba838800000000000080,0x6396780000000000000000007bf7fe4314700000000000000000005b75f600000000000000000081,0x796386000000000000000000610201ff7be6000000000000000001e71a6000000000000000000081,0x1ffb7dafba79a0000000000019e31c29a218200000000000080,0x1ffb7dafba79a000000000001b69348b2830800000000000080,0x280380000000680780000000a80b80000000e80f80000001281380000001681780000001a81b80000001e81f8084,0x6bb6fa0000000000000000007bf7fe43147000000000000000000053557400000000000000000081,0x1ffbdf3beb9e200000000000079a59238a18200000000000080,0x1ffd7dcfbc79c0000000000019e51c49a418400000000000080,0x300380000000700780000000b00b80000000f00f80000001301380000001701780000001b01b80000001f01f8084,0x1ffdef9bedae800000000000079c69838c28800000000000080,0x1c73d76000000000001e7bf7e000000000001863966000000000001a6bb6e00000000000000000082,0,0,0,0,0,0,0,0xdb4cb00000005944919e58e09a48a11c50c0184080df,0x1df3d700000019e3960000001581500000001181100000000db2d300000009a2920000000580500000000180100e0,0x80000280000480580680780880000a80000c80d80e80f81080001280001481581681781880001a80001c81d81e81f80e2,0,0,0,0,0,0,0,0]
def al5:Array Nat:=#[0,0,0x17dd6d95d54d13cd2c91c50c079c69859449038c288184080e9,0x1bedae99e58e0000000000000bacaa89a48a17dd6d95d54d000000000000079c698594490000000000000eb,0x1df5cf00000019e58e0000000db4cb00000009a48a17dd6d80000013cd2c800000079c69800000038c288000000ed,0x1ef9cf0000001ae98e00000016d94d00000012c90c0000000eb8cb0000000aa88a0000000698490000000288080ec,0x1ef9cf0000001ae98e00000016d94d00000012c90c0fbcdb4000000bac9a400000079c59400000038c184000000ed,0x1ef9cf0000001ae98e0000000eb8cb0000000aa88a17dd5d40000013cd1c400000079c59400000038c184000000ed,0x1f79d70000001b69960000001759550000001349140000000f38d30000000b28920000000718510000000308100ec,0x1f79d70000001b69960000001759550000001349140fbadb2000000baa9a200000079a59200000038a182000000ed,0x1f79d70000001b69960000000f38d30000000b289217db5d20000013cb1c200000079a59200000038a182000000ed,0x1f80075e80071b80065a80061780055680051380045280040f80034e80030b80024a80020780014680010380004280000ee,0x1ffbdf2000000000001b699617db5d2000000000001349140fbadb2000000000000b2892079a592000000000000308100f0,0x1f80073f00071b80063b00061780053700051380043300040f80032f00030b80022b00020780012700010380002300000ee,0x1f81f01d81d01b81b01981901781701581501381301181100f80f00d80d00b80b00980900780700580500380300180100ef,0x1f81f01e81e01b81b01a81a01781701681601381301281200f80f00e80e00b80b00a80a00780700680600380300280200ef,0x1bedae99e58e000000000000038c288184081ffdef9df5cf000000000000079c698594490000000000000eb,0x1ffdef9df5cf1bedae99e58e00000000000000000000000017dd6d95d54d13cd2c91c50c0000000000000000000000000f2,0,0,0,0,0,0,0,0,0x1b81a819e58e0000000000000b80a809a48a17816815d54d13812811c50c078068059449038028018408103,0x1e81cf0000001a818e00000016814d00000012810c0f80db4e80cb0b809a4a808a078059468049038018428008104,0x1e81cf0000001a818e0000000e80cb0000000a808a17815d56814d13811c52810c078059468049038018428008104,0x1f81e81df5cf1b81a819e58e00000000000000000000000017816815d54d13812811c50c078068059449038028018408107,0x1f81e81df5cf1b81a819e58e0000e80000cb0000a800008a17816815d54d13812811c50c000068000049000028000008108,0x1f81e81df5cf1b81a819e58e0f80000db4000b800009a40017816815d54d13812811c50c078000059400038000018400109,0x1f81e81df5cf1b81a819e58e0f80e80db4cb00000000000017816815d54d13812811c50c07806805944900000000000010a,0,0x1f81d81ef9cf1b81981ae98e17815816d94d13811812c90c0f80d80eb8cb0b80980aa88a078058069849038018028808112,0x1f81f01df3d71b81b019e39617817015d35513813011c3140f80f00db2d30b80b009a292078070059251038030018210112,0x1f81d81f79d71b81981b69961781581759551381181349140f80d80f38d30b80980b2892078058071851038018030810112,0x1f81f01ef3e71b81b01ae3a617817016d36513813012c3240f80f00eb2e30b80b00aa2a2078070069261038030028220112,0x1f81e81f75e71b81a81b65a61781681755651381281345240f80e80f34e30b80a80b24a2078068071461038028030420112,0]
def alAt (i:Nat):Nat:=(if i<144 then (if i<48 then al0.getD (i-0) 0 else (if i<96 then al1.getD (i-48) 0 else al2.getD (i-96) 0)) else (if i<192 then al3.getD (i-144) 0 else (if i<240 then al4.getD (i-192) 0 else al5.getD (i-240) 0)))
def noHint (_ : Nat) : Nat := 0
def e0:Word:=0x8888
def e1:Word:=0x9900
def e2:Word:=0xa0a0
def e3:Word:=0xaa00
def e4:Word:=0xf0f0
def e5:Word:=0xf0000
def e6:Word:=0x990000
def e7:Word:=0xa50000
def e8:Word:=0x3003000
def e9:Word:=0x404c4c4
def ea:Word:=0x5005000
def eb:Word:=0x8008000
def ec:Word:=0x9000900
def ed:Word:=0xa000000
def ee:Word:=0xa00a000
def ef:Word:=0xa00a0a0
def eg:Word:=0xa02a020
def eh:Word:=0xa08a080
def ei:Word:=0xa0a0a0a
def ej:Word:=0xa0aa000
def ek:Word:=0xa0aa0a0
def el:Word:=0xa0aaaaa
def em:Word:=0xc00c000
def en:Word:=0xc00c0c0
def eo:Word:=0xc04c040
def ep:Word:=0xc08c080
def eq:Word:=0xc0cc000
def er:Word:=0xc0cc0c0
def es:Word:=0xc0ccccc
def et:Word:=0xf000000
def eu:Word:=0xf000f00
def ev:Word:=0xf00f000
def ew:Word:=0xf00ff00
def ex:Word:=0xf030000
def ey:Word:=0xf050000
def ez:Word:=0xf0a0000
def eA:Word:=0xf0c0000
def eB:Word:=0xf0f0000
def eC:Word:=0x11001100
def eD:Word:=0x21002100
def eE:Word:=0x22008800
def eF:Word:=0x22228888
def eG:Word:=0x30003000
def eH:Word:=0x3000c000
def eI:Word:=0x3030c0c0
def eJ:Word:=0x30c00000
def eK:Word:=0x33000000
def eL:Word:=0x3300cc00
def eM:Word:=0x33330000
def eN:Word:=0x44008800
def eO:Word:=0x44448888
def eP:Word:=0x5000a000
def eQ:Word:=0x5050a0a0
def eR:Word:=0x55000000
def eS:Word:=0x5500aa00
def eT:Word:=0x55550000
def eU:Word:=0x80802020
def eV:Word:=0x80808080
def eW:Word:=0x82008200
def eX:Word:=0x84008400
def eY:Word:=0x84008484
def eZ:Word:=0x84848400
def e10:Word:=0x84848484
def e11:Word:=0x88008800
def e12:Word:=0x88008888
def e13:Word:=0x88808880
def e14:Word:=0x88888800
def e15:Word:=0x88888888
def e16:Word:=0x8c008c00
def e17:Word:=0x8c8c8c8c
def e18:Word:=0x90009000
def e19:Word:=0x90009090
def e1a:Word:=0x90109010
def e1b:Word:=0x90809080
def e1c:Word:=0x90909000
def e1d:Word:=0x90909090
def e1e:Word:=0x99000000
def e1f:Word:=0x99009900
def e1g:Word:=0x99110000
def e1h:Word:=0x99880000
def e1i:Word:=0x99900000
def e1j:Word:=0x99990000
def e1k:Word:=0x99998888
def e1l:Word:=0x99999000
def e1m:Word:=0x99999900
def e1n:Word:=0xa000a000
def e1o:Word:=0xa000a0a0
def e1p:Word:=0xa020a020
def e1q:Word:=0xa080a080
def e1r:Word:=0xa0a0a000
def e1s:Word:=0xa0a0a0a0
def e1t:Word:=0xa5000000
def e1u:Word:=0xa500a500
def e1v:Word:=0xa5210000
def e1w:Word:=0xa5840000
def e1x:Word:=0xa5a50000
def e1y:Word:=0xaa00aa00
def e1z:Word:=0xaaaa0000
def e1A:Word:=0xaaaaaaaa
def e1B:Word:=0xaf000000
def e1C:Word:=0xaf00af00
def e1D:Word:=0xafaf0000
def e1E:Word:=0xb000b000
def e1F:Word:=0xb0b0b0b0
def e1G:Word:=0xbb000000
def e1H:Word:=0xbbbb0000
def e1I:Word:=0xc000c000
def e1J:Word:=0xc0c0c0c0
def e1K:Word:=0xc3000000
def e1L:Word:=0xcc00cc00
def e1M:Word:=0xcccccccc
def e1N:Word:=0xee00ee00
def e1O:Word:=0xf000f000
def e1P:Word:=0xf0f0f0f0
def e1Q:Word:=0xff000000
def e1R:Word:=0xff00ff00
def e1S:Word:=0xffff0000
def e1T:Word:=0xffffff00
def e1U:Word:=0xf00000000
def e1V:Word:=0x30030003000
def e1W:Word:=0x30300000000
def e1X:Word:=0xa000000a000
def e1Y:Word:=0xa0a0000a0a0
def e1Z:Word:=0xb000000bb00
def e20:Word:=0xc000000c000
def e21:Word:=0xc0c0000c0c0
def e22:Word:=0xf0000000000
def e23:Word:=0xf000000f000
def e24:Word:=0xf0f00000000
def e25:Word:=0x210000002100
def e26:Word:=0x840000008400
def e27:Word:=0x840000008484
def e28:Word:=0x840084008400
def e29:Word:=0x848400008484
def e2a:Word:=0x880000008800
def e2b:Word:=0x888800008888
def e2c:Word:=0x888888888888
def e2d:Word:=0x888899998888
def e2e:Word:=0x8c0000008c00
def e2f:Word:=0x8c8c00008c8c
def e2g:Word:=0x900000009000
def e2h:Word:=0x909000009090
def e2i:Word:=0x990000000000
def e2j:Word:=0x990000009900
def e2k:Word:=0x998800009988
def e2l:Word:=0x999900000000
def e2m:Word:=0xa0000000a000
def e2n:Word:=0xa0000000a0a0
def e2o:Word:=0xa000a000a000
def e2p:Word:=0xa0200000a020
def e2q:Word:=0xa0800000a080
def e2r:Word:=0xa0a00000a0a0
def e2s:Word:=0xa50000000000
def e2t:Word:=0xa5000000a500
def e2u:Word:=0xa52100000000
def e2v:Word:=0xa58400000000
def e2w:Word:=0xa5a500000000
def e2x:Word:=0xaa000000aa00
def e2y:Word:=0xaaaa0000aaaa
def e2z:Word:=0xaf0000000000
def e2A:Word:=0xaf000000af00
def e2B:Word:=0xcc000000cc00
def e2C:Word:=0xcccc0000cccc
def e2D:Word:=0xf0000000f000
def e2E:Word:=0xf0f00000f0f0
def e2F:Word:=0xff0000000000
def e2G:Word:=0xff000000ff00
def e2H:Word:=0xffff00000000
def e2I:Word:=0x3000003000000
def e2J:Word:=0x3030000000000
def e2K:Word:=0x4000440004000
def e2L:Word:=0x400c00400c000
def e2M:Word:=0x5000005000000
def e2N:Word:=0x7000007000000
def e2O:Word:=0x8000008000000
def e2P:Word:=0x8000880008000
def e2Q:Word:=0x8008008008000
def e2R:Word:=0x8800000088000
def e2S:Word:=0x9000000090000
def e2T:Word:=0x9900000000000
def e2U:Word:=0xa0000000a0000
def e2V:Word:=0xa000000a00000
def e2W:Word:=0xa00000a000000
def e2X:Word:=0xa00000a000a00
def e2Y:Word:=0xa0000a0000000
def e2Z:Word:=0xa00020a000200
def e30:Word:=0xa00080a000800
def e31:Word:=0xa000a00000000
def e32:Word:=0xa000a000a000a
def e33:Word:=0xa000a0a000000
def e34:Word:=0xa000a0a000a00
def e35:Word:=0xa000a0a0a0a0a
def e36:Word:=0xa000aa000a000
def e37:Word:=0xa000aa0a0a0a0
def e38:Word:=0xa00a000000000
def e39:Word:=0xa00a00000a000
def e3a:Word:=0xa00a00a00a000
def e3b:Word:=0xa0a0000000000
def e3c:Word:=0xa0a0000000a00
def e3d:Word:=0xa0a0000020200
def e3e:Word:=0xa0a0000080800
def e3f:Word:=0xa0a00000a0000
def e3g:Word:=0xa0a00000a0a00
def e3h:Word:=0xa0a0000a0a000
def e3i:Word:=0xa0a0a000a0a0a
def e3j:Word:=0xa0f0f00000000
def e3k:Word:=0xb0000b0000000
def e3l:Word:=0xb000b00000000
def e3m:Word:=0xc0000000c0000
def e3n:Word:=0xc00000c000000
def e3o:Word:=0xc00000c000c00
def e3p:Word:=0xc000030c00000
def e3q:Word:=0xc0000c0000000
def e3r:Word:=0xc00080c000800
def e3s:Word:=0xc000c00000000
def e3t:Word:=0xc000c0c000000
def e3u:Word:=0xc000c0c000c00
def e3v:Word:=0xc000c0c0c0c0c
def e3w:Word:=0xc000cc000c000
def e3x:Word:=0xc00c000000000
def e3y:Word:=0xc00c004004000
def e3z:Word:=0xc00c00400c000
def e3A:Word:=0xc00c00c00c000
def e3B:Word:=0xc0c0000000000
def e3C:Word:=0xc0c0000000c00
def e3D:Word:=0xc0c00000c0000
def e3E:Word:=0xc0c00000c0c00
def e3F:Word:=0xc0c0000c0c000
def e3G:Word:=0xe0000e0000000
def e3H:Word:=0xe000e00000000
def e3I:Word:=0xe000e000eeeee
def e3J:Word:=0xe00ee0e0eeeee
def e3K:Word:=0xeeeee000eeeee
def e3L:Word:=0xf000000000000
def e3M:Word:=0xf000000030000
def e3N:Word:=0xf0000000c0000
def e3O:Word:=0xf0000000f0000
def e3P:Word:=0xf000000f00000
def e3Q:Word:=0xf000005000000
def e3R:Word:=0xf000007000000
def e3S:Word:=0xf00000f000000
def e3T:Word:=0xf00000f0f0000
def e3U:Word:=0xf0000f0000000
def e3V:Word:=0xf0000f0f00000
def e3W:Word:=0xf000300000000
def e3X:Word:=0xf000a00000000
def e3Y:Word:=0xf000c00000000
def e3Z:Word:=0xf000f00000000
def e40:Word:=0xf00f000000000
def e41:Word:=0xf00f008000000
def e42:Word:=0xf00f008008000
def e43:Word:=0xf00f00a000000
def e44:Word:=0xf0f0000000000
def e45:Word:=0xf0f0f00000000
def e46:Word:=0x20002080008000
def e47:Word:=0x22000000220000
def e48:Word:=0x22000088000000
def e49:Word:=0x22002200000000
def e4a:Word:=0x22002222002200
def e4b:Word:=0x22220000222200
def e4c:Word:=0x22220000888800
def e4d:Word:=0x30003030003000
def e4e:Word:=0x30300000303000
def e4f:Word:=0x30300000c0c000
def e4g:Word:=0x33000000330000
def e4h:Word:=0x33000000cc0000
def e4i:Word:=0x33000033000000
def e4j:Word:=0x33003300000000
def e4k:Word:=0x33330000000000
def e4l:Word:=0x4400440044cccc
def e4m:Word:=0x44004444004400
def e4n:Word:=0x44008844008800
def e4o:Word:=0x50005050005000
def e4p:Word:=0x5000a05000a000
def e4q:Word:=0x55000055000000
def e4r:Word:=0x55005500000000
def e4s:Word:=0x5500aa00000000
def e4t:Word:=0x80008080808080
def e4u:Word:=0x88000088880000
def e4v:Word:=0x88008800000000
def e4w:Word:=0x88008800880088
def e4x:Word:=0x88008888008800
def e4y:Word:=0x880088f800f800
def e4z:Word:=0x88880000888800
def e4A:Word:=0x88888800888888
def e4B:Word:=0x8c000000008c00
def e4C:Word:=0x8c00008c000000
def e4D:Word:=0x8c00008c8c0000
def e4E:Word:=0x8c008c8c8c8c8c
def e4F:Word:=0x8c8c8c008c8c8c
def e4G:Word:=0x90009000900090
def e4H:Word:=0x90900000909000
def e4I:Word:=0x99000000990000
def e4J:Word:=0x99008899998888
def e4K:Word:=0x99990000000000
def e4L:Word:=0x99999900000000
def e4M:Word:=0xa000000000a000
def e4N:Word:=0xa00000a0000000
def e4O:Word:=0xa00000a0a00000
def e4P:Word:=0xa000a000000000
def e4Q:Word:=0xa000a0a000a000
def e4R:Word:=0xa000a0a0a0a0a0
def e4S:Word:=0xa0a00000a0a000
def e4T:Word:=0xa0a0a000a0a0a0
def e4U:Word:=0xaa000000000000
def e4V:Word:=0xaa0000000000aa
def e4W:Word:=0xaa00000000aa00
def e4X:Word:=0xaa000000aa0000
def e4Y:Word:=0xaa0000aa000000
def e4Z:Word:=0xaa0000aaaa0000
def e50:Word:=0xaa00aa00000000
def e51:Word:=0xaa00aa00aa0000
def e52:Word:=0xaa00aa00aa00aa
def e53:Word:=0xaa00aa00aaaaaa
def e54:Word:=0xaa00aa22222222
def e55:Word:=0xaa00aa22aa22aa
def e56:Word:=0xaa00aaaa00aa00
def e57:Word:=0xaa00aaaaaaaaaa
def e58:Word:=0xaaa0aa00aaa0aa
def e59:Word:=0xaaaa0000000000
def e5a:Word:=0xaaaa0000aaaa00
def e5b:Word:=0xaaaaaa00aaaaaa
def e5c:Word:=0xaaccee00aaccee
def e5d:Word:=0xaf000000000000
def e5e:Word:=0xaf000000af0000
def e5f:Word:=0xaf0000afaf0000
def e5g:Word:=0xaf00af00000000
def e5h:Word:=0xafafaf00000000
def e5i:Word:=0xc000c0c000c000
def e5j:Word:=0xc0c00000c0c000
def e5k:Word:=0xcc000000000000
def e5l:Word:=0xcc0000000000cc
def e5m:Word:=0xcc00000000cc00
def e5n:Word:=0xcc000000cc0000
def e5o:Word:=0xcc0000cc000000
def e5p:Word:=0xcc00cc00000000
def e5q:Word:=0xcc00cc00cc00cc
def e5r:Word:=0xcc00cc00cccccc
def e5s:Word:=0xcc00cccc00cc00
def e5t:Word:=0xcc88cc00cc88cc
def e5u:Word:=0xccc0cc00ccc0cc
def e5v:Word:=0xcccc0000000000
def e5w:Word:=0xcccc0000cccc00
def e5x:Word:=0xee0000eeeeeeee
def e5y:Word:=0xee00ee00ee0000
def e5z:Word:=0xee00ee00ee00ee
def e5A:Word:=0xee00ee00eeeeee
def e5B:Word:=0xee00eeeeeeeeee
def e5C:Word:=0xeee0ee00eee0ee
def e5D:Word:=0xeeeeee00eeeeee
def e5E:Word:=0xf0000000000000
def e5F:Word:=0xf00000000000f0
def e5G:Word:=0xf000000000f000
def e5H:Word:=0xf0000000f00000
def e5I:Word:=0xf00000f0000000
def e5J:Word:=0xf000f000000000
def e5K:Word:=0xf000f000f000f0
def e5L:Word:=0xf000f0f000f000
def e5M:Word:=0xf0a0f000f0a0f0
def e5N:Word:=0xf0f00000000000
def e5O:Word:=0xf0f00000f0f000
def e5P:Word:=0xf80088f8f88888
def e5Q:Word:=0xfe00fe00fe00f0
def e5R:Word:=0xff000000000000
def e5S:Word:=0xff000000ff0000
def e5T:Word:=0xff0000ff000000
def e5U:Word:=0xff00aa00ff00aa
def e5V:Word:=0xff00f000ff00f0
def e5W:Word:=0xff00ff00000000
def e5X:Word:=0xff00ff00ff0000
def e5Y:Word:=0xffff0000000000
def e5Z:Word:=0xffffff00000000
def e60:Word:=0x100000004000000
def e61:Word:=0x100000010000000
def e62:Word:=0x100010001000100
def e63:Word:=0x100010010001000
def e64:Word:=0x100020000000000
def e65:Word:=0x100020004000800
def e66:Word:=0x100020010002000
def e67:Word:=0x100040010004000
def e68:Word:=0x101000001010000
def e69:Word:=0x101000004040000
def e6a:Word:=0x101000010100000
def e6b:Word:=0x101010100000000
def e6c:Word:=0x101020200000000
def e6d:Word:=0x101040400000000
def e6e:Word:=0x104000001040000
def e6f:Word:=0x104000010400000
def e6g:Word:=0x104010400000000
def e6h:Word:=0x104020800000000
def e6i:Word:=0x108000000000000
def e6j:Word:=0x108000010800000
def e6k:Word:=0x108010800000000
def e6l:Word:=0x200020010001000
def e6m:Word:=0x200020020002000
def e6n:Word:=0x202000002020000
def e6o:Word:=0x202000020200000
def e6p:Word:=0x202020200000000
def e6q:Word:=0x208000010400000
def e6r:Word:=0x208000020800000
def e6s:Word:=0x208020800000000
def e6t:Word:=0x208020802080208
def e6u:Word:=0x208020820802080
def e6v:Word:=0x220022002200220
def e6w:Word:=0x300000003000000
def e6x:Word:=0x300000030000000
def e6y:Word:=0x300020003000200
def e6z:Word:=0x300030000000000
def e6A:Word:=0x300030003000300
def e6B:Word:=0x300030020002000
def e6C:Word:=0x300030030003000
def e6D:Word:=0x300200003002000
def e6E:Word:=0x302000030200000
def e6F:Word:=0x303000000000000
def e6G:Word:=0x303000003030000
def e6H:Word:=0x308000003080000
def e6I:Word:=0x308030800000000
def e6J:Word:=0x30c000000000000
def e6K:Word:=0x30c0000030c0000
def e6L:Word:=0x30c000020800000
def e6M:Word:=0x30c000030c00000
def e6N:Word:=0x30c020800000000
def e6O:Word:=0x30c030c00000000
def e6P:Word:=0x30c208000000000
def e6Q:Word:=0x320000003200000
def e6R:Word:=0x320032000000000
def e6S:Word:=0x330000003300000
def e6T:Word:=0x330033000000000
def e6U:Word:=0x400040004000400
def e6V:Word:=0x400040040004000
def e6W:Word:=0x400040084008400
def e6X:Word:=0x400840004008400
def e6Y:Word:=0x404000004040000
def e6Z:Word:=0x404040404048c8c
def e70:Word:=0x4040404c0c0c0c0
def e71:Word:=0x4040c0c4040c0c0
def e72:Word:=0x408000004080000
def e73:Word:=0x408040800000000
def e74:Word:=0x408040804080408
def e75:Word:=0x408040840804080
def e76:Word:=0x40c000040c00000
def e77:Word:=0x40c0404040c0404
def e78:Word:=0x40c040c040c040c
def e79:Word:=0x40c040c40c040c0
def e7a:Word:=0x420000004200000
def e7b:Word:=0x420042000000000
def e7c:Word:=0x480048004800480
def e7d:Word:=0x48c048c048c8c8c
def e7e:Word:=0x500000005000000
def e7f:Word:=0x500000050000000
def e7g:Word:=0x5000000a5000000
def e7h:Word:=0x500050000000000
def e7i:Word:=0x500050005000500
def e7j:Word:=0x50005000500af00
def e7k:Word:=0x500050050005000
def e7l:Word:=0x5000500f000f000
def e7m:Word:=0x5000f0005000f00
def e7n:Word:=0x500a50000000000
def e7o:Word:=0x505000000000000
def e7p:Word:=0x505000005050000
def e7q:Word:=0x5050000f0f00000
def e7r:Word:=0x5050f0f00000000
def e7s:Word:=0x50a0000050a0000
def e7t:Word:=0x50a000050a00000
def e7u:Word:=0x50a050a00000000
def e7v:Word:=0x50f000000000000
def e7w:Word:=0x50f0000050f0000
def e7x:Word:=0x50f050f00000000
def e7y:Word:=0x5a0000005a00000
def e7z:Word:=0x5a005a000000000
def e7A:Word:=0x700070070007000
def e7B:Word:=0x707000070700000
def e7C:Word:=0x707070700000000
def e7D:Word:=0x800020008000200
def e7E:Word:=0x800020088002200
def e7F:Word:=0x800030008000300
def e7G:Word:=0x800040008000400
def e7H:Word:=0x800050008000500
def e7I:Word:=0x800080003000300
def e7J:Word:=0x800080008000800
def e7K:Word:=0x800080020002000
def e7L:Word:=0x800080040004000
def e7M:Word:=0x800080088008800
def e7N:Word:=0x8000800f000f000
def e7O:Word:=0x808000002020202
def e7P:Word:=0x808000003030000
def e7Q:Word:=0x808000004040000
def e7R:Word:=0x808000008080000
def e7S:Word:=0x808000020200000
def e7T:Word:=0x808000040400000
def e7U:Word:=0x808000080800000
def e7V:Word:=0x808000088880000
def e7W:Word:=0x8080000f0f00000
def e7X:Word:=0x808000802020002
def e7Y:Word:=0x808020200000000
def e7Z:Word:=0x808020200080002
def e80:Word:=0x808020208080000
def e81:Word:=0x808020208080202
def e82:Word:=0x808030300000000
def e83:Word:=0x808040408080404
def e84:Word:=0x808050500000000
def e85:Word:=0x808080008080800
def e86:Word:=0x808080800000000
def e87:Word:=0x808080802020202
def e88:Word:=0x808080808080808
def e89:Word:=0x808080880808080
def e8a:Word:=0x808080888888888
def e8b:Word:=0x8080808f080f080
def e8c:Word:=0x808808008088080
def e8d:Word:=0x80a0000080a0000
def e8e:Word:=0x80a040500000000
def e8f:Word:=0x80a080a00000000
def e8g:Word:=0x880000008800000
def e8h:Word:=0x880088000000000
def e8i:Word:=0x900000099000000
def e8j:Word:=0x900090000000000
def e8k:Word:=0x900090009000900
def e8l:Word:=0x909000009090000
def e8m:Word:=0x909090900000000
def e8n:Word:=0x999099909990000
def e8o:Word:=0xa00000005000000
def e8p:Word:=0xa000000a0000000
def e8q:Word:=0xa0004000a000400
def e8r:Word:=0xa0008000a000800
def e8s:Word:=0xa000a0008000800
def e8t:Word:=0xa000a000a000a00
def e8u:Word:=0xa000a00a000a000
def e8v:Word:=0xa000a00aa00aa00
def e8w:Word:=0xa000a00e0c0e0c0
def e8x:Word:=0xa000a0a0a000a0a
def e8y:Word:=0xa00a0000a00a000
def e8z:Word:=0xa0800000a080000
def e8A:Word:=0xa080a0800000000
def e8B:Word:=0xa0a000000000000
def e8C:Word:=0xa0a00000000000a
def e8D:Word:=0xa0a000000000808
def e8E:Word:=0xa0a000000000a0a
def e8F:Word:=0xa0a00000000a0a0
def e8G:Word:=0xa0a0000000a0000
def e8H:Word:=0xa0a000008080000
def e8I:Word:=0xa0a00000a0a0000
def e8J:Word:=0xa0a0000a0a00000
def e8K:Word:=0xa0a000a00000000
def e8L:Word:=0xa0a040400000000
def e8M:Word:=0xa0a080800000000
def e8N:Word:=0xa0a08080a0a0808
def e8O:Word:=0xa0a0a0000000000
def e8P:Word:=0xa0a0a0a00000000
def e8Q:Word:=0xa0a0a0a00a000a0
def e8R:Word:=0xa0a0a0a0a0a0a0a
def e8S:Word:=0xa0a0a0aa0a0a0a0
def e8T:Word:=0xa0a0a0aaa000000
def e8U:Word:=0xa0a0a0aaaaa0000
def e8V:Word:=0xa0a0a0aaaaaaaaa
def e8W:Word:=0xa0aa0a000000000
def e8X:Word:=0xa0aa0a00a0aa0a0
def e8Y:Word:=0xb000000bb000000
def e8Z:Word:=0xb000b000b000b00
def e90:Word:=0xb000b00bb00bb00
def e91:Word:=0xb0b0000bbbb0000
def e92:Word:=0xb0b030300000000
def e93:Word:=0xb0b0b0b00000000
def e94:Word:=0xb0b0b0bbb000000
def e95:Word:=0xb0b0b0bbbbb0000
def e96:Word:=0xc00000003000000
def e97:Word:=0xc00000003000300
def e98:Word:=0xc00030000000000
def e99:Word:=0xc0003000c000000
def e9a:Word:=0xc0003000c000300
def e9b:Word:=0xc0008000c000800
def e9c:Word:=0xc000c000c000c00
def e9d:Word:=0xc000c00c000c000
def e9e:Word:=0xc0020000c002000
def e9f:Word:=0xc00c0000c00c000
def e9g:Word:=0xc0800000c080000
def e9h:Word:=0xc080000c0800000
def e9i:Word:=0xc0c000000000000
def e9j:Word:=0xc0c00000000000c
def e9k:Word:=0xc0c000000000c0c
def e9l:Word:=0xc0c00000000c0c0
def e9m:Word:=0xc0c0000000c0000
def e9n:Word:=0xc0c000003030000
def e9o:Word:=0xc0c00000c0c0000
def e9p:Word:=0xc0c0000c0c00000
def e9q:Word:=0xc0c000c00000000
def e9r:Word:=0xc0c030300000000
def e9s:Word:=0xc0c080800000000
def e9t:Word:=0xc0c08080c0c0808
def e9u:Word:=0xc0c0c0000000000
def e9v:Word:=0xc0c0c0c00000000
def e9w:Word:=0xc0c0c0c0c0c0c0c
def e9x:Word:=0xc0c0c0c40404040
def e9y:Word:=0xc0c0c0cc0c0c0c0
def e9z:Word:=0xc0c202000000000
def e9A:Word:=0xc0cc0c000000000
def e9B:Word:=0xc0cc0c00c0cc0c0
def e9C:Word:=0xc0f0c0c0c0f0c0c
def e9D:Word:=0xd0d000000000000
def e9E:Word:=0xe0c0000e0c00000
def e9F:Word:=0xe0c0e0ca000a000
def e9G:Word:=0xe0e0000e0e00000
def e9H:Word:=0xe0e0000eeeeeeee
def e9I:Word:=0xe0e0e0e0e0e0000
def e9J:Word:=0xe0eeeee0e0eeeee
def e9K:Word:=0xeee0e0e0eee0e0e
def e9L:Word:=0xeee0eee00000eee
def e9M:Word:=0xeee0eee0eee0000
def e9N:Word:=0xeee0eee0eee0eee
def e9O:Word:=0xf00000000000000
def e9P:Word:=0xf00000000000c00
def e9Q:Word:=0xf00000000000f00
def e9R:Word:=0xf0000000000f000
def e9S:Word:=0xf0000000c000000
def e9T:Word:=0xf0000000f000000
def e9U:Word:=0xf000000f0000000
def e9V:Word:=0xf000a0000000000
def e9W:Word:=0xf000a000f000a00
def e9X:Word:=0xf000c000f000c00
def e9Y:Word:=0xf000f0000000000
def e9Z:Word:=0xf000f000f000f00
def ea0:Word:=0xf000f0050005000
def ea1:Word:=0xf000f00f000f000
def ea2:Word:=0xf000f00ffff0f00
def ea3:Word:=0xf00f00000000000
def ea4:Word:=0xf00f0000f00f000
def ea5:Word:=0xf00ff000f00ff00
def ea6:Word:=0xf0500000f050000
def ea7:Word:=0xf080f0880808080
def ea8:Word:=0xf0a000000000000
def ea9:Word:=0xf0a0000f0a00000
def eaa:Word:=0xf0a0f000f0a0f00
def eab:Word:=0xf0c000000000000
def eac:Word:=0xf0e0f0e0f0e0c0c
def ead:Word:=0xf0e0f0e0f0e0f00
def eae:Word:=0xf0f000000000000
def eaf:Word:=0xf0f00000f0f0000
def eag:Word:=0xf0f0000f0f00000
def eah:Word:=0xf0f0a0a00000000
def eai:Word:=0xf0f0c0c00000000
def eaj:Word:=0xf0f0f000f0f0f00
def eak:Word:=0xf0f0f00f0f00000
def eal:Word:=0xf0f0f0f00000000
def eam:Word:=0xf0f0f0f80808080
def ean:Word:=0xf0ff0f000000000
def eao:Word:=0xf0fffff00000000
def eap:Word:=0xfff00000fff0000
def eaq:Word:=0xfff0fff0fff0000
def ear:Word:=0x1010101010101010
def eas:Word:=0x1010101010109090
def eat:Word:=0x101010101010f0f0
def eau:Word:=0x1010101010909090
def eav:Word:=0x1010101099991010
def eaw:Word:=0x1010109010101090
def eax:Word:=0x101030305050f0f0
def eay:Word:=0x1010909010109090
def eaz:Word:=0x1020102010201020
def eaA:Word:=0x1020408010204080
def eaB:Word:=0x103050f0103050f0
def eaC:Word:=0x1080108010801080
def eaD:Word:=0x1099101010991010
def eaE:Word:=0x10f010f010f010f0
def eaF:Word:=0x10f010f010f0f0f0
def eaG:Word:=0x1100110011001100
def eaH:Word:=0x110011001100ff00
def eaI:Word:=0x110033005500ff00
def eaJ:Word:=0x1100440011004400
def eaK:Word:=0x111011101110fff0
def eaL:Word:=0x1111000011110000
def eaM:Word:=0x1111110011111100
def eaN:Word:=0x1111111111000000
def eaO:Word:=0x1111111111110000
def eaP:Word:=0x1111999911110000
def eaQ:Word:=0x1122000011220000
def eaR:Word:=0x1122112200000000
def eaS:Word:=0x1122448800000000
def eaT:Word:=0x113355ff00000000
def eaU:Word:=0x1188000011880000
def eaV:Word:=0x1188118800000000
def eaW:Word:=0x1199119911990000
def eaX:Word:=0x1900190019001900
def eaY:Word:=0x1919190019191900
def eaZ:Word:=0x1919191919190000
def eb0:Word:=0x2000030020000300
def eb1:Word:=0x2000200003000300
def eb2:Word:=0x2000200020002000
def eb3:Word:=0x2020000003030000
def eb4:Word:=0x2020000020200000
def eb5:Word:=0x2020020220200202
def eb6:Word:=0x2020030300000000
def eb7:Word:=0x2020200020202000
def eb8:Word:=0x2020202000000000
def eb9:Word:=0x2020202002020202
def eba:Word:=0x2020202020002000
def ebb:Word:=0x2020202020202020
def ebc:Word:=0x2020202080808080
def ebd:Word:=0x20202020a0a0a0a0
def ebe:Word:=0x2020808020208080
def ebf:Word:=0x2020a0a02020a0a0
def ebg:Word:=0x2021000020210000
def ebh:Word:=0x2021202100000000
def ebi:Word:=0x2100200021002000
def ebj:Word:=0x2100210020002000
def ebk:Word:=0x2100210021002100
def ebl:Word:=0x2121000020200000
def ebm:Word:=0x2121000021210000
def ebn:Word:=0x2121202000000000
def ebo:Word:=0x2121212100000000
def ebp:Word:=0x2200220022002200
def ebq:Word:=0x2200220088008800
def ebr:Word:=0x2200880022008800
def ebs:Word:=0x2222000000002222
def ebt:Word:=0x2222000022000000
def ebu:Word:=0x2222000022220000
def ebv:Word:=0x2222000088880000
def ebw:Word:=0x2222220000000000
def ebx:Word:=0x2222222200000000
def eby:Word:=0x2222222222222222
def ebz:Word:=0x2222222288888888
def ebA:Word:=0x22222222aaaaaaaa
def ebB:Word:=0x2222888800000000
def ebC:Word:=0x2222888822228888
def ebD:Word:=0x2222aaaa2222aaaa
def ebE:Word:=0x22aa000022aa22aa
def ebF:Word:=0x22aa222222aa2222
def ebG:Word:=0x22aa22aa22aa0000
def ebH:Word:=0x22aa22aa22aa22aa
def ebI:Word:=0x2300000023002300
def ebJ:Word:=0x2300230023002300
def ebK:Word:=0x23002300af00af00
def ebL:Word:=0x2300af002300af00
def ebM:Word:=0x2323000023230000
def ebN:Word:=0x23230000afaf0000
def ebO:Word:=0x2323232300000000
def ebP:Word:=0x2323afaf00000000
def ebQ:Word:=0x23af23af23af0000
def ebR:Word:=0x3000030030000300
def ebS:Word:=0x3000300030003000
def ebT:Word:=0x3000c0003000c000
def ebU:Word:=0x3030000000003030
def ebV:Word:=0x3030000030300000
def ebW:Word:=0x3030030300000000
def ebX:Word:=0x3030303000000000
def ebY:Word:=0x3030303030303030
def ebZ:Word:=0x30303030c0c0c0c0
def ec0:Word:=0x3030c0c000000000
def ec1:Word:=0x3030c0c03030c0c0
def ec2:Word:=0x307030703070f0f0
def ec3:Word:=0x3300000000003300
def ec4:Word:=0x3300000033000000
def ec5:Word:=0x3300330000000000
def ec6:Word:=0x3300330033003300
def ec7:Word:=0x33003300cc00cc00
def ec8:Word:=0x3300cc0000000000
def ec9:Word:=0x3300cc003300cc00
def eca:Word:=0x3322332233220000
def ecb:Word:=0x3333000000000000
def ecc:Word:=0x3333000033330000
def ecd:Word:=0x33330000cccc0000
def ece:Word:=0x3333330033333300
def ecf:Word:=0x3333333300000000
def ecg:Word:=0x3333cccc00000000
def ech:Word:=0x3f3f0f0f33330000
def eci:Word:=0x4040101040401010
def ecj:Word:=0x4040404004040404
def eck:Word:=0x4040404040404040
def ecl:Word:=0x4040808040408080
def ecm:Word:=0x4400110044001100
def ecn:Word:=0x4400440044004400
def eco:Word:=0x4400880044008800
def ecp:Word:=0x4444000044440000
def ecq:Word:=0x4444111100000000
def ecr:Word:=0x4444444400000000
def ecs:Word:=0x4444444444444444
def ect:Word:=0x4444444488888888
def ecu:Word:=0x4444888800000000
def ecv:Word:=0x4444888844448888
def ecw:Word:=0x5000500005000500
def ecx:Word:=0x5000500050005000
def ecy:Word:=0x5000a0005000a000
def ecz:Word:=0x5050000005050000
def ecA:Word:=0x5050000050500000
def ecB:Word:=0x5050505000000000
def ecC:Word:=0x5050505050505050
def ecD:Word:=0x50505050a0a0a0a0
def ecE:Word:=0x5050a0a05050a0a0
def ecF:Word:=0x5500000055000000
def ecG:Word:=0x5500550055005500
def ecH:Word:=0x55005500aa00aa00
def ecI:Word:=0x55005500ffff5500
def ecJ:Word:=0x5500aa0000000000
def ecK:Word:=0x5500aa005500aa00
def ecL:Word:=0x5500ddcc5500ddcc
def ecM:Word:=0x5500ff005500ff00
def ecN:Word:=0x5555000000000000
def ecO:Word:=0x5555000055550000
def ecP:Word:=0x55550000aaaa0000
def ecQ:Word:=0x5555550055555500
def ecR:Word:=0x5555555500000000
def ecS:Word:=0x5555aaaa00000000
def ecT:Word:=0x5555ffff00000000
def ecU:Word:=0x55aa55aa55aa55aa
def ecV:Word:=0x55cc55cc55cc55cc
def ecW:Word:=0x55ff000055ff0000
def ecX:Word:=0x55ff44cc55ff44cc
def ecY:Word:=0x55ff55ff55ff0000
def ecZ:Word:=0x5f0f5f0f55005500
def ed0:Word:=0x7077707070777070
def ed1:Word:=0x7700770077007700
def ed2:Word:=0x7733550077335500
def ed3:Word:=0x7770777077707770
def ed4:Word:=0x7777000077770000
def ed5:Word:=0x7777333355550000
def ed6:Word:=0x7777707077777070
def ed7:Word:=0x7777770077777700
def ed8:Word:=0x7777777777770000
def ed9:Word:=0x8000080080000800
def eda:Word:=0x8000100080001000
def edb:Word:=0x8000800008000800
def edc:Word:=0x8000840080008400
def edd:Word:=0x8008000080080000
def ede:Word:=0x8008100100000000
def edf:Word:=0x8008800880088008
def edg:Word:=0x8020802080208020
def edh:Word:=0x8040804080408040
def edi:Word:=0x8080000008080000
def edj:Word:=0x8080000080800000
def edk:Word:=0x8080080800000000
def edl:Word:=0x8080101080801010
def edm:Word:=0x8080800080808000
def edn:Word:=0x8080808000000000
def edo:Word:=0x8080808010101010
def edp:Word:=0x8080808080808080
def edq:Word:=0x8080808099998080
def edr:Word:=0x8099808080998080
def eds:Word:=0x80a080a080a080a0
def edt:Word:=0x80f080f080f080f0
def edu:Word:=0x8200820082008200
def edv:Word:=0x8241000082410000
def edw:Word:=0x8241824100000000
def edx:Word:=0x8282000082820000
def edy:Word:=0x8282828200000000
def edz:Word:=0x8282828282828282
def edA:Word:=0x8400840084008400
def edB:Word:=0x8421000084210000
def edC:Word:=0x8421842100000000
def edD:Word:=0x8484000084840000
def edE:Word:=0x8484848400000000
def edF:Word:=0x8484848484848484
def edG:Word:=0x8800000000008800
def edH:Word:=0x8800110088001100
def edI:Word:=0x8800880011001100
def edJ:Word:=0x8800880088008800
def edK:Word:=0x8800888888008888
def edL:Word:=0x8822000088220000
def edM:Word:=0x8822882200000000
def edN:Word:=0x8822882288228822
def edO:Word:=0x8844000088440000
def edP:Word:=0x8844884400000000
def edQ:Word:=0x8844884488448844
def edR:Word:=0x8888000000008888
def edS:Word:=0x8888000011110000
def edT:Word:=0x8888000088880000
def edU:Word:=0x8888111100000000
def edV:Word:=0x8888880088888800
def edW:Word:=0x8888888800000000
def edX:Word:=0x8888888800008888
def edY:Word:=0x8888888888000000
def edZ:Word:=0x8888888888880000
def ee0:Word:=0x8888888888888000
def ee1:Word:=0x8888888888888888
def ee2:Word:=0x88888888ffff8888
def ee3:Word:=0x8888999900000000
def ee4:Word:=0x8888f8f88888f8f8
def ee5:Word:=0x8899889988990000
def ee6:Word:=0x88aa000088aa0000
def ee7:Word:=0x88aa88aa00000000
def ee8:Word:=0x88f888f888f80000
def ee9:Word:=0x88f888f888f888f8
def eea:Word:=0x88ff888888ff8888
def eeb:Word:=0x8900890089008900
def eec:Word:=0x8988898889880900
def eed:Word:=0x8989890089898900
def eee:Word:=0x8989898989890000
def eef:Word:=0x8a8a8a8a8a8a8a8a
def eeg:Word:=0x8c0000008c008c00
def eeh:Word:=0x8c008c008c008c00
def eei:Word:=0x8c008c8c8c008c8c
def eej:Word:=0x8c2300008c230000
def eek:Word:=0x8c238c2300000000
def eel:Word:=0x8c8c000000000000
def eem:Word:=0x8c8c00008c8c0000
def een:Word:=0x8c8c00008c8c8c8c
def eeo:Word:=0x8c8c8c008c8c8c00
def eep:Word:=0x8c8c8c8c00000000
def eeq:Word:=0x8c8c8c8c00008c8c
def eer:Word:=0x8c8c8c8c8c008c00
def ees:Word:=0x8c8c8c8c8c8c8c8c
def eet:Word:=0x8c8cafaf00000000
def eeu:Word:=0x8caf8c8c8caf8c8c
def eev:Word:=0x8caf8caf8caf0000
def eew:Word:=0x8f888f888f888f88
def eex:Word:=0x8f8f88888f8f8888
def eey:Word:=0x9000000000009000
def eez:Word:=0x9000000009000000
def eeA:Word:=0x9000090000000000
def eeB:Word:=0x9000900090009000
def eeC:Word:=0x9000909090009090
def eeD:Word:=0x9009000090090000
def eeE:Word:=0x9009900900000000
def eeF:Word:=0x9010901090109010
def eeG:Word:=0x9080908090809080
def eeH:Word:=0x9090000000000000
def eeI:Word:=0x9090000000009090
def eeJ:Word:=0x9090000090900000
def eeK:Word:=0x9090900090909000
def eeL:Word:=0x9090909000000000
def eeM:Word:=0x9090909090000000
def eeN:Word:=0x9090909090900000
def eeO:Word:=0x9090909090909090
def eeP:Word:=0x9800980098009000
def eeQ:Word:=0x9888988898889000
def eeR:Word:=0x9898989898989090
def eeS:Word:=0x9900000000000000
def eeT:Word:=0x9900000000009900
def eeU:Word:=0x9900000099000000
def eeV:Word:=0x9900090099000900
def eeW:Word:=0x9900100099001000
def eeX:Word:=0x9900110099001100
def eeY:Word:=0x9900800099008000
def eeZ:Word:=0x9900880099008800
def ef0:Word:=0x9900888899008888
def ef1:Word:=0x9900990000000000
def ef2:Word:=0x9900990000001100
def ef3:Word:=0x9900990000008800
def ef4:Word:=0x9900990000009000
def ef5:Word:=0x9900990099000000
def ef6:Word:=0x9900990099009900
def ef7:Word:=0x9900998800008888
def ef8:Word:=0x9900999000009090
def ef9:Word:=0x9910101099101010
def efa:Word:=0x9980808099808080
def efb:Word:=0x9988000099880000
def efc:Word:=0x9988998899889988
def efd:Word:=0x9999000000000000
def efe:Word:=0x9999000099990000
def eff:Word:=0x9999000099998888
def efg:Word:=0x9999101010101010
def efh:Word:=0x9999101099991010
def efi:Word:=0x9999110099991100
def efj:Word:=0x9999111100000000
def efk:Word:=0x9999808080808080
def efl:Word:=0x9999808099998080
def efm:Word:=0x9999880099998800
def efn:Word:=0x9999888899998888
def efo:Word:=0x9999900099999000
def efp:Word:=0x9999990000000000
def efq:Word:=0x9999990099999900
def efr:Word:=0x9999999900000000
def efs:Word:=0x9999999900008888
def eft:Word:=0x9999999900009090
def efu:Word:=0x9999999911110000
def efv:Word:=0x9999999988880000
def efw:Word:=0x9999999990900000
def efx:Word:=0x9999999999000000
def efy:Word:=0x9999999999990000
def efz:Word:=0x9999999999999000
def efA:Word:=0xa0000000a0000000
def efB:Word:=0xa000a000a000a000
def efC:Word:=0xa000a50000000000
def efD:Word:=0xa00a0000a00a0000
def efE:Word:=0xa00aa00a00000000
def efF:Word:=0xa00aa00aa00aa00a
def efG:Word:=0xa020a020a020a020
def efH:Word:=0xa0500000a0500000
def efI:Word:=0xa050a05000000000
def efJ:Word:=0xa050a050a050a050
def efK:Word:=0xa080a080a080a080
def efL:Word:=0xa0a0000000000000
def efM:Word:=0xa0a000000000a0a0
def efN:Word:=0xa0a00000a0a00000
def efO:Word:=0xa0a00000a0a0a0a0
def efP:Word:=0xa0a02020a0a02020
def efQ:Word:=0xa0a08080a0a08080
def efR:Word:=0xa0a0a000a0a0a000
def efS:Word:=0xa0a0a0a000000000
def efT:Word:=0xa0a0a0a00000a0a0
def efU:Word:=0xa0a0a0a020202020
def efV:Word:=0xa0a0a0a080808080
def efW:Word:=0xa0a0a0a0a000a000
def efX:Word:=0xa0a0a0a0a0a0a0a0
def efY:Word:=0xa2a2a2a2a2a2a2a2
def efZ:Word:=0xa3a00000a3a0a3a0
def eg0:Word:=0xa3a0a3a0a3a0a3a0
def eg1:Word:=0xa5000000a5000000
def eg2:Word:=0xa500a50000000000
def eg3:Word:=0xa500a500a500a500
def eg4:Word:=0xa5210000a5210000
def eg5:Word:=0xa521a52100000000
def eg6:Word:=0xa5a50000a5a50000
def eg7:Word:=0xa5a5a5a500000000
def eg8:Word:=0xaa0000000000aa00
def eg9:Word:=0xaa00aa00aa000000
def ega:Word:=0xaa00aa00aa00aa00
def egb:Word:=0xaa00aa00ffffaa00
def egc:Word:=0xaa00aaaa00000000
def egd:Word:=0xaa00aaaaaa00aaaa
def ege:Word:=0xaa00eeccaa00eecc
def egf:Word:=0xaa00ff00aa00ff00
def egg:Word:=0xaa220000aa220000
def egh:Word:=0xaa22aa2200000000
def egi:Word:=0xaa22aa22aa220000
def egj:Word:=0xaa22aa22aa22aa22
def egk:Word:=0xaa550000aa550000
def egl:Word:=0xaa55aa5500000000
def egm:Word:=0xaa88aa88aa88aa88
def egn:Word:=0xaaaa000000000000
def ego:Word:=0xaaaa00000000aaaa
def egp:Word:=0xaaaa0000aaaa0000
def egq:Word:=0xaaaa0000aaaaaaaa
def egr:Word:=0xaaaa2222aaaa2222
def egs:Word:=0xaaaa8888aaaa8888
def egt:Word:=0xaaaaaa00aa00aa00
def egu:Word:=0xaaaaaa00aaaaaa00
def egv:Word:=0xaaaaaaaa00000000
def egw:Word:=0xaaaaaaaa0000aa00
def egx:Word:=0xaaaaaaaa0000aaaa
def egy:Word:=0xaaaaaaaa22222222
def egz:Word:=0xaaaaaaaa88888888
def egA:Word:=0xaaaaaaaaaa00aa00
def egB:Word:=0xaaaaaaaaaaaa0000
def egC:Word:=0xaaaaaaaaaaaaaaaa
def egD:Word:=0xaaaaffff00000000
def egE:Word:=0xaaff0000aaff0000
def egF:Word:=0xaaff88ccaaff88cc
def egG:Word:=0xaaffaa00aaffaa00
def egH:Word:=0xaaffaaaaaaffaaaa
def egI:Word:=0xaaffaaffaaff0000
def egJ:Word:=0xacac2020acac2020
def egK:Word:=0xaeaaaeaaaeaa8c00
def egL:Word:=0xaf00000000000000
def egM:Word:=0xaf000000af000000
def egN:Word:=0xaf000000af00af00
def egO:Word:=0xaf002300af002300
def egP:Word:=0xaf008c00af008c00
def egQ:Word:=0xaf00af0000000000
def egR:Word:=0xaf00af000000af00
def egS:Word:=0xaf00af0023002300
def egT:Word:=0xaf00af008c008c00
def egU:Word:=0xaf00af00af000000
def egV:Word:=0xaf00af00af00af00
def egW:Word:=0xaf00afaf00000000
def egX:Word:=0xaf0faf0faa00aa00
def egY:Word:=0xaf230000af230000
def egZ:Word:=0xaf23af2300000000
def eh0:Word:=0xaf23af23af230000
def eh1:Word:=0xaf8c0000af8c0000
def eh2:Word:=0xaf8ca080af8ca080
def eh3:Word:=0xaf8caf8c00000000
def eh4:Word:=0xafa0afa0afa0a0a0
def eh5:Word:=0xafaf000000000000
def eh6:Word:=0xafaf000023230000
def eh7:Word:=0xafaf00008c8c0000
def eh8:Word:=0xafaf0000af000000
def eh9:Word:=0xafaf0000afaf0000
def eha:Word:=0xafaf232300000000
def ehb:Word:=0xafaf8c8c00000000
def ehc:Word:=0xafafaf0000000000
def ehd:Word:=0xafafafaf00000000
def ehe:Word:=0xafafafafafaf0000
def ehf:Word:=0xb0b0b0b0b0b0b0b0
def ehg:Word:=0xbb00bb00bb00bb00
def ehh:Word:=0xbb33aa00bb33aa00
def ehi:Word:=0xbbbb0000bbbb0000
def ehj:Word:=0xbbbb3333aaaa0000
def ehk:Word:=0xbbbbbbbb00000000
def ehl:Word:=0xc000c000c000c000
def ehm:Word:=0xc00c0000c00c0000
def ehn:Word:=0xc00cc00c00000000
def eho:Word:=0xc00cc00cc00cc00c
def ehp:Word:=0xc0c000000000c0c0
def ehq:Word:=0xc0c00000c0c00000
def ehr:Word:=0xc0c0c0c000000000
def ehs:Word:=0xc0c0c0c0c0c0c0c0
def eht:Word:=0xc300c300c300c300
def ehu:Word:=0xc3c30000c3c30000
def ehv:Word:=0xc3c3c3c300000000
def ehw:Word:=0xc4c4c4c4c4c4c4c4
def ehx:Word:=0xcc00cc00cc00cc00
def ehy:Word:=0xcc00cc00ff00ff00
def ehz:Word:=0xcc88cc88cc880000
def ehA:Word:=0xcccc000000000000
def ehB:Word:=0xcccc00000000cccc
def ehC:Word:=0xcccc0000cccc0000
def ehD:Word:=0xcccccc00cccccc00
def ehE:Word:=0xcccccccc00000000
def ehF:Word:=0xcccccccccccccccc
def ehG:Word:=0xcf00cf00cf00cf00
def ehH:Word:=0xcfcf0000cfcf0000
def ehI:Word:=0xcfcf0f0fcccc0000
def ehJ:Word:=0xcfcfcfcf00000000
def ehK:Word:=0xd0d0d0d0d0d0d0d0
def ehL:Word:=0xdd00dd00dd00dd00
def ehM:Word:=0xddcc5500ddcc5500
def ehN:Word:=0xddccddcc55005500
def ehO:Word:=0xdddd0000dddd0000
def ehP:Word:=0xdddddddd00000000
def ehQ:Word:=0xe0e0e0e0e0e00000
def ehR:Word:=0xe0e0eeeee0e0eeee
def ehS:Word:=0xe0eee000e0eee000
def ehT:Word:=0xe0eee0e0e0eee0e0
def ehU:Word:=0xe0eee0ee0000e0ee
def ehV:Word:=0xe0eee0eee0ee0000
def ehW:Word:=0xe0eee0eee0eee0ee
def ehX:Word:=0xee00ee00ee000000
def ehY:Word:=0xee00ee00ee00ee00
def ehZ:Word:=0xee00eeeeee00eeee
def ei0:Word:=0xee00eeeeeeeeeeee
def ei1:Word:=0xee0eee00ee0eee00
def ei2:Word:=0xee0eee0eee0e0000
def ei3:Word:=0xee0eee0eee0eee0e
def ei4:Word:=0xeeccaa00eeccaa00
def ei5:Word:=0xeecceeccaa00aa00
def ei6:Word:=0xeee0ee00eee0ee00
def ei7:Word:=0xeee0eee0eee00000
def ei8:Word:=0xeee0eee0eee0eee0
def ei9:Word:=0xeeee0000eeee0000
def eia:Word:=0xeeee0000eeeeeeee
def eib:Word:=0xeeee0e0eeeee0e0e
def eic:Word:=0xeeeeccccaaaa0000
def eid:Word:=0xeeeee0e0eeeee0e0
def eie:Word:=0xeeeeee00eeeeee00
def eif:Word:=0xeeeeeeee0000eeee
def eig:Word:=0xeeeeeeeeeeee0000
def eih:Word:=0xeeeeeeeeeeeeeeee
def eii:Word:=0xeefeeefeeefe00f0
def eij:Word:=0xefeeefeeefee0f00
def eik:Word:=0xf00000000000f000
def eil:Word:=0xf000f000f000f000
def eim:Word:=0xf000f000fffff000
def ein:Word:=0xf000f0f0f000f0f0
def eio:Word:=0xf000ff00f000ff00
def eip:Word:=0xf00f0000f00f0000
def eiq:Word:=0xf00ff00f00000000
def eir:Word:=0xf0e0f0e0f0e0f000
def eis:Word:=0xf0f0000000000000
def eit:Word:=0xf0f000000000f0f0
def eiu:Word:=0xf0f00000f0f00000
def eiv:Word:=0xf0f0f000f0f0f000
def eiw:Word:=0xf0f0f0f000000000
def eix:Word:=0xf0f0f0f0f0f0f0f0
def eiy:Word:=0xf0f0ffff00000000
def eiz:Word:=0xf0ff0000f0ff0000
def eiA:Word:=0xf0fff000f0fff000
def eiB:Word:=0xf0fff0f0f0fff0f0
def eiC:Word:=0xf0fff0fff0ff0000
def eiD:Word:=0xf300f300f300f300
def eiE:Word:=0xf3f30000f3f30000
def eiF:Word:=0xf3f3f3f300000000
def eiG:Word:=0xf500f500f500f500
def eiH:Word:=0xf5f50000f5f50000
def eiI:Word:=0xf5f5f5f500000000
def eiJ:Word:=0xf7f07700f7f07700
def eiK:Word:=0xf7f0f7f0f7f0f7f0
def eiL:Word:=0xf888f888f888f888
def eiM:Word:=0xf888f8f8f888f8f8
def eiN:Word:=0xf8f88888f8f88888
def eiO:Word:=0xfcfcf0f0cccc0000
def eiP:Word:=0xfdfcf5f0ddcc5500
def eiQ:Word:=0xfe00fe00fe00f000
def eiR:Word:=0xfeeefeeefeeef000
def eiS:Word:=0xfef0ee00fef0ee00
def eiT:Word:=0xfef0fef0fef0f0f0
def eiU:Word:=0xfef0fef0fef0fef0
def eiV:Word:=0xfefcfaf0eeccaa00
def eiW:Word:=0xfefcfaf0fefcfaf0
def eiX:Word:=0xfefef0f0eeee0000
def eiY:Word:=0xfefefcfcfafaf0f0
def eiZ:Word:=0xfefefefefefef0f0
def ej0:Word:=0xff00000000000000
def ej1:Word:=0xff0000000000ff00
def ej2:Word:=0xff000000ff000000
def ej3:Word:=0xff000f00ff000f00
def ej4:Word:=0xff005500ff005500
def ej5:Word:=0xff00aa00ff00aa00
def ej6:Word:=0xff00f000ff00f000
def ej7:Word:=0xff00ff0000000000
def ej8:Word:=0xff00ff000000ff00
def ej9:Word:=0xff00ff00ff000000
def eja:Word:=0xff00ff00ff00ff00
def ejb:Word:=0xff00ff00ffffff00
def ejc:Word:=0xff00ffaaff00ffaa
def ejd:Word:=0xff00fff0ff00fff0
def eje:Word:=0xff00ffff00000000
def ejf:Word:=0xff00ffffff000000
def ejg:Word:=0xff0f0000ff0f0000
def ejh:Word:=0xff0fff000f0f0000
def eji:Word:=0xff0fff00ff0fff00
def ejj:Word:=0xff0fff0fff0f0000
def ejk:Word:=0xff550000ff550000
def ejl:Word:=0xff55cc44ff55cc44
def ejm:Word:=0xff55ff0055550000
def ejn:Word:=0xff55ff00ff55ff00
def ejo:Word:=0xff55ff55ff550000
def ejp:Word:=0xff888888ff888888
def ejq:Word:=0xff888f88ff888f88
def ejr:Word:=0xff88ff8888888888
def ejs:Word:=0xff88ff88ff888888
def ejt:Word:=0xff88ff88ff88ff88
def eju:Word:=0xffaa0000ffaa0000
def ejv:Word:=0xffaa3322ffaa3322
def ejw:Word:=0xffaacc88ffaacc88
def ejx:Word:=0xffaaff00aaaa0000
def ejy:Word:=0xffaaff00ffaaff00
def ejz:Word:=0xffaaffaaffaa0000
def ejA:Word:=0xffaaffaaffaaaaaa
def ejB:Word:=0xffaaffaaffaaffaa
def ejC:Word:=0xffccddccffccddcc
def ejD:Word:=0xffccffccffcccccc
def ejE:Word:=0xffccffccffccffcc
def ejF:Word:=0xffeeffeeffeecccc
def ejG:Word:=0xffeeffeeffeeff00
def ejH:Word:=0xfff00000fff00000
def ejI:Word:=0xfff0ff00f0f00000
def ejJ:Word:=0xfff0ff00fff0ff00
def ejK:Word:=0xfff0fff0fff00000
def ejL:Word:=0xfff0fff0fff0fff0
def ejM:Word:=0xffff000000000000
def ejN:Word:=0xffff0000ffff0000
def ejO:Word:=0xffffaaaaffffaaaa
def ejP:Word:=0xffffccccffffcccc
def ejQ:Word:=0xfffff0f0fffff0f0
def ejR:Word:=0xffffff0000000000
def ejS:Word:=0xffffff00ffffff00
def ejT:Word:=0xffffffff00000000
def ejU:Word:=0xffffffffff000000
def ejV:Word:=0xffffffffffff0000
def nx0:Array Node:=#[⟨0,2,[e60,e64],noHint⟩,⟨3,3,[e4U,e5k,e5E],noHint⟩,⟨51,3,[e2U,e85,e8I,e8O],noHint⟩,⟨127,4,[e11,e1y,e1L,e1O,e1Q],noHint⟩,⟨127,4,[e1y,e1L,e1N,e1O,e1Q],noHint⟩,⟨127,4,[e3,e1y,e1L,e1O,e1Q],noHint⟩,⟨127,4,[eR,e1y,e1L,e1O,e1Q],noHint⟩,⟨127,5,[e1y,e1L,e1O,e1Q],noHint⟩,⟨129,3,[e3a,e3A,e3S,e41],noHint⟩,⟨129,4,[e2O,e3a,e3A,e3S,e40],noHint⟩,⟨129,4,[e2N,e3a,e3A,e3S,e40],noHint⟩,⟨129,4,[e3a,e3A,e3S,e40,e42],noHint⟩,⟨129,3,[e3a,e3A,e3R,e40],noHint⟩,⟨129,4,[eb,e3a,e3A,e3S,e40],noHint⟩,⟨129,3,[e2Q,e2W,e3n,e40],noHint⟩,⟨129,4,[e2Q,e2W,e3A,e3S,e40],noHint⟩]
def nx1:Array Node:=#[⟨129,3,[ee,em,e2Q,e3S],noHint⟩,⟨129,4,[ee,e2Q,e3A,e3S,e40],noHint⟩,⟨129,5,[e2Q,e3a,e3A,e3S,e40],noHint⟩,⟨129,4,[e2L,e3a,e3A,e3S,e40],noHint⟩,⟨129,4,[e3a,e3A,e3S,e40,e43],noHint⟩,⟨129,3,[e3a,e3z,e3S,e40],noHint⟩,⟨129,4,[ed,e3a,e3A,e3S,e40],noHint⟩,⟨129,3,[ee,et,e2W,e3A],noHint⟩,⟨129,4,[ee,e2W,e3A,e3S,e40],noHint⟩,⟨129,4,[e2W,e3a,e3n,e3A,e40],noHint⟩,⟨129,4,[et,e2W,e3a,e3A,e40],noHint⟩,⟨129,5,[e2W,e3a,e3A,e3S,e40],noHint⟩,⟨129,4,[e3a,e3y,e3A,e3S,e40],noHint⟩,⟨129,4,[e3a,e3A,e3Q,e3S,e40],noHint⟩,⟨129,4,[ee,em,e3a,e3A,e3S],noHint⟩,⟨129,4,[ee,et,e3a,e3A,e3S],noHint⟩]
def nx2:Array Node:=#[⟨129,5,[ee,e3a,e3A,e3S,e40],noHint⟩,⟨129,4,[e39,e3a,e3A,e3S,e40],noHint⟩,⟨129,5,[et,e3a,e3A,e3S,e40],noHint⟩,⟨129,6,[e3a,e3A,e3S,e40],noHint⟩,⟨130,2,[e3p,e6s,e6C],noHint⟩,⟨130,3,[e6s,e6z,e6C,e6M],noHint⟩,⟨130,3,[eG,e6s,e6C,e6M],noHint⟩,⟨130,2,[e1V,e6s,e6M],noHint⟩,⟨130,3,[e6s,e6C,e6J,e6M],noHint⟩,⟨130,3,[eJ,e6s,e6C,e6M],noHint⟩,⟨130,4,[e6s,e6C,e6M,e6O],noHint⟩,⟨130,4,[e6u,e6x,e6C,e6M,e6O],noHint⟩,⟨130,3,[e3p,e6u,e6C,e6O],noHint⟩,⟨130,4,[e6u,e6z,e6C,e6M,e6O],noHint⟩,⟨130,4,[eG,e6u,e6C,e6M,e6O],noHint⟩,⟨130,3,[e1V,e6u,e6M,e6O],noHint⟩]
def nx3:Array Node:=#[⟨130,4,[e6u,e6C,e6J,e6M,e6O],noHint⟩,⟨130,4,[eJ,e6u,e6C,e6M,e6O],noHint⟩,⟨130,5,[e6u,e6C,e6M,e6O],noHint⟩,⟨132,3,[e7U,e9G,e9U,eae],noHint⟩,⟨132,4,[e7U,e8J,e9p,e9U,eae],noHint⟩,⟨132,4,[e8J,e9p,e9G,e9U,eae],noHint⟩,⟨132,3,[e8J,e9p,e9D,e9U],noHint⟩,⟨132,4,[e6o,e8J,e9p,e9U,eae],noHint⟩,⟨132,3,[e8J,e9E,e9U,eae],noHint⟩,⟨132,3,[e76,e8J,e9U,eae],noHint⟩,⟨132,3,[e7v,e8J,e9p,e9U],noHint⟩,⟨132,4,[e8p,e8J,e9p,e9U,eae],noHint⟩,⟨132,3,[e8J,e9h,e9U,eae],noHint⟩,⟨132,3,[e6E,e8J,e9U,eae],noHint⟩,⟨132,3,[e8J,e9p,e9U,ea8],noHint⟩,⟨132,4,[e8J,e9p,e9U,ea9,eae],noHint⟩]
def nx4:Array Node:=#[⟨132,4,[e2V,e8J,e9p,e9U,eae],noHint⟩,⟨132,4,[e7f,e8J,e9p,e9U,eae],noHint⟩,⟨132,5,[e8J,e9p,e9U,eae],noHint⟩,⟨222,4,[e2,el,es,ew,eB],noHint⟩,⟨222,3,[e9,el,ew,eB],noHint⟩,⟨222,4,[ei,el,es,ew,eB],noHint⟩,⟨222,5,[e4,el,es,ew,eB],noHint⟩,⟨223,6,[e7p,e9t,e9W,eaf,eah],noHint⟩,⟨227,6,[edA,efG,eg3,eg4,eg5],noHint⟩,⟨234,5,[e4y,e56,e5s,e5L,e5T,e5W],noHint⟩,⟨234,6,[e1O,e4x,e56,e5s,e5L,e5T,e5W],noHint⟩,⟨234,7,[e4x,e56,e5s,e5L,e5T,e5W],noHint⟩,⟨234,7,[e1y,e56,e5s,e5L,e5T,e5W],noHint⟩,⟨234,8,[e56,e5s,e5L,e5T,e5W],noHint⟩,⟨235,5,[e78,e8R,e9Z,eaf,eal],noHint⟩,⟨235,5,[e7w,e8R,e9w,e9Z,eaf,eal],noHint⟩]
def nx5:Array Node:=#[⟨235,5,[e8t,e8I,e9w,e9Z,eaf,eal],noHint⟩,⟨235,6,[e8t,e8R,e9w,e9Z,eaf,eal],noHint⟩,⟨235,5,[e2U,e8R,e9w,e9Z,eaf,eal],noHint⟩,⟨235,4,[e3j,e8R,e9w,e9Z,eaf],noHint⟩,⟨235,5,[e8R,e9w,e9Z,ea6,eaf,eal],noHint⟩,⟨235,6,[e32,e8R,e9w,e9Z,eaf,eal],noHint⟩,⟨235,5,[e8R,e9w,e9Z,eaa,eaf,eal],noHint⟩,⟨235,5,[e7m,e8R,e9w,e9Z,eaf,eal],noHint⟩,⟨235,5,[e8I,e8R,e9w,e9T,e9Z,eal],noHint⟩,⟨235,6,[e8I,e8R,e9w,e9Z,eaf,eal],noHint⟩,⟨235,5,[e3i,e8R,e9w,e9Z,eaf,eal],noHint⟩,⟨235,5,[e45,e8R,e9w,e9Z,eaf],noHint⟩,⟨235,6,[e8R,e9w,e9T,e9Z,eaf,eal],noHint⟩,⟨235,4,[e77,e8R,e9Z,eaf,eal],noHint⟩,⟨235,5,[e8x,e8R,e9w,e9Z,eaf,eal],noHint⟩,⟨235,6,[e3O,e8R,e9w,e9Z,eaf,eal],noHint⟩]
def nx6:Array Node:=#[⟨235,7,[e8R,e9w,e9Z,eaf,eal],noHint⟩,⟨236,6,[e7A,e8S,e9y,ea1,eag,eal],noHint⟩,⟨236,6,[e7B,e89,e8S,e9y,ea1,eag,eal],noHint⟩,⟨236,6,[e86,e8S,e9y,ea1,eag,eal],noHint⟩,⟨236,6,[e89,e8S,e9y,ea1,eag,eal,eam],noHint⟩,⟨236,5,[e7N,e8S,e9y,ea1,eag,eal],noHint⟩,⟨236,5,[e7C,e8u,e9y,ea1,eag,eal],noHint⟩,⟨236,5,[e7C,e8S,e9y,ea1,eae,eag],noHint⟩,⟨236,6,[e7C,e8S,e9y,ea1,eag,eal],noHint⟩,⟨236,5,[e7W,e89,e8S,e9y,ea1,eal],noHint⟩,⟨236,6,[e7C,e89,e8S,e9y,ea1,eag,eal],noHint⟩,⟨236,5,[e7x,e89,e9y,ea1,eag,eal],noHint⟩,⟨236,6,[e89,e8u,e9y,ea1,eag,eal],noHint⟩,⟨236,5,[e89,e8P,e9v,ea1,eag,eal],noHint⟩,⟨236,6,[e89,e8P,e9y,ea1,eag,eal],noHint⟩,⟨236,5,[e8S,e9y,ea1,ea7,eag,eal],noHint⟩]
def nx7:Array Node:=#[⟨236,6,[e89,e8S,e9y,e9Y,ea1,eag,eal],noHint⟩,⟨236,5,[e8b,e8S,e9y,ea1,eag,eal],noHint⟩,⟨236,6,[e1O,e89,e8S,e9y,ea1,eag,eal],noHint⟩,⟨236,6,[e89,e8S,e9y,ea1,eae,eag,eal],noHint⟩,⟨236,7,[e89,e8S,e9y,ea1,eag,eal],noHint⟩,⟨236,5,[e79,e8P,e9y,ea1,eag,eal],noHint⟩,⟨236,6,[e79,e8S,e9y,ea1,eag,eal],noHint⟩,⟨236,6,[e7x,e8S,e9y,ea1,eag,eal],noHint⟩,⟨236,6,[e8u,e8P,e9y,ea1,eag,eal],noHint⟩,⟨236,5,[e8S,e9y,e9F,ea1,eag,eal],noHint⟩,⟨236,6,[e8u,e8S,e9v,e9y,ea1,eag,eal],noHint⟩,⟨236,5,[e8w,e8S,e9y,ea1,eag,eal],noHint⟩,⟨236,6,[e1J,e8u,e8S,e9y,ea1,eag,eal],noHint⟩,⟨236,7,[e8u,e8S,e9y,ea1,eag,eal],noHint⟩,⟨236,5,[e8S,e92,e9y,ea1,eag,eal],noHint⟩,⟨236,6,[e71,e8S,e9y,ea1,eag,eal],noHint⟩]
def nx8:Array Node:=#[⟨236,6,[e7r,e8S,e9y,ea1,eag,eal],noHint⟩,⟨236,7,[e8J,e8S,e9y,ea1,eag,eal],noHint⟩,⟨236,6,[e70,e8S,e9y,ea1,eag,eal],noHint⟩,⟨236,6,[e70,e8P,e8S,e9y,ea1,eag,eal],noHint⟩,⟨236,6,[e7l,e8S,e9y,ea1,eag,eal],noHint⟩,⟨236,6,[e7q,e8P,e8S,e9y,ea1,eag,eal],noHint⟩,⟨236,6,[e8P,e8S,e9v,e9y,ea1,eag,eal],noHint⟩,⟨236,6,[e8P,e8S,e9y,e9Y,ea1,eag],noHint⟩,⟨236,6,[e8P,e8S,e9y,e9Y,ea1,eag,eal],noHint⟩,⟨236,6,[e1O,e8P,e8S,e9y,ea1,eag],noHint⟩,⟨236,7,[e8P,e8S,e9y,ea1,eag,eal],noHint⟩,⟨236,6,[e8S,e9x,e9y,ea1,eag,eal],noHint⟩,⟨236,6,[e8S,e9y,ea0,ea1,eag,eal],noHint⟩,⟨236,6,[e1s,e8S,e9y,e9Y,ea1,eag],noHint⟩,⟨236,7,[e1s,e8S,e9y,ea1,eag,eal],noHint⟩,⟨236,6,[e37,e8S,e9y,ea1,eag,eal],noHint⟩]
def nx9:Array Node:=#[⟨236,6,[e8S,e9y,e9Y,ea1,eak,eal],noHint⟩,⟨236,6,[e3V,e8S,e9y,e9Y,ea1,eal],noHint⟩,⟨236,7,[e8S,e9y,e9Y,ea1,eag,eal],noHint⟩,⟨236,6,[e8Q,e8S,e9y,ea1,eag,eal],noHint⟩,⟨236,7,[e1O,e8S,e9y,ea1,eag,eal],noHint⟩,⟨236,7,[e8S,e9y,ea1,eae,eag,eal],noHint⟩,⟨236,8,[e8S,e9y,ea1,eag,eal],noHint⟩,⟨237,6,[eaX,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,5,[e4I,ee1,eeO,ef6,efl,efr],noHint⟩,⟨237,5,[ee1,eeO,eeY,ef6,efe,efr],noHint⟩,⟨237,5,[ee1,eeO,ef6,efd,efl,efr],noHint⟩,⟨237,6,[ee1,eeO,ef6,efe,efl,efr],noHint⟩,⟨237,5,[ee1,eeO,ef6,efa,efe,efr],noHint⟩,⟨237,5,[edp,ee1,eeO,ef6,efe,efx],noHint⟩,⟨237,5,[e4L,edp,ee1,eeO,ef6,efe],noHint⟩,⟨237,6,[edp,ee1,eeO,eeU,ef6,efe,efr],noHint⟩]
def nxa:Array Node:=#[⟨237,5,[eaY,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,5,[edp,edV,eeO,ef6,efe,efr],noHint⟩,⟨237,5,[edp,ee1,eeO,ef6,efe,efp],noHint⟩,⟨237,5,[e1m,edp,ee1,eeO,ef6,efe],noHint⟩,⟨237,6,[edp,ee1,eeO,ef6,efe,efq,efr],noHint⟩,⟨237,6,[e2j,edp,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,5,[edr,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,6,[e4I,edp,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,5,[ee1,eeO,ef6,efe,efk,efr],noHint⟩,⟨237,4,[eaZ,ee1,eeO,ef6,efd],noHint⟩,⟨237,5,[edp,ee1,eeO,ef6,efd,efy],noHint⟩,⟨237,6,[edp,ee1,eeO,ef6,efd,efe,efr],noHint⟩,⟨237,5,[eaZ,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,5,[edp,edZ,eeO,ef6,efe,efr],noHint⟩,⟨237,6,[edp,ee1,eeO,ef6,efe,efr,efy],noHint⟩,⟨237,5,[edq,ee1,eeO,ef6,efe,efr],noHint⟩]
def nxb:Array Node:=#[⟨237,6,[e1j,edp,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,7,[edp,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,6,[ee1,eeb,eeO,ef6,efe,efr],noHint⟩,⟨237,5,[ee1,eeO,eeU,ef6,efh,efr],noHint⟩,⟨237,5,[ee1,eeO,eeW,ef6,efe,efr],noHint⟩,⟨237,6,[ee1,eeO,ef6,efe,efh,efr],noHint⟩,⟨237,5,[ee1,eeO,ef6,ef9,efe,efr],noHint⟩,⟨237,5,[ear,ee1,eeO,ef6,efe,efx],noHint⟩,⟨237,5,[e4L,ear,ee1,eeO,ef6,efe],noHint⟩,⟨237,6,[ear,ee1,eeO,eeU,ef6,efe,efr],noHint⟩,⟨237,5,[ee1,eed,eeO,ef6,efe,efr],noHint⟩,⟨237,5,[ear,edV,eeO,ef6,efe,efr],noHint⟩,⟨237,5,[ear,ee1,eeO,ef6,efe,efp],noHint⟩,⟨237,5,[e1m,ear,ee1,eeO,ef6,efe],noHint⟩,⟨237,6,[ear,ee1,eeO,ef6,efe,efq,efr],noHint⟩,⟨237,6,[e2j,ear,ee1,eeO,ef6,efe,efr],noHint⟩]
def nxc:Array Node:=#[⟨237,5,[eaD,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,6,[e4I,ear,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,5,[ee1,eeO,ef6,efe,efg,efr],noHint⟩,⟨237,5,[ear,ee1,eeO,ef6,efd,efy],noHint⟩,⟨237,6,[ear,ee1,eeO,ef6,efd,efe,efr],noHint⟩,⟨237,5,[ee1,eee,eeO,ef6,efe,efr],noHint⟩,⟨237,5,[ear,edZ,eeO,ef6,efe,efr],noHint⟩,⟨237,6,[ear,ee1,eeO,ef6,efe,efr,efy],noHint⟩,⟨237,5,[eav,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,6,[e1j,ear,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,7,[ear,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,6,[ee1,eeO,ef6,efe,efm,efr],noHint⟩,⟨237,6,[e2b,edJ,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,4,[eaW,ee1,eeB,efe,efr],noHint⟩,⟨237,4,[edJ,edZ,eeB,efe,efr],noHint⟩,⟨237,5,[edJ,ee1,eeB,efe,efr,efy],noHint⟩]
def nxd:Array Node:=#[⟨237,6,[edJ,ee1,eeB,efe,efr],noHint⟩,⟨237,6,[edJ,ee1,eeB,ef6,efe,efr],noHint⟩,⟨237,6,[e8k,edJ,ee1,ef6,efe,efr],noHint⟩,⟨237,5,[eaW,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,5,[edJ,edZ,eeO,ef6,efe,efr],noHint⟩,⟨237,5,[edJ,ee1,eeO,ef5,efe,efr],noHint⟩,⟨237,6,[edJ,ee1,eeO,ef6,efe,efr,efy],noHint⟩,⟨237,7,[edJ,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,6,[ee1,eeG,ef6,efe,efr],noHint⟩,⟨237,6,[ee1,eeO,ef6,efb,efr],noHint⟩,⟨237,6,[e2k,ee1,eeO,ef6,efr],noHint⟩,⟨237,7,[ee1,eeO,ef6,efc,efe,efr],noHint⟩,⟨237,6,[ee1,eeF,ef6,efe,efr],noHint⟩,⟨237,6,[e4w,ee1,eeB,efe,efr],noHint⟩,⟨237,7,[e4w,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,6,[ee1,eeO,ef6,efe,efi,efr],noHint⟩]
def nxe:Array Node:=#[⟨237,6,[e8k,eaG,ee1,ef6,efe,efr],noHint⟩,⟨237,5,[ee1,ee5,eeO,ef6,efe,efr],noHint⟩,⟨237,5,[eaG,edZ,eeO,ef6,efe,efr],noHint⟩,⟨237,6,[eaG,ee1,eeO,ef6,efe,efr,efy],noHint⟩,⟨237,7,[eaG,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,6,[e2b,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,6,[eay,ee1,ef6,efe,efr],noHint⟩,⟨237,5,[edW,ee1,eeO,ef6,efe,efv],noHint⟩,⟨237,5,[edZ,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,6,[ee1,eeO,ef6,efe,efr,efv],noHint⟩,⟨237,5,[edT,edW,ee1,eeO,ef6,efy],noHint⟩,⟨237,6,[edT,edW,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,5,[edT,ee1,eeO,ef6,eff,efr],noHint⟩,⟨237,5,[e15,edT,ee1,eeO,ef6,efy],noHint⟩,⟨237,6,[e15,edT,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,5,[eaP,ee1,eeO,ef6,efr,efy],noHint⟩]
def nxf:Array Node:=#[⟨237,6,[edT,ee1,eeO,ef6,efr,efy],noHint⟩,⟨237,7,[edT,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,5,[e1k,e8k,ee1,ef6,efe,efr],noHint⟩,⟨237,6,[e8k,ee1,ef6,efe,efn,efr],noHint⟩,⟨237,5,[ee1,eeO,eeZ,ef1,efe,efr],noHint⟩,⟨237,6,[ee1,eeO,eeZ,ef6,efe,efr],noHint⟩,⟨237,5,[e4J,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,5,[e1k,ee1,eeO,ef1,ef6,efe],noHint⟩,⟨237,6,[ee1,eeO,ef1,ef6,efe,efn,efr],noHint⟩,⟨237,6,[e1f,ee1,eeO,ef6,efe,efn,efr],noHint⟩,⟨237,5,[ee1,eeO,ef2,ef6,efe,efr],noHint⟩,⟨237,6,[e1k,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,7,[ee1,eeO,ef6,efe,efn,efr],noHint⟩,⟨237,6,[ee1,eeO,eeX,ef6,efe,efr],noHint⟩,⟨237,6,[e2b,ee1,eeO,eeX,ef6,efe,efr],noHint⟩,⟨237,5,[ee1,eeB,ef6,efe,efr,efs],noHint⟩]
def nxg:Array Node:=#[⟨237,5,[e8k,ee1,ef6,efe,efr,efs],noHint⟩,⟨237,5,[ee1,eeO,ef1,ef6,efe,efs],noHint⟩,⟨237,5,[ee1,eeO,ef3,ef6,efe,efr],noHint⟩,⟨237,6,[ee1,eeO,ef6,efe,efr,efs],noHint⟩,⟨237,6,[e2b,ee1,eeO,ef6,efe,efr,efs],noHint⟩,⟨237,5,[e0,ee1,eeB,ef6,efe,efr],noHint⟩,⟨237,6,[e0,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,6,[e2b,ee1,eeO,ef6,efe,efj,efr],noHint⟩,⟨237,5,[e15,e2b,ee1,eeO,ef6,efy],noHint⟩,⟨237,6,[e15,e2b,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,4,[e2b,ee1,eeB,ef5,efr],noHint⟩,⟨237,5,[e2b,ee1,eeB,ef6,efr,efy],noHint⟩,⟨237,6,[e2b,ee1,eeB,ef6,efe,efr],noHint⟩,⟨237,5,[e2b,e8k,ee1,ef6,efr,efy],noHint⟩,⟨237,6,[e2b,e8k,ee1,ef6,efe,efr],noHint⟩,⟨237,5,[e2b,ee1,eeO,ef0,ef6,efr],noHint⟩]
def nxh:Array Node:=#[⟨237,4,[e2b,edY,eeO,ef6,efx],noHint⟩,⟨237,4,[e2b,eaN,eeO,ef6,efx],noHint⟩,⟨237,5,[e2b,ee1,eeO,ef6,efx],noHint⟩,⟨237,5,[e2b,ee1,eeO,ef6,efr,efx],noHint⟩,⟨237,6,[e2b,ee1,eeO,eeU,ef6,efr],noHint⟩,⟨237,6,[e2b,e2j,ee1,eeO,ef6,efr],noHint⟩,⟨237,5,[ee1,eeO,ef6,ef7,efe,efr],noHint⟩,⟨237,6,[e2b,ee1,eeO,ef1,ef6,efe,efr],noHint⟩,⟨237,6,[e1f,e2b,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,5,[e2b,ee1,eeO,ef5,ef6,efr],noHint⟩,⟨237,6,[e2b,ee1,eeO,ef6,efr,efy],noHint⟩,⟨237,5,[e2b,e2d,ee1,eeO,ef6,efr],noHint⟩,⟨237,6,[e1j,e2b,ee1,eeO,ef6,efr],noHint⟩,⟨237,7,[e2b,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,6,[ee1,eeO,ef6,efe,efu],noHint⟩,⟨237,6,[ee1,eeO,ef6,efe,efr,efu],noHint⟩]
def nxi:Array Node:=#[⟨237,6,[ee1,ee3,eeO,ef6,efe],noHint⟩,⟨237,7,[eaL,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,4,[ee1,eeB,ef5,efo,efr],noHint⟩,⟨237,5,[ee1,eeB,ef6,efo,efr,efy],noHint⟩,⟨237,4,[ee0,eeB,ef6,efe,efr],noHint⟩,⟨237,5,[ee1,eeB,ef6,efe,efr,efz],noHint⟩,⟨237,5,[e1l,ee1,eeB,ef6,efe,efr],noHint⟩,⟨237,6,[ee1,eeB,ef6,efe,efo,efr],noHint⟩,⟨237,4,[ee1,eeQ,ef6,efe,efr],noHint⟩,⟨237,5,[edZ,ee1,eeB,ef6,efe,efr],noHint⟩,⟨237,5,[e8n,ee1,eeB,ef6,efe,efr],noHint⟩,⟨237,5,[ee1,eeB,ef5,efe,efr],noHint⟩,⟨237,5,[ee1,eeB,ef5,efe,efr,efy],noHint⟩,⟨237,6,[ee1,eeB,ef6,efe,efr,efy],noHint⟩,⟨237,7,[ee1,eeB,ef6,efe,efr],noHint⟩,⟨237,6,[ee1,eeO,ef6,efe,efo,efr],noHint⟩]
def nxj:Array Node:=#[⟨237,5,[e8n,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,5,[ee1,eeB,eeO,ef5,efe,efr],noHint⟩,⟨237,6,[ee1,eeB,eeO,ef6,efe,efr,efy],noHint⟩,⟨237,7,[ee1,eeB,eeO,ef6,efe,efr],noHint⟩,⟨237,6,[ee1,eeB,ef6,efe,efr],noHint⟩,⟨237,7,[e4G,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,4,[ee1,eec,ef6,efe,efr],noHint⟩,⟨237,5,[e8k,edZ,ee1,ef6,efe,efr],noHint⟩,⟨237,6,[e8k,ee1,ef6,efe,efr,efy],noHint⟩,⟨237,7,[e8k,ee1,ef6,efe,efr],noHint⟩,⟨237,6,[ee1,eeO,ef6,efe,efr,efw],noHint⟩,⟨237,7,[ee1,eeJ,eeO,ef6,efe,efr],noHint⟩,⟨237,6,[ee1,eeO,eeV,ef6,efe,efr],noHint⟩,⟨237,5,[ee1,eeO,ef1,ef6,efe,eft],noHint⟩,⟨237,5,[ee1,eeO,ef4,ef6,efe,efr],noHint⟩,⟨237,6,[ee1,eeO,ef6,efe,efr,eft],noHint⟩]
def nxk:Array Node:=#[⟨237,5,[ee1,eeO,ef6,ef8,efe,efr],noHint⟩,⟨237,6,[e2h,ee1,eeO,ef1,ef6,efe,efr],noHint⟩,⟨237,7,[e2h,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,6,[e4A,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,4,[eau,ee1,ef6,efe,efx],noHint⟩,⟨237,5,[edY,ee1,eeO,ef6,efe,efx],noHint⟩,⟨237,5,[eaN,ee1,eeO,ef6,efe,efx],noHint⟩,⟨237,5,[ee1,eeM,eeO,ef6,efe,efx],noHint⟩,⟨237,6,[ee1,eeO,ef6,efe,efx],noHint⟩,⟨237,5,[edY,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,6,[ee1,eeO,ef6,efe,efr,efx],noHint⟩,⟨237,6,[e4L,ee1,eeO,ef6,efe],noHint⟩,⟨237,7,[ee1,eeO,eeU,ef6,efe,efr],noHint⟩,⟨237,5,[edm,edV,eeO,ef6,efe,efr],noHint⟩,⟨237,5,[eaw,edV,eeO,ef6,efe,efr],noHint⟩,⟨237,6,[edV,eeO,ef6,efe,efr],noHint⟩]
def nxl:Array Node:=#[⟨237,6,[edV,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,6,[eaM,eeO,ef6,efe,efr],noHint⟩,⟨237,6,[ee1,eeK,ef6,efe,efr],noHint⟩,⟨237,6,[ee1,eeO,ef6,efe,efp],noHint⟩,⟨237,6,[e1m,ee1,eeO,ef6,efe],noHint⟩,⟨237,7,[ee1,eeO,ef6,efe,efq,efr],noHint⟩,⟨237,6,[e1,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,7,[e2j,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,6,[edK,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,6,[ee1,eeC,ef6,efe,efr],noHint⟩,⟨237,7,[e4I,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,4,[e2c,edZ,eeO,ef6,efy],noHint⟩,⟨237,4,[e2c,eaO,eeO,ef6,efy],noHint⟩,⟨237,5,[e2c,ee1,eeO,ef6,efy],noHint⟩,⟨237,6,[e2c,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,4,[eas,ee1,ef6,efd,efy],noHint⟩]
def nxm:Array Node:=#[⟨237,5,[edZ,ee1,eeO,ef6,efd,efy],noHint⟩,⟨237,5,[eaO,ee1,eeO,ef6,efd,efy],noHint⟩,⟨237,5,[ee1,eeN,eeO,ef6,efd,efy],noHint⟩,⟨237,6,[ee1,eeO,ef6,efd,efy],noHint⟩,⟨237,7,[ee1,eeO,ef6,efd,efe,efr],noHint⟩,⟨237,4,[edZ,ee1,eeP,efe,efr],noHint⟩,⟨237,5,[edZ,ee1,eeR,ef6,efe,efr],noHint⟩,⟨237,5,[eas,edZ,ee1,ef6,efe,efr],noHint⟩,⟨237,6,[edZ,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,5,[eas,ee1,ef6,efe,efr,efy],noHint⟩,⟨237,6,[edZ,ee1,eeO,ef6,efe,efr,efy],noHint⟩,⟨237,6,[eaO,ee1,eeO,ef6,efe,efr,efy],noHint⟩,⟨237,6,[ee1,eeN,eeO,ef6,efe,efr,efy],noHint⟩,⟨237,6,[ee1,eeO,ef5,ef6,efe,efr],noHint⟩,⟨237,6,[ee1,eeO,ef5,ef6,efe,efr,efy],noHint⟩,⟨237,7,[ee1,eeO,ef6,efe,efr,efy],noHint⟩]
def nxn:Array Node:=#[⟨237,6,[edX,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,6,[ee1,eeO,ef6,efe,efr,efy],noHint⟩,⟨237,7,[e1j,ee1,eeO,ef6,efe,efr],noHint⟩,⟨237,8,[ee1,eeO,ef6,efe,efr],noHint⟩,⟨238,5,[ee1,efX,ega,egp,egv,egw],noHint⟩,⟨238,5,[e3,ee1,efX,ega,egp,egv],noHint⟩,⟨238,5,[e2x,ee1,efX,ega,egn,egv],noHint⟩,⟨238,6,[e2x,ee1,efX,ega,egp,egv],noHint⟩,⟨238,5,[e4U,ee1,efX,ega,egp,egv],noHint⟩,⟨238,5,[ee1,efX,ega,egc,egp,egv],noHint⟩,⟨238,5,[e4X,ee1,efX,ega,egv,egB],noHint⟩,⟨238,6,[e4X,ee1,efX,ega,egp,egv],noHint⟩,⟨238,5,[ee1,efX,ega,egp,egt,egv],noHint⟩,⟨238,6,[ee1,efX,ega,egn,egp,egv],noHint⟩,⟨238,5,[ee1,efX,eg9,ega,egp,egv],noHint⟩,⟨238,6,[ee1,efX,ega,egp,egv,egB],noHint⟩]
def nxo:Array Node:=#[⟨238,7,[ee1,efX,ega,egp,egv],noHint⟩,⟨258,5,[e1C,e4E,e4R,e55,e5f,e5g],noHint⟩,⟨258,6,[e16,e1C,e4E,e4R,e57,e5f,e5g],noHint⟩,⟨258,5,[e1B,e1C,e4E,e4R,e4Z,e5g],noHint⟩,⟨258,6,[e1B,e1C,e4E,e4R,e57,e5f,e5g],noHint⟩,⟨258,5,[e1C,e4D,e4E,e4R,e4Z,e5g],noHint⟩,⟨258,6,[e1C,e4D,e4E,e4R,e57,e5f,e5g],noHint⟩,⟨258,5,[e1C,e4E,e4R,e54,e5f,e5g],noHint⟩,⟨258,6,[e17,e1C,e4E,e4R,e57,e5f,e5g],noHint⟩,⟨258,5,[e1C,e4E,e4R,e4U,e4Z,e5f],noHint⟩,⟨258,5,[e1z,e1C,e4E,e4R,e4Z,e5f],noHint⟩,⟨258,5,[e1C,e1D,e4E,e4R,e4Z],noHint⟩,⟨258,5,[e1C,e1D,e4E,e4R,e4Z,e5g],noHint⟩,⟨258,6,[e1C,e4E,e4R,e4Z,e5f,e5g],noHint⟩,⟨258,6,[e1C,e4E,e4R,e57,e5d,e5f],noHint⟩,⟨258,6,[e1C,e1D,e4E,e4R,e57,e5f],noHint⟩]
def nxp:Array Node:=#[⟨258,6,[e1C,e1D,e4E,e4R,e57,e5f,e5g],noHint⟩,⟨258,7,[e1C,e4E,e4R,e57,e5f,e5g],noHint⟩,⟨259,6,[e8a,e8V,e8Z,e90,e91,e93],noHint⟩,⟨259,4,[e1F,e8a,e8v,e91,e94],noHint⟩,⟨259,5,[e1F,e8a,e8v,e8Y,e91,e93],noHint⟩,⟨259,6,[e1F,e8a,e8v,e90,e91,e93],noHint⟩,⟨259,4,[e1F,e8a,e8T,e90,e91],noHint⟩,⟨259,5,[e1F,e8a,e8V,e90,e91,e94],noHint⟩,⟨259,6,[e1F,e8a,e8V,e8Y,e90,e91,e93],noHint⟩,⟨259,6,[e1F,e1Z,e8a,e8V,e90,e91,e93],noHint⟩,⟨259,5,[e1F,e8a,e8U,e90,e91,e93],noHint⟩,⟨259,6,[e1F,e8a,e8V,e90,e91,e93,e95],noHint⟩,⟨259,6,[e1F,e1H,e8a,e8V,e90,e91,e93],noHint⟩,⟨259,7,[e1F,e8a,e8V,e90,e91,e93],noHint⟩,⟨260,5,[eeh,efG,ega,egY,egZ,eh0],noHint⟩,⟨260,6,[eeh,efG,ega,egY,egZ],noHint⟩]
def nxq:Array Node:=#[⟨260,6,[eeh,efG,ega,egV,egY,egZ],noHint⟩,⟨260,5,[eeh,efG,egi,egV,egY,egZ],noHint⟩,⟨260,5,[eeh,efG,egj,egU,egY,egZ],noHint⟩,⟨260,6,[eeh,efG,egj,egV,egY,egZ,eh0],noHint⟩,⟨260,7,[eeh,efG,egj,egV,egY,egZ],noHint⟩,⟨261,6,[e9Z,ebJ,egm,egV,eh1,eh3],noHint⟩,⟨261,6,[ebJ,egm,egV,eh1,eh2,eh3],noHint⟩,⟨261,7,[ebJ,efK,egm,egV,eh1,eh3],noHint⟩,⟨262,4,[ebE,een,efO,egM,eh5],noHint⟩,⟨262,5,[ebE,een,efO,egN,eh5,eh9],noHint⟩,⟨262,5,[eeg,een,efO,egq,egM,eh5],noHint⟩,⟨262,6,[eeg,een,efO,egq,egN,eh5,eh9],noHint⟩,⟨262,5,[een,efZ,egq,egN,eh5,eh9],noHint⟩,⟨262,6,[ebI,een,efO,egq,egN,eh5,eh9],noHint⟩,⟨262,6,[e5d,een,efO,egq,egN,eh9],noHint⟩,⟨262,6,[een,efO,egq,egM,egN,eh5],noHint⟩]
def nxr:Array Node:=#[⟨262,7,[een,efO,egq,egN,eh5,eh9],noHint⟩,⟨263,6,[egr,egJ,egO,eh9,eha],noHint⟩,⟨263,7,[eem,efP,egr,egO,eh9,eha],noHint⟩,⟨265,7,[e5e,eeo,efR,egu,eh9,ehc],noHint⟩,⟨273,6,[e2A,ebH,ees,efX,egV,eh9,ehd],noHint⟩,⟨273,6,[e5e,ebH,ees,efX,egV,eh9,ehd],noHint⟩,⟨273,6,[ebH,ees,efX,egV,eh5,eh9,ehd],noHint⟩,⟨273,5,[ebG,ees,efX,egV,eh9,ehd],noHint⟩,⟨273,5,[ebH,ees,efX,egU,eh9,ehd],noHint⟩,⟨273,6,[ebH,ees,efX,egV,eh9,ehd,ehe],noHint⟩,⟨273,7,[ebH,ees,efX,egV,eh9,ehd],noHint⟩,⟨273,7,[ebM,eeh,efX,egC,egV,eh9,ehd],noHint⟩,⟨273,7,[e2A,eeh,ees,efX,egC,egV,eh9,ehd],noHint⟩,⟨273,7,[e5e,eeh,ees,efX,egC,egV,eh9,ehd],noHint⟩,⟨273,7,[eeh,ees,efX,egC,egV,eh5,eh9,ehd],noHint⟩,⟨273,6,[ebQ,ees,efX,egC,egV,eh9,ehd],noHint⟩]
def nxs:Array Node:=#[⟨273,5,[ees,efX,egK,egV,eh9,ehd],noHint⟩,⟨273,6,[eeh,ees,efX,egB,egV,eh9,ehd],noHint⟩,⟨273,6,[eeh,ees,efX,egC,egU,eh9,ehd],noHint⟩,⟨273,7,[eeh,ees,efX,egC,egV,eh9,ehd,ehe],noHint⟩,⟨273,8,[eeh,ees,efX,egC,egV,eh9,ehd],noHint⟩,⟨273,6,[e2A,ees,eg0,egC,egV,eh9,ehd],noHint⟩,⟨273,6,[e5e,ees,eg0,egC,egV,eh9,ehd],noHint⟩,⟨273,6,[ees,eg0,egC,egV,eh5,eh9,ehd],noHint⟩,⟨273,6,[ees,eg0,egC,egV,eh9,ehd,ehe],noHint⟩,⟨273,7,[ees,eg0,egC,egV,eh9,ehd],noHint⟩,⟨273,7,[e2A,ebJ,ees,efX,egC,egV,eh9,ehd],noHint⟩,⟨273,7,[e5e,ebJ,ees,efX,egC,egV,eh9,ehd],noHint⟩,⟨273,7,[ebJ,ees,efX,egC,egV,eh5,eh9,ehd],noHint⟩,⟨273,6,[ees,eev,efX,egC,egV,eh9,ehd],noHint⟩,⟨273,7,[ebJ,ees,efX,egC,egV,eh9,ehd,ehe],noHint⟩,⟨273,8,[ebJ,ees,efX,egC,egV,eh9,ehd],noHint⟩]
def nxt:Array Node:=#[⟨273,7,[ees,eet,efX,egC,egV,eh9,ehd],noHint⟩,⟨273,8,[ebM,ees,efX,egC,egV,eh9,ehd],noHint⟩,⟨273,8,[e2A,ees,efX,egC,egV,eh9,ehd],noHint⟩,⟨273,6,[e5e,e9C,ees,egC,egV,eh9,ehd],noHint⟩,⟨273,7,[e5e,ees,eeu,efX,egC,egV,eh9,ehd],noHint⟩,⟨273,6,[e5e,ebF,ees,efX,egV,eh9,ehd],noHint⟩,⟨273,7,[e5e,eei,ees,efX,egC,egV,eh9,ehd],noHint⟩,⟨273,7,[e5d,ees,efX,egC,egV,eh9,ehd],noHint⟩,⟨273,7,[ees,efX,egC,egV,egW,eh9,ehd],noHint⟩,⟨273,7,[e5e,ees,efX,egC,egV,ehd,ehe],noHint⟩,⟨273,8,[e5e,ees,efX,egC,egV,eh9,ehd],noHint⟩,⟨273,8,[ees,efX,egC,egV,eh5,eh9,ehd],noHint⟩,⟨273,6,[edZ,ees,efX,egB,egV,eh9,ehd],noHint⟩,⟨273,6,[e6Z,ees,efX,egB,egV,eh9,ehd],noHint⟩,⟨273,5,[e7d,efX,egB,egV,eh9,ehd],noHint⟩,⟨273,6,[ees,efX,eg9,egB,egV,eh9,ehd],noHint⟩]
def nxu:Array Node:=#[⟨273,6,[e51,ees,efX,egB,egV,eh9,ehd],noHint⟩,⟨273,6,[e7j,ees,efX,egB,egV,eh9,ehd],noHint⟩,⟨273,7,[ees,efX,egB,egV,eh9,ehd],noHint⟩,⟨273,6,[ees,egC,egU,egV,eh4,eh9,ehd],noHint⟩,⟨273,7,[ees,efX,egC,egU,egV,eh9,ehd],noHint⟩,⟨273,8,[ees,efX,egC,egV,eh9,ehd,ehe],noHint⟩,⟨273,9,[ees,efX,egC,egV,eh9,ehd],noHint⟩,⟨279,9,[egC,ehF,eix,eja,ejt,ejN,ejT],noHint⟩,⟨279,8,[ed1,egC,ehF,eix,eiK,eja,ejN,ejT],noHint⟩,⟨279,8,[ed1,edt,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[ed1,egC,ehF,eix,eja,ejL,ejN,ejT],noHint⟩,⟨279,8,[e5K,ed1,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[egC,ehF,eix,eiJ,eja,ejN,ejT],noHint⟩,⟨279,8,[ed1,egC,ehF,eiu,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[eaf,ed1,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[ed1,egC,ehF,eix,eja,ejM,ejN,ejT],noHint⟩]
def nxv:Array Node:=#[⟨279,9,[ed1,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[ed4,egC,ehF,eiw,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[eal,ed4,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[ed4,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,6,[egC,ehF,eix,eiL,eja,ejN,ejU],noHint⟩,⟨279,6,[e5Z,egC,ehF,eix,eiL,eja,ejN],noHint⟩,⟨279,7,[egC,ehF,eix,eiL,ej2,eja,ejN,ejT],noHint⟩,⟨279,6,[egC,ehF,eix,eiL,eja,ejN,ejR],noHint⟩,⟨279,6,[e1T,egC,ehF,eix,eiL,eja,ejN],noHint⟩,⟨279,7,[egC,ehF,eix,eiL,eja,ejN,ejS,ejT],noHint⟩,⟨279,7,[e2G,egC,ehF,eix,eiL,eja,ejN,ejT],noHint⟩,⟨279,7,[e5S,egC,ehF,eix,eiL,eja,ejN,ejT],noHint⟩,⟨279,6,[egC,ehF,eix,eiL,eja,ejM,ejV],noHint⟩,⟨279,7,[egC,ehF,eix,eiL,eja,ejM,ejN,ejT],noHint⟩,⟨279,7,[egC,ehF,eix,eiL,eja,ejN,ejT,ejV],noHint⟩,⟨279,7,[e1S,egC,ehF,eix,eiL,eja,ejN,ejT],noHint⟩]
def nxw:Array Node:=#[⟨279,8,[egC,ehF,eix,eiL,eja,ejN,ejT],noHint⟩,⟨279,8,[eap,ee1,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[eaf,ee1,egC,ehF,eil,eja,ejN,ejT],noHint⟩,⟨279,7,[egC,ehF,eil,eix,eja,ejp,ejN,ejT],noHint⟩,⟨279,7,[ee1,egC,ehF,eil,eix,eja,ejN,ejU],noHint⟩,⟨279,7,[e5Z,ee1,egC,ehF,eil,eix,eja,ejN],noHint⟩,⟨279,8,[ee1,egC,ehF,eil,eix,ej2,eja,ejN,ejT],noHint⟩,⟨279,7,[ed7,egC,ehF,eil,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[ee1,egC,ehF,eil,eix,eja,ejN,ejR],noHint⟩,⟨279,7,[e1T,ee1,egC,ehF,eil,eix,eja,ejN],noHint⟩,⟨279,8,[ee1,egC,ehF,eil,eix,eja,ejN,ejS,ejT],noHint⟩,⟨279,8,[e2G,ee1,egC,ehF,eil,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[ee1,egC,ehF,eix,eiA,eja,ejN,ejT],noHint⟩,⟨279,8,[e5S,ee1,egC,ehF,eil,eix,eja,ejN,ejT],noHint⟩,⟨279,6,[ee1,egC,ehF,eil,eix,ej9,ejM],noHint⟩,⟨279,7,[ee1,egC,ehF,eil,eix,eja,ejM,ejV],noHint⟩]
def nxx:Array Node:=#[⟨279,8,[ee1,egC,ehF,eil,eix,eja,ejM,ejN,ejT],noHint⟩,⟨279,7,[ed8,egC,ehF,eil,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[eaq,ee1,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[ee1,egC,ehF,eil,eix,ej9,ejN,ejT],noHint⟩,⟨279,7,[e5X,ee1,egC,ehF,eil,eix,ejN,ejT],noHint⟩,⟨279,8,[ee1,egC,ehF,eil,eix,eja,ejN,ejT,ejV],noHint⟩,⟨279,7,[ee2,egC,ehF,eil,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[ee1,egC,ehF,eim,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[e1S,ee1,egC,ehF,eil,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[ee1,egC,ehF,eil,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[ed3,egC,ehF,eix,eja,ejN,ejT,ejV],noHint⟩,⟨279,8,[ed3,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[ee1,egC,ehF,eix,eja,ejH,ejN,ejT],noHint⟩,⟨279,7,[ed8,egC,ehF,eix,eja,ejL,ejN,ejT],noHint⟩,⟨279,7,[ee1,egC,ehF,eix,eja,ejK,ejN,ejT],noHint⟩,⟨279,8,[ee1,egC,ehF,eix,eja,ejL,ejN,ejT,ejV],noHint⟩]
def nxy:Array Node:=#[⟨279,9,[ee1,egC,ehF,eix,eja,ejL,ejN,ejT],noHint⟩,⟨279,6,[ee8,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[ee9,egC,ehF,eix,eja,ejN,ejT,ejV],noHint⟩,⟨279,8,[ee9,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[ee1,egC,ehF,eix,eja,ejg,ejN,ejT],noHint⟩,⟨279,7,[ee1,egC,ehF,eix,eja,ejj,ejN,ejT],noHint⟩,⟨279,7,[e5K,ed8,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[e5K,ee1,egC,ehF,eix,ej9,ejN,ejT],noHint⟩,⟨279,8,[e5K,ee1,egC,ehF,eix,eja,ejN,ejT,ejV],noHint⟩,⟨279,9,[e5K,ee1,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,6,[eew,egC,ehF,eix,eja,ejN,ejU],noHint⟩,⟨279,6,[e5Z,eew,egC,ehF,eix,eja,ejN],noHint⟩,⟨279,7,[eew,egC,ehF,eix,ej2,eja,ejN,ejT],noHint⟩,⟨279,6,[eew,egC,ehF,eix,eja,ejN,ejR],noHint⟩,⟨279,6,[e1T,eew,egC,ehF,eix,eja,ejN],noHint⟩,⟨279,7,[eew,egC,ehF,eix,eja,ejN,ejS,ejT],noHint⟩]
def nxz:Array Node:=#[⟨279,7,[e2G,eew,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[e5S,eew,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,6,[eew,egC,ehF,eix,eja,ejM,ejV],noHint⟩,⟨279,7,[eew,egC,ehF,eix,eja,ejM,ejN,ejT],noHint⟩,⟨279,7,[eew,egC,ehF,eix,eja,ejN,ejT,ejV],noHint⟩,⟨279,7,[e1S,eew,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[eew,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[ee1,egC,ehF,eix,eiz,eja,ejN,ejT],noHint⟩,⟨279,7,[e9Z,egC,ehF,eiN,eja,ejN,ejT],noHint⟩,⟨279,8,[e9Z,ee1,egC,ehF,eiu,eja,ejN,ejT],noHint⟩,⟨279,7,[e9Z,egC,ehF,eix,eja,ejp,ejN,ejT],noHint⟩,⟨279,7,[e9Z,ee1,egC,ehF,eix,eja,ejN,ejU],noHint⟩,⟨279,7,[e5Z,e9Z,ee1,egC,ehF,eix,eja,ejN],noHint⟩,⟨279,8,[e9Z,ee1,egC,ehF,eix,ej2,eja,ejN,ejT],noHint⟩,⟨279,7,[e9Z,ed7,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[e9Z,ee1,egC,ehF,eix,eja,ejN,ejR],noHint⟩]
def nxA:Array Node:=#[⟨279,7,[e1T,e9Z,ee1,egC,ehF,eix,eja,ejN],noHint⟩,⟨279,8,[e9Z,ee1,egC,ehF,eix,eja,ejN,ejS,ejT],noHint⟩,⟨279,8,[e2G,e9Z,ee1,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[e5S,e9Z,ee1,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[e9Z,ee1,egC,ehF,eix,eja,ejM,ejV],noHint⟩,⟨279,8,[e9Z,ee1,egC,ehF,eix,eja,ejM,ejN,ejT],noHint⟩,⟨279,7,[ee1,egC,ehF,eix,eiC,eja,ejN,ejT],noHint⟩,⟨279,7,[e9Z,ed8,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[e9Z,ee1,egC,ehF,eix,eja,ejN,ejT,ejV],noHint⟩,⟨279,7,[ea2,ee1,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[e9Z,ee2,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[e1S,e9Z,ee1,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[e9Z,ee1,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,6,[e5P,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[egC,ehF,eix,eiN,ej7,eja,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,eix,eiN,eja,ejN,ejT],noHint⟩]
def nxB:Array Node:=#[⟨279,8,[ee1,egC,ehF,eix,eja,ejJ,ejN,ejT],noHint⟩,⟨279,8,[ea5,ee1,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[eao,ee1,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[egC,ehF,eiu,eix,eja,ejr,ejN,ejT],noHint⟩,⟨279,7,[ee1,egC,ehF,eix,eja,ejI,ejN,ejT],noHint⟩,⟨279,8,[ee1,egC,ehF,eiu,eix,ej7,eja,ejN,ejT],noHint⟩,⟨279,9,[ee1,egC,ehF,eiu,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[ed6,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[ee1,egC,ehF,eix,ej6,eja,ejN,ejT],noHint⟩,⟨279,8,[e5V,ee1,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[ee1,egC,ehF,eix,eja,ejN,ejQ,ejT],noHint⟩,⟨279,8,[ee4,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[ee1,egC,ehF,eix,eja,ejd,ejN,ejT],noHint⟩,⟨279,7,[egC,ehF,eix,ej3,eja,ejq,ejN,ejT],noHint⟩,⟨279,8,[ee1,egC,ehF,eix,ej3,eja,ejN,ejT],noHint⟩,⟨279,9,[e2E,ee1,egC,ehF,eix,eja,ejN,ejT],noHint⟩]
def nxC:Array Node:=#[⟨279,7,[eex,egC,ehF,eix,ej7,eja,ejN,ejT],noHint⟩,⟨279,8,[eex,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[ee1,egC,ehF,eix,eja,eji,ejN,ejT],noHint⟩,⟨279,8,[ee1,egC,ehF,eio,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[ee1,egC,ehF,eix,eiy,eja,ejN,ejT],noHint⟩,⟨279,7,[ee1,egC,ehF,eix,eja,ejh,ejN,ejT],noHint⟩,⟨279,7,[eaf,egC,ehF,eix,eja,ejr,ejN,ejT],noHint⟩,⟨279,8,[eaf,ee1,egC,ehF,eix,ej7,eja,ejN,ejT],noHint⟩,⟨279,9,[eaf,ee1,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[egC,ehF,eix,ej7,eja,ejp,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,eix,eja,ejp,ejN,ejT],noHint⟩,⟨279,8,[ee1,egC,ehF,eix,eja,ejN,ejU],noHint⟩,⟨279,8,[e5Z,ee1,egC,ehF,eix,eja,ejN],noHint⟩,⟨279,8,[e5Z,ee1,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[ee1,egC,ehF,eix,ej2,ej7,eja,ejN,ejT],noHint⟩,⟨279,8,[ee1,egC,ehF,eix,ej2,eja,ejM,ejT],noHint⟩]
def nxD:Array Node:=#[⟨279,7,[ee1,egC,ehF,eix,eja,ejf,ejT],noHint⟩,⟨279,8,[e2H,ee1,egC,ehF,eix,ej2,eja,ejT],noHint⟩,⟨279,9,[ee1,egC,ehF,eix,ej2,eja,ejN,ejT],noHint⟩,⟨279,8,[ed7,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[ee1,egC,ehF,eiv,eja,ejN,ejT],noHint⟩,⟨279,8,[eaj,ee1,egC,ehF,eja,ejN,ejT],noHint⟩,⟨279,8,[ee1,egC,ehF,eix,eja,ejN,ejR],noHint⟩,⟨279,8,[e1T,ee1,egC,ehF,eix,eja,ejN],noHint⟩,⟨279,9,[ee1,egC,ehF,eix,eja,ejN,ejS,ejT],noHint⟩,⟨279,8,[e2G,e5S,ee1,egC,ehF,eix,eja,ejT],noHint⟩,⟨279,9,[e2G,ee1,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[eea,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[e5S,ed0,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[e5S,ee1,egC,ehF,eix,eiB,eja,ejN,ejT],noHint⟩,⟨279,7,[e5S,egC,ehF,eix,eiM,eja,ejN,ejT],noHint⟩,⟨279,8,[e5S,ee1,egC,ehF,ein,eix,eja,ejN,ejT],noHint⟩]
def nxE:Array Node:=#[⟨279,7,[e5R,ee1,egC,ehF,eix,eja,ejV],noHint⟩,⟨279,8,[e5R,ee1,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[ee1,egC,ehF,eix,eja,eje,ejN,ejT],noHint⟩,⟨279,8,[e5S,ee1,egC,ehF,eix,eja,ejT,ejV],noHint⟩,⟨279,8,[e1S,e5S,ee1,egC,ehF,eix,eja,ejT],noHint⟩,⟨279,9,[e5S,ee1,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[ee1,egC,ehF,eix,ej9,eja,ejM],noHint⟩,⟨279,8,[ee1,egC,ehF,eix,eja,ejM,ejV],noHint⟩,⟨279,9,[ee1,egC,ehF,eix,eja,ejM,ejN,ejT],noHint⟩,⟨279,8,[ed8,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[egC,ehF,eix,ej9,eja,ejs,ejN,ejT],noHint⟩,⟨279,8,[ee1,egC,ehF,eix,ej9,eja,ejN,ejT],noHint⟩,⟨279,8,[e5X,ee1,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[ee1,egC,ehF,eix,eja,ejN,ejT,ejV],noHint⟩,⟨279,8,[ee2,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[ee1,egC,ehF,eix,eja,ejb,ejN,ejT],noHint⟩]
def nxF:Array Node:=#[⟨279,8,[ee1,egC,ehF,eix,ej8,eja,ejN,ejT],noHint⟩,⟨279,9,[e1S,ee1,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,10,[ee1,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,ehY,eix,eiU,eja,ejN,ejT],noHint⟩,⟨279,8,[eaE,egC,ehF,ehY,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,ehY,eil,eix,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,ehY,eix,eja,ejL,ejN,ejT],noHint⟩,⟨279,8,[e5K,egC,ehF,ehY,eix,ejN,ejT],noHint⟩,⟨279,8,[e5K,egC,ehF,ehY,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[egC,ehF,eix,eiS,eja,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,ehY,eiu,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[egC,ehF,ehY,eix,eji,ejN,ejT],noHint⟩,⟨279,8,[eaf,egC,ehF,ehY,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,ehY,eix,eja,ejM,ejN,ejT],noHint⟩,⟨279,9,[egC,ehF,ehY,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[e5z,egC,ehF,eil,eix,ejN,ejT],noHint⟩]
def nxG:Array Node:=#[⟨279,9,[e5z,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[e2E,egC,ehF,ei9,eix,eja,ejT],noHint⟩,⟨279,7,[egC,ehF,eix,eiX,eja,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,ei9,eiw,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[eal,egC,ehF,ei9,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,ei9,eix,eja,ejT,ejV],noHint⟩,⟨279,9,[egC,ehF,ei9,eix,eja,ejN,ejT],noHint⟩,⟨279,6,[e9N,egC,ehF,eix,eja,ejN,ejU],noHint⟩,⟨279,6,[e5Z,e9N,egC,ehF,eix,eja,ejN],noHint⟩,⟨279,7,[e9N,egC,ehF,eix,ej2,eja,ejN,ejT],noHint⟩,⟨279,6,[e9N,egC,ehF,eix,eja,ejN,ejR],noHint⟩,⟨279,6,[e1T,e9N,egC,ehF,eix,eja,ejN],noHint⟩,⟨279,7,[e9N,egC,ehF,eix,eja,ejN,ejS,ejT],noHint⟩,⟨279,7,[e2G,e9N,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[e5S,e9N,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,5,[e9N,egC,ehF,eix,ej9,ejM],noHint⟩]
def nxH:Array Node:=#[⟨279,6,[e9N,egC,ehF,eix,eja,ejM,ejV],noHint⟩,⟨279,7,[e9N,egC,ehF,eix,eja,ejM,ejN,ejT],noHint⟩,⟨279,6,[e9M,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,6,[e9N,egC,ehF,eix,ej9,ejN,ejT],noHint⟩,⟨279,6,[e5X,e9N,egC,ehF,eix,ejN,ejT],noHint⟩,⟨279,7,[e9N,egC,ehF,eix,eja,ejN,ejT,ejV],noHint⟩,⟨279,6,[e9L,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[e1S,e9N,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[e9N,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[eap,egC,ehF,eih,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[egC,ehF,ei8,eil,eja,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,eih,eil,eja,ejL,ejN,ejT],noHint⟩,⟨279,8,[eaf,egC,ehF,eih,eil,eja,ejN,ejT],noHint⟩,⟨279,7,[e5D,egC,ehF,eil,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[egC,ehF,eih,eil,eix,eja,ejN,ejU],noHint⟩,⟨279,7,[e5Z,egC,ehF,eih,eil,eix,eja,ejN],noHint⟩]
def nxI:Array Node:=#[⟨279,8,[egC,ehF,eih,eil,eix,ej2,eja,ejN,ejT],noHint⟩,⟨279,7,[egC,ehF,eie,eil,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[egC,ehF,eih,eil,eix,eja,ejN,ejR],noHint⟩,⟨279,7,[e1T,egC,ehF,eih,eil,eix,eja,ejN],noHint⟩,⟨279,8,[egC,ehF,eih,eil,eix,eja,ejN,ejS,ejT],noHint⟩,⟨279,8,[e2G,egC,ehF,eih,eil,eix,eja,ejN,ejT],noHint⟩,⟨279,6,[egC,ehF,ehS,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[egC,ehF,eih,eix,eiA,eja,ejN,ejT],noHint⟩,⟨279,8,[e5S,egC,ehF,eih,eil,eix,eja,ejN,ejT],noHint⟩,⟨279,6,[egC,ehF,eih,eil,eix,ej9,ejM],noHint⟩,⟨279,7,[egC,ehF,eih,eil,eix,eja,ejM,ejV],noHint⟩,⟨279,8,[egC,ehF,eih,eil,eix,eja,ejM,ejN,ejT],noHint⟩,⟨279,6,[egC,ehF,eix,eiR,eja,ejN,ejT],noHint⟩,⟨279,7,[egC,ehF,eig,eil,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[eaq,egC,ehF,eih,eix,eja,ejN,ejT],noHint⟩,⟨279,6,[e5A,egC,ehF,eil,eix,ejN,ejT],noHint⟩]
def nxJ:Array Node:=#[⟨279,7,[egC,ehF,eih,eil,eix,ej9,ejN,ejT],noHint⟩,⟨279,7,[e5X,egC,ehF,eih,eil,eix,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,eih,eil,eix,eja,ejN,ejT,ejV],noHint⟩,⟨279,7,[egC,ehF,eif,eil,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[egC,ehF,eih,eim,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[e1S,egC,ehF,eih,eil,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[egC,ehF,eih,eil,eix,eja,ejN,ejT],noHint⟩,⟨279,6,[egC,ehF,ei7,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[egC,ehF,ei8,eix,eja,ejN,ejT,ejV],noHint⟩,⟨279,8,[egC,ehF,ei8,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[e3K,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,eih,eix,eja,ejH,ejN,ejT],noHint⟩,⟨279,6,[eaK,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[egC,ehF,eig,eix,eja,ejL,ejN,ejT],noHint⟩,⟨279,6,[e3I,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[egC,ehF,eih,eix,eja,ejK,ejN,ejT],noHint⟩]
def nxK:Array Node:=#[⟨279,8,[egC,ehF,eih,eix,eja,ejL,ejN,ejT,ejV],noHint⟩,⟨279,9,[egC,ehF,eih,eix,eja,ejL,ejN,ejT],noHint⟩,⟨279,6,[egC,ehF,ei2,eix,eja,ejN,ejT],noHint⟩,⟨279,6,[egC,ehF,ei3,eix,ej9,ejN,ejT],noHint⟩,⟨279,7,[egC,ehF,ei3,eix,eja,ejN,ejT,ejV],noHint⟩,⟨279,8,[egC,ehF,ei3,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,eih,eix,eja,ejg,ejN,ejT],noHint⟩,⟨279,7,[egC,ehF,eih,eix,eja,ejj,ejN,ejT],noHint⟩,⟨279,6,[egC,ehF,eii,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[e5K,egC,ehF,eig,eix,eja,ejN,ejT],noHint⟩,⟨279,6,[e5A,e5K,egC,ehF,eix,ejN,ejT],noHint⟩,⟨279,7,[e5K,egC,ehF,eih,eix,ej9,ejN,ejT],noHint⟩,⟨279,8,[e5K,egC,ehF,eih,eix,eja,ejN,ejT,ejV],noHint⟩,⟨279,9,[e5K,egC,ehF,eih,eix,eja,ejN,ejT],noHint⟩,⟨279,6,[egC,ehF,ehW,eix,eja,ejN,ejU],noHint⟩,⟨279,6,[e5Z,egC,ehF,ehW,eix,eja,ejN],noHint⟩]
def nxL:Array Node:=#[⟨279,7,[egC,ehF,ehW,eix,ej2,eja,ejN,ejT],noHint⟩,⟨279,6,[egC,ehF,ehW,eix,eja,ejN,ejR],noHint⟩,⟨279,6,[e1T,egC,ehF,ehW,eix,eja,ejN],noHint⟩,⟨279,7,[egC,ehF,ehW,eix,eja,ejN,ejS,ejT],noHint⟩,⟨279,7,[e2G,egC,ehF,ehW,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[e5S,egC,ehF,ehW,eix,eja,ejN,ejT],noHint⟩,⟨279,6,[egC,ehF,ehW,eix,eja,ejM,ejV],noHint⟩,⟨279,7,[egC,ehF,ehW,eix,eja,ejM,ejN,ejT],noHint⟩,⟨279,6,[egC,ehF,ehV,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[egC,ehF,ehW,eix,eja,ejN,ejT,ejV],noHint⟩,⟨279,6,[egC,ehF,ehU,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[e1S,egC,ehF,ehW,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,ehW,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,eih,eix,eiz,eja,ejN,ejT],noHint⟩,⟨279,7,[e9J,e9Z,egC,ehF,eja,ejN,ejT],noHint⟩,⟨279,8,[e9Z,egC,ehF,eih,eiu,eja,ejN,ejT],noHint⟩]
def nxM:Array Node:=#[⟨279,7,[e5D,e9Z,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[e9Z,egC,ehF,eih,eix,eja,ejN,ejU],noHint⟩,⟨279,7,[e5Z,e9Z,egC,ehF,eih,eix,eja,ejN],noHint⟩,⟨279,8,[e9Z,egC,ehF,eih,eix,ej2,eja,ejN,ejT],noHint⟩,⟨279,7,[e9Z,egC,ehF,eie,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[e9Z,egC,ehF,eih,eix,eja,ejN,ejR],noHint⟩,⟨279,7,[e1T,e9Z,egC,ehF,eih,eix,eja,ejN],noHint⟩,⟨279,8,[e9Z,egC,ehF,eih,eix,eja,ejN,ejS,ejT],noHint⟩,⟨279,8,[e2G,e9Z,egC,ehF,eih,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[e5S,e9Z,egC,ehF,eih,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[e9Z,egC,ehF,eih,eix,eja,ejM,ejV],noHint⟩,⟨279,8,[e9Z,egC,ehF,eih,eix,eja,ejM,ejN,ejT],noHint⟩,⟨279,7,[egC,ehF,eih,eix,eiC,eja,ejN,ejT],noHint⟩,⟨279,6,[egC,ehF,eij,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[e9Z,egC,ehF,eig,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[e9Z,egC,ehF,eih,eix,eja,ejN,ejT,ejV],noHint⟩]
def nxN:Array Node:=#[⟨279,7,[ea2,egC,ehF,eih,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[e9Z,egC,ehF,eif,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[e1S,e9Z,egC,ehF,eih,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[e9Z,egC,ehF,eih,eix,eja,ejN,ejT],noHint⟩,⟨279,6,[e3J,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[e9J,egC,ehF,eix,ej7,eja,ejN,ejT],noHint⟩,⟨279,8,[e9J,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[egC,ehF,ei6,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,eih,eix,eja,ejJ,ejN,ejT],noHint⟩,⟨279,8,[ea5,egC,ehF,eih,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[eao,egC,ehF,eih,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[e5B,egC,ehF,eiu,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[egC,ehF,eih,eix,eja,ejI,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,eih,eiu,eix,ej7,eja,ejN,ejT],noHint⟩,⟨279,9,[egC,ehF,eih,eiu,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,eid,eix,eja,ejN,ejT],noHint⟩]
def nxO:Array Node:=#[⟨279,8,[egC,ehF,eih,eix,ej6,eja,ejN,ejT],noHint⟩,⟨279,8,[e5V,egC,ehF,eih,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[egC,ehF,eih,eix,eja,ejN,ejQ,ejT],noHint⟩,⟨279,8,[egC,ehF,eib,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,eih,eix,eja,ejd,ejN,ejT],noHint⟩,⟨279,6,[e58,e5u,eih,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[e58,ehF,eih,eix,ej3,eja,ejN,ejT],noHint⟩,⟨279,7,[e5C,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[e5C,egC,ehF,eix,ej3,eja,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,eih,eix,ej3,eja,ejN,ejT],noHint⟩,⟨279,9,[e2E,egC,ehF,eih,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[egC,ehF,ehR,eix,ej7,eja,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,ehR,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[egC,ehF,ei1,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,eih,eix,eja,eji,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,eih,eio,eix,eja,ejN,ejT],noHint⟩]
def nxP:Array Node:=#[⟨279,7,[e9H,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,eih,eix,eiy,eja,ejN,ejT],noHint⟩,⟨279,7,[egC,ehF,eih,eix,eja,ejh,ejN,ejT],noHint⟩,⟨279,7,[e5B,eaf,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[eaf,egC,ehF,eih,eix,ej7,eja,ejN,ejT],noHint⟩,⟨279,9,[eaf,egC,ehF,eih,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[e5D,egC,ehF,eix,ej7,eja,ejN,ejT],noHint⟩,⟨279,8,[e5D,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,eih,eix,eja,ejN,ejU],noHint⟩,⟨279,8,[e5Z,egC,ehF,eih,eix,eja,ejN],noHint⟩,⟨279,8,[e5Z,egC,ehF,eih,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,eih,eix,ej2,ej7,eja,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,eih,eix,ej2,eja,ejM,ejT],noHint⟩,⟨279,7,[egC,ehF,eia,eix,ej2,eja,ejT],noHint⟩,⟨279,7,[egC,ehF,eih,eix,eja,ejf,ejT],noHint⟩,⟨279,8,[e2H,egC,ehF,eih,eix,ej2,eja,ejT],noHint⟩]
def nxQ:Array Node:=#[⟨279,9,[egC,ehF,eih,eix,ej2,eja,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,eie,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,eih,eiv,eja,ejN,ejT],noHint⟩,⟨279,8,[eaj,egC,ehF,eih,eja,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,eih,eix,eja,ejN,ejR],noHint⟩,⟨279,8,[e1T,egC,ehF,eih,eix,eja,ejN],noHint⟩,⟨279,9,[egC,ehF,eih,eix,eja,ejN,ejS,ejT],noHint⟩,⟨279,8,[e2G,e5S,egC,ehF,eih,eix,eja,ejT],noHint⟩,⟨279,9,[e2G,egC,ehF,eih,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[e1S,egC,ehF,ehZ,eix,eja,ejT],noHint⟩,⟨279,8,[egC,ehF,ehZ,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[e5S,egC,ehF,ehT,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[e5S,egC,ehF,eih,eix,eiB,eja,ejN,ejT],noHint⟩,⟨279,7,[e5S,e9K,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[e5S,egC,ehF,eih,ein,eix,eja,ejN,ejT],noHint⟩,⟨279,6,[egC,ehF,ei0,eix,eja,ejV],noHint⟩]
def nxR:Array Node:=#[⟨279,7,[egC,ehF,ei0,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[e5R,egC,ehF,eih,eix,eja,ejV],noHint⟩,⟨279,8,[e5R,egC,ehF,eih,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[e5x,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,eih,eix,eja,eje,ejN,ejT],noHint⟩,⟨279,8,[e5S,egC,ehF,eih,eix,eja,ejT,ejV],noHint⟩,⟨279,8,[e1S,e5S,egC,ehF,eih,eix,eja,ejT],noHint⟩,⟨279,9,[e5S,egC,ehF,eih,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[egC,ehF,eih,eix,ej9,eja,ejM],noHint⟩,⟨279,8,[egC,ehF,eih,eix,eja,ejM,ejV],noHint⟩,⟨279,9,[egC,ehF,eih,eix,eja,ejM,ejN,ejT],noHint⟩,⟨279,7,[egC,ehF,ehQ,eig,eix,eja,ejN,ejT],noHint⟩,⟨279,6,[egC,ehF,eig,eix,eiQ,ejN,ejT],noHint⟩,⟨279,6,[e5Q,egC,ehF,eig,eix,ejN,ejT],noHint⟩,⟨279,7,[egC,ehF,eig,eix,eiZ,eja,ejN,ejT],noHint⟩,⟨279,6,[e9I,eat,egC,ehF,eja,ejN,ejT],noHint⟩]
def nxS:Array Node:=#[⟨279,7,[e9I,egC,ehF,eig,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[eat,egC,ehF,eig,eix,eja,ejN,ejT],noHint⟩,⟨279,6,[egC,ehF,eig,eiT,eja,ejN,ejT],noHint⟩,⟨279,6,[eaF,egC,ehF,eig,eja,ejN,ejT],noHint⟩,⟨279,7,[egC,ehF,ehX,eig,eix,eja,ejN,ejT],noHint⟩,⟨279,6,[egC,ehF,eig,eir,eja,ejN,ejT],noHint⟩,⟨279,6,[ead,egC,ehF,eig,eja,ejN,ejT],noHint⟩,⟨279,7,[egC,ehF,eig,eix,eja,ejG,ejN,ejT],noHint⟩,⟨279,6,[e5y,eaH,egC,ehF,eix,ejN,ejT],noHint⟩,⟨279,7,[e5y,egC,ehF,eig,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[eaH,egC,ehF,eig,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,eig,eix,eja,ejN,ejT],noHint⟩,⟨279,6,[e53,e5r,eih,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[e53,ehF,eih,eix,ej9,eja,ejN,ejT],noHint⟩,⟨279,7,[e5A,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[e5A,egC,ehF,eix,ej9,eja,ejN,ejT],noHint⟩]
def nxT:Array Node:=#[⟨279,8,[egC,ehF,eih,eix,ej9,eja,ejN,ejT],noHint⟩,⟨279,8,[e5X,egC,ehF,eih,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[egC,ehF,eih,eix,eja,ejN,ejT,ejV],noHint⟩,⟨279,8,[egC,ehF,eif,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,eih,eix,eja,ejb,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,eih,eix,ej8,eja,ejN,ejT],noHint⟩,⟨279,9,[e1S,egC,ehF,eih,eix,eja,ejN,ejT],noHint⟩,⟨279,10,[egC,ehF,eih,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[ecW,egC,ehE,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[ecf,ecW,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[ecW,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[ecU,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[ega,ehF,eix,eja,ejB,ejN,ejT],noHint⟩,⟨279,7,[ecO,ehF,ei5,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[ecO,ega,ehE,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[ecf,ecO,ega,ehF,eix,eja,ejN,ejT],noHint⟩]
def nxU:Array Node:=#[⟨279,9,[ecO,ega,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[e5K,ega,egC,ehx,ehF,eix,ejN,ejT],noHint⟩,⟨279,9,[ega,egC,ehx,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[ecV,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[ega,egC,ehF,eix,eja,ejE,ejN,ejT],noHint⟩,⟨279,9,[e5q,ega,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[ec6,ega,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[egC,ehF,ei4,eix,eiW,eja,ejN,ejT],noHint⟩,⟨279,7,[eaB,egC,ehF,ei4,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[eaT,egC,ehF,ei4,eix,eja,ejN,ejT],noHint⟩,⟨279,6,[egC,ehF,eix,eiV,eja,ejN,ejT],noHint⟩,⟨279,7,[egC,ehF,ei4,eiw,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[eal,egC,ehF,ei4,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,ei4,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[ega,egC,ehF,eix,eiO,eja,ejN,ejT],noHint⟩,⟨279,8,[ega,egC,ehC,ehF,eiw,eix,eja,ejN,ejT],noHint⟩]
def nxV:Array Node:=#[⟨279,7,[egC,egX,ehC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[ega,egC,ehF,ehI,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[eal,ega,egC,ehC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[ega,egC,ehC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[ecX,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[ega,egC,ehF,eix,eja,ejN,ejP,ejT],noHint⟩,⟨279,8,[ege,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[e2C,ega,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[eal,egC,ehh,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[egC,ehh,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[ech,ega,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[eal,ecc,ega,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[ecc,ega,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[ega,egC,ehF,eix,eja,ejN,ejU],noHint⟩,⟨279,8,[e5Z,ega,egC,ehF,eix,eja,ejN],noHint⟩,⟨279,9,[ega,egC,ehF,eix,ej2,eja,ejN,ejT],noHint⟩]
def nxW:Array Node:=#[⟨279,8,[ega,egC,ehD,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[ece,ega,egC,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[ega,egC,ehF,eix,eja,ejN,ejR],noHint⟩,⟨279,8,[e1T,ega,egC,ehF,eix,eja,ejN],noHint⟩,⟨279,9,[ega,egC,ehF,eix,eja,ejN,ejS,ejT],noHint⟩,⟨279,9,[e2G,ega,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[egC,egG,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[e5S,ega,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[ega,egC,ehF,eix,ej9,ejM],noHint⟩,⟨279,8,[ega,egC,ehF,eix,eja,ejM,ejV],noHint⟩,⟨279,9,[ega,egC,ehF,eix,eja,ejM,ejN,ejT],noHint⟩,⟨279,8,[ecY,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[ega,egC,ehF,eix,ej9,ejN,ejT],noHint⟩,⟨279,8,[e5X,ega,egC,ehF,eix,ejN,ejT],noHint⟩,⟨279,9,[ega,egC,ehF,eix,eja,ejN,ejT,ejV],noHint⟩,⟨279,8,[egb,egC,ehF,eix,eja,ejN,ejT],noHint⟩]
def nxX:Array Node:=#[⟨279,9,[e1S,ega,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,10,[ega,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[ec6,egC,ehF,eix,eja,ejB,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,eix,eja,ejw,ejN,ejT],noHint⟩,⟨279,9,[egC,ehF,eix,eja,ejB,ejN,ejP,ejT],noHint⟩,⟨279,8,[egC,ehF,eix,eja,ejv,ejN,ejT],noHint⟩,⟨279,8,[e2C,egC,ehF,eix,eja,eju,ejT],noHint⟩,⟨279,9,[e2C,egC,ehF,eix,eja,ejB,ejN,ejT],noHint⟩,⟨279,9,[egC,ehF,eix,eja,eju,ejN,ejT],noHint⟩,⟨279,6,[ec2,egC,ehF,eja,ejz,ejN,ejT],noHint⟩,⟨279,7,[egC,ehz,ehF,eix,eja,ejz,ejN,ejT],noHint⟩,⟨279,6,[eac,egC,ehF,eja,ejz,ejN,ejT],noHint⟩,⟨279,7,[egC,ehF,eix,eja,ejz,ejF,ejN,ejT],noHint⟩,⟨279,6,[e4l,eca,egC,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[e4l,egC,ehF,eix,eja,ejz,ejN,ejT],noHint⟩,⟨279,7,[eca,egC,ehF,eix,eja,ejz,ejN,ejT],noHint⟩]
def nxY:Array Node:=#[⟨279,8,[egC,ehF,eix,eja,ejz,ejN,ejT],noHint⟩,⟨279,9,[egC,ehF,eix,eja,ejB,ejN,ejT,ejV],noHint⟩,⟨279,10,[egC,ehF,eix,eja,ejB,ejN,ejT],noHint⟩,⟨279,9,[egC,ehF,eix,eja,ejk,ejN,ejT],noHint⟩,⟨279,9,[e52,ecG,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[e52,ec6,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,eix,eja,ejl,ejN,ejT],noHint⟩,⟨279,9,[e52,egC,ehF,eix,eja,ejN,ejP,ejT],noHint⟩,⟨279,8,[e5c,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[e2C,e52,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,eix,eja,ejo,ejN,ejT],noHint⟩,⟨279,7,[e52,egC,ehF,eix,ej9,ejD,ejN,ejT],noHint⟩,⟨279,7,[e52,e5r,egC,ehF,eix,ej9,ejN,ejT],noHint⟩,⟨279,8,[e52,egC,ehF,eix,ej9,ejN,ejT],noHint⟩,⟨279,9,[e52,egC,ehF,eix,eja,ejN,ejT,ejV],noHint⟩,⟨279,10,[e52,egC,ehF,eix,eja,ejN,ejT],noHint⟩]
def nxZ:Array Node:=#[⟨279,8,[egC,egE,ehE,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[ecf,egC,egE,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[egC,egE,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[egp,ehF,ehN,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[ecG,egp,ehE,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[ecf,ecG,egp,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[ecG,egp,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[ec6,ecG,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,6,[egC,ehF,eix,eiP,eja,ejN,ejT],noHint⟩,⟨279,7,[egC,ehF,ehM,eiw,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[eal,egC,ehF,ehM,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,ehM,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[ecG,egC,ehF,eix,eiO,eja,ejN,ejT],noHint⟩,⟨279,8,[ecG,egC,ehC,ehF,eiw,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[ecZ,egC,ehC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[ecG,egC,ehF,ehI,eix,eja,ejN,ejT],noHint⟩]
def nx10:Array Node:=#[⟨279,8,[eal,ecG,egC,ehC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[ecG,egC,ehC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[egC,egF,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[ecG,egC,ehF,eix,eja,ejN,ejP,ejT],noHint⟩,⟨279,8,[ecL,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[e2C,ecG,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[eal,ed2,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[ed2,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[ech,ecG,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[eal,ecc,ecG,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[ecc,ecG,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[ecG,egC,ehF,eix,eja,ejN,ejU],noHint⟩,⟨279,8,[e5Z,ecG,egC,ehF,eix,eja,ejN],noHint⟩,⟨279,9,[ecG,egC,ehF,eix,ej2,eja,ejN,ejT],noHint⟩,⟨279,8,[ecG,egC,ehD,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[ece,ecG,egC,eix,eja,ejN,ejT],noHint⟩]
def nx11:Array Node:=#[⟨279,8,[ecG,egC,ehF,eix,eja,ejN,ejR],noHint⟩,⟨279,8,[e1T,ecG,egC,ehF,eix,eja,ejN],noHint⟩,⟨279,9,[ecG,egC,ehF,eix,eja,ejN,ejS,ejT],noHint⟩,⟨279,9,[e2G,ecG,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[e5S,ecG,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[ecG,egC,ehF,eix,eja,ejM,ejV],noHint⟩,⟨279,9,[ecG,egC,ehF,eix,eja,ejM,ejN,ejT],noHint⟩,⟨279,8,[egC,egI,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[ecG,egC,ehF,eix,eja,ejN,ejT,ejV],noHint⟩,⟨279,8,[ecI,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[e1S,ecG,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,10,[ecG,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[egC,ehF,eix,eja,ejy,ejN,ejT],noHint⟩,⟨279,8,[ecM,egC,ehE,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[ecf,ecM,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[ecM,egC,ehF,eix,eja,ejN,ejT],noHint⟩]
def nx12:Array Node:=#[⟨279,9,[ecT,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[egC,ehF,eic,eix,eiY,eja,ejN,ejT],noHint⟩,⟨279,7,[eax,egC,ehF,eic,eix,eja,ejN,ejT],noHint⟩,⟨279,7,[eaI,egC,ehF,eic,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,eic,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[egp,egC,ehE,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[egC,ehj,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[egp,egC,ehy,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[ecf,egp,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,eix,eja,ejx,ejN,ejT],noHint⟩,⟨279,9,[egp,egC,ehF,eix,ej7,eja,ejN,ejT],noHint⟩,⟨279,10,[egp,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[egC,ehF,eix,ej5,eja,ejN,ejT],noHint⟩,⟨279,9,[e5U,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,10,[egC,ehF,eix,eja,ejN,ejO,ejT],noHint⟩,⟨279,9,[egC,ehF,eix,eja,ejc,ejN,ejT],noHint⟩]
def nx13:Array Node:=#[⟨279,8,[egC,ehF,eix,ej4,eja,ejC,ejN,ejT],noHint⟩,⟨279,7,[e5t,e5M,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[e5t,egC,ehF,eix,ej4,eja,ejN,ejT],noHint⟩,⟨279,9,[egC,ehF,eix,ej4,eja,ejN,ejT],noHint⟩,⟨279,10,[e2y,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[egC,ehF,eix,eja,ejn,ejN,ejT],noHint⟩,⟨279,8,[ecf,egf,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[egf,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[egC,egD,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[ed5,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[ecf,ecO,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,eix,eja,ejm,ejN,ejT],noHint⟩,⟨279,9,[ecO,egC,ehF,eix,ej7,eja,ejN,ejT],noHint⟩,⟨279,10,[ecO,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[e5S,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[egC,ehF,eix,eja,ejN,ejU],noHint⟩]
def nx14:Array Node:=#[⟨279,9,[e5Z,egC,ehF,eix,eja,ejN],noHint⟩,⟨279,9,[e5Z,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[egC,ehF,eix,ej2,ej7,eja,ejN,ejT],noHint⟩,⟨279,9,[egC,ehF,eix,ej2,eja,ejM,ejT],noHint⟩,⟨279,8,[egC,ehF,eix,eja,ejf,ejT],noHint⟩,⟨279,9,[e2H,egC,ehF,eix,ej2,eja,ejT],noHint⟩,⟨279,10,[egC,ehF,eix,ej2,eja,ejN,ejT],noHint⟩,⟨279,9,[egu,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[ecQ,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[egC,ehF,eix,eja,ejN,ejR],noHint⟩,⟨279,9,[e1T,egC,ehF,eix,eja,ejN],noHint⟩,⟨279,10,[egC,ehF,eix,eja,ejN,ejS,ejT],noHint⟩,⟨279,9,[e2G,e5S,egC,ehF,eix,eja,ejT],noHint⟩,⟨279,10,[e2G,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[e5S,egC,egH,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[e5S,egd,egC,ehF,eix,eja,ejN,ejT],noHint⟩]
def nx15:Array Node:=#[⟨279,8,[e5R,egC,ehF,eix,eja,ejV],noHint⟩,⟨279,9,[e5R,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,9,[egC,ehF,eix,eja,eje,ejN,ejT],noHint⟩,⟨279,9,[e5S,egC,ehF,eix,eja,ejT,ejV],noHint⟩,⟨279,9,[e1S,e5S,egC,ehF,eix,eja,ejT],noHint⟩,⟨279,10,[e5S,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,eix,ej9,eja,ejM],noHint⟩,⟨279,9,[egC,ehF,eix,eja,ejM,ejV],noHint⟩,⟨279,10,[egC,ehF,eix,eja,ejM,ejN,ejT],noHint⟩,⟨279,8,[egC,ehF,eix,ej9,eja,ejA,ejN,ejT],noHint⟩,⟨279,7,[e53,e5r,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,8,[e53,egC,ehF,eix,ej9,eja,ejN,ejT],noHint⟩,⟨279,9,[egC,ehF,eix,ej9,eja,ejN,ejT],noHint⟩,⟨279,9,[e5X,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,10,[egC,ehF,eix,eja,ejN,ejT,ejV],noHint⟩,⟨279,9,[egC,ehF,eix,eja,ejb,ejN,ejT],noHint⟩]
def nx16:Array Node:=#[⟨279,9,[egC,ehF,eix,ej8,eja,ejN,ejT],noHint⟩,⟨279,10,[e1S,egC,ehF,eix,eja,ejN,ejT],noHint⟩,⟨279,11,[egC,ehF,eix,eja,ejN,ejT],noHint⟩]
def nxAt (i:Nat):Node:=(if i<544 then (if i<272 then (if i<128 then (if i<64 then (if i<32 then (if i<16 then nx0.getD (i-0) ⟨0,0,[],fun _=>0⟩ else nx1.getD (i-16) ⟨0,0,[],fun _=>0⟩) else (if i<48 then nx2.getD (i-32) ⟨0,0,[],fun _=>0⟩ else nx3.getD (i-48) ⟨0,0,[],fun _=>0⟩)) else (if i<96 then (if i<80 then nx4.getD (i-64) ⟨0,0,[],fun _=>0⟩ else nx5.getD (i-80) ⟨0,0,[],fun _=>0⟩) else (if i<112 then nx6.getD (i-96) ⟨0,0,[],fun _=>0⟩ else nx7.getD (i-112) ⟨0,0,[],fun _=>0⟩))) else (if i<192 then (if i<160 then (if i<144 then nx8.getD (i-128) ⟨0,0,[],fun _=>0⟩ else nx9.getD (i-144) ⟨0,0,[],fun _=>0⟩) else (if i<176 then nxa.getD (i-160) ⟨0,0,[],fun _=>0⟩ else nxb.getD (i-176) ⟨0,0,[],fun _=>0⟩)) else (if i<224 then (if i<208 then nxc.getD (i-192) ⟨0,0,[],fun _=>0⟩ else nxd.getD (i-208) ⟨0,0,[],fun _=>0⟩) else (if i<240 then nxe.getD (i-224) ⟨0,0,[],fun _=>0⟩ else (if i<256 then nxf.getD (i-240) ⟨0,0,[],fun _=>0⟩ else nxg.getD (i-256) ⟨0,0,[],fun _=>0⟩))))) else (if i<400 then (if i<336 then (if i<304 then (if i<288 then nxh.getD (i-272) ⟨0,0,[],fun _=>0⟩ else nxi.getD (i-288) ⟨0,0,[],fun _=>0⟩) else (if i<320 then nxj.getD (i-304) ⟨0,0,[],fun _=>0⟩ else nxk.getD (i-320) ⟨0,0,[],fun _=>0⟩)) else (if i<368 then (if i<352 then nxl.getD (i-336) ⟨0,0,[],fun _=>0⟩ else nxm.getD (i-352) ⟨0,0,[],fun _=>0⟩) else (if i<384 then nxn.getD (i-368) ⟨0,0,[],fun _=>0⟩ else nxo.getD (i-384) ⟨0,0,[],fun _=>0⟩))) else (if i<464 then (if i<432 then (if i<416 then nxp.getD (i-400) ⟨0,0,[],fun _=>0⟩ else nxq.getD (i-416) ⟨0,0,[],fun _=>0⟩) else (if i<448 then nxr.getD (i-432) ⟨0,0,[],fun _=>0⟩ else nxs.getD (i-448) ⟨0,0,[],fun _=>0⟩)) else (if i<496 then (if i<480 then nxt.getD (i-464) ⟨0,0,[],fun _=>0⟩ else nxu.getD (i-480) ⟨0,0,[],fun _=>0⟩) else (if i<512 then nxv.getD (i-496) ⟨0,0,[],fun _=>0⟩ else (if i<528 then nxw.getD (i-512) ⟨0,0,[],fun _=>0⟩ else nxx.getD (i-528) ⟨0,0,[],fun _=>0⟩)))))) else (if i<816 then (if i<672 then (if i<608 then (if i<576 then (if i<560 then nxy.getD (i-544) ⟨0,0,[],fun _=>0⟩ else nxz.getD (i-560) ⟨0,0,[],fun _=>0⟩) else (if i<592 then nxA.getD (i-576) ⟨0,0,[],fun _=>0⟩ else nxB.getD (i-592) ⟨0,0,[],fun _=>0⟩)) else (if i<640 then (if i<624 then nxC.getD (i-608) ⟨0,0,[],fun _=>0⟩ else nxD.getD (i-624) ⟨0,0,[],fun _=>0⟩) else (if i<656 then nxE.getD (i-640) ⟨0,0,[],fun _=>0⟩ else nxF.getD (i-656) ⟨0,0,[],fun _=>0⟩))) else (if i<736 then (if i<704 then (if i<688 then nxG.getD (i-672) ⟨0,0,[],fun _=>0⟩ else nxH.getD (i-688) ⟨0,0,[],fun _=>0⟩) else (if i<720 then nxI.getD (i-704) ⟨0,0,[],fun _=>0⟩ else nxJ.getD (i-720) ⟨0,0,[],fun _=>0⟩)) else (if i<768 then (if i<752 then nxK.getD (i-736) ⟨0,0,[],fun _=>0⟩ else nxL.getD (i-752) ⟨0,0,[],fun _=>0⟩) else (if i<784 then nxM.getD (i-768) ⟨0,0,[],fun _=>0⟩ else (if i<800 then nxN.getD (i-784) ⟨0,0,[],fun _=>0⟩ else nxO.getD (i-800) ⟨0,0,[],fun _=>0⟩))))) else (if i<960 then (if i<880 then (if i<848 then (if i<832 then nxP.getD (i-816) ⟨0,0,[],fun _=>0⟩ else nxQ.getD (i-832) ⟨0,0,[],fun _=>0⟩) else (if i<864 then nxR.getD (i-848) ⟨0,0,[],fun _=>0⟩ else nxS.getD (i-864) ⟨0,0,[],fun _=>0⟩)) else (if i<912 then (if i<896 then nxT.getD (i-880) ⟨0,0,[],fun _=>0⟩ else nxU.getD (i-896) ⟨0,0,[],fun _=>0⟩) else (if i<928 then nxV.getD (i-912) ⟨0,0,[],fun _=>0⟩ else (if i<944 then nxW.getD (i-928) ⟨0,0,[],fun _=>0⟩ else nxX.getD (i-944) ⟨0,0,[],fun _=>0⟩)))) else (if i<1024 then (if i<992 then (if i<976 then nxY.getD (i-960) ⟨0,0,[],fun _=>0⟩ else nxZ.getD (i-976) ⟨0,0,[],fun _=>0⟩) else (if i<1008 then nx10.getD (i-992) ⟨0,0,[],fun _=>0⟩ else nx11.getD (i-1008) ⟨0,0,[],fun _=>0⟩)) else (if i<1056 then (if i<1040 then nx12.getD (i-1024) ⟨0,0,[],fun _=>0⟩ else nx13.getD (i-1040) ⟨0,0,[],fun _=>0⟩) else (if i<1072 then nx14.getD (i-1056) ⟨0,0,[],fun _=>0⟩ else (if i<1088 then nx15.getD (i-1072) ⟨0,0,[],fun _=>0⟩ else nx16.getD (i-1088) ⟨0,0,[],fun _=>0⟩)))))))
def vx0:Array View:=#[⟨0x100020004000800,⟨11,by decide⟩,0x20004000000,[e60,e64],2,hint 0xda0b6⟩,⟨0x100020010002000,⟨13,by decide⟩,0x20010000000,[e61,e64],2,hint 0⟩,⟨0x108000010800000,⟨23,by decide⟩,0x8000010000000,[e61,e6i],2,hint 0⟩,⟨0xff000000000000,⟨48,by decide⟩,0xe8000000000000,[e4U,e5k,e5E],3,hint 0x32e54a993254a⟩,⟨0x101020204040808,⟨3,by decide⟩,0x20004000000,[e65,e69,e6c],3,hint 0x3eddb368305b36⟩,⟨0x300030030003000,⟨12,by decide⟩,0x200020030000000,[e6m,e6x,e6z],2,hint 0x40810204081020⟩,⟨0xf00f000,⟨12,by decide⟩,0xe008000,[ee,em,et],3,hint 0⟩,⟨0x3300cc00,⟨10,by decide⟩,0x32008000,[eE,eH,eK],3,hint 0⟩,⟨0x5500aa00,⟨9,by decide⟩,0x54008000,[eN,eP,eR],3,hint 0⟩,⟨0x99009900,⟨8,by decide⟩,0x98008000,[e11,e18,e1e],3,hint 0⟩,⟨0xa500a500,⟨8,by decide⟩,0xa4008000,[eX,e1n,e1t],3,hint 0⟩,⟨0xc300c300,⟨8,by decide⟩,0xc2008000,[eW,e1I,e1K],3,hint 0⟩,⟨0xf000000f000,⟨12,by decide⟩,0xe0000008000,[e1X,e20,e22],3,hint 0⟩,⟨0x990000009900,⟨8,by decide⟩,0x980000008000,[e2a,e2g,e2i],3,hint 0⟩,⟨0xa5000000a500,⟨8,by decide⟩,0xa40000008000,[e26,e2m,e2s],3,hint 0⟩,⟨0x9900000099000,⟨12,by decide⟩,0x8900000008000,[e2R,e2S,e2T],3,hint 0⟩]
def vx1:Array View:=#[⟨0xa000aa000a000,⟨13,by decide⟩,0x80000a0008000,[e2P,e2Y,e31],3,hint 0⟩,⟨0xa00a00a00a000,⟨13,by decide⟩,0x800000a008000,[e2Q,e2W,e38],3,hint 0⟩,⟨0xc000cc000c000,⟨14,by decide⟩,0x80000c0008000,[e2P,e3q,e3s],3,hint 0⟩,⟨0xc00c00c00c000,⟨14,by decide⟩,0x800000c008000,[e2Q,e3n,e3x],3,hint 0⟩,⟨0xf00000f000000,⟨24,by decide⟩,0x800000e000000,[e2W,e3n,e3L],3,hint 0⟩,⟨0xf0f0000000000,⟨40,by decide⟩,0x80e0000000000,[e3b,e3B,e3L],3,hint 0⟩,⟨0x22002288008800,⟨11,by decide⟩,0x20000088008000,[e46,e48,e49],3,hint 0⟩,⟨0x101020210102020,⟨5,by decide⟩,0x20010000000,[e66,e6a,e6c],3,hint 0⟩,⟨0x101040410104040,⟨6,by decide⟩,0x40010000000,[e67,e6a,e6d],3,hint 0⟩,⟨0x104020810402080,⟨7,by decide⟩,0x20010000000,[e66,e6f,e6h],3,hint 0⟩,⟨0x108010810801080,⟨7,by decide⟩,0x8000010000000,[e63,e6j,e6k],3,hint 0⟩,⟨0x208020810401040,⟨6,by decide⟩,0x208020010000000,[e6l,e6q,e6s],3,hint 0⟩,⟨0x208020820802080,⟨7,by decide⟩,0x208020020000000,[e6m,e6r,e6s],3,hint 0⟩,⟨0x408040804080408,⟨3,by decide⟩,0x408040004000000,[e6U,e72,e73],3,hint 0⟩,⟨0x420042004200420,⟨5,by decide⟩,0x420040004000000,[e6U,e7a,e7b],3,hint 0⟩,⟨0x500050050005000,⟨12,by decide⟩,0x400040050000000,[e6V,e7f,e7h],2,hint 0⟩]
def vx2:Array View:=#[⟨0x808020208080202,⟨1,by decide⟩,0x808020008000000,[e7D,e7R,e7Y],3,hint 0⟩,⟨0x808080808080808,⟨3,by decide⟩,0x808080008000000,[e7J,e7R,e86],3,hint 0⟩,⟨0x808080820202020,⟨5,by decide⟩,0x808080020000000,[e7K,e7S,e86],3,hint 0⟩,⟨0x808080840404040,⟨6,by decide⟩,0x808080040000000,[e7L,e7T,e86],3,hint 0⟩,⟨0x880088008800880,⟨7,by decide⟩,0x880080008000000,[e7J,e8g,e8h],3,hint 0⟩,⟨0xa0a000005050000,⟨16,by decide⟩,0xa08000004000000,[e7Q,e8o,e8B],3,hint 0⟩,⟨0xf0f000000000000,⟨48,by decide⟩,0xe08000000000000,[e8B,e9i,e9O],3,hint 0⟩,⟨0x8008100180081001,⟨0,by decide⟩,0x8008100080000000,[eda,edd,ede],3,hint 0⟩,⟨0x8080080880800808,⟨3,by decide⟩,0x8080080080000000,[ed9,edj,edk],3,hint 0⟩,⟨0x8080808008080808,⟨3,by decide⟩,0x8080800008000000,[edb,edi,edn],3,hint 0⟩,⟨0x9090000009090000,⟨16,by decide⟩,0x9080000008000000,[edi,eez,eeH],3,hint 0⟩,⟨0x9090090900000000,⟨32,by decide⟩,0x9080080000000000,[edk,eeA,eeH],3,hint 0⟩,⟨0x9900000000009900,⟨8,by decide⟩,0x9800000000008000,[edG,eey,eeS],3,hint 0⟩,⟨0xf00f0f0,⟨4,by decide⟩,0xe008000,[ef,en,et,ev],4,hint 0x42850a142850a13060c183060c18⟩,⟨0x99999900,⟨8,by decide⟩,0x98008000,[e6,e14,e1c,e1j],4,hint 0x44e8d9b3468d1a72e5cb93468d1a⟩,⟨0xaf000000af00,⟨8,by decide⟩,0xae0000008000,[e2e,e2m,e2x,e2z],3,hint 0x468d1a3468d1a3468d1a3468d1a3⟩]
def vx3:Array View:=#[⟨0xe000ee000e000,⟨13,by decide⟩,0x80000e0008000,[e2K,e3w,e3G,e3H],4,hint 0x4874e1c7cf8e1c4874e1c7cf8e1c⟩,⟨0x808020288882222,⟨1,by decide⟩,0x808020088000000,[eU,e7E,e7V,e7Y],3,hint 0x4a952a54a952a54a952a54a952a5⟩,⟨0xa0a08080a0a0808,⟨3,by decide⟩,0xa0808000a000000,[e6n,e8r,e8I,e8M],4,hint 0x4d299b372e5cb98b162c572e5cb9⟩,⟨0xa0a0a000a0a0a00,⟨9,by decide⟩,0xa080a000a000000,[e2U,e85,e8I,e8O],3,hint 0x4ce53362c58b1810204062c58b1⟩,⟨0xf03f030,⟨4,by decide⟩,0xe008000,[eg,em,ev,ex],4,hint 0⟩,⟨0xf05f050,⟨4,by decide⟩,0xe008000,[ee,eo,ev,ey],4,hint 0⟩,⟨0xf0af0a0,⟨5,by decide⟩,0xe008000,[ea,ep,ev,ez],4,hint 0⟩,⟨0xf0cf0c0,⟨6,by decide⟩,0xe008000,[e8,eh,ev,eA],4,hint 0⟩,⟨0xf0ff000,⟨12,by decide⟩,0xe008000,[e5,ej,eq,eB],4,hint 0⟩,⟨0x99009999,⟨0,by decide⟩,0x98008000,[e12,e19,e1e,e1f],4,hint 0⟩,⟨0x99119911,⟨0,by decide⟩,0x98008000,[e11,e1a,e1f,e1g],4,hint 0⟩,⟨0x99889988,⟨3,by decide⟩,0x98008000,[eC,e1b,e1f,e1h],4,hint 0⟩,⟨0x99909990,⟨4,by decide⟩,0x98008000,[ec,e13,e1f,e1i],4,hint 0⟩,⟨0xa500a5a5,⟨0,by decide⟩,0xa4008000,[eY,e1o,e1t,e1u],4,hint 0⟩,⟨0xa521a521,⟨0,by decide⟩,0xa4008000,[eX,e1p,e1u,e1v],4,hint 0⟩,⟨0xa584a584,⟨2,by decide⟩,0xa4008000,[eD,e1q,e1u,e1w],4,hint 0⟩]
def vx4:Array View:=#[⟨0xa5a5a500,⟨8,by decide⟩,0xa4008000,[e7,eZ,e1r,e1x],4,hint 0⟩,⟨0xaf00af00,⟨8,by decide⟩,0xae008000,[e16,e1n,e1y,e1B],3,hint 0⟩,⟨0xbb00bb00,⟨8,by decide⟩,0xba008000,[e11,e1y,e1E,e1G],3,hint 0⟩,⟨0xa5000000a5a5,⟨0,by decide⟩,0xa40000008000,[e27,e2n,e2s,e2t],4,hint 0⟩,⟨0xa500a500a500,⟨8,by decide⟩,0xa400a4008000,[e1t,e28,e2o,e2s],4,hint 0⟩,⟨0xa5210000a521,⟨0,by decide⟩,0xa40000008000,[e26,e2p,e2t,e2u],4,hint 0⟩,⟨0xa5840000a584,⟨2,by decide⟩,0xa40000008000,[e25,e2q,e2t,e2v],4,hint 0⟩,⟨0xb000bb000b000,⟨12,by decide⟩,0x80000b0008000,[e2P,e36,e3k,e3l],3,hint 0⟩,⟨0xf00000f000f00,⟨8,by decide⟩,0x800000e000000,[e2X,e3o,e3L,e3S],4,hint 0⟩,⟨0xf00030f000300,⟨8,by decide⟩,0x800000e000000,[e2Z,e3n,e3S,e3W],4,hint 0⟩,⟨0xf000a0f000a00,⟨9,by decide⟩,0x800000e000000,[e2M,e3r,e3S,e3X],4,hint 0⟩,⟨0xf000c0f000c00,⟨10,by decide⟩,0x800000e000000,[e2I,e30,e3S,e3Y],4,hint 0⟩,⟨0xf000f0f000000,⟨24,by decide⟩,0x800000e000000,[e1U,e33,e3t,e3Z],4,hint 0⟩,⟨0xf0f0000000f00,⟨8,by decide⟩,0x80e0000000000,[e3c,e3C,e3L,e44],4,hint 0⟩,⟨0xf0f0000030300,⟨8,by decide⟩,0x80e0000000000,[e3d,e3B,e3M,e44],4,hint 0⟩,⟨0xf0f00000c0c00,⟨10,by decide⟩,0x80e0000000000,[e2J,e3e,e3N,e44],4,hint 0⟩]
def vx5:Array View:=#[⟨0xf0f00000f0000,⟨16,by decide⟩,0x80e0000000000,[e22,e3f,e3D,e44],4,hint 0⟩,⟨0x88008888888888,⟨3,by decide⟩,0x88000088008000,[e11,e4t,e4u,e4v],3,hint 0⟩,⟨0xa000a0a0a0a0a0,⟨5,by decide⟩,0xa00000a0008000,[e1n,e4t,e4O,e4P],3,hint 0⟩,⟨0xaf00000000af00,⟨8,by decide⟩,0xa8000000008000,[e4B,e4M,e4W,e5d],4,hint 0⟩,⟨0xaf0000af000000,⟨24,by decide⟩,0xa80000ae000000,[e4C,e4N,e4Y,e5d],4,hint 0⟩,⟨0x308030803080308,⟨3,by decide⟩,0x208020002000000,[e62,e6A,e6H,e6I],4,hint 0⟩,⟨0x30c0208030c0208,⟨3,by decide⟩,0x208020002000000,[e6e,e6y,e6K,e6N],4,hint 0⟩,⟨0x30c030c20802080,⟨7,by decide⟩,0x208020020000000,[e6g,e6B,e6L,e6O],4,hint 0⟩,⟨0x30c2080030c2080,⟨7,by decide⟩,0x208200002000000,[e6e,e6D,e6K,e6P],4,hint 0⟩,⟨0x320032003200320,⟨5,by decide⟩,0x220020002000000,[e62,e6A,e6Q,e6R],4,hint 0⟩,⟨0x5000500a500a500,⟨8,by decide⟩,0x4000400a4008000,[e1n,e6W,e7g,e7h],4,hint 0⟩,⟨0x500a5000500a500,⟨8,by decide⟩,0x400a40004008000,[e2m,e6X,e7e,e7n],4,hint 0⟩,⟨0x808030308080303,⟨0,by decide⟩,0x808020008000000,[e7F,e7R,e81,e82],4,hint 0⟩,⟨0x808050508080505,⟨0,by decide⟩,0x808040008000000,[e7H,e7R,e83,e84],4,hint 0⟩,⟨0x808080803030303,⟨0,by decide⟩,0x808080002000000,[e7I,e7P,e86,e87],4,hint 0⟩,⟨0x808080888888888,⟨3,by decide⟩,0x808080088008000,[eV,e7M,e7V,e86],4,hint 0⟩]
def vx6:Array View:=#[⟨0x80a0405080a0405,⟨0,by decide⟩,0x808040008000000,[e7G,e83,e8d,e8e],4,hint 0⟩,⟨0x80a080a080a080a,⟨1,by decide⟩,0x808080008000000,[e7J,e88,e8d,e8f],4,hint 0⟩,⟨0x900090099009900,⟨8,by decide⟩,0x800080098008000,[e18,e7M,e8i,e8j],4,hint 0⟩,⟨0xa0a04040a0a0404,⟨2,by decide⟩,0xa0804000a000000,[e6n,e8q,e8I,e8L],4,hint 0⟩,⟨0xa0a0a0a08080808,⟨3,by decide⟩,0xa080a0008000000,[e6p,e8s,e8H,e8P],4,hint 0⟩,⟨0xc0c000003030303,⟨0,by decide⟩,0xc08000002000000,[e7O,e97,e9i,e9n],4,hint 0⟩,⟨0xc0c000c03030003,⟨0,by decide⟩,0xc08000002000000,[e7X,e96,e9n,e9q],4,hint 0⟩,⟨0xc0c0303000c0003,⟨0,by decide⟩,0xc08020000000000,[e7Z,e98,e9m,e9r],4,hint 0⟩,⟨0xc0c03030c0c0000,⟨18,by decide⟩,0xc0802000c000000,[e1W,e80,e99,e9r],4,hint 0⟩,⟨0xc0c08080c0c0808,⟨3,by decide⟩,0xc0808000c000000,[e6Y,e9b,e9o,e9s],4,hint 0⟩,⟨0xc0c0c000c0c0c00,⟨10,by decide⟩,0xc080c000c000000,[e3m,e85,e9o,e9u],3,hint 0⟩,⟨0xc0c20200c0c2020,⟨5,by decide⟩,0xc0820000c000000,[e6Y,e9e,e9o,e9z],4,hint 0⟩,⟨0xf0a00000f0a0000,⟨17,by decide⟩,0xe0800000e000000,[e7e,e9g,e9T,ea8],3,hint 0⟩,⟨0xf0c00000f0c0000,⟨18,by decide⟩,0xe0800000e000000,[e6w,e8z,e9T,eab],3,hint 0⟩,⟨0xf0c0f0c00000000,⟨34,by decide⟩,0xe080e0000000000,[e6z,e8A,e9Y,eab],3,hint 0⟩,⟨0xf0f00000000000f,⟨0,by decide⟩,0xe08000000000000,[e8C,e9j,e9O,eae],4,hint 0⟩]
def vx7:Array View:=#[⟨0xf0f000000000c0c,⟨2,by decide⟩,0xe08000000000000,[e6F,e8D,e9P,eae],4,hint 0⟩,⟨0xf0f0000000f0000,⟨16,by decide⟩,0xe08000000000000,[e8G,e9m,e9O,eae],4,hint 0⟩,⟨0xf0f00000c0c0000,⟨18,by decide⟩,0xe0800000c000000,[e6F,e8H,e9S,eae],4,hint 0⟩,⟨0xf0f000f00000000,⟨32,by decide⟩,0xe08000000000000,[e8K,e9q,e9O,eae],4,hint 0⟩,⟨0xf0f0a0a00000000,⟨33,by decide⟩,0xe080a0000000000,[e7o,e9s,e9V,eae],4,hint 0⟩,⟨0x2020030320200303,⟨0,by decide⟩,0x2020020020000000,[eb0,eb4,eb5,eb6],4,hint 0⟩,⟨0x2020202003030303,⟨0,by decide⟩,0x2020200002000000,[eb1,eb3,eb8,eb9],4,hint 0⟩,⟨0x2021202120212021,⟨0,by decide⟩,0x2020200020000000,[eb2,ebb,ebg,ebh],4,hint 0⟩,⟨0x2121202021212020,⟨5,by decide⟩,0x2020200020000000,[e68,ebi,ebm,ebn],4,hint 0⟩,⟨0x2121212120202020,⟨5,by decide⟩,0x2020200020000000,[e6b,ebj,ebl,ebo],4,hint 0⟩,⟨0x2222220022222200,⟨9,by decide⟩,0x2220220022000000,[e47,eb7,ebu,ebw],3,hint 0⟩,⟨0x2222222222002200,⟨9,by decide⟩,0x2220220022000000,[e49,eba,ebt,ebx],3,hint 0⟩,⟨0xa000a500a000a500,⟨8,by decide⟩,0xa000a400a0008000,[edc,efA,efB,efC],4,hint 0⟩,⟨0xafaf000000000000,⟨48,by decide⟩,0xaea8000000000000,[eel,efL,egn,egL],4,hint 0⟩,⟨0xf0ff0f0,⟨4,by decide⟩,0xe008000,[ek,er,ev,eB],4,hint 0x42850a13060c1842850a13060c18⟩,⟨0xff00ff00,⟨8,by decide⟩,0xfe008000,[e1y,e1L,e1O,e1Q],5,hint 0x674e1c3468d1a62c58b162c58b1⟩]
def vx8:Array View:=#[⟨0xf000ff000f000,⟨12,by decide⟩,0x80000f0008000,[e36,e3w,e3U,e3Z],4,hint 0x4874e1c76eddbb4874e1c76eddbb⟩,⟨0xf00f00f00f000,⟨12,by decide⟩,0x800000e008000,[e3a,e3A,e3S,e40],6,hint 0x874e1c64c8e1c3c74e1c64c8e1c⟩,⟨0x30c030c30c030c0,⟨6,by decide⟩,0x208020030000000,[e6u,e6C,e6M,e6O],5,hint 0xb0debd76eddbb850a14276eddbb⟩,⟨0xa0a0a0a0a0a0a0a,⟨1,by decide⟩,0xa080a000a000000,[e88,e8t,e8I,e8P],4,hint 0x4d299b362c58b1810204062c58b1⟩,⟨0xf0f0000f0f00000,⟨20,by decide⟩,0xe080000f0000000,[e8J,e9p,e9U,eae],5,hint 0xd2e54a78f1e3c912244878f1e3c⟩,⟨0x3333cccc,⟨2,by decide⟩,0x32008000,[eF,eI,eL,eM],4,hint 0⟩,⟨0x5555aaaa,⟨1,by decide⟩,0x54008000,[eO,eQ,eS,eT],4,hint 0⟩,⟨0x99999999,⟨0,by decide⟩,0x98008000,[e15,e1d,e1f,e1j],4,hint 0⟩,⟨0xa5a5a5a5,⟨0,by decide⟩,0xa4008000,[e10,e1s,e1u,e1x],4,hint 0⟩,⟨0xf0f0000f0f0,⟨4,by decide⟩,0xe0000008000,[e1Y,e21,e23,e24],4,hint 0⟩,⟨0x999900009999,⟨0,by decide⟩,0x980000008000,[e2b,e2h,e2j,e2l],4,hint 0⟩,⟨0xa5a50000a5a5,⟨0,by decide⟩,0xa40000008000,[e29,e2r,e2t,e2w],4,hint 0⟩,⟨0xff000000ff00,⟨8,by decide⟩,0xfe0000008000,[e2x,e2B,e2D,e2F],5,hint 0⟩,⟨0xf000f0f000f00,⟨8,by decide⟩,0x800000e000000,[e34,e3u,e3S,e3Z],4,hint 0⟩,⟨0xf0f00000f0f00,⟨8,by decide⟩,0x80e0000000000,[e3g,e3E,e3O,e44],4,hint 0⟩,⟨0xf0f0000f0f000,⟨12,by decide⟩,0x80e0000008000,[e3h,e3F,e3P,e44],6,hint 0⟩]
def vx9:Array View:=#[⟨0x33003333003300,⟨8,by decide⟩,0x20000032000000,[e4a,e4d,e4i,e4j],4,hint 0⟩,⟨0x33330000333300,⟨8,by decide⟩,0x20320000000000,[e4b,e4e,e4g,e4k],4,hint 0⟩,⟨0x33330000cccc00,⟨10,by decide⟩,0x20320000008000,[e4c,e4f,e4h,e4k],6,hint 0⟩,⟨0x55005555005500,⟨8,by decide⟩,0x40000054000000,[e4m,e4o,e4q,e4r],4,hint 0⟩,⟨0x5500aa5500aa00,⟨9,by decide⟩,0x40000054008000,[e4n,e4p,e4q,e4s],6,hint 0⟩,⟨0x99990000999900,⟨8,by decide⟩,0x88980000008000,[e4z,e4H,e4I,e4K],4,hint 0⟩,⟨0xaa00aaaa00aa00,⟨9,by decide⟩,0xa80000aa008000,[e4x,e4Q,e4Y,e50],5,hint 0⟩,⟨0xaaaa0000aaaa00,⟨9,by decide⟩,0xa8aa0000008000,[e4z,e4S,e4X,e59],5,hint 0⟩,⟨0xcc00cccc00cc00,⟨10,by decide⟩,0xc80000cc008000,[e4x,e5i,e5o,e5p],5,hint 0⟩,⟨0xf000f0f000f000,⟨12,by decide⟩,0xe00000f0008000,[e4Q,e5i,e5I,e5J],5,hint 0⟩,⟨0xf0f00000f0f000,⟨12,by decide⟩,0xe0f00000008000,[e4S,e5j,e5H,e5N],5,hint 0⟩,⟨0xff0000000000ff,⟨0,by decide⟩,0xe8000000000000,[e4V,e5l,e5F,e5R],4,hint 0⟩,⟨0xff00000000ff00,⟨8,by decide⟩,0xe8000000008000,[e4W,e5m,e5G,e5R],6,hint 0⟩,⟨0xff000000ff0000,⟨16,by decide⟩,0xe8000000000000,[e4X,e5n,e5H,e5R],4,hint 0⟩,⟨0xff0000ff000000,⟨24,by decide⟩,0xe80000fe000000,[e4Y,e5o,e5I,e5R],6,hint 0⟩,⟨0xff00ff00000000,⟨32,by decide⟩,0xe8000000000000,[e50,e5p,e5J,e5R],4,hint 0⟩]
def vxa:Array View:=#[⟨0xffff0000000000,⟨40,by decide⟩,0xe8fe0000000000,[e59,e5v,e5N,e5R],6,hint 0⟩,⟨0x30c030c030c030c,⟨2,by decide⟩,0x208020002000000,[e6t,e6A,e6K,e6O],4,hint 0⟩,⟨0x330033003300330,⟨4,by decide⟩,0x220020002000000,[e6v,e6A,e6S,e6T],4,hint 0⟩,⟨0x50a050a050a050a,⟨1,by decide⟩,0x408040004000000,[e74,e7i,e7s,e7u],4,hint 0⟩,⟨0x50a050a50a050a0,⟨5,by decide⟩,0x408040050000000,[e75,e7k,e7t,e7u],5,hint 0⟩,⟨0x5a005a005a005a0,⟨5,by decide⟩,0x4a0040004000000,[e7c,e7i,e7y,e7z],5,hint 0⟩,⟨0x909090909090909,⟨0,by decide⟩,0x808080008000000,[e88,e8k,e8l,e8m],4,hint 0⟩,⟨0xa0a0a0aa0a0a0a0,⟨5,by decide⟩,0xa080a00a0008000,[e89,e8u,e8J,e8P],5,hint 0⟩,⟨0xa0aa0a00a0aa0a0,⟨5,by decide⟩,0xa08a0000a008000,[e8c,e8y,e8I,e8W],5,hint 0⟩,⟨0xc0c03030c0c0303,⟨0,by decide⟩,0xc0802000c000000,[e81,e9a,e9o,e9r],4,hint 0⟩,⟨0xc0c0c0c0c0c0c0c,⟨2,by decide⟩,0xc080c000c000000,[e88,e9c,e9o,e9v],4,hint 0⟩,⟨0xc0c0c0cc0c0c0c0,⟨6,by decide⟩,0xc080c00c0008000,[e89,e9d,e9p,e9v],5,hint 0⟩,⟨0xf000f00f000f000,⟨12,by decide⟩,0xe000e00f0008000,[e8u,e9d,e9U,e9Y],5,hint 0⟩,⟨0xf00f0000f00f000,⟨12,by decide⟩,0xe00f0000e008000,[e8y,e9f,e9T,ea3],5,hint 0⟩,⟨0xf0f000000000f0f,⟨0,by decide⟩,0xe08000000000000,[e8E,e9k,e9Q,eae],4,hint 0⟩,⟨0xf0f00000000f0f0,⟨4,by decide⟩,0xe08000000008000,[e8F,e9l,e9R,eae],6,hint 0⟩]
def vxb:Array View:=#[⟨0xf0f00000f0f0000,⟨16,by decide⟩,0xe0800000e000000,[e8I,e9o,e9T,eae],4,hint 0⟩,⟨0xf0f0f0f00000000,⟨32,by decide⟩,0xe080e0000000000,[e8P,e9v,e9Y,eae],4,hint 0⟩,⟨0xf0ff0f000000000,⟨36,by decide⟩,0xe08f00000000000,[e8W,e9A,ea3,eae],5,hint 0⟩,⟨0x1122112211221122,⟨1,by decide⟩,0x1020100010000000,[eaz,eaG,eaQ,eaR],4,hint 0⟩,⟨0x1122448811224488,⟨3,by decide⟩,0x1020440010000000,[eaA,eaJ,eaQ,eaS],5,hint 0⟩,⟨0x1188118811881188,⟨3,by decide⟩,0x1088100010000000,[eaC,eaG,eaU,eaV],5,hint 0⟩,⟨0x2121212121212121,⟨0,by decide⟩,0x2020200020000000,[ebb,ebk,ebm,ebo],4,hint 0⟩,⟨0x2222222222222222,⟨1,by decide⟩,0x2220220022000000,[ebb,ebp,ebu,ebx],4,hint 0⟩,⟨0x2222222288888888,⟨3,by decide⟩,0x2220220088008000,[ebc,ebq,ebv,ebx],5,hint 0⟩,⟨0x2222888822228888,⟨3,by decide⟩,0x2220880022008000,[ebe,ebr,ebu,ebB],5,hint 0⟩,⟨0x3030030330300303,⟨0,by decide⟩,0x3020020030000000,[eb5,ebR,ebV,ebW],4,hint 0⟩,⟨0x3030303030303030,⟨4,by decide⟩,0x3020300030000000,[ebb,ebS,ebV,ebX],4,hint 0⟩,⟨0x3030c0c03030c0c0,⟨6,by decide⟩,0x3020c00030008000,[ebe,ebT,ebV,ec0],5,hint 0⟩,⟨0x3300cc003300cc00,⟨10,by decide⟩,0x3200cc0032008000,[ebr,ebT,ec4,ec8],5,hint 0⟩,⟨0x3333000000003333,⟨0,by decide⟩,0x3220000000000000,[ebs,ebU,ec3,ecb],4,hint 0⟩,⟨0x3333000033330000,⟨16,by decide⟩,0x3220000032000000,[ebu,ebV,ec4,ecb],4,hint 0⟩]
def vxc:Array View:=#[⟨0x3333333300000000,⟨32,by decide⟩,0x3220320000000000,[ebx,ebX,ec5,ecb],4,hint 0⟩,⟨0x4444111144441111,⟨0,by decide⟩,0x4440100044000000,[eci,ecm,ecp,ecq],4,hint 0⟩,⟨0x4444444444444444,⟨2,by decide⟩,0x4440440044000000,[eck,ecn,ecp,ecr],4,hint 0⟩,⟨0x4444888844448888,⟨3,by decide⟩,0x4440880044008000,[ecl,eco,ecp,ecu],5,hint 0⟩,⟨0x5050505005050505,⟨0,by decide⟩,0x5040500004000000,[ecj,ecw,ecz,ecB],4,hint 0⟩,⟨0x5050505050505050,⟨4,by decide⟩,0x5040500050000000,[eck,ecx,ecA,ecB],4,hint 0⟩,⟨0x5500aa005500aa00,⟨9,by decide⟩,0x5400aa0054008000,[eco,ecy,ecF,ecJ],5,hint 0⟩,⟨0x5555000055550000,⟨16,by decide⟩,0x5440000054000000,[ecp,ecA,ecF,ecN],4,hint 0⟩,⟨0x8241824182418241,⟨0,by decide⟩,0x8240820082008000,[edh,edu,edv,edw],5,hint 0⟩,⟨0x8282828282828282,⟨1,by decide⟩,0x8280820082008000,[edp,edu,edx,edy],5,hint 0⟩,⟨0x8421842184218421,⟨0,by decide⟩,0x8420840084008000,[edg,edA,edB,edC],5,hint 0⟩,⟨0x8484848484848484,⟨2,by decide⟩,0x8480840084008000,[edp,edA,edD,edE],5,hint 0⟩,⟨0x8822882288228822,⟨1,by decide⟩,0x8820880088008000,[edg,edJ,edL,edM],5,hint 0⟩,⟨0x8844884488448844,⟨2,by decide⟩,0x8840880088008000,[edh,edJ,edO,edP],5,hint 0⟩,⟨0x8888111188881111,⟨0,by decide⟩,0x8888100088000000,[edl,edH,edT,edU],4,hint 0⟩,⟨0x8888888811111111,⟨0,by decide⟩,0x8888880010000000,[edo,edI,edS,edW],4,hint 0⟩]
def vxd:Array View:=#[⟨0x8888888888888888,⟨3,by decide⟩,0x8888880088008000,[edp,edJ,edT,edW],4,hint 0⟩,⟨0x9009900990099009,⟨0,by decide⟩,0x9008900090008000,[edf,eeB,eeD,eeE],5,hint 0⟩,⟨0x9090909090909090,⟨4,by decide⟩,0x9080900090008000,[edp,eeB,eeJ,eeL],5,hint 0⟩,⟨0x9900990099009900,⟨8,by decide⟩,0x9800980098008000,[edJ,eeB,eeU,ef1],4,hint 0⟩,⟨0x9999000000009999,⟨0,by decide⟩,0x9888000000008000,[edR,eeI,eeT,efd],4,hint 0⟩,⟨0xa00aa00aa00aa00a,⟨1,by decide⟩,0xa008a000a0008000,[edf,efB,efD,efE],5,hint 0⟩,⟨0xa050a050a050a050,⟨4,by decide⟩,0xa040a000a0008000,[edh,efB,efH,efI],5,hint 0⟩,⟨0xa0a0a0a0a0a0a0a0,⟨5,by decide⟩,0xa0a0a000a0008000,[edp,efB,efN,efS],4,hint 0⟩,⟨0xa500a500a500a500,⟨8,by decide⟩,0xa400a400a4008000,[edA,efB,eg1,eg2],4,hint 0⟩,⟨0xaaaa00000000aaaa,⟨1,by decide⟩,0xaaa8000000008000,[edR,efM,eg8,egn],5,hint 0⟩,⟨0xc00cc00cc00cc00c,⟨2,by decide⟩,0xc008c000c0008000,[edf,ehl,ehm,ehn],5,hint 0⟩,⟨0xc0c0c0c0c0c0c0c0,⟨6,by decide⟩,0xc0c0c000c0008000,[edp,ehl,ehq,ehr],4,hint 0⟩,⟨0xf0f000000000f0f0,⟨4,by decide⟩,0xf0e0000000008000,[efM,ehp,eik,eis],5,hint 0⟩,⟨0xffff000000000000,⟨48,by decide⟩,0xfee8000000000000,[egn,ehA,eis,ej0],6,hint 0⟩,⟨0xf0fffff,⟨0,by decide⟩,0xe008000,[e4,el,es,ew,eB],5,hint 0xe68e9a3868e1a3060c183060c1862c58b162c58b13060c183060c18⟩,⟨0xf0f0a0a0f0f0a0a,⟨1,by decide⟩,0xe080a000e000000,[e7p,e9t,e9W,eaf,eah],6,hint 0x10d1c3466cd9b362c58b162c58b18102040810204062c58b162c58b1⟩]
def vxe:Array View:=#[⟨0x2323232323232323,⟨0,by decide⟩,0x2220220022000000,[ebb,eby,ebJ,ebM,ebO],5,hint 0x54a9a3466cd9b362c58b162c58b18102040810204062c58b162c58b1⟩,⟨0x88aa88aa88aa88aa,⟨1,by decide⟩,0x88a8880088008000,[eds,edJ,ee1,ee6,ee7],5,hint 0x58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c⟩,⟨0x8c238c238c238c23,⟨0,by decide⟩,0x8c208c008c008000,[edg,edN,eeh,eej,eek],5,hint 0x56ad5ab56ad5ab56ad5ab56ad5ab56ad5ab56ad5ab56ad5ab56ad5ab⟩,⟨0xa521a521a521a521,⟨0,by decide⟩,0xa420a400a4008000,[edA,efG,eg3,eg4,eg5],6,hint 0x1270c997e70c996ad4c996ad4c998910c998910c996ad4c996ad4c99⟩,⟨0xaf00af00af00af00,⟨8,by decide⟩,0xae00ae00ae008000,[eeh,efB,ega,egM,egQ],4,hint 0x5cb972e5cb972e5cb972e5cb972e5cb972e5cb972e5cb972e5cb972e⟩,⟨0xf000f0f0f0f0f,⟨0,by decide⟩,0x800000e000000,[eu,e35,e3v,e3T,e3Z],5,hint 0⟩,⟨0xf0f0c0c0f0f0c0c,⟨2,by decide⟩,0xe080c000e000000,[e6G,e8N,e9X,eaf,eai],6,hint 0⟩,⟨0xaa22aa22aa22aa22,⟨1,by decide⟩,0xaa20aa00aa008000,[edJ,efG,ega,egg,egh],5,hint 0⟩,⟨0xffffffff,⟨0,by decide⟩,0xfe008000,[e1A,e1M,e1P,e1R,e1S],6,hint 0x50a142850a14283060c183060c1850a142850a14283060c183060c18⟩,⟨0xff00ff00ff00ff,⟨0,by decide⟩,0xe8000000000000,[e52,e5q,e5K,e5S,e5W],5,hint 0x52a54a952a54a993264c993264c98f1e3c78f1e3c78f1e3c78f1e3c7⟩,⟨0xff00ffff00ff00,⟨8,by decide⟩,0xe80000fe008000,[e56,e5s,e5L,e5T,e5W],8,hint 0x1474e1c3468d1a62c58b162c58b13c74e1c3468d1a62c58b162c58b1⟩,⟨0xf0f0f0f0f0f0f0f,⟨0,by decide⟩,0xe080e000e000000,[e8R,e9w,e9Z,eaf,eal],7,hint 0x16d1c3466cd9b362c58b162c58b18102040810204062c58b162c58b1⟩,⟨0xf0f0f0ff0f0f0f0,⟨4,by decide⟩,0xe080e00f0008000,[e8S,e9y,ea1,eag,eal],8,hint 0x1874e1c3060c1876eddbb3060c188508e1c3060c1876eddbb3060c18⟩,⟨0x9999999999999999,⟨0,by decide⟩,0x9888980098008000,[ee1,eeO,ef6,efe,efr],8,hint 0x1a6cd1a3060c1872e4d1a3060c188b14d1a3060c1872e4d1a3060c18⟩,⟨0xaaaaaaaaaaaaaaaa,⟨1,by decide⟩,0xaaa8aa00aa008000,[ee1,efX,ega,egp,egv],7,hint 0x1c70d1a3060c1862c58b13060c1881020403060c1862c58b13060c18⟩,⟨0xf00ff00ff00ff00f,⟨0,by decide⟩,0xf008f000f0008000,[efF,eho,eil,eip,eiq],6,hint 0x5a74e1c2e5cb9776eddbb2e5cb978d1a3462e5cb9776eddbb2e5cb97⟩]
def vxf:Array View:=#[⟨0xff00ff00ff00ff00,⟨8,by decide⟩,0xfe00fe00fe008000,[ega,ehx,eil,ej2,ej7],6,hint 0x50a142850a142862c58b162c58b18102040810204062c58b162c58b1⟩,⟨0xffff0000ffff0000,⟨16,by decide⟩,0xfee80000fe000000,[egp,ehC,eiu,ej2,ejM],7,hint 0x5ebd7af5ebd7af66cd9b366cd9b38f1e3c78f1e3c766cd9b366cd9b3⟩,⟨0xffff0000ffff,⟨0,by decide⟩,0xfe0000008000,[e2y,e2C,e2E,e2G,e2H],6,hint 0⟩,⟨0xffff0000ffff00,⟨8,by decide⟩,0xe8fe0000008000,[e5a,e5w,e5O,e5S,e5Y],8,hint 0⟩,⟨0xf0ff0f00f0ff0f0,⟨4,by decide⟩,0xe08f0000e008000,[e8X,e9B,ea4,eaf,ean],8,hint 0⟩,⟨0x3333333333333333,⟨0,by decide⟩,0x3220320032000000,[eby,ebY,ec6,ecc,ecf],7,hint 0⟩,⟨0x33333333cccccccc,⟨2,by decide⟩,0x32203200cc008000,[ebz,ebZ,ec7,ecd,ecf],8,hint 0⟩,⟨0x3333cccc3333cccc,⟨2,by decide⟩,0x3220cc0032008000,[ebC,ec1,ec9,ecc,ecg],8,hint 0⟩,⟨0x5555555555555555,⟨0,by decide⟩,0x5440540054000000,[ecs,ecC,ecG,ecO,ecR],7,hint 0⟩,⟨0x55555555aaaaaaaa,⟨1,by decide⟩,0x54405400aa008000,[ect,ecD,ecH,ecP,ecR],8,hint 0⟩,⟨0x5555aaaa5555aaaa,⟨1,by decide⟩,0x5440aa0054008000,[ecv,ecE,ecK,ecO,ecS],8,hint 0⟩,⟨0xa5a5a5a5a5a5a5a5,⟨0,by decide⟩,0xa4a0a400a4008000,[edF,efX,eg3,eg6,eg7],8,hint 0⟩,⟨0xaa55aa55aa55aa55,⟨0,by decide⟩,0xaa40aa00aa008000,[edQ,efJ,ega,egk,egl],6,hint 0⟩,⟨0xc3c3c3c3c3c3c3c3,⟨0,by decide⟩,0xc2c0c200c2008000,[edz,ehs,eht,ehu,ehv],8,hint 0⟩,⟨0xcccccccccccccccc,⟨2,by decide⟩,0xccc8cc00cc008000,[ee1,ehs,ehx,ehC,ehE],7,hint 0⟩,⟨0xf0f0f0f0f0f0f0f0,⟨4,by decide⟩,0xf0e0f000f0008000,[efX,ehs,eil,eiu,eiw],7,hint 0⟩]
def vxg:Array View:=#[⟨0xffff00000000ffff,⟨0,by decide⟩,0xfee8000000008000,[ego,ehB,eit,ej1,ejM],8,hint 0⟩,⟨0xffffffff00000000,⟨32,by decide⟩,0xfee8fe0000000000,[egv,ehE,eiw,ej7,ejM],7,hint 0⟩,⟨0xaf00afafafafaf,⟨0,by decide⟩,0xa80000ae008000,[e1C,e4E,e4R,e57,e5f,e5g],7,hint 0x1e60e183460d186860e183460d1862618986261898626189862618988e60e183460d188e60e183460d186261898626189862618986261898⟩,⟨0xb0b0b0bbbbbbbbb,⟨0,by decide⟩,0xa080a00ba008000,[e1F,e8a,e8V,e90,e91,e93],7,hint 0x2068e1a6868e1a3060c183060c1862c58b162c58b13060c183060c18810204081020403060c183060c1862c58b162c58b13060c183060c18⟩,⟨0xaf23af23af23af23,⟨0,by decide⟩,0xae20ae00ae008000,[eeh,efG,egj,egV,egY,egZ],7,hint 0x2270d1a6870d1a6670d1a6670d1a62c58b162c58b162c58b162c58b1810204081020408102040810204062c58b162c58b162c58b162c58b1⟩,⟨0xaf8caf8caf8caf8c,⟨2,by decide⟩,0xae88ae00ae008000,[ebJ,efK,egm,egV,eh1,eh3],7,hint 0x2470d1a6870d1a3060c183060c1862c58b162c58b13060c183060c18810204081020403060c183060c1862c58b162c58b13060c183060c18⟩,⟨0xafaf0000afafafaf,⟨0,by decide⟩,0xaea80000ae008000,[een,efO,egq,egN,eh5,eh9],7,hint 0x2670d1a6870d1a3060c183060c188e70d1a8e70d1a3060c183060c1862c58b162c58b13060c183060c1862c58b162c58b13060c183060c18⟩,⟨0xafaf2323afaf2323,⟨0,by decide⟩,0xaea82200ae000000,[eem,efP,egr,egO,eh9,eha],7,hint 0x28e263868d1a3466cd9b366cd9b362c58b162c58b162c58b162c58b1810204081020408102040810204062c58b162c58b162c58b162c58b1⟩,⟨0xafaf8c8cafaf8c8c,⟨2,by decide⟩,0xaea88c00ae008000,[ebM,efQ,egs,egP,eh9,ehb],7,hint 0x60c0d1a60c0d1a3060c183060c186ad5ab56ad5ab53060c183060c18891224489122443060c183060c186ad5ab56ad5ab53060c183060c18⟩,⟨0xafafaf00afafaf00,⟨8,by decide⟩,0xaea8ae00ae008000,[e5e,eeo,efR,egu,eh9,ehc],7,hint 0x2acce1c3468d1a68cce1c3468d1a62c58b162c58b162c58b162c58b1810204081020408102040810204062c58b162c58b162c58b162c58b1⟩,⟨0xafafaf00afafaf,⟨0,by decide⟩,0xa8ae0000008000,[e2A,e4F,e4T,e5b,e5e,e5h],7,hint 0⟩,⟨0x23232323afafafaf,⟨0,by decide⟩,0x22202200ae008000,[e17,ebd,ebA,ebK,ebN,ebO],7,hint 0⟩,⟨0x2323afaf2323afaf,⟨0,by decide⟩,0x2220ae0022008000,[e2f,ebf,ebD,ebL,ebM,ebP],7,hint 0⟩,⟨0xafafafaf0000afaf,⟨0,by decide⟩,0xaea8ae0000008000,[eeq,efT,egx,egR,eh5,ehd],7,hint 0⟩,⟨0xafafafaf23232323,⟨0,by decide⟩,0xaea8ae0022000000,[eep,efU,egy,egS,eh6,ehd],7,hint 0⟩,⟨0xafafafaf8c8c8c8c,⟨2,by decide⟩,0xaea8ae008c008000,[ebO,efV,egz,egT,eh7,ehd],7,hint 0⟩]
def vxh:Array View:=#[⟨0xafafafafaf00af00,⟨8,by decide⟩,0xaea8ae00ae008000,[e5g,eer,efW,egA,eh8,ehd],7,hint 0⟩,⟨0xafafafafafafafaf,⟨0,by decide⟩,0xaea8ae00ae008000,[ees,efX,egC,egV,eh9,ehd],9,hint 0x2c70d1a6870d1a3060c183060c1862c58b162c58b13060c183060c18810204081020403060c183060c1862c58b162c58b13060c183060c18⟩,⟨0xbbbbbbbbbbbbbbbb,⟨0,by decide⟩,0xbaa8ba00ba008000,[ee1,egC,ehf,ehg,ehi,ehk],9,hint 0⟩,⟨0xcfcfcfcfcfcfcfcf,⟨0,by decide⟩,0xcec8ce00ce008000,[eef,ehs,ehF,ehG,ehH,ehJ],9,hint 0⟩,⟨0xdddddddddddddddd,⟨0,by decide⟩,0xdcc8dc00dc008000,[ee1,ehF,ehK,ehL,ehO,ehP],9,hint 0⟩,⟨0xf3f3f3f3f3f3f3f3,⟨0,by decide⟩,0xf2e0f200f2008000,[efY,ehs,eix,eiD,eiE,eiF],9,hint 0⟩,⟨0xf5f5f5f5f5f5f5f5,⟨0,by decide⟩,0xf4e0f400f4008000,[efX,ehw,eix,eiG,eiH,eiI],9,hint 0⟩,⟨0xffffffffffffffff,⟨0,by decide⟩,0xfee8fe00fe008000,[egC,ehF,eix,eja,ejN,ejT],11,hint 0x4e74e1c3468d1a3060c183060c1862c58b162c58b13060c183060c18810204081020403060c183060c1862c58b162c58b13060c183060c18⟩]
def vxAt (i:Nat):View:=(if i<144 then (if i<64 then (if i<32 then (if i<16 then vx0.getD (i-0) ⟨0,0,0,[],0,fun _=>0⟩ else vx1.getD (i-16) ⟨0,0,0,[],0,fun _=>0⟩) else (if i<48 then vx2.getD (i-32) ⟨0,0,0,[],0,fun _=>0⟩ else vx3.getD (i-48) ⟨0,0,0,[],0,fun _=>0⟩)) else (if i<96 then (if i<80 then vx4.getD (i-64) ⟨0,0,0,[],0,fun _=>0⟩ else vx5.getD (i-80) ⟨0,0,0,[],0,fun _=>0⟩) else (if i<112 then vx6.getD (i-96) ⟨0,0,0,[],0,fun _=>0⟩ else (if i<128 then vx7.getD (i-112) ⟨0,0,0,[],0,fun _=>0⟩ else vx8.getD (i-128) ⟨0,0,0,[],0,fun _=>0⟩)))) else (if i<208 then (if i<176 then (if i<160 then vx9.getD (i-144) ⟨0,0,0,[],0,fun _=>0⟩ else vxa.getD (i-160) ⟨0,0,0,[],0,fun _=>0⟩) else (if i<192 then vxb.getD (i-176) ⟨0,0,0,[],0,fun _=>0⟩ else vxc.getD (i-192) ⟨0,0,0,[],0,fun _=>0⟩)) else (if i<240 then (if i<224 then vxd.getD (i-208) ⟨0,0,0,[],0,fun _=>0⟩ else vxe.getD (i-224) ⟨0,0,0,[],0,fun _=>0⟩) else (if i<256 then vxf.getD (i-240) ⟨0,0,0,[],0,fun _=>0⟩ else (if i<272 then vxg.getD (i-256) ⟨0,0,0,[],0,fun _=>0⟩ else vxh.getD (i-272) ⟨0,0,0,[],0,fun _=>0⟩)))))
def node := nxAt
def view := vxAt
def aliasValues (s : Nat) : Array Nat :=
  (List.ofFn (fun i : Fin 64 => (s >>> (6*i.val)) % 64)).toArray
end GroupMetadata
def viewsGet (i : Nat) : Option View :=
  if i<280 then some (GroupMetadata.view i) else none
def nodesGet (i : Nat) : Option Node :=
  if i<1091 then some (GroupMetadata.node i) else none
def fastViews : QFast.Table View := ⟨280,viewsGet⟩
def fastNodes : QFast.Table Node := ⟨1091,nodesGet⟩
def rootAliases (i : Nat) : Option (Nat × Array Nat) :=
  let w := GroupMetadata.alAt i
  if w % 512 = 0 then none else some ((w % 512)-1,GroupMetadata.aliasValues (w >>> 9))
end SignedProjection

namespace SignedProjection
namespace GGStock
abbrev work := RecipeCache.stockAtOK fastViews RecipeCache.Data.stockAt
theorem join {s a b : Nat} (x : QFast.passBlock work s a = true)
    (y : QFast.passBlock work (s+a) b = true) : QFast.passBlock work s (a+b) = true :=
  QFast.merge_blocks x y
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem ok : QFast.passBlock work 0 280 = true :=
  (@join 0 140 140 (@join 0 70 70 (@join 0 35 35 (@join 0 17 18 (by decide +kernel) (by decide +kernel)) (@join 35 17 18 (by decide +kernel) (by decide +kernel))) (@join 70 35 35 (@join 70 17 18 (by decide +kernel) (by decide +kernel)) (@join 105 17 18 (by decide +kernel) (by decide +kernel)))) (@join 140 70 70 (@join 140 35 35 (@join 140 17 18 (by decide +kernel) (by decide +kernel)) (@join 175 17 18 (by decide +kernel) (by decide +kernel))) (@join 210 35 35 (@join 210 17 18 (by decide +kernel) (by decide +kernel)) (@join 245 17 18 (by decide +kernel) (by decide +kernel)))))
end GGStock
namespace GGRoots
abbrev work := QFast.symCheckRoot rootAliases fastViews fastNodes
theorem join {s a b : Nat} (x : QFast.passBlock work s a = true)
    (y : QFast.passBlock work (s+a) b = true) : QFast.passBlock work s (a+b) = true :=
  QFast.merge_blocks x y
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem ok : QFast.passBlock work 0 280 = true :=
  (@join 0 140 140 (@join 0 70 70 (@join 0 35 35 (@join 0 17 18 (@join 0 8 9 (by decide +kernel) (by decide +kernel)) (@join 17 9 9 (by decide +kernel) (by decide +kernel))) (@join 35 17 18 (@join 35 8 9 (by decide +kernel) (by decide +kernel)) (@join 52 9 9 (by decide +kernel) (by decide +kernel)))) (@join 70 35 35 (@join 70 17 18 (@join 70 8 9 (by decide +kernel) (by decide +kernel)) (@join 87 9 9 (by decide +kernel) (by decide +kernel))) (@join 105 17 18 (@join 105 8 9 (by decide +kernel) (by decide +kernel)) (@join 122 9 9 (by decide +kernel) (by decide +kernel))))) (@join 140 70 70 (@join 140 35 35 (@join 140 17 18 (@join 140 8 9 (by decide +kernel) (by decide +kernel)) (@join 157 9 9 (by decide +kernel) (by decide +kernel))) (@join 175 17 18 (@join 175 8 9 (by decide +kernel) (by decide +kernel)) (@join 192 9 9 (by decide +kernel) (by decide +kernel)))) (@join 210 35 35 (@join 210 17 18 (@join 210 8 9 (by decide +kernel) (by decide +kernel)) (@join 227 9 9 (by decide +kernel) (by decide +kernel))) (@join 245 17 18 (@join 245 8 9 (by decide +kernel) (by decide +kernel)) (@join 262 9 9 (by decide +kernel) (by decide +kernel))))))
end GGRoots
namespace GGNodes
abbrev work := Grouped.nodeAt fastViews fastNodes RecipeCache.Data.table Grouped.packet
theorem join {s a b : Nat} (x : QFast.passBlock work s a = true) (y : QFast.passBlock work (s+a) b = true) : QFast.passBlock work s (a+b) = true := QFast.merge_blocks x y
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v0 : QFast.passBlock work 0 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v8 : QFast.passBlock work 8 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v17 : QFast.passBlock work 17 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v25 : QFast.passBlock work 25 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v34 : QFast.passBlock work 34 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v42 : QFast.passBlock work 42 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v51 : QFast.passBlock work 51 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v59 : QFast.passBlock work 59 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v68 : QFast.passBlock work 68 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v76 : QFast.passBlock work 76 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v85 : QFast.passBlock work 85 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v93 : QFast.passBlock work 93 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v102 : QFast.passBlock work 102 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v110 : QFast.passBlock work 110 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v119 : QFast.passBlock work 119 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v127 : QFast.passBlock work 127 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v136 : QFast.passBlock work 136 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v144 : QFast.passBlock work 144 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v153 : QFast.passBlock work 153 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v161 : QFast.passBlock work 161 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v170 : QFast.passBlock work 170 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v178 : QFast.passBlock work 178 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v187 : QFast.passBlock work 187 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v195 : QFast.passBlock work 195 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v204 : QFast.passBlock work 204 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v212 : QFast.passBlock work 212 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v221 : QFast.passBlock work 221 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v229 : QFast.passBlock work 229 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v238 : QFast.passBlock work 238 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v246 : QFast.passBlock work 246 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v255 : QFast.passBlock work 255 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v263 : QFast.passBlock work 263 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v272 : QFast.passBlock work 272 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v280 : QFast.passBlock work 280 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v289 : QFast.passBlock work 289 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v297 : QFast.passBlock work 297 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v306 : QFast.passBlock work 306 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v314 : QFast.passBlock work 314 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v323 : QFast.passBlock work 323 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v331 : QFast.passBlock work 331 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v340 : QFast.passBlock work 340 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v348 : QFast.passBlock work 348 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v357 : QFast.passBlock work 357 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v365 : QFast.passBlock work 365 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v374 : QFast.passBlock work 374 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v382 : QFast.passBlock work 382 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v391 : QFast.passBlock work 391 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v399 : QFast.passBlock work 399 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v408 : QFast.passBlock work 408 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v416 : QFast.passBlock work 416 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v425 : QFast.passBlock work 425 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v433 : QFast.passBlock work 433 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v442 : QFast.passBlock work 442 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v450 : QFast.passBlock work 450 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v459 : QFast.passBlock work 459 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v467 : QFast.passBlock work 467 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v476 : QFast.passBlock work 476 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v484 : QFast.passBlock work 484 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v493 : QFast.passBlock work 493 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v501 : QFast.passBlock work 501 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v510 : QFast.passBlock work 510 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v518 : QFast.passBlock work 518 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v527 : QFast.passBlock work 527 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v536 : QFast.passBlock work 536 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v545 : QFast.passBlock work 545 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v553 : QFast.passBlock work 553 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v562 : QFast.passBlock work 562 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v570 : QFast.passBlock work 570 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v579 : QFast.passBlock work 579 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v587 : QFast.passBlock work 587 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v596 : QFast.passBlock work 596 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v604 : QFast.passBlock work 604 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v613 : QFast.passBlock work 613 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v621 : QFast.passBlock work 621 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v630 : QFast.passBlock work 630 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v638 : QFast.passBlock work 638 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v647 : QFast.passBlock work 647 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v655 : QFast.passBlock work 655 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v664 : QFast.passBlock work 664 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v672 : QFast.passBlock work 672 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v681 : QFast.passBlock work 681 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v689 : QFast.passBlock work 689 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v698 : QFast.passBlock work 698 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v706 : QFast.passBlock work 706 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v715 : QFast.passBlock work 715 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v723 : QFast.passBlock work 723 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v732 : QFast.passBlock work 732 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v740 : QFast.passBlock work 740 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v749 : QFast.passBlock work 749 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v757 : QFast.passBlock work 757 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v766 : QFast.passBlock work 766 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v774 : QFast.passBlock work 774 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v783 : QFast.passBlock work 783 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v791 : QFast.passBlock work 791 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v800 : QFast.passBlock work 800 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v809 : QFast.passBlock work 809 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v818 : QFast.passBlock work 818 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v826 : QFast.passBlock work 826 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v835 : QFast.passBlock work 835 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v843 : QFast.passBlock work 843 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v852 : QFast.passBlock work 852 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v860 : QFast.passBlock work 860 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v869 : QFast.passBlock work 869 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v877 : QFast.passBlock work 877 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v886 : QFast.passBlock work 886 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v894 : QFast.passBlock work 894 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v903 : QFast.passBlock work 903 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v911 : QFast.passBlock work 911 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v920 : QFast.passBlock work 920 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v928 : QFast.passBlock work 928 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v937 : QFast.passBlock work 937 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v945 : QFast.passBlock work 945 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v954 : QFast.passBlock work 954 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v962 : QFast.passBlock work 962 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v971 : QFast.passBlock work 971 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v979 : QFast.passBlock work 979 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v988 : QFast.passBlock work 988 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v996 : QFast.passBlock work 996 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v1005 : QFast.passBlock work 1005 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v1013 : QFast.passBlock work 1013 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v1022 : QFast.passBlock work 1022 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v1030 : QFast.passBlock work 1030 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v1039 : QFast.passBlock work 1039 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v1047 : QFast.passBlock work 1047 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v1056 : QFast.passBlock work 1056 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v1064 : QFast.passBlock work 1064 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v1073 : QFast.passBlock work 1073 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem v1082 : QFast.passBlock work 1082 9 = true := by decide +kernel
theorem ok : QFast.passBlock work 0 1091 = true := (@join 0 545 546 (@join 0 272 273 (@join 0 136 136 (@join 0 68 68 (@join 0 34 34 (@join 0 17 17 (@join 0 8 9 v0 v8) (@join 17 8 9 v17 v25)) (@join 34 17 17 (@join 34 8 9 v34 v42) (@join 51 8 9 v51 v59))) (@join 68 34 34 (@join 68 17 17 (@join 68 8 9 v68 v76) (@join 85 8 9 v85 v93)) (@join 102 17 17 (@join 102 8 9 v102 v110) (@join 119 8 9 v119 v127)))) (@join 136 68 68 (@join 136 34 34 (@join 136 17 17 (@join 136 8 9 v136 v144) (@join 153 8 9 v153 v161)) (@join 170 17 17 (@join 170 8 9 v170 v178) (@join 187 8 9 v187 v195))) (@join 204 34 34 (@join 204 17 17 (@join 204 8 9 v204 v212) (@join 221 8 9 v221 v229)) (@join 238 17 17 (@join 238 8 9 v238 v246) (@join 255 8 9 v255 v263))))) (@join 272 136 137 (@join 272 68 68 (@join 272 34 34 (@join 272 17 17 (@join 272 8 9 v272 v280) (@join 289 8 9 v289 v297)) (@join 306 17 17 (@join 306 8 9 v306 v314) (@join 323 8 9 v323 v331))) (@join 340 34 34 (@join 340 17 17 (@join 340 8 9 v340 v348) (@join 357 8 9 v357 v365)) (@join 374 17 17 (@join 374 8 9 v374 v382) (@join 391 8 9 v391 v399)))) (@join 408 68 69 (@join 408 34 34 (@join 408 17 17 (@join 408 8 9 v408 v416) (@join 425 8 9 v425 v433)) (@join 442 17 17 (@join 442 8 9 v442 v450) (@join 459 8 9 v459 v467))) (@join 476 34 35 (@join 476 17 17 (@join 476 8 9 v476 v484) (@join 493 8 9 v493 v501)) (@join 510 17 18 (@join 510 8 9 v510 v518) (@join 527 9 9 v527 v536)))))) (@join 545 273 273 (@join 545 136 137 (@join 545 68 68 (@join 545 34 34 (@join 545 17 17 (@join 545 8 9 v545 v553) (@join 562 8 9 v562 v570)) (@join 579 17 17 (@join 579 8 9 v579 v587) (@join 596 8 9 v596 v604))) (@join 613 34 34 (@join 613 17 17 (@join 613 8 9 v613 v621) (@join 630 8 9 v630 v638)) (@join 647 17 17 (@join 647 8 9 v647 v655) (@join 664 8 9 v664 v672)))) (@join 681 68 69 (@join 681 34 34 (@join 681 17 17 (@join 681 8 9 v681 v689) (@join 698 8 9 v698 v706)) (@join 715 17 17 (@join 715 8 9 v715 v723) (@join 732 8 9 v732 v740))) (@join 749 34 35 (@join 749 17 17 (@join 749 8 9 v749 v757) (@join 766 8 9 v766 v774)) (@join 783 17 18 (@join 783 8 9 v783 v791) (@join 800 9 9 v800 v809))))) (@join 818 136 137 (@join 818 68 68 (@join 818 34 34 (@join 818 17 17 (@join 818 8 9 v818 v826) (@join 835 8 9 v835 v843)) (@join 852 17 17 (@join 852 8 9 v852 v860) (@join 869 8 9 v869 v877))) (@join 886 34 34 (@join 886 17 17 (@join 886 8 9 v886 v894) (@join 903 8 9 v903 v911)) (@join 920 17 17 (@join 920 8 9 v920 v928) (@join 937 8 9 v937 v945)))) (@join 954 68 69 (@join 954 34 34 (@join 954 17 17 (@join 954 8 9 v954 v962) (@join 971 8 9 v971 v979)) (@join 988 17 17 (@join 988 8 9 v988 v996) (@join 1005 8 9 v1005 v1013))) (@join 1022 34 35 (@join 1022 17 17 (@join 1022 8 9 v1022 v1030) (@join 1039 8 9 v1039 v1047)) (@join 1056 17 18 (@join 1056 8 9 v1056 v1064) (@join 1073 9 9 v1073 v1082)))))))
end GGNodes
end SignedProjection

namespace SignedProjection
def bMatches (z : Option View) : Bool :=
  match z with
  | none => false
  | some v => vg v == (0xfee8fe00fe008000 : Word) && vk v == 11 && (vs v).toFinset == Direct64.cols.toFinset

theorem rootNegative : ¬ CoreSigned.build signedOps (0xfee8fe00fe008000 : BitVec 64) 11 Direct64.cols.toFinset := by
  have shape : bMatches (QFast.get fastViews 279) = true := by decide +kernel
  cases ev : QFast.get fastViews 279 with
  | none => simp [ev, bMatches] at shape
  | some v =>
    have valid := Grouped.certifiedGroup rootAliases fastViews fastNodes RecipeCache.Data.table Grouped.packet (RecipeCache.Data.valid GGStock.ok) GGRoots.ok GGNodes.ok ev
    simp only [ev,bMatches,Bool.and_eq_true,beq_iff_eq] at shape
    change ¬ CoreSigned.build signedOps (vg v) (vk v) (vs v).toFinset at valid
    rwa [shape.1.1,shape.1.2,shape.2] at valid
end SignedProjection
end PEqualNP.Outside.L_meta_12138_aux

open PEqualNP.Outside.L_meta_12138_aux in
theorem PEqualNP.Outside.L_meta_12138 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276682240 * 2 ^ 32 + 4261445632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276682240 * 2 ^ 32 + 4261445632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  LowerSymSix.finish SignedProjection.rootNegative
