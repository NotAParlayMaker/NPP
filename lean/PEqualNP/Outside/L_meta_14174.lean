import PEqualNP.MetaComplexity.Helpers.ForestElim

namespace PEqualNP.Outside.L_meta_14174

namespace CoreSigned

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

def F (x : Fin 6 → Bool) : Bool := Nat.testBit (4278119584 * 2 ^ 32 + 4278119584) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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

namespace Direct64
open PEqualNP.CircuitLowerBounds SignedProjection
abbrev W := BitVec 64
abbrev basicOps (a b : W) := signedOps a b
abbrev goal : W := ~~~0xfefeeca0fefeeca0
open CoreSigned (build)
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

theorem sample64 : ∀ k : Fin 64, CoreSigned.F (fun i => (cols.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
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

theorem low (reject : ¬ build basicOps (0xfefeeca0fefeeca0 : W) 6 cols.toFinset)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = CoreSigned.F x) : 6 < binaryCost gs := by
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

namespace SignedProjection.Fast
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
      | some v => cutOK v g k ws (val/1024)
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
    exact cutOK_sound (known _ lt _ hv) ok
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

end SignedProjection.Fast

namespace SevenGlue
open SignedProjection

def rootMatches (item : Option View) : Bool :=
  match item with
  | none => false
  | some v => vg v == (0xfefeeca0fefeeca0 : BitVec 64) && vk v == 6 &&
      (vs v).toFinset == Direct64.cols.toFinset

theorem from_blocks (views : Fast.Table View) (nodes : Fast.Table Node)
    (roots : Fast.passBlock (Fast.checkRootAt views nodes) 0 views.1 = true)
    (states : Fast.passBlock (Fast.checkNodeAt views nodes) 0 nodes.1 = true)
    (which : Nat) (shape : rootMatches (Fast.get views which) = true) :
    ¬ CoreSigned.build SignedProjection.signedOps (0xfefeeca0fefeeca0 : BitVec 64) 6 Direct64.cols.toFinset := by
  cases ev : Fast.get views which with
  | none => simp [rootMatches,ev] at shape
  | some v =>
    have valid := Fast.certified_view views nodes roots states ev
    simp only [rootMatches,ev,Bool.and_eq_true,beq_iff_eq] at shape
    rcases shape with ⟨⟨goal,budget⟩,stock⟩
    unfold ViewOK at valid
    rw [goal,budget,stock] at valid
    exact valid
end SevenGlue

namespace SignedProjection
def labelsBlock0 : Array Nat := #[
  1,
  5,
  9,
  13,
  17,
  20,
  21,
  24,
  25,
  28,
  29,
  33,
  36,
  37,
  40,
  41
]
def labelsBlock1 : Array Nat := #[
  44,
  45,
  49,
  52,
  53,
  56,
  57,
  61,
  65,
  68,
  69,
  72,
  73,
  76,
  77,
  80
]
def labelsBlock2 : Array Nat := #[
  81,
  85,
  88,
  89,
  93,
  97,
  100,
  101,
  105,
  109,
  112,
  113,
  117,
  121,
  125,
  129
]
def labelsBlock3 : Array Nat := #[
  133,
  137,
  141,
  145,
  149,
  153,
  157,
  161,
  165,
  169,
  173,
  177,
  181,
  185,
  189,
  193
]
def labelsBlock4 : Array Nat := #[
  197,
  201,
  205,
  209,
  213,
  217,
  221,
  225,
  229,
  233,
  237,
  241,
  245,
  249,
  253,
  257
]
def labelsBlock5 : Array Nat := #[
  261,
  265,
  269,
  273,
  276,
  277,
  284,
  300,
  308,
  324,
  332,
  356,
  532,
  540,
  552,
  556
]
def labelsBlock6 : Array Nat := #[
  568,
  580,
  584,
  592,
  600,
  788,
  796,
  808,
  812,
  824,
  836,
  840,
  844,
  872,
  1044,
  1052
]
def labelsBlock7 : Array Nat := #[
  1076,
  1080,
  1104,
  1112,
  1556,
  1564,
  1576,
  1580,
  1592,
  1608,
  1616,
  1624,
  1640,
  2068,
  2076,
  2088
]
def labelsBlock8 : Array Nat := #[
  2092,
  2104,
  2116,
  2124,
  2128,
  2132,
  2136,
  2148,
  2152,
  2160,
  2324,
  2332,
  2344,
  2348,
  2356,
  2372
]
def labelsBlock9 : Array Nat := #[
  2388,
  2404,
  2584,
  2596,
  3092,
  3100,
  3112,
  3124,
  3128,
  3152,
  3156,
  3184,
  4098,
  4102,
  4106,
  4110
]
def labelsBlock10 : Array Nat := #[
  4114,
  4118,
  4122,
  4126,
  4130,
  4134,
  4136,
  4138,
  4140,
  4142,
  4146,
  4150,
  4152,
  4154,
  4156,
  4158
]
def labelsBlock11 : Array Nat := #[
  4162,
  4164,
  4166,
  4168,
  4170,
  4172,
  4174,
  4176,
  4178,
  4182,
  4184,
  4186,
  4190,
  4194,
  4196,
  4198
]
def labelsBlock12 : Array Nat := #[
  4202,
  4206,
  4208,
  4210,
  4214,
  4218,
  4222,
  4226,
  4230,
  4234,
  6184,
  6188,
  6200,
  6212,
  6220,
  6224
]
def labelsBlock13 : Array Nat := #[
  6228,
  6232,
  6244,
  6248,
  6256,
  5308510,
  5378142
]
def labelsGet (i : Nat) : Option Nat :=
  if i < 112 then
    if i < 48 then
      if i < 16 then
        labelsBlock0[(i - 0)]?
      else
        if i < 32 then
          labelsBlock1[(i - 16)]?
        else
          labelsBlock2[(i - 32)]?
    else
      if i < 80 then
        if i < 64 then
          labelsBlock3[(i - 48)]?
        else
          labelsBlock4[(i - 64)]?
      else
        if i < 96 then
          labelsBlock5[(i - 80)]?
        else
          labelsBlock6[(i - 96)]?
  else
    if i < 160 then
      if i < 128 then
        labelsBlock7[(i - 112)]?
      else
        if i < 144 then
          labelsBlock8[(i - 128)]?
        else
          labelsBlock9[(i - 144)]?
    else
      if i < 192 then
        if i < 176 then
          labelsBlock10[(i - 160)]?
        else
          labelsBlock11[(i - 176)]?
      else
        if i < 208 then
          labelsBlock12[(i - 192)]?
        else
          labelsBlock13[(i - 208)]?
def hints (enc i : Nat) : Nat := (labelsGet ((enc >>> (i * 8)) % 256)).getD 0
def viewsBlock0 : Array View := #[
  ⟨0x660,⟨5,by decide⟩,0x240,[0x440, 0x600],2,hints 0x55070c07⟩,
  ⟨0x1428,⟨3,by decide⟩,0x420,[0x1020, 0x1400],2,hints 0x52050e05⟩,
  ⟨0x1020408,⟨3,by decide⟩,0x20400,[0x1000400, 0x1020000],2,hints 0x510e190e⟩,
  ⟨0x1100440,⟨6,by decide⟩,0x100400,[0x1000400, 0x1100000],2,hints 0x530e1f0e⟩,
  ⟨0xff0,⟨4,by decide⟩,0xca0,[0xaa0, 0xcc0, 0xf00],2,hints 0x9c057f0576050e05⟩,
  ⟨0x55aa,⟨1,by decide⟩,0x44a0,[0x4488, 0x50a0, 0x5500],2,hints 0x9d7f0505670e0505⟩,
  ⟨0x330033,⟨0,by decide⟩,0x320020,[0x220022, 0x300030, 0x330000],3,hints 0x4f6e540559191f05⟩,
  ⟨0x3300cc,⟨2,by decide⟩,0x320080,[0x220088, 0x3000c0, 0x330000],3,hints 0x4d7566096a191f09⟩,
  ⟨0x333300,⟨8,by decide⟩,0x322000,[0x222200, 0x303000, 0x330000],3,hints 0x46978e138f191f13⟩,
  ⟨0x990099,⟨0,by decide⟩,0x980080,[0x880088, 0x900090, 0x990000],3,hints 0x506f66096c1d1f09⟩,
  ⟨0xc300c3,⟨0,by decide⟩,0xc20080,[0x820082, 0xc000c0, 0xc30000],3,hints 0x4975560959192209⟩,
  ⟨0x3030c0c,⟨2,by decide⟩,0x2020c00,[0x2020808, 0x3000c00, 0x3030000],2,hints 0x9eb10e0e6a190e0e⟩,
  ⟨0x3300330,⟨4,by decide⟩,0x2300020,[0x2200220, 0x3000300, 0x3300000],3,hints 0x4e058a051f051f05⟩,
  ⟨0x3300cc0,⟨6,by decide⟩,0x2300c80,[0x2200880, 0x3000c00, 0x3300000],3,hints 0x9f090e091f090e09⟩,
  ⟨0x3c003c0,⟨6,by decide⟩,0x2c00080,[0x2800280, 0x3000300, 0x3c00000],3,hints 0x47098b0922092209⟩,
  ⟨0x50a050a,⟨1,by decide⟩,0x40a0400,[0x4080408, 0x5000500, 0x50a0000],2,hints 0x9e7f670e1919190e⟩
]
def viewsBlock1 : Array View := #[
  ⟨0x5500550,⟨4,by decide⟩,0x4500400,[0x4400440, 0x5000500, 0x5500000],2,hints 0x9f7f760e1f1f1f0e⟩,
  ⟨0xa050a05,⟨0,by decide⟩,0xa040800,[0x8040804, 0xa000a00, 0xa050000],3,hints 0x4b8d5f10621b2610⟩,
  ⟨0x11114444,⟨2,by decide⟩,0x10104400,[0x10104040, 0x11004400, 0x11110000],2,hints 0x9fb70e0e7a1f0e0e⟩,
  ⟨0x11221122,⟨1,by decide⟩,0x10220020,[0x10201020, 0x11001100, 0x11220000],3,hints 0x4805940519051905⟩,
  ⟨0x11224488,⟨3,by decide⟩,0x10224480,[0x10204080, 0x11004400, 0x11220000],3,hints 0x9e090e0919090e09⟩,
  ⟨0x11881188,⟨3,by decide⟩,0x10880080,[0x10801080, 0x11001100, 0x11880000],3,hints 0x4c0995091d091d09⟩,
  ⟨0x50055005,⟨0,by decide⟩,0x50044000,[0x40044004, 0x50005000, 0x50050000],3,hints 0x4a986015621b2a15⟩,
  ⟨0xff00ff,⟨0,by decide⟩,0xfe00a0,[0xaa00aa, 0xcc00cc, 0xf000f0, 0xff0000],4,hints 0xa26eb36e5405540559191b191f051b05⟩,
  ⟨0xffff00,⟨8,by decide⟩,0xfeec00,[0xaaaa00, 0xcccc00, 0xf0f000, 0xff0000],4,hints 0xa4970e0e8e130e0e8f190e0e1f130e0e⟩,
  ⟨0xf0f0f0f,⟨0,by decide⟩,0xe0e0c00,[0xa0a0a0a, 0xc0c0c0c, 0xf000f00, 0xf0f0000],3,hints 0xb2b17f7f5e5e0e0e59191b1959190e0e⟩,
  ⟨0xff00ff0,⟨4,by decide⟩,0xef00ca0,[0xaa00aa0, 0xcc00cc0, 0xf000f00, 0xff00000],5,hints 0x37057f0576050e051f051f051f050e05⟩,
  ⟨0x33333333,⟨0,by decide⟩,0x32322020,[0x22222222, 0x30303030, 0x33003300, 0x33330000],3,hints 0xa26e5405a26e540559191f0559191f05⟩,
  ⟨0x3333cccc,⟨2,by decide⟩,0x3232cc80,[0x22228888, 0x3030c0c0, 0x3300cc00, 0x33330000],5,hints 0x277566090e0e0e096a191f090e0e0e09⟩,
  ⟨0x55555555,⟨0,by decide⟩,0x54544400,[0x44444444, 0x50505050, 0x55005500, 0x55550000],3,hints 0xbb7fb77f5e0e5e0e621b1f1b5e0e1f0e⟩,
  ⟨0x55aa55aa,⟨1,by decide⟩,0x54aa44a0,[0x44884488, 0x50a050a0, 0x55005500, 0x55aa0000],5,hints 0xf7f0505670e050519190505190e0505⟩,
  ⟨0x99999999,⟨0,by decide⟩,0x98988880,[0x88888888, 0x90909090, 0x99009900, 0x99990000],4,hints 0xa56f6609681066096c1d1f0968101f09⟩
]
def viewsBlock2 : Array View := #[
  ⟨0xc3c3c3c3,⟨0,by decide⟩,0xc2c2c080,[0x82828282, 0xc0c0c0c0, 0xc300c300, 0xc3c30000],4,hints 0xa7755609787515095919220959191509⟩,
  ⟨0xcc33cc33,⟨0,by decide⟩,0xcc32cc20,[0x88228822, 0xc030c030, 0xcc00cc00, 0xcc330000],4,hints 0xa26e54050e0e0e0559191f050e0e0e05⟩,
  ⟨0xffffffff,⟨0,by decide⟩,0xfefeeca0,[0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],6,hints 0x6e7f6e540554055e5e0e0e54050e0559191b191f051b0559190e0e1f050e05⟩,
  ⟨0xffffffffffffffff,⟨0,by decide⟩,0xfefeeca0fefeeca0,[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],6,hints 0xc96e7f6e540554055e5e0e0e54050e0559191b191f051b0559190e0e1f050e05c96e7f6e540554055e5e0e0e54050e0559191b191f051b0559190e0e1f050e05⟩
]
def viewsGet (i : Nat) : Option View :=
  if i < 16 then
    viewsBlock0[(i - 0)]?
  else
    if i < 32 then
      viewsBlock1[(i - 16)]?
    else
      viewsBlock2[(i - 32)]?
def nodesBlock0 : Array Node := #[
  ⟨34,6,[0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hints 0xbc5e915bbcbc5959bcbd918fbc5e59590d54721fbfb7591f0ab77272bf545954c0547854c08e5e58c08e7876c0545e54c37f621bc3b3591bc3b36262c37f5959bcb35e0ebc7fc80ebc7f5e5ebcb3bcb3c77f6656c798545408986665bf7f5454066e5919c4b1621903b15959c46e6262c56e685fc5975e5ec5976867c56e5e5ebfb15405c46eb705026e5454bfb1b7b1c66e8d6ec6757f6f01758d74c16e7f6e⟩,
  ⟨34,5,[0xaaaaaaaa, 0xcccccccc, 0xeeeeeeee, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hints 0x5b598f591f1f725454587654597259725ec55ebc54b754b75a59625957575ed5565465547f7f596259625f5e675e545d54b76e6e8d7574⟩,
  ⟨34,5,[0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xfafafafa, 0xff00ff00, 0xffff0000],hints 0x5b598f5959625962685e685e5459725454587854b7541b1b62590e0e5eb37f8d8d7f5654655459625962685e685eb16e546ebf6e6f746e⟩,
  ⟨34,5,[0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000, 0xffffaaaa],hints 0x62595e68685e5b598f59045454bf5459b754545876547f8d8d7f5a596a590e0e5eb3565465546e6e59b16b685e685e54b754b18d7f8d7f⟩,
  ⟨34,4,[0xf0f0a0a, 0xaaaaaaaa, 0xcccccccc, 0xff00ff00, 0xffff0000],hints 0x2a1f841f221f631f0e0e5eb3051f59050513680505095c05541f591f545e585454655654b1055405⟩,
  ⟨34,5,[0x55550000, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hints 0x5b598f595459b754545876545a596a590e0e5eb35654655419596e5f5e675e050554b76e6f746e6259bc5ec55eb754b754b37fb37fb16e⟩,
  ⟨34,5,[0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xfcfcfcfc, 0xff00ff00, 0xffff0000],hints 0x5b598f59625962595ec05ebc64597259605e765e5454625962595e715ed67f7f669865191959625f5e675eb16e6eb15d5d66b16e6f746e⟩,
  ⟨34,5,[0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000, 0xfffff0f0],hints 0x59595e78785e5e72995e545472b779785e785e7f98987f73727a720e0e5eb37f98987f0b6e6ec46e72b16e5f5e675eb16e6eb16e6f746e⟩,
  ⟨34,4,[0x55555050, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hints 0x2619821905197205051378051d1961190e0e5eb309055c05621972196e5e705eb1056e056e746f6e⟩,
  ⟨34,5,[0xf0f0000, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hints 0x5e72995e1f72545458765473727a720e0e5eb3565465546e72b16e5f5e675e050554b16e6f746e5959bc5ec05eb754b37fb37fb16eb16e⟩,
  ⟨30,5,[0x44884488, 0x50a050a0, 0x55005500, 0x55aa0000],hints 0xa1679b6724cd191923cd9b82a1671919a1059b05afd4191921d49b9ba10519051e059405afd467671cd4947daf056705b67f6c1db6d31919b6d36c6ab67f1919b611670eb67f940eb67f6767b6b69494b67f6609b6980505b6986665b67f0505⟩,
  ⟨30,4,[0x11001100, 0x50a050a0, 0x55005500, 0x55aa0000],hints 0xe9b0e181919179b9b0e190e059b05d41919d49b9b051905051405d40e0ed412d4050e057f9b7fd31919d39b887f1919b6b6947f0e0e7fd47f98050598d4817f0505⟩,
  ⟨30,3,[0x11001100, 0x50a050a0, 0x55a055a0, 0x55aa0000],hints 0xe199b0e89199b1905057f198819cd0e7f947d7d⟩,
  ⟨30,3,[0x5000500, 0x11001100, 0x50a050a0, 0x55aa0000],hints 0x5199b057f1988197f0594050e19160ed4050e947f0e⟩,
  ⟨30,2,[0x11001100, 0x50a050a0, 0x55aa0500],hints 0x50e8905940e7f0e7f058505⟩,
  ⟨30,3,[0x11001100, 0x50a050a0, 0x55aa0000, 0x55aa5500],hints 0x190e050ed40505899b05940e7fca827f7f058105⟩
]
def nodesBlock1 : Array Node := #[
  ⟨30,3,[0x5500, 0x11001100, 0x50a050a0, 0x55aa0000],hints 0x519d4057f19cd197f0581059b0e0e051a050e947f0e⟩,
  ⟨30,2,[0x11001100, 0x50a055a0, 0x55aa0000],hints 0x51989057d198519cd057d05⟩,
  ⟨30,4,[0x44884488, 0x50a050a0, 0x55005500, 0x55a055a0, 0x55aa0000],hints 0x9b199b1994199a19676789199b19050594d47d1d196a19b97f7fb6127f7f947f81967f⟩,
  ⟨30,4,[0x5000500, 0x44884488, 0x50a050a0, 0x55005500, 0x55aa0000],hints 0x94199a1905199b056994051d196a19147f7f9409056505a11920196767d4057f987f98⟩,
  ⟨30,3,[0x44884488, 0x50a050a0, 0x55005500, 0x55aa0500],hints 0x6719821905198905056985051d196a19167f7f8209056505⟩,
  ⟨30,4,[0x44884488, 0x50a050a0, 0x55005500, 0x55aa0000, 0x55aa50a0],hints 0x19196794946767cd9a6705059bd4a1946794677f98987f7f9bd37f0e0e67947f98987f⟩,
  ⟨30,4,[0x44884488, 0x50a050a0, 0x55005500, 0x55aa0000, 0x55aa5500],hints 0x191967679bcd8205d4d40505899b0505cdd005b87f7fb67f88ca7f177f7fcd09056505⟩,
  ⟨30,4,[0x5500, 0x44884488, 0x50a050a0, 0x55005500, 0x55aa0000],hints 0x6dcd190519d40505cdd0051d196a19187f7fcd090565059b196767af0525057fd37fd3⟩,
  ⟨30,3,[0x44884488, 0x50a055a0, 0x55005500, 0x55aa0000],hints 0x6d1985190519890505677d051d196a191a7d7e7d09056505⟩,
  ⟨28,5,[0x22228888, 0x3030c0c0, 0x3300cc00, 0x33330000],hints 0xa30eca0ea3a36a6aa336caa6a30e6a0e34667a1fa9b76a1f30b77a7aa9666a66a3667815a3d40e0ea3d47876a3660e0e2e756a19b4b17a1929b16a6ab4757a75a3756810a3d20e0ea3d26867a3750e0ea9b16609b475b70928756666a9b1b7b1⟩,
  ⟨28,4,[0x22228888, 0x3030c0c0, 0x3232c8c8, 0x3300cc00, 0x33330000],hints 0xe6aa60e6aca6aca680e680e666a7a66660e780eb7666a7a6a75680e680eb1756675a9⟩,
  ⟨28,4,[0x22228888, 0x3030c0c0, 0x3300cc00, 0x33330000, 0x33338888],hints 0x7a6a0e68680e0e6a2d0e2b6666a9666ab766150e760e75756ab1cb680e680e66b766b1⟩,
  ⟨28,3,[0x3030808, 0x22228888, 0x3300cc00, 0x33330000],hints 0xe1f2c0e091f6a09090e6809661f6a1f660e680eb1096609⟩,
  ⟨28,2,[0x3030808, 0x22228888, 0x3333cc00],hints 0x90e6809660e680ea6096609⟩,
  ⟨28,3,[0x22228888, 0x3030c0c0, 0x33338888, 0x3333cc00],hints 0x680e680e150e760e2c6666a6680e680e757566ae66a8⟩,
  ⟨28,4,[0x11110000, 0x22228888, 0x3030c0c0, 0x3300cc00, 0x33330000],hints 0xe6a2f0e666ab766150e760e196a75100e670e090966b77a6aa30eb80eb766b766b175⟩
]
def nodesBlock2 : Array Node := #[
  ⟨28,3,[0x11110000, 0x22228888, 0x3030c0c0, 0x3333cc00],hints 0x150e760e100e670e090966b77a0ea666ac66a875⟩,
  ⟨28,4,[0x22228888, 0x3030c0c0, 0x3300cc00, 0x33330000, 0x3333c0c0],hints 0x6a6a0e78780e0e7a330e66667ab7cc780e780e317575b4757ab175100e670eb17575b1⟩,
  ⟨28,3,[0x11114040, 0x3030c0c0, 0x3300cc00, 0x33330000],hints 0xe19320e09197a09090e780975197a19750e780eb1097509⟩,
  ⟨28,2,[0x11114040, 0x3030c0c0, 0x3333cc00],hints 0x90e7809750e780ea6097509⟩,
  ⟨28,3,[0x22228888, 0x3030c0c0, 0x3333c0c0, 0x3333cc00],hints 0x6a0e780e780e780e6666100e670e327575a6ae7575ac⟩,
  ⟨28,4,[0x3030000, 0x22228888, 0x3030c0c0, 0x3300cc00, 0x33330000],hints 0xe7a350e1f7a66150e760e757ab175100e670e090966b16a6aa30eab0eb766b175b175⟩,
  ⟨28,3,[0x3030000, 0x22228888, 0x3030c0c0, 0x3333cc00],hints 0x150e760e100e670e090966b16a0eac66a675a875⟩,
  ⟨28,4,[0x22228888, 0x3030c0c0, 0x33330000, 0x3333cc00],hints 0xa3a36aa60e0e667815b70e0eb77876660e0e663566b7a6a6b733ac66a666756810b10e0eb16867750e0e752f75b1a6a6b12da875a675b1660975b709756666b1b7b1⟩,
  ⟨26,5,[0xaa00aa0, 0xcc00cc0, 0xf000f00, 0xff00000],hints 0xa076917644cf1f1f43cf9184a0761f1faa7f7b22aad31f1faad37b7aaa7f1f1faa3f760eaa7f8a0eaa7f7676aaaa8a8aa0059105b0d21f1f3ed29191a0051f053a058a05b0d2767638d28a7db0057605aa058d05aa757f09aa758d74aa057f05⟩,
  ⟨26,4,[0xaa00aa0, 0xcc00cc0, 0xf000f00, 0xfa00fa0, 0xff00000],hints 0x911f911f8a1f901f7676221f7a1fad7f7faa397f7f8a871f911f05058ad27d807f8c7f⟩,
  ⟨26,3,[0x3000300, 0xaa00aa0, 0xfa00fa0, 0xff00000],hints 0xe1f910e871f911f05057f1f881fcf0e7f8a7d7d⟩,
  ⟨26,4,[0x5000500, 0xaa00aa0, 0xcc00cc0, 0xf000f00, 0xff00000],hints 0x8a1f901f221f7a1f3d7f7f8a051f9105778a0505097405a01f3b1f76767f8d7f8dd205⟩,
  ⟨26,3,[0xaa00aa0, 0xcc00cc0, 0xf000f00, 0xff00500],hints 0x761f841f221f7a1f3c7f7f84051f87050577850505097405⟩,
  ⟨26,2,[0x3000300, 0xaa00aa0, 0xff00500],hints 0x50e87058a0e7f0e7f058505⟩,
  ⟨26,3,[0x3000300, 0x5000500, 0xaa00aa0, 0xff00000],hints 0x51f91050e1f3c0ed2057f1f881f7f058a058a0e7f0e⟩,
  ⟨26,4,[0xaa00aa0, 0xcc00cc0, 0xf000f00, 0xff00000, 0xff00aa0],hints 0x1f1f768a8a7676cf90767f8d8d7f7f91d37f0e0e768a050591d2a08a768a768d7f8d7f⟩
]
def nodesBlock3 : Array Node := #[
  ⟨26,4,[0x3000300, 0xaa00aa0, 0xf000f00, 0xff00000],hints 0xe910e411f1f4091910e1f0e059105d21f1fd29191051f05053d05d20e0ed239d2050e057f917fd31f1fd391887f1f1faaaa8a7f0e0e7fd27f8d05058dd2807f0505⟩,
  ⟨26,3,[0x3000300, 0xaa00aa0, 0xff00000, 0xff00f00],hints 0x1f0e050ed205058791058a0e7fca847f7f058005⟩,
  ⟨26,3,[0xf00, 0x3000300, 0xaa00aa0, 0xff00000],hints 0x51fd2057f1fcf1f7f058005910e0e0542050e8a7f0e⟩,
  ⟨26,2,[0x3000300, 0xaa00fa0, 0xff00000],hints 0x51f87057d1f851fcf057d05⟩,
  ⟨26,4,[0xaa00aa0, 0xcc00cc0, 0xf000f00, 0xff00000, 0xff00f00],hints 0x1f1f767691cf84ab7f7faa7f88ca7f407f7fcf05d2d2050587910505cfd00505097405⟩,
  ⟨26,4,[0xf00, 0xaa00aa0, 0xcc00cc0, 0xf000f00, 0xff00000],hints 0x7ccf1f221f7a1f417f7fcf051fd20505cfd00505097405911f76767fd37fd3b0054505⟩,
  ⟨26,3,[0xaa00fa0, 0xcc00cc0, 0xf000f00, 0xff00000],hints 0x7c1f851f221f7a1f427d7e7d051f870505767d0505097405⟩,
  ⟨8,3,[0x222200, 0x303000, 0x330000],hints 0x8e991fb78f1fb799998e8f8e978f19b19919b18f8f979997b18e1397b713978e8eb1b7b1⟩,
  ⟨14,3,[0x2800280, 0x3000300, 0x3c00000],hints 0x8b918bd12222d191868b2222099109d22222d29191092209098b09d2d1d1d28b7e09d109⟩,
  ⟨19,3,[0x10201020, 0x11001100, 0x11220000],hints 0x949b94cd1919cd9b82941919059b05d41919d49b9b051905059405d4cdcdd4947d05cd05⟩,
  ⟨10,3,[0x820082, 0xc000c0, 0xc30000],hints 0x567b22ba5922ba7b7b565956755919b17b19b15959757b75b1560975ba09755656b1bab1⟩,
  ⟨22,3,[0x40044004, 0x50005000, 0x50050000],hints 0x609b2ac2622ac29b9b60626098621bb39b1bb36262989b98b3601598c215986060b3c2b3⟩,
  ⟨17,3,[0x8040804, 0xa000a00, 0xa050000],hints 0x5f9126be6226be91915f625f8d621bb3911bb362628d918db35f108dbe108d5f5fb3beb3⟩,
  ⟨21,3,[0x10801080, 0x11001100, 0x11880000],hints 0x959b95ce1d1dce9b83951d1d099b09d41d1dd49b9b091d09099509d4ceced4957e09ce09⟩,
  ⟨7,3,[0x220088, 0x3000c0, 0x330000],hints 0x667a1fb76a1fb77a7a666a66756a19b17a19b16a6a757a75b1660975b709756666b1b7b1⟩,
  ⟨12,3,[0x2200220, 0x3000300, 0x3300000],hints 0x8a918acf1f1fcf91848a1f1f059105d21f1fd29191051f05058a05d2cfcfd28a7d05cf05⟩
]
def nodesBlock4 : Array Node := #[
  ⟨6,3,[0x220022, 0x300030, 0x330000],hints 0x54721fb7591fb772725459546e5919b17219b159596e726eb154056eb7056e5454b1b7b1⟩,
  ⟨9,3,[0x880088, 0x900090, 0x990000],hints 0x66721fb76c1fb77272666c666f6c1db5721db56c6c6f726fb566096fb7096f6666b5b7b5⟩,
  ⟨2,2,[0x1000400, 0x1020000],hints 0xeca0ecd1919cdcaca0e190e⟩,
  ⟨1,2,[0x1020, 0x1400],hints 0x59405960e0e969494050e05⟩,
  ⟨3,2,[0x1000400, 0x1100000],hints 0xeca0ecf1f1fcfcaca0e1f0e⟩,
  ⟨0,2,[0x440, 0x600],hints 0x79207930c0c939292070c07⟩
]
def nodesGet (i : Nat) : Option Node :=
  if i < 32 then
    if i < 16 then
      nodesBlock0[(i - 0)]?
    else
      nodesBlock1[(i - 16)]?
  else
    if i < 48 then
      nodesBlock2[(i - 32)]?
    else
      if i < 64 then
        nodesBlock3[(i - 48)]?
      else
        nodesBlock4[(i - 64)]?
def fastViews : Fast.Table View := ⟨36,viewsGet⟩
def fastNodes : Fast.Table Node := ⟨70,nodesGet⟩
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkRoots_0 : Fast.passBlock (Fast.checkRootAt fastViews fastNodes) 0 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkRoots_10 : Fast.passBlock (Fast.checkRootAt fastViews fastNodes) 10 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkRoots_20 : Fast.passBlock (Fast.checkRootAt fastViews fastNodes) 20 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkRoots_30 : Fast.passBlock (Fast.checkRootAt fastViews fastNodes) 30 6 = true := by decide +kernel
theorem combineRoots_0_0 : Fast.passBlock (Fast.checkRootAt fastViews fastNodes) 0 20 = true := @Fast.merge_blocks (Fast.checkRootAt fastViews fastNodes) 0 10 10 checkRoots_0 checkRoots_10
theorem combineRoots_0_20 : Fast.passBlock (Fast.checkRootAt fastViews fastNodes) 20 16 = true := @Fast.merge_blocks (Fast.checkRootAt fastViews fastNodes) 20 10 6 checkRoots_20 checkRoots_30
theorem combineRoots_1_0 : Fast.passBlock (Fast.checkRootAt fastViews fastNodes) 0 36 = true := @Fast.merge_blocks (Fast.checkRootAt fastViews fastNodes) 0 20 16 combineRoots_0_0 combineRoots_0_20
theorem certifiedRoots : Fast.passBlock (Fast.checkRootAt fastViews fastNodes) 0 36 = true := combineRoots_1_0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_0 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 0 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_10 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 10 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_20 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 20 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_30 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 30 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_40 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 40 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_50 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 50 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_60 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 60 10 = true := by decide +kernel
theorem combineNodes_0_0 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 0 20 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 0 10 10 checkNodes_0 checkNodes_10
theorem combineNodes_0_20 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 20 20 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 20 10 10 checkNodes_20 checkNodes_30
theorem combineNodes_0_40 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 40 20 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 40 10 10 checkNodes_40 checkNodes_50
theorem combineNodes_1_0 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 0 40 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 0 20 20 combineNodes_0_0 combineNodes_0_20
theorem combineNodes_1_40 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 40 30 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 40 20 10 combineNodes_0_40 checkNodes_60
theorem combineNodes_2_0 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 0 70 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 0 40 30 combineNodes_1_0 combineNodes_1_40
theorem certifiedNodes : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 0 70 = true := combineNodes_2_0
end SignedProjection

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def graph (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)

def witness : Circuit :=
  ⟨[⟨.or,[1,2]⟩, ⟨.or,[0,8]⟩, ⟨.or,[5,7]⟩, ⟨.and,[9,10]⟩,
    ⟨.or,[3,8]⟩, ⟨.and,[6,12]⟩, ⟨.or,[0,7]⟩, ⟨.and,[4,14]⟩,
    ⟨.or,[11,13]⟩, ⟨.or,[16,15]⟩],17⟩

theorem witnessMono : Monotone2 witness := by simp [Monotone2,witness]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem witnessEval : ∀ x, witness.eval (List.ofFn x) = graph x := by decide +kernel

def f1 (x : Fin 8 → Bool) := graph (Function.update x 2 false)
def f2 (x : Fin 8 → Bool) := f1 (Function.update x 3 false)
def f3 (x : Fin 8 → Bool) := f2 (Function.update x 5 false)

def relabel : Fin 8 → Fin 6 := ![0,1,0,0,2,0,3,4]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem core_eq : ∀ x : Fin 6 → Bool, f3 (x ∘ relabel) = CoreSigned.F x := by decide +kernel

theorem core_reject (h : HasCircuitSize 6 CoreSigned.F 6) : False := by
  obtain ⟨C, legal, hs, ev⟩ := h
  have lo := Direct64.low (SevenGlue.from_blocks SignedProjection.fastViews SignedProjection.fastNodes
    SignedProjection.certifiedRoots SignedProjection.certifiedNodes 35 (by decide +kernel)) C.gates C.output legal ev
  have cf : Direct64.binaryCost C.gates ≤ C.gates.length := List.length_filter_le _ _
  change C.gates.length ≤ 6 at hs
  omega

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem lower (h : HasCircuitSize 8 graph 9) : False := by
  have a : HasCircuitSize 8 f1 8 := Helpers.Forest.one_gate_at 7 graph 2 false 8
    ⟨fun j => decide (j=5), by decide +kernel⟩
    ⟨fun _ => false,fun _ => true,by decide +kernel⟩ h
  have b : HasCircuitSize 8 f2 7 := Helpers.Forest.one_gate_at 7 f1 3 false 7
    ⟨fun j => decide (j=6), by decide +kernel⟩
    ⟨fun _ => false,fun _ => true,by decide +kernel⟩ a
  have c : HasCircuitSize 8 f3 6 := Helpers.Forest.one_gate_at 7 f2 5 false 6
    ⟨fun j => decide (j=0), by decide +kernel⟩
    ⟨fun _ => false,fun _ => true,by decide +kernel⟩ b
  have u := Helpers.PermInputs.relabel_size relabel f3 6 c
  rw [funext core_eq] at u
  exact core_reject u

end PEqualNP.Outside.L_meta_14174

theorem PEqualNP.Outside.L_meta_14174 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gs o legal _ ev
  have h : 10 ≤ gs.length := by
    by_contra! bad
    exact L_meta_14174.lower ⟨⟨gs,o⟩,legal,by change gs.length ≤ 9; omega,ev⟩
  exact ⟨L_meta_14174.witness.gates,L_meta_14174.witness.output,L_meta_14174.witnessMono,h,
    L_meta_14174.witnessEval⟩
