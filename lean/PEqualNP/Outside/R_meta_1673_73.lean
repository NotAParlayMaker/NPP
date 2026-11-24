import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The three test inputs are the two endpoints separately and the two together.
-- Cut at the first new column that separates the edge from both singletons.
-- In the OR case both predecessor patterns must already have been generated.
set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_1673_73
    (positive :
      let s := (fun _ : Fin 9 → Bool => false) :: (List.ofFn (fun (i : Fin 9) (x : Fin 9 → Bool) => x i) ++ [fun x => x 0 || x 1])
      let sig := fun (f : (Fin 9 → Bool) → Bool) =>
        (f (fun i => decide (i = 0)), f (fun i => decide (i = 1)), f (fun i => decide (i = 0 ∨ i = 1)))
      ∀ t : List ((Fin 9 → Bool) → Bool), t.length ≤ 14 →
        (∀ k : Fin t.length, let w := s ++ t.take k.val
          ∃ a ∈ w, ∃ b ∈ w, t.get k = (fun x => a x && b x) ∨
            t.get k = (fun x => a x || b x) ∨ t.get k = (fun x => !(a x))) →
        (∃ k : Fin t.length, let w := s ++ t.take k.val
          (∀ u ∈ w, (sig u).1 = (sig u).2.1 → (sig u).1 = (sig u).2.2) ∧
          ∃ a ∈ w, ∃ b ∈ w, sig a = (true, false, true) ∧ sig b = (false, true, true) ∧
            t.get k = (fun x => a x && b x)) →
        (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) ∉ t)
    (negative :
      let s := (fun _ : Fin 9 → Bool => false) :: (List.ofFn (fun (i : Fin 9) (x : Fin 9 → Bool) => x i) ++ [fun x => x 0 || x 1])
      let sig := fun (f : (Fin 9 → Bool) → Bool) =>
        (f (fun i => decide (i = 0)), f (fun i => decide (i = 1)), f (fun i => decide (i = 0 ∨ i = 1)))
      ∀ t : List ((Fin 9 → Bool) → Bool), t.length ≤ 14 →
        (∀ k : Fin t.length, let w := s ++ t.take k.val
          ∃ a ∈ w, ∃ b ∈ w, t.get k = (fun x => a x && b x) ∨
            t.get k = (fun x => a x || b x) ∨ t.get k = (fun x => !(a x))) →
        (∃ k : Fin t.length, let w := s ++ t.take k.val
          (∀ u ∈ w, (sig u).1 = (sig u).2.1 → (sig u).1 = (sig u).2.2) ∧
          ∃ a ∈ w, ∃ b ∈ w, sig a = (true, false, false) ∧ sig b = (false, true, false) ∧
            t.get k = (fun x => a x || b x)) →
        (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) ∉ t)
    : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 1)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro C fan first computes
  by_contra short
  have limit : C.size ≤ 15 := by omega
  let F := (Fin 9 → Bool) → Bool
  let zero : F := fun _ => false
  let raw := List.ofFn (fun (i : Fin 9) (x : Fin 9 → Bool) => x i)
  let top : F := fun x => x 0 || x 1
  let seed := raw ++ [top]
  let goal : F := fun x => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
    (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let sig := fun (f : F) => (f (fun i => decide (i = 0)), f (fun i => decide (i = 1)),
    f (fun i => decide (i = 0 ∨ i = 1)))
  let safe := fun (r : Bool × Bool × Bool) => r.1 = r.2.1 → r.1 = r.2.2
  let allowed := fun (w : List F) (u : F) => ∃ a ∈ zero :: w, ∃ b ∈ zero :: w,
    u = (fun x => a x && b x) ∨ u = (fun x => a x || b x) ∨ u = (fun x => !(a x))
  let valid := fun (w t : List F) => ∀ j : Fin t.length, allowed (w ++ t.take j.val) (t.get j)
  let value := fun (w : List F) (g : Gate) (x : Fin 9 → Bool) =>
    g.op.eval (g.inputs.map fun i => w.getD i zero x)
  let step := fun (w : List F) (g : Gate) => w ++ [value w g]
  have reads (w : List F) (i : ℕ) : w.getD i zero ∈ zero :: w := by
    by_cases h : i < w.length
    · rw [List.getD_eq_getElem _ _ h]
      exact List.mem_cons_of_mem _ (List.getElem_mem h)
    · rw [List.getD_eq_default _ _ (by omega)]
      exact List.mem_cons_self
  have gateOK (w : List F) (g : Gate)
      (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
      allowed w (value w g) := by
    rcases g with ⟨op, pins⟩
    obtain ⟨hop,hlen⟩ := hg
    change op = .and ∨ op = .or ∨ op = .not at hop
    change pins.length ≤ 2 at hlen
    cases pins with
    | nil =>
      refine ⟨zero, List.mem_cons_self, zero, List.mem_cons_self, ?_⟩
      rcases hop with rfl | rfl | rfl
      · exact Or.inr (Or.inr rfl)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr rfl)
    | cons i rest =>
      cases rest with
      | nil =>
        refine ⟨w.getD i zero, reads w i, w.getD i zero, reads w i, ?_⟩
        rcases hop with rfl | rfl | rfl
        · left
          funext x
          change ([w.getD i zero x] : List Bool).all id = _
          simp
        · right; left
          funext x
          change ([w.getD i zero x] : List Bool).any id = _
          simp
        · exact Or.inr (Or.inr rfl)
      | cons j rest =>
        cases rest with
        | cons k rest => simp at hlen
        | nil =>
          refine ⟨w.getD i zero, reads w i, w.getD j zero, reads w j, ?_⟩
          rcases hop with rfl | rfl | rfl
          · left
            funext x
            change ([w.getD i zero x, w.getD j zero x] : List Bool).all id = _
            simp
          · right; left
            funext x
            change ([w.getD i zero x, w.getD j zero x] : List Bool).any id = _
            simp
          · exact Or.inr (Or.inr rfl)
  have trace (gs : List Gate) (w : List F) (hf : FanInTwo ⟨gs, 0⟩) :
      ∃ t, gs.foldl step w = w ++ t ∧ t.length = gs.length ∧ valid w t := by
    induction gs generalizing w with
    | nil => exact ⟨[], (List.append_nil w).symm, rfl, fun j => Fin.elim0 j⟩
    | cons g gs ih =>
      have tailFan : FanInTwo ⟨gs, 0⟩ := fun a ha => hf a (List.mem_cons_of_mem _ ha)
      obtain ⟨t, eq, len, ok⟩ := ih (step w g) tailFan
      refine ⟨value w g :: t, ?_, by simp [len], ?_⟩
      · simpa [List.foldl_cons, step, List.append_assoc] using eq
      · intro j
        refine Fin.cases ?_ (fun i => ?_) j
        · simpa using gateOK w g (hf g List.mem_cons_self)
        · simpa [step, List.append_assoc] using ok i
  have reading (w : List F) (i : ℕ) (x : Fin 9 → Bool) :
      (w.map (fun a => a x)).getD i false = w.getD i zero x :=
    List.getD_map w zero (fun a => a x)
  have sound (gs : List Gate) (w : List F) (x : Fin 9 → Bool) :
      (gs.foldl step w).map (fun a => a x) = (Circuit.mk gs 0).wires (w.map (fun a => a x)) := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      delta Circuit.wires
      simp only [List.foldl_cons, step, List.map_append, List.map_cons, List.map_nil,
        value, reading]
  have seedSafe : ∀ u ∈ zero :: seed, safe (sig u) := by
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact fun _ => rfl
    · rcases List.mem_append.mp hu with hu | hu
      · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
        by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;> simp [safe, sig, h0, h1]
      · obtain rfl := List.mem_singleton.mp hu
        exact fun _ => rfl
  have targetUnsafe : ¬safe (sig goal) := by decide
  have earliest (l : List F) (ex : ∃ u ∈ l, ¬safe (sig u)) :
      ∃ j : Fin l.length, ¬safe (sig (l.get j)) ∧ ∀ u ∈ l.take j.val, safe (sig u) := by
    induction l with
    | nil => simp at ex
    | cons a l ih =>
      by_cases ha : safe (sig a)
      · obtain ⟨u,hu,bad⟩ := ex
        obtain ⟨j,before,hs⟩ := ih ⟨u,(List.mem_cons.mp hu).resolve_left (fun h => bad (h ▸ ha)),bad⟩
        refine ⟨j.succ,before,?_⟩
        intro u hu
        rcases List.mem_cons.mp (by simpa using hu : u ∈ a :: l.take j.val) with rfl | hm
        · exact ha
        · exact hs _ hm
      · exact ⟨0,ha,by simp⟩
  have andCut : ∀ r s : Bool × Bool × Bool, safe r → safe s →
      ¬safe (r.1 && s.1, r.2.1 && s.2.1, r.2.2 && s.2.2) →
      (r = (true,false,true) ∧ s = (false,true,true)) ∨
      (s = (true,false,true) ∧ r = (false,true,true)) := by decide
  have orCut : ∀ r s : Bool × Bool × Bool, safe r → safe s →
      ¬safe (r.1 || s.1, r.2.1 || s.2.1, r.2.2 || s.2.2) →
      (r = (true,false,false) ∧ s = (false,true,false)) ∨
      (s = (true,false,false) ∧ r = (false,true,false)) := by decide
  have negSafe : ∀ r : Bool × Bool × Bool, safe r → safe (!r.1,!r.2.1,!r.2.2) := by decide
  obtain ⟨gs,out⟩ := C
  cases gs with
  | nil =>
    have wrong := first (fun _ => true)
    change (List.ofFn (fun _ : Fin 9 => true)).getD 9 false = true at wrong
    rw [List.getD_eq_default _ _ (by simp)] at wrong
    contradiction
  | cons g gs =>
    have tailFan : FanInTwo ⟨gs, 0⟩ := fun a ha => fan a (List.mem_cons_of_mem _ ha)
    obtain ⟨t, hfold, len, ok⟩ := trace gs (step raw g) tailFan
    have columns (x : Fin 9 → Bool) :
        (Circuit.mk (g :: gs) out).wires (List.ofFn x) = ((raw ++ [value raw g]) ++ t).map (fun a => a x) := by
      have h := sound (g :: gs) raw x
      rw [List.foldl_cons, hfold] at h
      delta Circuit.wires at h ⊢
      simpa [step, raw, List.map_ofFn, Function.comp_def] using h.symm
    have forced : value raw g = top := by
      funext x
      have h := first x
      rw [columns] at h
      rw [reading, List.getD_append _ _ _ 9 (by simp [raw]),
        List.getD_append_right _ _ _ 9 (by simp [raw])] at h
      simpa [raw, top] using h
    have picked : (seed ++ t).getD out zero = goal := by
      funext x
      have h := congrFun computes x
      change ((Circuit.mk (g :: gs) out).wires (List.ofFn x)).getD out false = goal x at h
      rwa [columns, forced, reading] at h
    have ht : goal ∈ t := by
      have hm := reads (seed ++ t) out
      rw [picked] at hm
      rcases List.mem_cons.mp hm with hz | hm
      · exact (targetUnsafe (hz ▸ seedSafe _ List.mem_cons_self)).elim
      · rcases List.mem_append.mp hm with hs | ht
        · exact (targetUnsafe (seedSafe _ (List.mem_cons_of_mem _ hs))).elim
        · exact ht
    have ok' : valid seed t := by simpa only [step, forced, seed] using ok
    have bound : t.length ≤ 14 := by
      change (g :: gs).length ≤ 15 at limit
      simp only [List.length_cons] at limit
      omega
    obtain ⟨k,hbad,prior⟩ := earliest t ⟨goal,ht,targetUnsafe⟩
    let w := zero :: (seed ++ t.take k.val)
    have clean (u : F) (hu : u ∈ w) : safe (sig u) := by
      rcases List.mem_cons.mp hu with rfl | hu
      · exact seedSafe _ List.mem_cons_self
      · rcases List.mem_append.mp hu with hs | hp
        · exact seedSafe _ (List.mem_cons_of_mem _ hs)
        · exact prior _ hp
    obtain ⟨a,ha,b,hb,hbin | hbin | hnot⟩ := ok' k
    · have cut := andCut (sig a) (sig b) (clean a ha) (clean b hb)
      rw [hbin] at hbad
      apply positive t bound ok' _ ht
      refine ⟨k,clean,?_⟩
      rcases cut hbad with ⟨h1,h2⟩ | ⟨h2,h1⟩
      · exact ⟨a,ha,b,hb,h1,h2,hbin⟩
      · exact ⟨b,hb,a,ha,h2,h1,hbin.trans (funext fun x => Bool.and_comm _ _)⟩
    · have cut := orCut (sig a) (sig b) (clean a ha) (clean b hb)
      rw [hbin] at hbad
      apply negative t bound ok' _ ht
      refine ⟨k,clean,?_⟩
      rcases cut hbad with ⟨h1,h2⟩ | ⟨h2,h1⟩
      · exact ⟨a,ha,b,hb,h1,h2,hbin⟩
      · exact ⟨b,hb,a,ha,h2,h1,hbin.trans (funext fun x => Bool.or_comm _ _)⟩
    · rw [hnot] at hbad
      exact hbad (negSafe (sig a) (clean a ha))
