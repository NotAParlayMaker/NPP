import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4610

private def combines (xs : List Nat) (v : Nat) : Prop :=
  ∃ a ∈ xs, ∃ b ∈ xs, v = a &&& b ∨ v = a ||| b

private def maskSteps (xs gs : List Nat) : Prop :=
  ∀ i : Fin gs.length, combines (xs ++ gs.take i.val) (gs.get i)

private lemma stepsCons (xs : List Nat) (g : Nat) (gs : List Nat) :
    maskSteps xs (g :: gs) ↔ combines xs g ∧ maskSteps (xs ++ [g]) gs := by
  constructor
  · intro h
    constructor
    · simpa [maskSteps] using h 0
    · intro i
      simpa [List.append_assoc, List.get_cons_succ'] using h i.succ
  · rintro ⟨hg, hs⟩ i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hg
    · simpa [List.append_assoc, List.get_cons_succ'] using hs j

private lemma cutAnd (m a b : Nat) :
    (a &&& b) &&& m = (a &&& m) &&& (b &&& m) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and]
  cases a.testBit i <;> cases b.testBit i <;> cases m.testBit i <;> rfl

private lemma cutOr (m a b : Nat) :
    (a ||| b) &&& m = (a &&& m) ||| (b &&& m) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_or]
  cases a.testBit i <;> cases b.testBit i <;> cases m.testBit i <;> rfl

private lemma liftMasks (m : Nat) (gs xs : List Nat)
    (h : maskSteps (xs.map (fun x => x &&& m)) gs) :
    ∃ out : List Nat, out.map (fun x => x &&& m) = gs ∧ maskSteps xs out := by
  induction gs generalizing xs with
  | nil =>
    exact ⟨[], rfl, fun i => Fin.elim0 i⟩
  | cons g gs ih =>
    obtain ⟨⟨a, ha, b, hb, hop⟩, ht⟩ := (stepsCons _ _ _).mp h
    obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
    have step (v : Nat) (op : v = a' &&& b' ∨ v = a' ||| b') (hm : v &&& m = g) :
        ∃ out : List Nat, out.map (fun x => x &&& m) = g :: gs ∧ maskSteps xs out := by
      have hh : maskSteps ((xs ++ [v]).map (fun x => x &&& m)) gs := by
        simpa [List.map_append, hm] using ht
      obtain ⟨vs, hv, hs⟩ := ih (xs ++ [v]) hh
      exact ⟨v :: vs, by simp [hm, hv], (stepsCons _ _ _).mpr ⟨⟨a', ha', b', hb', op⟩, hs⟩⟩
    rcases hop with ha | hb
    · exact step _ (Or.inl rfl) ((cutAnd m a' b').trans ha.symm)
    · exact step _ (Or.inr rfl) ((cutOr m a' b').trans hb.symm)

private lemma maskInvariant (P : Nat → Prop)
    (hAnd : ∀ a b, P a → P b → P (a &&& b))
    (hOr : ∀ a b, P a → P b → P (a ||| b))
    (gs xs : List Nat) (hp : ∀ a ∈ xs, P a) (hs : maskSteps xs gs) :
    ∀ w ∈ xs ++ gs, P w := by
  induction gs generalizing xs with
  | nil => simpa using hp
  | cons g gs ih =>
    obtain ⟨⟨a, ha, b, hb, hop⟩, hs'⟩ := (stepsCons _ _ _).mp hs
    have hg : P g := hop.elim (fun e => e ▸ hAnd a b (hp a ha) (hp b hb))
      (fun e => e ▸ hOr a b (hp a ha) (hp b hb))
    have hh : ∀ a ∈ xs ++ [g], P a := by
      intro a hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hp a hm
      · simpa using (List.mem_singleton.mp hm).symm ▸ hg
    simpa [List.append_assoc] using ih (xs ++ [g]) hh hs'

private lemma maskImplies (xs gs : List Nat) (hs : maskSteps xs gs)
    (i j : Nat) (h : ∀ a ∈ xs, a.testBit i = true → a.testBit j = true)
    (w : Nat) (hw : w ∈ xs ++ gs) :
    w.testBit i = true → w.testBit j = true := by
  refine maskInvariant (fun x => x.testBit i = true → x.testBit j = true) ?_ ?_ gs xs h hs w hw
  · intro a b ha hb
    simp only [Nat.testBit_and, Bool.and_eq_true]
    exact fun h => ⟨ha h.1, hb h.2⟩
  · intro a b ha hb
    simp only [Nat.testBit_or, Bool.or_eq_true]
    exact fun h => h.elim (fun h => Or.inl (ha h)) (fun h => Or.inr (hb h))

end PEqualNP.Outside.L_meta_4610

open PEqualNP.Outside.L_meta_4610

theorem PEqualNP.Outside.L_meta_4610 :
    have x1 : List ℕ → List ℕ → Prop := fun (x1 x2 : List ℕ) => ∀ (x3 : Fin x2.length), ∃ x4 ∈ x1 ++ List.take (↑x3) x2, ∃ x5 ∈ x1 ++ List.take (↑x3) x2, x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5; have x2 : List ℕ → ℕ → ℕ → Prop := fun (x2 : List ℕ) (x3 x4 : ℕ) => ∀ (x5 : ℕ), ∃ (x6 : ℕ), x3.testBit x6 = Bool.true ∧ x4.testBit x6 = x4.testBit x5 ∧ ∀ x7 ∈ x2, if x4.testBit x5 = Bool.true then x7.testBit x6 = Bool.true → x7.testBit x5 = Bool.true else x7.testBit x5 = Bool.true → x7.testBit x6 = Bool.true; ∀ (x3 : List ℕ) (x4 x5 : ℕ) (x6 : List ℕ),   x2 x3 x4 x5 →     have x8 : List ℕ := List.map (fun (x8 : ℕ) => x8 &&& x4) x3;     x1 x8 x6 → x5 &&& x4 ∈ x8 ++ x6 → ∃ (x11 : List ℕ), x11.length ≤ x6.length ∧ x1 x3 x11 ∧ x5 ∈ x3 ++ x11 := by
  dsimp only
  intro xs m target gs hRepresentative hProgram hTarget
  change maskSteps (xs.map (fun x => x &&& m)) gs at hProgram
  obtain ⟨out, hm, ho⟩ := liftMasks m gs xs hProgram
  have hlen := congrArg List.length hm
  simp only [List.length_map] at hlen
  refine ⟨out, hlen.le, ho, ?_⟩
  rw [← hm, ← List.map_append] at hTarget
  obtain ⟨w, hw, he⟩ := List.mem_map.mp hTarget
  have keep (j : Nat) (hj : m.testBit j = true) : w.testBit j = target.testBit j := by
    have hh := congrArg (fun n : Nat => n.testBit j) he
    simp only [Nat.testBit_and, hj, Bool.and_true] at hh
    exact hh
  have eq : w = target := by
    apply Nat.eq_of_testBit_eq
    intro i
    obtain ⟨j, hj, ht, h⟩ := hRepresentative i
    have same := (keep j hj).trans ht
    cases hi : target.testBit i
    · by_contra contra
      have wit : w.testBit i = true := by cases hwi : w.testBit i <;> simp_all
      have base : ∀ x ∈ xs, x.testBit i = true → x.testBit j = true := by simpa only [hi, Bool.false_eq_true, ite_false] using h
      have bad := maskImplies xs out ho i j base w hw wit
      rw [same, hi] at bad
      exact Bool.noConfusion bad
    · have base : ∀ x ∈ xs, x.testBit j = true → x.testBit i = true := by simpa only [hi, ite_true] using h
      exact maskImplies xs out ho j i base w hw (same.trans hi)
  exact eq ▸ hw
