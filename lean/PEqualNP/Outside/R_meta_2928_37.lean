import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_2928_37
    (base : ∀ (a b : Fin 11) (C : Circuit), a≤b → FanInTwo C → C.size≤13 →
    ((a=b ∨ b=10 ∨ a=0 ∨ b=9) ∨ 11*a.val+b.val ∈ ([13,17,25,29,37] : List Nat) ∨
      C.size<13 ∨ C.output≠23 ∨ (∃ i j : Fin 9, i≠j ∧ (⟨.and,[i.val,j.val]⟩ : Gate) ∈ C.gates)) →
    let w := fun (x : Fin 9 → Bool) => List.ofFn x ++ [!x 0]
      let r := fun (j : Fin 11) (x : Fin 9 → Bool) => (w x).getD j.val false
      ¬∀ x, C.eval (w x ++ [r a x || r b x]) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (remaining : ∀ (a b : Fin 11) (C : Circuit), 11*a.val+b.val ∈ ([14,15,16,18,19,26,28,30,39,50,73] : List Nat) →
    FanInTwo C → C.size=13 → C.output=23 → (¬∃ i j : Fin 9, i≠j ∧ (⟨.and,[i.val,j.val]⟩ : Gate) ∈ C.gates) →
    let w := fun (x : Fin 9 → Bool) => List.ofFn x ++ [!x 0]
      let r := fun (j : Fin 11) (x : Fin 9 → Bool) => (w x).getD j.val false
      (∀ j∈[a,b], ∃ x, r j x=false ∧ (r a x || r b x)=true ∧
        C.eval (w x ++ [false]) ≠ C.eval (w x ++ [true])) →
      ¬∀ x, C.eval (w x ++ [r a x || r b x]) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 x2 : Fin (11 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x1 ≤ x2 →     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size ≤ (13 : ℕ) →         ∃ (x7 : BitVec (9 : ℕ)),           have x8 : Fin (9 : ℕ) → Bool := fun (x8 : Fin (9 : ℕ)) => x7.getLsbD ↑x8;           have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];           x3.eval (x9 ++ [x9.getD (↑x1) Bool.false || x9.getD (↑x2) Bool.false]) ≠ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x10 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x8 x10.1 && x8 x10.2 := by
  let target (x : Fin 9 → Bool) := x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
      x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let bank (x : Fin 9 → Bool) := List.ofFn x ++ [!x 0]
  let val (j : Nat) (x : Fin 9 → Bool) := (bank x).getD j false
  have getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
    simp

  let wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
    if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

  let relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
    ⟨g.op, g.inputs.map (wmap n m π)⟩

  let relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
    ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  let Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
    n ≤ W.length ∧ W'.length + n = W.length + m ∧
      ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

  have rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
      (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
    obtain ⟨h1, h2, h3⟩ := h
    have hv : (relGate n m π g).op.eval
        ((relGate n m π g).inputs.map fun i => W'.getD i false)
        = g.op.eval (g.inputs.map fun i => W.getD i false) := by
      simp only [relGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a _
      exact h3 a
    refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
    intro w
    simp only [step, hv]
    rcases Nat.lt_trichotomy w W.length with hw | hw | hw
    · have hlt : wmap n m π w < W'.length := by
        unfold wmap
        split
        · have := (π ⟨w, by assumption⟩).2; omega
        · omega
      rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
      exact h3 w
    · have he : wmap n m π w = W'.length := by
        unfold wmap
        split
        · omega
        · omega
      rw [he, hw, getD_snoc_eq, getD_snoc_eq]
    · have hge : W'.length + 1 ≤ wmap n m π w := by
        unfold wmap
        split
        · omega
        · omega
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

  have rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
      ∀ W W' : List Bool, Rel n m π W W' →
        Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
    induction gs with
    | nil => intro W W' h; exact h
    | cons g gs ih =>
      intro W W' h
      exact ih _ _ (rel_step n m π W W' g h)
  let perm : Fin 9 → Fin 9 := ![0,5,8,3,4,1,7,6,2]
  let ext : Fin 11 → Fin 11 := ![0,5,8,3,4,1,7,6,2,9,10]
  have targetPerm (x : Fin 9 → Bool) : target (x ∘ perm) = target x := by
    change (x 0 && x 5 || x 5 && x 8 || x 8 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 1 ||
      x 5 && x 7 || x 8 && x 6 || x 3 && x 2 || x 1 && x 6 || x 7 && x 2 || x 2 && x 1) = _
    unfold target
    ac_rfl
  let sig (a b : Fin 11) (x : Fin 9 → Bool) := bank x ++ [val a.val x || val b.val x]
  have permRel (a b : Fin 11) (x : Fin 9 → Bool) :
      Rel 9 9 perm (sig a b (x ∘ perm)) (sig (ext a) (ext b) x) := by
    have vp (i : Fin 11) : val (ext i).val x = val i.val (x ∘ perm) := by fin_cases i <;> rfl
    refine ⟨by simp [sig,bank],by simp [sig,bank],?_⟩
    intro i
    by_cases hi : i < 9
    · let t : Fin 9 := ⟨i,hi⟩
      change (sig (ext a) (ext b) x).getD (wmap 9 9 perm t.val) false =
        (sig a b (x ∘ perm)).getD t.val false
      generalize t = u
      fin_cases u <;> rfl
    have wp : wmap 9 9 perm i = i := by simp [wmap,hi];omega
    rw [wp]
    by_cases h9 : i = 9
    · subst i; rfl
    by_cases h10 : i = 10
    · subst i
      change (val (ext a).val x || val (ext b).val x) = _
      rw [vp,vp];rfl
    rw [List.getD_eq_default _ _ (by simp [sig,bank];omega),List.getD_eq_default _ _ (by simp [sig,bank];omega)]
  let fails (a b : Fin 11) := ∀ C : Circuit, FanInTwo C → C.size ≤ 13 → ¬∀ x, C.eval (sig a b x) = target x
  have turn (a b : Fin 11) (h : fails (ext a) (ext b)) : fails a b := by
    intro C hf hs
    intro he
    let D := relabel 9 9 perm C
    have fanD : FanInTwo D := by
      intro g hg
      obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hg
      exact ⟨(hf k hk).1,by simpa [relGate] using (hf k hk).2⟩
    apply h D fanD (by change (C.gates.map _).length ≤ 13;rw [List.length_map];exact hs)
    intro x
    exact ((rel_fold 9 9 perm C.gates _ _ (permRel a b x)).2.2 C.output).trans
      ((he (x ∘ perm)).trans (targetPerm x))
  have flipFail (a b : Fin 11) (h : fails b a) : fails a b := by
    intro C hf hs
    simpa only [sig,Bool.or_comm (val b.val _) (val a.val _)] using h C hf hs

  let triv (a b : Fin 11) := a=b ∨ b=10 ∨ a=0 ∨ b=9
  let near : List Nat := [13,17,25,29,37]
  let rest : List Nat := [14,15,16,18,19,26,28,30,39,50,73]
  let code (a b : Fin 11) := 11*a.val+b.val
  let reps (a b : Fin 11) := code a b∈near ∨ code a b∈rest
  have cover : ∀ a b : Fin 11, a≤b → triv a b ∨ reps a b ∨ reps (ext a) (ext b) ∨ reps (ext b) (ext a) := by
    unfold triv reps near rest code ext;decide +kernel
  have order : ∀ a b : Fin 11,reps a b → a≤b := by unfold reps near rest code;decide +kernel
  let has (C : Circuit) := ∃ i j : Fin 9,i ≠ j ∧ (⟨.and,[i.val,j.val]⟩ : Gate)∈C.gates
  let known := ∀ (a b : Fin 11) (C : Circuit), a≤b → FanInTwo C → C.size≤13 →
    (triv a b ∨ code a b∈near ∨ C.size<13 ∨ C.output≠23 ∨ has C) → ¬∀ x,C.eval (sig a b x)=target x
  let hard := ∀ (a b : Fin 11) (C : Circuit), code a b∈rest → FanInTwo C → C.size=13 → C.output=23 →
    (¬has C) → (∀ j∈[a,b], ∃ x, val j.val x=false ∧ (val a.val x || val b.val x)=true ∧
         C.eval (bank x ++ [false]) ≠ C.eval (bank x ++ [true])) → ¬∀ x,C.eval (sig a b x)=target x
  have handle (K : known) (H : hard) (a b : Fin 11) (ab : a≤b) : fails a b := by
    have good (i j : Fin 11) (rep : reps i j) : fails i j := by
      intro C hf hs corr
      have le := order i j rep
      by_cases short : C.size<13
      · exact K _ _ C le hf hs (Or.inr (Or.inr (Or.inl short))) corr
      by_cases out : C.output=23
      · by_cases raw : has C
        · exact K _ _ C le hf hs (Or.inr (Or.inr (Or.inr (Or.inr raw)))) corr
        rcases rep with near|rest
        · exact K _ _ C le hf hs (Or.inr (Or.inl near)) corr
        apply H i j C rest hf (by omega) out raw _ corr
        intro z mem
        have nz := K z z C (by rfl) hf hs (Or.inl (Or.inl rfl))
        simp only [sig,Bool.or_self] at nz
        push Not at nz
        obtain ⟨x,hx⟩ := nz
        rw [←corr x] at hx
        change C.eval (bank x ++ [val z.val x]) ≠ C.eval (bank x ++ [val i.val x || val j.val x]) at hx
        have sub : val z.val x=true → (val i.val x || val j.val x)=true := by
          intro h
          rcases (by simpa using mem : z=i ∨ z=j) with rfl|rfl <;> simp [h]
        have diff : val z.val x ≠ (val i.val x || val j.val x) := fun e => hx (by rw [← e])
        cases zz : val z.val x with
        | true => exact False.elim (diff (zz.trans (sub zz).symm))
        | false =>
          have hk : (val i.val x || val j.val x)=true := by
            cases h : (val i.val x || val j.val x)
            · exact False.elim (diff (zz.trans h.symm))
            · rfl
          exact ⟨x,zz,hk,by simpa only [zz,hk] using hx⟩
      · exact K _ _ C le hf hs (Or.inr (Or.inr (Or.inr (Or.inl out)))) corr
    rcases cover a b ab with t|r|r|r
    · intro C hf hs; exact K _ _ C ab hf hs (Or.inl t)
    · exact good _ _ r
    · exact turn a b (good _ _ r)
    · exact turn a b (flipFail _ _ (good _ _ r))
  intro a b C le hf hs
  by_contra! all
  apply handle base remaining a b le C hf hs
  intro x
  let k := BitVec.ofBoolListLE (List.ofFn x)
  have bits (j : Fin 9) : k.getLsbD j.val = x j := by
    change (BitVec.ofBoolListLE (List.ofFn x)).getLsbD j.val = _
    rw [BitVec.getLsbD_ofBoolListLE];fin_cases j <;> rfl
  let y : Fin 9 → Bool := fun i => k.getLsbD i.val
  have yx : y=x := funext bits
  let es : List (Fin 9 × Fin 9) :=
    [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
  have hh := all k
  change ¬ C.eval (sig a b y) ≠ es.any (fun e => y e.1 && y e.2) at hh
  have h := not_ne_iff.mp hh
  rw [yx] at h
  simpa only [es,target,List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc] using h
