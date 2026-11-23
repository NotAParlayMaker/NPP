import Mathlib
import PEqualNP.Defs


section

namespace PEqualNP.Library.Machines

open Turing

theorem iterate_none {σ : Type} (f : σ → Option σ) (n : ℕ) :
    (flip bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

theorem simulate {σ τ : Type} (f : σ → Option σ) (g : τ → Option τ) (emb : σ → τ)
    (h : ∀ c c', f c = some c' → g (emb c) = some (emb c')) :
    ∀ (n : ℕ) (a b : σ), (flip bind f)^[n] (some a) = some b →
      (flip bind g)^[n] (some (emb a)) = some (emb b) := by
  intro n
  induction n with
  | zero =>
    intro a b hab
    have : a = b := Option.some.inj hab
    rw [this]; rfl
  | succ n ih =>
    intro a b hab
    rw [Function.iterate_succ_apply] at hab ⊢
    cases hfa : f a with
    | none =>
      have e : flip bind f (some a) = none := hfa
      rw [e, iterate_none] at hab
      exact absurd hab (by simp)
    | some c =>
      have e : flip bind f (some a) = some c := hfa
      have e' : flip bind g (some (emb a)) = some (emb c) := h a c hfa
      rw [e] at hab
      rw [e']
      exact ih c b hab

section pushes

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

def pushes : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => pushes q + 1
  | .peek _ _ q => pushes q
  | .pop _ _ q => pushes q
  | .load _ q => pushes q
  | .branch _ q₁ q₂ => max (pushes q₁) (pushes q₂)
  | .goto _ => 0
  | .halt => 0

theorem stepAux_length (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (k : K) :
    ((TM2.stepAux q v S).stk k).length ≤ (S k).length + pushes q := by
  induction q generalizing v S with
  | push k' f q ih =>
    simp only [TM2.stepAux, pushes]
    refine (ih _ _).trans ?_
    by_cases h : k = k'
    · subst h
      rw [Function.update_self, List.length_cons]; omega
    · rw [Function.update_of_ne h]; omega
  | peek k' f q ih => exact ih _ _
  | pop k' f q ih =>
    simp only [TM2.stepAux, pushes]
    refine (ih _ _).trans ?_
    by_cases h : k = k'
    · subst h
      rw [Function.update_self, List.length_tail]; omega
    · rw [Function.update_of_ne h]
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [TM2.stepAux, pushes]
    cases f v
    · exact (ih₂ v S).trans (by have := le_max_right (pushes q₁) (pushes q₂); omega)
    · exact (ih₁ v S).trans (by have := le_max_left (pushes q₁) (pushes q₂); omega)
  | goto f => simp [TM2.stepAux, pushes]
  | halt => simp [TM2.stepAux, pushes]

end pushes

noncomputable def maxPush (tm : FinTM2) : ℕ :=
  (@Finset.univ tm.Λ tm.ΛFin).sup fun l => pushes (tm.m l)

theorem step_length (tm : FinTM2) (c c' : TM2.Cfg tm.Γ tm.Λ tm.σ)
    (h : TM2.step tm.m c = some c') (k : tm.K) :
    (c'.stk k).length ≤ (c.stk k).length + maxPush tm := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    refine (stepAux_length _ _ _ _).trans ?_
    have : pushes (tm.m l) ≤ maxPush tm :=
      Finset.le_sup (f := fun l => pushes (tm.m l)) (@Finset.mem_univ tm.Λ tm.ΛFin l)
    simpa using this

theorem run_length (tm : FinTM2) (k : tm.K) :
    ∀ (n : ℕ) (a b : TM2.Cfg tm.Γ tm.Λ tm.σ),
      (flip bind (TM2.step tm.m))^[n] (some a) = some b →
      (b.stk k).length ≤ (a.stk k).length + maxPush tm * n := by
  intro n
  induction n with
  | zero =>
    intro a b hab
    have : a = b := Option.some.inj hab
    rw [this]; simp
  | succ n ih =>
    intro a b hab
    rw [Function.iterate_succ_apply] at hab
    cases hfa : TM2.step tm.m a with
    | none =>
      have e : flip bind (TM2.step tm.m) (some a) = none := hfa
      rw [e, iterate_none] at hab
      exact absurd hab (by simp)
    | some c =>
      have e : flip bind (TM2.step tm.m) (some a) = some c := hfa
      rw [e] at hab
      have h1 := ih c b hab
      have h2 := step_length tm a c hfa k
      rw [Nat.mul_succ]; omega

theorem initList_eq (tm : FinTM2) (s : List (tm.Γ tm.k₀)) :
    initList tm s =
      (⟨some tm.main, tm.initialState, Function.update (fun _ => []) tm.k₀ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ) := by
  unfold initList
  congr 1
  funext k
  by_cases h : k = tm.k₀
  · subst h; simp
  · simp [h]

theorem haltList_eq (tm : FinTM2) (s : List (tm.Γ tm.k₁)) :
    haltList tm s =
      (⟨none, tm.initialState, Function.update (fun _ => []) tm.k₁ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ) := by
  unfold haltList
  congr 1
  funext k
  by_cases h : k = tm.k₁
  · subst h; simp
  · simp [h]

theorem eval_mono (p : Polynomial ℕ) {x y : ℕ} (h : x ≤ y) : p.eval x ≤ p.eval y := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.eval_add, Polynomial.eval_add]; exact add_le_add hp hq
  | monomial d c =>
    rw [Polynomial.eval_monomial, Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)

end PEqualNP.Library.Machines

end

section

namespace PEqualNP.Library.Machines

open Turing

section update

variable {ι : Type} [DecidableEq ι] {β : ι → Type}

theorem update3_fst (E : ∀ i, β i) {a b c : ι} (hab : a ≠ b) (hac : a ≠ c)
    (x x' : β a) (y : β b) (z : β c) :
    Function.update (Function.update (Function.update (Function.update E a x) b y) c z) a x' =
      Function.update (Function.update (Function.update E a x') b y) c z := by
  rw [Function.update_comm hac.symm, Function.update_comm hab.symm, Function.update_idem]

theorem update3_snd (E : ∀ i, β i) {a b c : ι} (hbc : b ≠ c)
    (x : β a) (y y' : β b) (z : β c) :
    Function.update (Function.update (Function.update (Function.update E a x) b y) c z) b y' =
      Function.update (Function.update (Function.update E a x) b y') c z := by
  rw [Function.update_comm hbc.symm, Function.update_idem]

end update

variable (M1 M2 : FinTM2)

abbrev CK : Type := Option (M1.K ⊕ M2.K)

abbrev CΓ : CK M1 M2 → Type
  | none => M2.Γ M2.k₀
  | some (Sum.inl k) => M1.Γ k
  | some (Sum.inr k) => M2.Γ k

abbrev CΛ : Type := M1.Λ ⊕ M2.Λ ⊕ Bool

abbrev Cσ : Type := M1.σ × M2.σ × Option (M2.Γ M2.k₀)

variable {M1 M2}

def tr1 : TM2.Stmt M1.Γ M1.Λ M1.σ → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | .push k f q => .push (some (Sum.inl k)) (fun s => f s.1) (tr1 q)
  | .peek k f q => .peek (some (Sum.inl k)) (fun s o => (f s.1 o, s.2)) (tr1 q)
  | .pop k f q => .pop (some (Sum.inl k)) (fun s o => (f s.1 o, s.2)) (tr1 q)
  | .load a q => .load (fun s => (a s.1, s.2)) (tr1 q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1) (tr1 q₁) (tr1 q₂)
  | .goto f => .goto (fun s => Sum.inl (f s.1))
  | .halt => .goto (fun _ => Sum.inr (Sum.inr false))

def tr2 : TM2.Stmt M2.Γ M2.Λ M2.σ → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | .push k f q => .push (some (Sum.inr k)) (fun s => f s.2.1) (tr2 q)
  | .peek k f q => .peek (some (Sum.inr k)) (fun s o => (s.1, f s.2.1 o, s.2.2)) (tr2 q)
  | .pop k f q => .pop (some (Sum.inr k)) (fun s o => (s.1, f s.2.1 o, s.2.2)) (tr2 q)
  | .load a q => .load (fun s => (s.1, a s.2.1, s.2.2)) (tr2 q)
  | .branch f q₁ q₂ => .branch (fun s => f s.2.1) (tr2 q₁) (tr2 q₂)
  | .goto f => .goto (fun s => Sum.inr (Sum.inl (f s.2.1)))
  | .halt => .halt

variable (M1 M2)

def tA (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀) :
    Option (M2.Γ M2.k₀) → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | none => .goto (fun _ => Sum.inr (Sum.inl M2.main))
  | some d =>
    .pop (some (Sum.inl M1.k₁)) (fun s o => (s.1, s.2.1, o.map φ))
      (.branch (fun s => s.2.2.isSome)
        (.push none (fun s => s.2.2.getD d) (.goto fun _ => Sum.inr (Sum.inr false)))
        (.goto fun _ => Sum.inr (Sum.inr true)))

def tB : Option (M2.Γ M2.k₀) → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | none => .goto (fun _ => Sum.inr (Sum.inl M2.main))
  | some d =>
    .pop none (fun s o => (s.1, s.2.1, o))
      (.branch (fun s => s.2.2.isSome)
        (.push (some (Sum.inr M2.k₀)) (fun s => s.2.2.getD d)
          (.goto fun _ => Sum.inr (Sum.inr true)))
        (.goto fun _ => Sum.inr (Sum.inl M2.main)))

def prog (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀) (d : Option (M2.Γ M2.k₀)) :
    CΛ M1 M2 → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | Sum.inl l => tr1 (M1.m l)
  | Sum.inr (Sum.inl l) => tr2 (M2.m l)
  | Sum.inr (Sum.inr false) => tA M1 M2 φ d
  | Sum.inr (Sum.inr true) => tB M1 M2 d

def comp (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀) (d : Option (M2.Γ M2.k₀)) : FinTM2 :=
  haveI := M1.kFin
  haveI := M2.kFin
  haveI := M1.ΛFin
  haveI := M2.ΛFin
  haveI := M1.σFin
  haveI := M2.σFin
  haveI := M2.Γk₀Fin
  { K := CK M1 M2
    k₀ := some (Sum.inl M1.k₀)
    k₁ := some (Sum.inr M2.k₁)
    Γ := CΓ M1 M2
    Λ := CΛ M1 M2
    main := Sum.inl M1.main
    σ := Cσ M1 M2
    initialState := (M1.initialState, M2.initialState, none)
    Γk₀Fin := M1.Γk₀Fin
    m := prog M1 M2 φ d }

variable {M1 M2}

def embStk1 (S : ∀ k, List (M1.Γ k)) : ∀ k, List (CΓ M1 M2 k)
  | none => []
  | some (Sum.inl k) => S k
  | some (Sum.inr _) => []

def embStk2 (S : ∀ k, List (M2.Γ k)) : ∀ k, List (CΓ M1 M2 k)
  | none => []
  | some (Sum.inl _) => []
  | some (Sum.inr k) => S k

theorem embStk1_update (S : ∀ k, List (M1.Γ k)) (k : M1.K) (x : List (M1.Γ k)) :
    (embStk1 (Function.update S k x) : ∀ k, List (CΓ M1 M2 k)) =
      Function.update (embStk1 S) (some (Sum.inl k)) x := by
  funext j
  rcases j with _ | j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · by_cases h : j = k
    · subst h
      rw [Function.update_self]
      show Function.update S j x j = x
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show Function.update S k x j = S j
      rw [Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)]; rfl

theorem embStk2_update (S : ∀ k, List (M2.Γ k)) (k : M2.K) (x : List (M2.Γ k)) :
    (embStk2 (Function.update S k x) : ∀ k, List (CΓ M1 M2 k)) =
      Function.update (embStk2 S) (some (Sum.inr k)) x := by
  funext j
  rcases j with _ | j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · by_cases h : j = k
    · subst h
      rw [Function.update_self]
      show Function.update S j x j = x
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show Function.update S k x j = S j
      rw [Function.update_of_ne h]

theorem embStk1_nil :
    (embStk1 (fun _ => []) : ∀ k, List (CΓ M1 M2 k)) = fun _ => [] := by
  funext j; rcases j with _ | j | j <;> rfl

theorem embStk2_nil :
    (embStk2 (fun _ => []) : ∀ k, List (CΓ M1 M2 k)) = fun _ => [] := by
  funext j; rcases j with _ | j | j <;> rfl

def emb1 (w : M2.σ × Option (M2.Γ M2.k₀)) (c : TM2.Cfg M1.Γ M1.Λ M1.σ) :
    TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2) :=
  ⟨some (c.l.elim (Sum.inr (Sum.inr false)) Sum.inl), (c.var, w), embStk1 c.stk⟩

def emb2 (u : M1.σ) (b : Option (M2.Γ M2.k₀)) (c : TM2.Cfg M2.Γ M2.Λ M2.σ) :
    TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2) :=
  ⟨c.l.map (fun l => Sum.inr (Sum.inl l)), (u, c.var, b), embStk2 c.stk⟩

theorem sim1 (w : M2.σ × Option (M2.Γ M2.k₀)) (q : TM2.Stmt M1.Γ M1.Λ M1.σ) (v : M1.σ)
    (S : ∀ k, List (M1.Γ k)) :
    TM2.stepAux (tr1 q) ((v, w) : Cσ M1 M2) (embStk1 S) = emb1 w (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    have := ih v (Function.update S k (f v :: S k))
    rw [embStk1_update] at this
    exact this
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    have := ih (f v (S k).head?) (Function.update S k (S k).tail)
    rw [embStk1_update] at this
    exact this
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [tr1, TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f => rfl
  | halt => rfl

theorem sim2 (u : M1.σ) (b : Option (M2.Γ M2.k₀)) (q : TM2.Stmt M2.Γ M2.Λ M2.σ) (v : M2.σ)
    (S : ∀ k, List (M2.Γ k)) :
    TM2.stepAux (tr2 q) ((u, v, b) : Cσ M1 M2) (embStk2 S) = emb2 u b (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    have := ih v (Function.update S k (f v :: S k))
    rw [embStk2_update] at this
    exact this
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    have := ih (f v (S k).head?) (Function.update S k (S k).tail)
    rw [embStk2_update] at this
    exact this
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [tr2, TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f => rfl
  | halt => rfl

variable (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀) (d : Option (M2.Γ M2.k₀))

theorem step1 (w : M2.σ × Option (M2.Γ M2.k₀)) (c c' : TM2.Cfg M1.Γ M1.Λ M1.σ)
    (h : TM2.step M1.m c = some c') :
    TM2.step (prog M1 M2 φ d) (emb1 w c) = some (emb1 w c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (sim1 w (M1.m l) v S)

theorem step2 (u : M1.σ) (b : Option (M2.Γ M2.k₀)) (c c' : TM2.Cfg M2.Γ M2.Λ M2.σ)
    (h : TM2.step M2.m c = some c') :
    TM2.step (prog M1 M2 φ d) (emb2 u b c) = some (emb2 u b c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (sim2 u b (M2.m l) v S)

def st (l : List (M1.Γ M1.k₁)) (t u : List (M2.Γ M2.k₀)) : ∀ k, List (CΓ M1 M2 k) :=
  Function.update (Function.update (Function.update (fun _ => [])
    (some (Sum.inl M1.k₁)) l) none t) (some (Sum.inr M2.k₀)) u

theorem st_fst (l : List (M1.Γ M1.k₁)) (t u : List (M2.Γ M2.k₀)) :
    (st l t u : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) = l := by
  unfold st
  rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp), Function.update_self]

theorem st_snd (l : List (M1.Γ M1.k₁)) (t u : List (M2.Γ M2.k₀)) :
    (st l t u : ∀ k, List (CΓ M1 M2 k)) none = t := by
  unfold st
  rw [Function.update_of_ne (by simp), Function.update_self]

theorem st_thd (l : List (M1.Γ M1.k₁)) (t u : List (M2.Γ M2.k₀)) :
    (st l t u : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀)) = u := by
  unfold st
  rw [Function.update_self]

theorem st_set_fst (l l' : List (M1.Γ M1.k₁)) (t u : List (M2.Γ M2.k₀)) :
    Function.update (st l t u : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) l' = st l' t u :=
  update3_fst _ (by simp) (by simp) _ _ _ _

theorem st_set_snd (l : List (M1.Γ M1.k₁)) (t t' u : List (M2.Γ M2.k₀)) :
    Function.update (st l t u : ∀ k, List (CΓ M1 M2 k)) none t' = st l t' u :=
  update3_snd _ (by simp) _ _ _ _

theorem st_set_thd (l : List (M1.Γ M1.k₁)) (t u u' : List (M2.Γ M2.k₀)) :
    Function.update (st l t u : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀)) u' = st l t u' :=
  Function.update_idem _ _ _

theorem st_start (l : List (M1.Γ M1.k₁)) :
    (st l [] [] : ∀ k, List (CΓ M1 M2 k)) =
      Function.update (fun _ => [] : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) l := by
  unfold st
  rw [Function.update_eq_self_iff.mpr, Function.update_eq_self_iff.mpr]
  · rw [Function.update_of_ne (by simp)]
  · rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp)]

theorem st_end (u : List (M2.Γ M2.k₀)) :
    (st [] [] u : ∀ k, List (CΓ M1 M2 k)) =
      Function.update (fun _ => [] : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀)) u := by
  unfold st
  congr 1
  rw [Function.update_eq_self_iff.mpr, Function.update_eq_self_iff.mpr]
  · rfl
  · rw [Function.update_of_ne (by simp)]

end PEqualNP.Library.Machines

end

section

namespace PEqualNP.Library.Machines

open Turing

variable {M1 M2 : FinTM2} (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀)

abbrev CCfg (M1 M2 : FinTM2) : Type := TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)

theorem stepA_cons (dd : M2.Γ M2.k₀) (v1 : M1.σ) (v2 : M2.σ) (b : Option (M2.Γ M2.k₀))
    (x : M1.Γ M1.k₁) (l : List (M1.Γ M1.k₁)) (t u : List (M2.Γ M2.k₀)) :
    TM2.step (prog M1 M2 φ (some dd))
        (⟨some (Sum.inr (Sum.inr false)), (v1, v2, b), st (x :: l) t u⟩ : CCfg M1 M2) =
      some ⟨some (Sum.inr (Sum.inr false)), (v1, v2, some (φ x)), st l (φ x :: t) u⟩ := by
  simp only [TM2.step, prog, tA, TM2.stepAux]
  rw [st_fst]
  simp only [List.head?_cons, List.tail_cons, Option.map_some, Option.isSome_some, Bool.cond_true,
    Option.getD_some]
  rw [st_set_fst, st_snd, st_set_snd]

theorem stepA_nil (dd : M2.Γ M2.k₀) (v1 : M1.σ) (v2 : M2.σ) (b : Option (M2.Γ M2.k₀))
    (t u : List (M2.Γ M2.k₀)) :
    TM2.step (prog M1 M2 φ (some dd))
        (⟨some (Sum.inr (Sum.inr false)), (v1, v2, b), st [] t u⟩ : CCfg M1 M2) =
      some ⟨some (Sum.inr (Sum.inr true)), (v1, v2, none), st [] t u⟩ := by
  simp only [TM2.step, prog, tA, TM2.stepAux]
  rw [st_fst]
  simp only [List.head?_nil, List.tail_nil, Option.map_none, Option.isSome_none, Bool.cond_false]
  rw [st_set_fst]

theorem stepB_cons (dd : M2.Γ M2.k₀) (v1 : M1.σ) (v2 : M2.σ) (b : Option (M2.Γ M2.k₀))
    (x : M2.Γ M2.k₀) (t u : List (M2.Γ M2.k₀)) :
    TM2.step (prog M1 M2 φ (some dd))
        (⟨some (Sum.inr (Sum.inr true)), (v1, v2, b), st [] (x :: t) u⟩ : CCfg M1 M2) =
      some ⟨some (Sum.inr (Sum.inr true)), (v1, v2, some x), st [] t (x :: u)⟩ := by
  simp only [TM2.step, prog, tB, TM2.stepAux]
  rw [st_snd]
  simp only [List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, Option.getD_some]
  rw [st_set_snd, st_thd, st_set_thd]

theorem stepB_nil (dd : M2.Γ M2.k₀) (v1 : M1.σ) (v2 : M2.σ) (b : Option (M2.Γ M2.k₀))
    (u : List (M2.Γ M2.k₀)) :
    TM2.step (prog M1 M2 φ (some dd))
        (⟨some (Sum.inr (Sum.inr true)), (v1, v2, b), st [] [] u⟩ : CCfg M1 M2) =
      some ⟨some (Sum.inr (Sum.inl M2.main)), (v1, v2, none), st [] [] u⟩ := by
  simp only [TM2.step, prog, tB, TM2.stepAux]
  rw [st_snd]
  simp only [List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]
  rw [st_set_snd]

theorem loopA (dd : M2.Γ M2.k₀) (v1 : M1.σ) (v2 : M2.σ) (u : List (M2.Γ M2.k₀)) :
    ∀ (l : List (M1.Γ M1.k₁)) (t : List (M2.Γ M2.k₀)) (b : Option (M2.Γ M2.k₀)),
      (flip bind (TM2.step (prog M1 M2 φ (some dd))))^[l.length + 1]
          (some (⟨some (Sum.inr (Sum.inr false)), (v1, v2, b), st l t u⟩ : CCfg M1 M2)) =
        some ⟨some (Sum.inr (Sum.inr true)), (v1, v2, none), st [] ((l.map φ).reverse ++ t) u⟩ := by
  intro l
  induction l with
  | nil => intro t b; exact stepA_nil φ dd v1 v2 b t u
  | cons x l ih =>
    intro t b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (prog M1 M2 φ (some dd)))
        (some (⟨some (Sum.inr (Sum.inr false)), (v1, v2, b), st (x :: l) t u⟩ : CCfg M1 M2)) =
        some ⟨some (Sum.inr (Sum.inr false)), (v1, v2, some (φ x)), st l (φ x :: t) u⟩ :=
      stepA_cons φ dd v1 v2 b x l t u
    rw [e, ih]
    simp

theorem loopB (dd : M2.Γ M2.k₀) (v1 : M1.σ) (v2 : M2.σ) :
    ∀ (t u : List (M2.Γ M2.k₀)) (b : Option (M2.Γ M2.k₀)),
      (flip bind (TM2.step (prog M1 M2 φ (some dd))))^[t.length + 1]
          (some (⟨some (Sum.inr (Sum.inr true)), (v1, v2, b), st [] t u⟩ : CCfg M1 M2)) =
        some ⟨some (Sum.inr (Sum.inl M2.main)), (v1, v2, none), st [] [] (t.reverse ++ u)⟩ := by
  intro t
  induction t with
  | nil => intro u b; exact stepB_nil φ dd v1 v2 b u
  | cons x t ih =>
    intro u b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (prog M1 M2 φ (some dd)))
        (some (⟨some (Sum.inr (Sum.inr true)), (v1, v2, b), st [] (x :: t) u⟩ : CCfg M1 M2)) =
        some ⟨some (Sum.inr (Sum.inr true)), (v1, v2, some x), st [] t (x :: u)⟩ :=
      stepB_cons φ dd v1 v2 b x t u
    rw [e, ih]
    simp

theorem transfer (d : Option (M2.Γ M2.k₀)) (hd : d = none → IsEmpty (M2.Γ M2.k₀))
    (v1 : M1.σ) (v2 : M2.σ) (o : List (M1.Γ M1.k₁)) :
    ∃ n, n ≤ 2 * o.length + 2 ∧
      (flip bind (TM2.step (prog M1 M2 φ d)))^[n]
          (some (⟨some (Sum.inr (Sum.inr false)), (v1, v2, none),
            Function.update (fun _ => [] : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) o⟩ :
            CCfg M1 M2)) =
        some ⟨some (Sum.inr (Sum.inl M2.main)), (v1, v2, none),
          Function.update (fun _ => [] : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀))
            (o.map φ)⟩ := by
  cases d with
  | none =>
    have := hd rfl
    have ho : o = [] := by
      cases o with
      | nil => rfl
      | cons x _ => exact (IsEmpty.false (φ x)).elim
    subst ho
    refine ⟨1, by omega, ?_⟩
    show some _ = some _
    simp only [prog, tA, TM2.stepAux, List.map_nil]
    rw [Function.update_eq_self_iff.mpr rfl, Function.update_eq_self_iff.mpr rfl]
  | some dd =>
    refine ⟨((o.map φ).reverse ++ []).length + 1 + (o.length + 1), by simp; omega, ?_⟩
    rw [Function.iterate_add_apply, ← st_start, loopA, loopB, ← st_end]
    simp

theorem emb1_init (d : Option (M2.Γ M2.k₀)) (i : List (M1.Γ M1.k₀)) :
    emb1 (M2.initialState, none) (initList M1 i) = initList (comp M1 M2 φ d) i := by
  rw [initList_eq]
  refine Eq.trans ?_ (initList_eq (comp M1 M2 φ d) i).symm
  show (⟨_, _, embStk1 _⟩ : CCfg M1 M2) = _
  rw [embStk1_update, embStk1_nil]
  rfl

theorem emb1_halt (w : M2.σ × Option (M2.Γ M2.k₀)) (o : List (M1.Γ M1.k₁)) :
    emb1 w (haltList M1 o) =
      (⟨some (Sum.inr (Sum.inr false)), (M1.initialState, w),
        Function.update (fun _ => [] : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) o⟩ :
        CCfg M1 M2) := by
  rw [haltList_eq]
  show (⟨_, _, embStk1 _⟩ : CCfg M1 M2) = _
  rw [embStk1_update, embStk1_nil]
  rfl

theorem emb2_init (u : M1.σ) (i : List (M2.Γ M2.k₀)) :
    emb2 u none (initList M2 i) =
      (⟨some (Sum.inr (Sum.inl M2.main)), (u, M2.initialState, none),
        Function.update (fun _ => [] : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀)) i⟩ :
        CCfg M1 M2) := by
  rw [initList_eq]
  show (⟨_, _, embStk2 _⟩ : CCfg M1 M2) = _
  rw [embStk2_update, embStk2_nil]
  rfl

theorem emb2_halt (d : Option (M2.Γ M2.k₀)) (o : List (M2.Γ M2.k₁)) :
    emb2 M1.initialState none (haltList M2 o) = haltList (comp M1 M2 φ d) o := by
  rw [haltList_eq]
  refine Eq.trans ?_ (haltList_eq (comp M1 M2 φ d) o).symm
  show (⟨_, _, embStk2 _⟩ : CCfg M1 M2) = _
  rw [embStk2_update, embStk2_nil]
  rfl

theorem comp_run (d : Option (M2.Γ M2.k₀)) (hd : d = none → IsEmpty (M2.Γ M2.k₀))
    (i : List (M1.Γ M1.k₀)) (o1 : List (M1.Γ M1.k₁)) (o2 : List (M2.Γ M2.k₁)) (s1 s2 : ℕ)
    (h1 : (flip bind (TM2.step M1.m))^[s1] (some (initList M1 i)) = some (haltList M1 o1))
    (h2 : (flip bind (TM2.step M2.m))^[s2] (some (initList M2 (o1.map φ))) =
      some (haltList M2 o2)) :
    ∃ n, n ≤ s1 + (2 * o1.length + 2) + s2 ∧ o1.length ≤ i.length + maxPush M1 * s1 ∧
      (flip bind (TM2.step (prog M1 M2 φ d)))^[n] (some (initList (comp M1 M2 φ d) i)) =
        some (haltList (comp M1 M2 φ d) o2) := by
  have p1 := simulate (TM2.step M1.m) (TM2.step (prog M1 M2 φ d))
    (emb1 (M2.initialState, none)) (step1 φ d _) s1 _ _ h1
  rw [emb1_init φ d, emb1_halt] at p1
  obtain ⟨nt, hnt, pt⟩ := transfer φ d hd M1.initialState M2.initialState o1
  have p2 := simulate (TM2.step M2.m) (TM2.step (prog M1 M2 φ d))
    (emb2 M1.initialState none) (step2 φ d _ _) s2 _ _ h2
  rw [emb2_init, emb2_halt φ d] at p2
  refine ⟨s2 + (nt + s1), by omega, ?_, ?_⟩
  · have := run_length M1 M1.k₁ s1 _ _ h1
    rw [haltList_eq, initList_eq] at this
    simp only [Function.update_self] at this
    refine this.trans (Nat.add_le_add_right ?_ _)
    by_cases h : M1.k₁ = M1.k₀
    · rw [h, Function.update_self]
    · rw [Function.update_of_ne h]; simp
  · rw [Function.iterate_add_apply, Function.iterate_add_apply, p1, pt, p2]
    rfl

theorem comp_polyTime {α β γ αΓ βΓ γΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ)
    (ec : γ → List γΓ) (f : α → β) (g : β → γ) (c1 : TM2ComputableInPolyTime ea eb f)
    (c2 : TM2ComputableInPolyTime eb ec g) :
    Nonempty (TM2ComputableInPolyTime ea ec (fun a => g (f a))) := by
  classical
  let φ : c1.tm.Γ c1.tm.k₁ → c2.tm.Γ c2.tm.k₀ :=
    fun x => c2.inputAlphabet.invFun (c1.outputAlphabet x)
  let d : Option (c2.tm.Γ c2.tm.k₀) :=
    if h : Nonempty (c2.tm.Γ c2.tm.k₀) then some (Classical.choice h) else none
  have hd : d = none → IsEmpty (c2.tm.Γ c2.tm.k₀) := by
    intro h
    by_cases hn : Nonempty (c2.tm.Γ c2.tm.k₀)
    · simp [d, hn] at h
    · exact not_nonempty_iff.mp hn
  let T : Polynomial ℕ :=
    c1.time + (Polynomial.C 2 * (Polynomial.X + Polynomial.C (maxPush c1.tm) * c1.time) +
      Polynomial.C 2) +
      c2.time.comp (Polynomial.X + Polynomial.C (maxPush c1.tm) * c1.time)
  have key : ∀ a, ∃ n, n ≤ T.eval (ea a).length ∧
      (flip bind (TM2.step (prog c1.tm c2.tm φ d)))^[n]
          (some (initList (comp c1.tm c2.tm φ d) (List.map c1.inputAlphabet.invFun (ea a)))) =
        some (haltList (comp c1.tm c2.tm φ d)
          (List.map c2.outputAlphabet.invFun (ec (g (f a))))) := by
    intro a
    have r1 := c1.outputsFun a
    have r2 := c2.outputsFun (f a)
    have hφ : (List.map c1.outputAlphabet.invFun (eb (f a))).map φ =
        List.map c2.inputAlphabet.invFun (eb (f a)) := by
      rw [List.map_map]
      refine List.map_congr_left fun y _ => ?_
      show c2.inputAlphabet.invFun (c1.outputAlphabet (c1.outputAlphabet.invFun y)) = _
      exact congrArg _ (c1.outputAlphabet.right_inv y)
    have h2 : (flip bind (TM2.step c2.tm.m))^[r2.steps]
        (some (initList c2.tm ((List.map c1.outputAlphabet.invFun (eb (f a))).map φ))) =
        some (haltList c2.tm (List.map c2.outputAlphabet.invFun (ec (g (f a))))) := by
      rw [hφ]; exact r2.evals_in_steps
    obtain ⟨n, hn, hlen, hrun⟩ := comp_run φ d hd _ _ _ r1.steps r2.steps r1.evals_in_steps h2
    refine ⟨n, hn.trans ?_, hrun⟩
    have b1 := r1.steps_le_m
    have b2 := r2.steps_le_m
    simp only [List.length_map] at hlen
    have hmul : maxPush c1.tm * r1.steps ≤
        maxPush c1.tm * Polynomial.eval (ea a).length c1.time := Nat.mul_le_mul_left _ b1
    have b3 : Polynomial.eval (eb (f a)).length c2.time ≤
        Polynomial.eval ((ea a).length + maxPush c1.tm * Polynomial.eval (ea a).length c1.time)
          c2.time := eval_mono _ (by omega)
    simp only [T, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_comp, List.length_map]
    omega
  exact ⟨{
    tm := comp c1.tm c2.tm φ d
    inputAlphabet := c1.inputAlphabet
    outputAlphabet := c2.outputAlphabet
    time := T
    outputsFun := fun a =>
      ⟨⟨Classical.choose (key a), (Classical.choose_spec (key a)).2⟩,
        (Classical.choose_spec (key a)).1⟩ }⟩

end PEqualNP.Library.Machines

end

section

namespace PEqualNP.Library.Machines

open Turing

variable {Γ₀ Γ₁ : Type}

abbrev FΓ (Γ₀ Γ₁ : Type) : Option Bool → Type
  | some false => Γ₀
  | none => Option Γ₀
  | some true => Γ₁

def fmProg (φ : Γ₀ → Option Γ₁) (d : Option Γ₁) : Bool → TM2.Stmt (FΓ Γ₀ Γ₁) Bool (Option Γ₀)
  | false =>
    .pop (some false) (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push none (fun s => s) (.goto fun _ => false))
        (.goto fun _ => true))
  | true =>
    .pop none (fun _ o => o.join)
      (.branch (fun s => s.isSome)
        (.branch (fun s => (s.bind φ).isSome)
          (match d with
            | some dd => .push (some true) (fun s => (s.bind φ).getD dd) (.goto fun _ => true)
            | none => .goto fun _ => true)
          (.goto fun _ => true))
        .halt)

def fm [Fintype Γ₀] (φ : Γ₀ → Option Γ₁) (d : Option Γ₁) : FinTM2 where
  K := Option Bool
  k₀ := some false
  k₁ := some true
  Γ := FΓ Γ₀ Γ₁
  Λ := Bool
  main := false
  σ := Option Γ₀
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Γ₀)
  m := fmProg φ d

def fst3 (l : List Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) : ∀ k, List (FΓ Γ₀ Γ₁ k) :=
  Function.update (Function.update (Function.update (fun _ => [])
    (some false) l) none t) (some true) u

theorem fst3_fst (l : List Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) :
    fst3 l t u (some false) = l := by
  unfold fst3
  rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp), Function.update_self]

theorem fst3_snd (l : List Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) :
    fst3 l t u none = t := by
  unfold fst3
  rw [Function.update_of_ne (by simp), Function.update_self]

theorem fst3_thd (l : List Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) :
    fst3 l t u (some true) = u := by
  unfold fst3
  rw [Function.update_self]

theorem fst3_set_fst (l l' : List Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) :
    Function.update (fst3 l t u) (some false) l' = fst3 l' t u :=
  update3_fst _ (by simp) (by simp) _ _ _ _

theorem fst3_set_snd (l : List Γ₀) (t t' : List (Option Γ₀)) (u : List Γ₁) :
    Function.update (fst3 l t u) none t' = fst3 l t' u :=
  update3_snd _ (by simp) _ _ _ _

theorem fst3_set_thd (l : List Γ₀) (t : List (Option Γ₀)) (u u' : List Γ₁) :
    Function.update (fst3 l t u) (some true) u' = fst3 l t u' :=
  Function.update_idem _ _ _

theorem fst3_start (l : List Γ₀) :
    (fst3 l [] [] : ∀ k, List (FΓ Γ₀ Γ₁ k)) =
      Function.update (fun _ => [] : ∀ k, List (FΓ Γ₀ Γ₁ k)) (some false) l := by
  unfold fst3
  rw [Function.update_eq_self_iff.mpr, Function.update_eq_self_iff.mpr]
  · rw [Function.update_of_ne (by simp)]
  · rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp)]

theorem fst3_end (u : List Γ₁) :
    (fst3 [] [] u : ∀ k, List (FΓ Γ₀ Γ₁ k)) =
      Function.update (fun _ => [] : ∀ k, List (FΓ Γ₀ Γ₁ k)) (some true) u := by
  unfold fst3
  congr 1
  rw [Function.update_eq_self_iff.mpr, Function.update_eq_self_iff.mpr]
  · rfl
  · rw [Function.update_of_ne (by simp)]

abbrev FCfg (Γ₀ Γ₁ : Type) : Type := TM2.Cfg (FΓ Γ₀ Γ₁) Bool (Option Γ₀)

variable (φ : Γ₀ → Option Γ₁) (d : Option Γ₁)

theorem fmA_cons (b : Option Γ₀) (x : Γ₀) (l : List Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (fmProg φ d) (⟨some false, b, fst3 (x :: l) t u⟩ : FCfg Γ₀ Γ₁) =
      some ⟨some false, some x, fst3 l (some x :: t) u⟩ := by
  simp only [TM2.step, fmProg, TM2.stepAux]
  rw [fst3_fst]
  simp only [List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true]
  rw [fst3_set_fst, fst3_snd, fst3_set_snd]

theorem fmA_nil (b : Option Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (fmProg φ d) (⟨some false, b, fst3 [] t u⟩ : FCfg Γ₀ Γ₁) =
      some ⟨some true, none, fst3 [] t u⟩ := by
  simp only [TM2.step, fmProg, TM2.stepAux]
  rw [fst3_fst]
  simp only [List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]
  rw [fst3_set_fst]

theorem fmB_cons (hd : d = none → ∀ x, φ x = none) (b : Option Γ₀) (x : Γ₀)
    (t : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (fmProg φ d) (⟨some true, b, fst3 [] (some x :: t) u⟩ : FCfg Γ₀ Γ₁) =
      some ⟨some true, some x, fst3 [] t ((φ x).toList ++ u)⟩ := by
  simp only [TM2.step, fmProg, TM2.stepAux]
  rw [fst3_snd]
  simp only [List.head?_cons, List.tail_cons, Option.join_some, Option.isSome_some,
    Bool.cond_true, Option.bind_some]
  rw [fst3_set_snd]
  cases hφ : φ x with
  | none => simp
  | some y =>
    cases d with
    | none => rw [hd rfl x] at hφ; exact absurd hφ (by simp)
    | some dd =>
      simp only [Option.isSome_some, Bool.cond_true, TM2.stepAux,
        Option.toList_some, List.singleton_append]
      rw [fst3_thd, fst3_set_thd]
      simp [hφ]

theorem fmB_nil (b : Option Γ₀) (u : List Γ₁) :
    TM2.step (fmProg φ d) (⟨some true, b, fst3 [] [] u⟩ : FCfg Γ₀ Γ₁) =
      some ⟨none, none, fst3 [] [] u⟩ := by
  simp only [TM2.step, fmProg, TM2.stepAux]
  rw [fst3_snd]
  simp only [List.head?_nil, List.tail_nil, Option.join_none, Option.isSome_none,
    Bool.cond_false]
  rw [fst3_set_snd]

theorem fmLoopA (u : List Γ₁) :
    ∀ (l : List Γ₀) (t : List (Option Γ₀)) (b : Option Γ₀),
      (flip bind (TM2.step (fmProg φ d)))^[l.length + 1]
          (some (⟨some false, b, fst3 l t u⟩ : FCfg Γ₀ Γ₁)) =
        some ⟨some true, none, fst3 [] (l.reverse.map some ++ t) u⟩ := by
  intro l
  induction l with
  | nil => intro t b; exact fmA_nil φ d b t u
  | cons x l ih =>
    intro t b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (fmProg φ d))
        (some (⟨some false, b, fst3 (x :: l) t u⟩ : FCfg Γ₀ Γ₁)) =
        some ⟨some false, some x, fst3 l (some x :: t) u⟩ := fmA_cons φ d b x l t u
    rw [e, ih]
    simp

theorem fmLoopB (hd : d = none → ∀ x, φ x = none) :
    ∀ (t : List Γ₀) (u : List Γ₁) (b : Option Γ₀),
      (flip bind (TM2.step (fmProg φ d)))^[t.length + 1]
          (some (⟨some true, b, fst3 [] (t.map some) u⟩ : FCfg Γ₀ Γ₁)) =
        some ⟨none, none, fst3 [] [] ((t.filterMap φ).reverse ++ u)⟩ := by
  intro t
  induction t with
  | nil => intro u b; exact fmB_nil φ d b u
  | cons x t ih =>
    intro u b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (fmProg φ d))
        (some (⟨some true, b, fst3 [] ((x :: t).map some) u⟩ : FCfg Γ₀ Γ₁)) =
        some ⟨some true, some x, fst3 [] (t.map some) ((φ x).toList ++ u)⟩ :=
      fmB_cons φ d hd b x (t.map some) u
    rw [e, ih]
    cases hφ : φ x <;> simp [hφ]

theorem fm_run [Fintype Γ₀] (hd : d = none → ∀ x, φ x = none) (l : List Γ₀) :
    (flip bind (TM2.step (fmProg φ d)))^[l.length + 1 + (l.length + 1)]
        (some (initList (fm φ d) l)) = some (haltList (fm φ d) (l.filterMap φ)) := by
  refine (congrArg (fun c => (flip bind (TM2.step (fmProg φ d)))^[l.length + 1 + (l.length + 1)]
    (some c)) (initList_eq (fm φ d) l)).trans
    (Eq.trans ?_ (congrArg some (haltList_eq (fm φ d) (l.filterMap φ))).symm)
  show (flip bind (TM2.step (fmProg φ d)))^[l.length + 1 + (l.length + 1)]
    (some (⟨some false, none, Function.update (fun _ => []) (some false) l⟩ : FCfg Γ₀ Γ₁)) =
    some (⟨none, none, Function.update (fun _ => []) (some true) (l.filterMap φ)⟩ : FCfg Γ₀ Γ₁)
  rw [Function.iterate_add_apply, ← fst3_start, fmLoopA, ← fst3_end]
  have := fmLoopB φ d hd l.reverse [] none
  rw [List.length_reverse] at this
  simpa [List.filterMap_reverse] using this

theorem filterMap_polyTime {α β αΓ βΓ : Type} [Fintype αΓ] (ea : α → List αΓ)
    (eb : β → List βΓ) (f : α → β) (φ : αΓ → Option βΓ)
    (h : ∀ a, eb (f a) = (ea a).filterMap φ) :
    Nonempty (TM2ComputableInPolyTime ea eb f) := by
  classical
  let d : Option βΓ := if h : Nonempty βΓ then some (Classical.choice h) else none
  have hd : d = none → ∀ x, φ x = none := by
    intro hdn x
    by_cases hn : Nonempty βΓ
    · simp [d, hn] at hdn
    · cases hφ : φ x with
      | none => rfl
      | some y => exact absurd ⟨y⟩ hn
  exact ⟨{
    tm := fm φ d
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.C 2 * Polynomial.X + Polynomial.C 2
    outputsFun := fun a =>
      { steps := (ea a).length + 1 + ((ea a).length + 1)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have := fm_run φ d hd (ea a)
          exact (congrArg (fun l => (flip bind (TM2.step (fmProg φ d)))^[(ea a).length + 1 +
            ((ea a).length + 1)] (some (initList (fm φ d) l))) (hm αΓ (ea a))).trans
            (this.trans (congrArg (fun l => some (haltList (fm φ d) l)) ((h a).symm.trans (hm βΓ (eb (f a))).symm)))
        steps_le_m := by
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X]
          omega } }⟩

end PEqualNP.Library.Machines

end

section

namespace PEqualNP.Library.Machines

open Turing

inductive TPK : Type
  | inp | t1 | t2 | t3 | out
  deriving DecidableEq

instance : Fintype TPK :=
  Fintype.ofList [.inp, .t1, .t2, .t3, .out] (fun x => by cases x <;> simp)

inductive TPL : Type
  | a | b | c | e
  deriving DecidableEq

instance : Fintype TPL :=
  Fintype.ofList [.a, .b, .c, .e] (fun x => by cases x <;> simp)

variable {Γ₀ Γ₁ : Type}

abbrev TPΓ (Γ₀ Γ₁ : Type) : TPK → Type
  | .inp => Γ₀
  | .t1 => Option Γ₀
  | .t2 => Option Γ₀
  | .t3 => Option Γ₀
  | .out => Γ₁

def tpWrite (φ : Γ₀ → Option Γ₁) (d : Option Γ₁) (lbl : TPL) :
    TM2.Stmt (TPΓ Γ₀ Γ₁) TPL (Option Γ₀) :=
  .branch (fun s => (s.bind φ).isSome)
    (match d with
      | some dd => .push .out (fun s => (s.bind φ).getD dd) (.goto fun _ => lbl)
      | none => .goto fun _ => lbl)
    (.goto fun _ => lbl)

def tpProg (φ₁ φ₂ : Γ₀ → Option Γ₁) (d : Option Γ₁) :
    TPL → TM2.Stmt (TPΓ Γ₀ Γ₁) TPL (Option Γ₀)
  | .a =>
    .pop .inp (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push .t1 (fun s => s) (.goto fun _ => .a))
        (.goto fun _ => .b))
  | .b =>
    .pop .t1 (fun _ o => o.join)
      (.branch (fun s => s.isSome)
        (.push .t2 (fun s => s) (tpWrite φ₂ d .b))
        (.goto fun _ => .c))
  | .c =>
    .pop .t2 (fun _ o => o.join)
      (.branch (fun s => s.isSome)
        (.push .t3 (fun s => s) (.goto fun _ => .c))
        (.goto fun _ => .e))
  | .e =>
    .pop .t3 (fun _ o => o.join)
      (.branch (fun s => s.isSome)
        (tpWrite φ₁ d .e)
        .halt)

def tp [Fintype Γ₀] (φ₁ φ₂ : Γ₀ → Option Γ₁) (d : Option Γ₁) : FinTM2 where
  K := TPK
  k₀ := .inp
  k₁ := .out
  Γ := TPΓ Γ₀ Γ₁
  Λ := TPL
  main := .a
  σ := Option Γ₀
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Γ₀)
  m := tpProg φ₁ φ₂ d

def st5 (l : List Γ₀) (a b c : List (Option Γ₀)) (u : List Γ₁) : ∀ k, List (TPΓ Γ₀ Γ₁ k)
  | .inp => l
  | .t1 => a
  | .t2 => b
  | .t3 => c
  | .out => u

theorem st5_set_inp (l l' : List Γ₀) (a b c : List (Option Γ₀)) (u : List Γ₁) :
    Function.update (st5 l a b c u) .inp l' = st5 l' a b c u := by
  funext k; cases k <;> simp [st5]

theorem st5_set_t1 (l : List Γ₀) (a a' b c : List (Option Γ₀)) (u : List Γ₁) :
    Function.update (st5 l a b c u) .t1 a' = st5 l a' b c u := by
  funext k; cases k <;> simp [st5]

theorem st5_set_t2 (l : List Γ₀) (a b b' c : List (Option Γ₀)) (u : List Γ₁) :
    Function.update (st5 l a b c u) .t2 b' = st5 l a b' c u := by
  funext k; cases k <;> simp [st5]

theorem st5_set_t3 (l : List Γ₀) (a b c c' : List (Option Γ₀)) (u : List Γ₁) :
    Function.update (st5 l a b c u) .t3 c' = st5 l a b c' u := by
  funext k; cases k <;> simp [st5]

theorem st5_set_out (l : List Γ₀) (a b c : List (Option Γ₀)) (u u' : List Γ₁) :
    Function.update (st5 l a b c u) .out u' = st5 l a b c u' := by
  funext k; cases k <;> simp [st5]

theorem st5_start (l : List Γ₀) :
    (st5 l [] [] [] [] : ∀ k, List (TPΓ Γ₀ Γ₁ k)) =
      Function.update (fun _ => [] : ∀ k, List (TPΓ Γ₀ Γ₁ k)) .inp l := by
  funext k; cases k <;> simp [st5]

theorem st5_end (u : List Γ₁) :
    (st5 [] [] [] [] u : ∀ k, List (TPΓ Γ₀ Γ₁ k)) =
      Function.update (fun _ => [] : ∀ k, List (TPΓ Γ₀ Γ₁ k)) .out u := by
  funext k; cases k <;> simp [st5]

abbrev TPCfg (Γ₀ Γ₁ : Type) : Type := TM2.Cfg (TPΓ Γ₀ Γ₁) TPL (Option Γ₀)

variable (φ₁ φ₂ : Γ₀ → Option Γ₁) (d : Option Γ₁)

theorem tpA_cons (s : Option Γ₀) (x : Γ₀) (l : List Γ₀) (a b c : List (Option Γ₀))
    (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .a, s, st5 (x :: l) a b c u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨some .a, some x, st5 l (some x :: a) b c u⟩ := by
  simp [TM2.step, tpProg, TM2.stepAux, st5, st5_set_inp, st5_set_t1]

theorem tpA_nil (s : Option Γ₀) (a b c : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .a, s, st5 [] a b c u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨some .b, none, st5 [] a b c u⟩ := by
  simp [TM2.step, tpProg, TM2.stepAux, st5, st5_set_inp]

theorem tpB_cons (hd : d = none → ∀ x, φ₂ x = none) (s : Option Γ₀) (x : Γ₀)
    (a b c : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .b, s, st5 [] (some x :: a) b c u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨some .b, some x, st5 [] a (some x :: b) c ((φ₂ x).toList ++ u)⟩ := by
  cases hφ : φ₂ x with
  | none =>
    cases d <;>
      simp [TM2.step, tpProg, tpWrite, TM2.stepAux, st5, st5_set_t1, st5_set_t2, hφ]
  | some y =>
    cases d with
    | none => rw [hd rfl x] at hφ; exact absurd hφ (by simp)
    | some dd =>
      simp [TM2.step, tpProg, tpWrite, TM2.stepAux, st5, st5_set_t1, st5_set_t2,
        st5_set_out, hφ]

theorem tpB_nil (s : Option Γ₀) (b c : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .b, s, st5 [] [] b c u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨some .c, none, st5 [] [] b c u⟩ := by
  simp [TM2.step, tpProg, TM2.stepAux, st5, st5_set_t1]

theorem tpC_cons (s : Option Γ₀) (x : Γ₀) (b c : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .c, s, st5 [] [] (some x :: b) c u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨some .c, some x, st5 [] [] b (some x :: c) u⟩ := by
  simp [TM2.step, tpProg, TM2.stepAux, st5, st5_set_t2, st5_set_t3]

theorem tpC_nil (s : Option Γ₀) (c : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .c, s, st5 [] [] [] c u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨some .e, none, st5 [] [] [] c u⟩ := by
  simp [TM2.step, tpProg, TM2.stepAux, st5, st5_set_t2]

theorem tpE_cons (hd : d = none → ∀ x, φ₁ x = none) (s : Option Γ₀) (x : Γ₀)
    (c : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .e, s, st5 [] [] [] (some x :: c) u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨some .e, some x, st5 [] [] [] c ((φ₁ x).toList ++ u)⟩ := by
  cases hφ : φ₁ x with
  | none =>
    cases d <;>
      simp [TM2.step, tpProg, tpWrite, TM2.stepAux, st5, st5_set_t3, hφ]
  | some y =>
    cases d with
    | none => rw [hd rfl x] at hφ; exact absurd hφ (by simp)
    | some dd =>
      simp [TM2.step, tpProg, tpWrite, TM2.stepAux, st5, st5_set_t3, st5_set_out, hφ]

theorem tpE_nil (s : Option Γ₀) (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .e, s, st5 [] [] [] [] u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨none, none, st5 [] [] [] [] u⟩ := by
  simp [TM2.step, tpProg, TM2.stepAux, st5, st5_set_t3]

theorem tpLoopA (b c : List (Option Γ₀)) (u : List Γ₁) :
    ∀ (l : List Γ₀) (a : List (Option Γ₀)) (s : Option Γ₀),
      (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1]
          (some (⟨some .a, s, st5 l a b c u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨some .b, none, st5 [] (l.reverse.map some ++ a) b c u⟩ := by
  intro l
  induction l with
  | nil => intro a s; exact tpA_nil φ₁ φ₂ d s a b c u
  | cons x l ih =>
    intro a s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (tpProg φ₁ φ₂ d))
        (some (⟨some .a, s, st5 (x :: l) a b c u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨some .a, some x, st5 l (some x :: a) b c u⟩ := tpA_cons φ₁ φ₂ d s x l a b c u
    rw [e, ih]
    simp

theorem tpLoopB (hd : d = none → ∀ x, φ₂ x = none) (c : List (Option Γ₀)) :
    ∀ (t : List Γ₀) (b : List (Option Γ₀)) (u : List Γ₁) (s : Option Γ₀),
      (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[t.length + 1]
          (some (⟨some .b, s, st5 [] (t.map some) b c u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨some .c, none,
          st5 [] [] (t.reverse.map some ++ b) c ((t.filterMap φ₂).reverse ++ u)⟩ := by
  intro t
  induction t with
  | nil => intro b u s; exact tpB_nil φ₁ φ₂ d s b c u
  | cons x t ih =>
    intro b u s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (tpProg φ₁ φ₂ d))
        (some (⟨some .b, s, st5 [] ((x :: t).map some) b c u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨some .b, some x, st5 [] (t.map some) (some x :: b) c ((φ₂ x).toList ++ u)⟩ :=
      tpB_cons φ₁ φ₂ d hd s x (t.map some) b c u
    rw [e, ih]
    cases hφ : φ₂ x <;> simp [hφ]

theorem tpLoopC (u : List Γ₁) :
    ∀ (t : List Γ₀) (c : List (Option Γ₀)) (s : Option Γ₀),
      (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[t.length + 1]
          (some (⟨some .c, s, st5 [] [] (t.map some) c u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨some .e, none, st5 [] [] [] (t.reverse.map some ++ c) u⟩ := by
  intro t
  induction t with
  | nil => intro c s; exact tpC_nil φ₁ φ₂ d s c u
  | cons x t ih =>
    intro c s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (tpProg φ₁ φ₂ d))
        (some (⟨some .c, s, st5 [] [] ((x :: t).map some) c u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨some .c, some x, st5 [] [] (t.map some) (some x :: c) u⟩ :=
      tpC_cons φ₁ φ₂ d s x (t.map some) c u
    rw [e, ih]
    simp

theorem tpLoopE (hd : d = none → ∀ x, φ₁ x = none) :
    ∀ (t : List Γ₀) (u : List Γ₁) (s : Option Γ₀),
      (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[t.length + 1]
          (some (⟨some .e, s, st5 [] [] [] (t.map some) u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨none, none, st5 [] [] [] [] ((t.filterMap φ₁).reverse ++ u)⟩ := by
  intro t
  induction t with
  | nil => intro u s; exact tpE_nil φ₁ φ₂ d s u
  | cons x t ih =>
    intro u s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (tpProg φ₁ φ₂ d))
        (some (⟨some .e, s, st5 [] [] [] ((x :: t).map some) u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨some .e, some x, st5 [] [] [] (t.map some) ((φ₁ x).toList ++ u)⟩ :=
      tpE_cons φ₁ φ₂ d hd s x (t.map some) u
    rw [e, ih]
    cases hφ : φ₁ x <;> simp [hφ]

theorem tp_run [Fintype Γ₀] (hd₁ : d = none → ∀ x, φ₁ x = none)
    (hd₂ : d = none → ∀ x, φ₂ x = none) (l : List Γ₀) :
    (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1 + (l.length + 1) + (l.length + 1) +
        (l.length + 1)]
        (some (initList (tp φ₁ φ₂ d) l)) =
      some (haltList (tp φ₁ φ₂ d) (l.filterMap φ₁ ++ l.filterMap φ₂)) := by
  refine (congrArg (fun c => (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1 +
    (l.length + 1) + (l.length + 1) + (l.length + 1)]
    (some c)) (initList_eq (tp φ₁ φ₂ d) l)).trans
    (Eq.trans ?_ (congrArg some
      (haltList_eq (tp φ₁ φ₂ d) (l.filterMap φ₁ ++ l.filterMap φ₂))).symm)
  show (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1 + (l.length + 1) + (l.length + 1) +
      (l.length + 1)]
    (some (⟨some .a, none, Function.update (fun _ => []) .inp l⟩ : TPCfg Γ₀ Γ₁)) =
    some (⟨none, none, Function.update (fun _ => []) .out
      (l.filterMap φ₁ ++ l.filterMap φ₂)⟩ : TPCfg Γ₀ Γ₁)
  have hA : (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1]
      (some (⟨some .a, none, st5 l [] [] [] []⟩ : TPCfg Γ₀ Γ₁)) =
      some ⟨some .b, none, st5 [] (l.reverse.map some) [] [] []⟩ := by
    simpa using tpLoopA φ₁ φ₂ d [] [] [] l [] none
  have hB : (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1]
      (some (⟨some .b, none, st5 [] (l.reverse.map some) [] [] []⟩ : TPCfg Γ₀ Γ₁)) =
      some ⟨some .c, none, st5 [] [] (l.map some) [] (l.filterMap φ₂)⟩ := by
    have := tpLoopB φ₁ φ₂ d hd₂ [] l.reverse [] [] none
    rw [List.length_reverse] at this
    simpa [List.filterMap_reverse] using this
  have hC : (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1]
      (some (⟨some .c, none, st5 [] [] (l.map some) [] (l.filterMap φ₂)⟩ : TPCfg Γ₀ Γ₁)) =
      some ⟨some .e, none, st5 [] [] [] (l.reverse.map some) (l.filterMap φ₂)⟩ := by
    simpa using tpLoopC φ₁ φ₂ d (l.filterMap φ₂) l [] none
  have hE : (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1]
      (some (⟨some .e, none, st5 [] [] [] (l.reverse.map some) (l.filterMap φ₂)⟩ :
        TPCfg Γ₀ Γ₁)) =
      some ⟨none, none, st5 [] [] [] [] (l.filterMap φ₁ ++ l.filterMap φ₂)⟩ := by
    have := tpLoopE φ₁ φ₂ d hd₁ l.reverse (l.filterMap φ₂) none
    rw [List.length_reverse] at this
    simpa [List.filterMap_reverse] using this
  rw [Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_add_apply,
    ← st5_start, hA, hB, hC, hE, st5_end]

theorem twoPass_polyTime {α β αΓ βΓ : Type} [Fintype αΓ] (ea : α → List αΓ)
    (eb : β → List βΓ) (f : α → β) (φ₁ φ₂ : αΓ → Option βΓ)
    (h : ∀ a, eb (f a) = (ea a).filterMap φ₁ ++ (ea a).filterMap φ₂) :
    Nonempty (Turing.TM2ComputableInPolyTime ea eb f) := by
  classical
  let d : Option βΓ := if h : Nonempty βΓ then some (Classical.choice h) else none
  have hd : ∀ φ : αΓ → Option βΓ, d = none → ∀ x, φ x = none := by
    intro φ hdn x
    by_cases hn : Nonempty βΓ
    · simp [d, hn] at hdn
    · cases hφ : φ x with
      | none => rfl
      | some y => exact absurd ⟨y⟩ hn
  exact ⟨{
    tm := tp φ₁ φ₂ d
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.C 4 * Polynomial.X + Polynomial.C 4
    outputsFun := fun a =>
      { steps := (ea a).length + 1 + ((ea a).length + 1) + ((ea a).length + 1) +
          ((ea a).length + 1)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have := tp_run φ₁ φ₂ d (hd φ₁) (hd φ₂) (ea a)
          exact (congrArg (fun l => (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[(ea a).length + 1 +
            ((ea a).length + 1) + ((ea a).length + 1) + ((ea a).length + 1)]
            (some (initList (tp φ₁ φ₂ d) l))) (hm αΓ (ea a))).trans
            (this.trans (congrArg (fun l => some (haltList (tp φ₁ φ₂ d) l))
              ((h a).symm.trans (hm βΓ (eb (f a))).symm)))
        steps_le_m := by
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X]
          omega } }⟩

end PEqualNP.Library.Machines

end

section

namespace PEqualNP.Library.Machines

open Turing

inductive FX
  | I | W | T | O
  deriving DecidableEq

instance : Fintype FX :=
  Fintype.ofList [FX.I, FX.W, FX.T, FX.O] (fun x => by cases x <;> simp)

inductive FL
  | l1 | l2 | l3 | l4 | l5
  deriving DecidableEq

instance : Fintype FL :=
  Fintype.ofList [FL.l1, FL.l2, FL.l3, FL.l4, FL.l5] (fun x => by cases x <;> simp)

variable (M : FinTM2)

abbrev FstΓ : M.K ⊕ FX → Type
  | Sum.inl k => M.Γ k
  | Sum.inr FX.I => Bool ⊕ Bool
  | Sum.inr FX.W => Bool
  | Sum.inr FX.T => Bool
  | Sum.inr FX.O => Bool ⊕ Bool

abbrev FstΛ : Type := M.Λ ⊕ FL

abbrev Fstσ : Type := M.σ × Option (Bool ⊕ Bool)

def bit : Option (Bool ⊕ Bool) → Bool
  | none => false
  | some (Sum.inl b) => b
  | some (Sum.inr b) => b

def isFst : Option (Bool ⊕ Bool) → Bool
  | some (Sum.inl _) => true
  | _ => false

variable {M}

def trF : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (FstΓ M) (FstΛ M) (Fstσ M)
  | .push k f q => .push (Sum.inl k) (fun s => f s.1) (trF q)
  | .peek k f q => .peek (Sum.inl k) (fun s o => (f s.1 o, s.2)) (trF q)
  | .pop k f q => .pop (Sum.inl k) (fun s o => (f s.1 o, s.2)) (trF q)
  | .load a q => .load (fun s => (a s.1, s.2)) (trF q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1) (trF q₁) (trF q₂)
  | .goto f => .goto (fun s => Sum.inl (f s.1))
  | .halt => .goto (fun _ => Sum.inr FL.l3)

variable (M)

def firstProg (e₀ : Bool → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → Bool) :
    FstΛ M → TM2.Stmt (FstΓ M) (FstΛ M) (Fstσ M)
  | Sum.inl l => trF (M.m l)
  | Sum.inr FL.l1 =>
    .pop (Sum.inr FX.I) (fun s o => (s.1, o))
      (.branch (fun s => s.2.isSome)
        (.branch (fun s => isFst s.2)
          (.push (Sum.inr FX.T) (fun s => bit s.2) (.goto fun _ => Sum.inr FL.l1))
          (.push (Sum.inr FX.W) (fun s => bit s.2) (.goto fun _ => Sum.inr FL.l1)))
        (.goto fun _ => Sum.inr FL.l2))
  | Sum.inr FL.l2 =>
    .pop (Sum.inr FX.T) (fun s o => (s.1, o.map Sum.inl))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inl M.k₀) (fun s => e₀ (bit s.2)) (.goto fun _ => Sum.inr FL.l2))
        (.goto fun _ => Sum.inl M.main))
  | Sum.inr FL.l3 =>
    .pop (Sum.inr FX.W) (fun s o => (s.1, o.map Sum.inl))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr FX.O) (fun s => Sum.inr (bit s.2)) (.goto fun _ => Sum.inr FL.l3))
        (.goto fun _ => Sum.inr FL.l4))
  | Sum.inr FL.l4 =>
    .pop (Sum.inl M.k₁) (fun s o => (s.1, o.map fun y => Sum.inl (e₁ y)))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr FX.T) (fun s => bit s.2) (.goto fun _ => Sum.inr FL.l4))
        (.goto fun _ => Sum.inr FL.l5))
  | Sum.inr FL.l5 =>
    .pop (Sum.inr FX.T) (fun s o => (s.1, o.map Sum.inl))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr FX.O) (fun s => Sum.inl (bit s.2)) (.goto fun _ => Sum.inr FL.l5))
        .halt)

def firstM (e₀ : Bool → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → Bool) : FinTM2 :=
  haveI := M.kFin
  haveI := M.ΛFin
  haveI := M.σFin
  { K := M.K ⊕ FX
    k₀ := Sum.inr FX.I
    k₁ := Sum.inr FX.O
    Γ := FstΓ M
    Λ := FstΛ M
    main := Sum.inr FL.l1
    σ := Fstσ M
    initialState := (M.initialState, none)
    Γk₀Fin := inferInstanceAs (Fintype (Bool ⊕ Bool))
    m := firstProg M e₀ e₁ }

variable {M}

def fstk (S : ∀ k, List (M.Γ k)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
    (o : List (Bool ⊕ Bool)) : ∀ k, List (FstΓ M k)
  | Sum.inl k => S k
  | Sum.inr FX.I => i
  | Sum.inr FX.W => w
  | Sum.inr FX.T => t
  | Sum.inr FX.O => o

section fstk

variable (S : ∀ k, List (M.Γ k)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
  (o : List (Bool ⊕ Bool))

theorem fstk_set_M (k : M.K) (x : List (M.Γ k)) :
    Function.update (fstk S i w t o) (Sum.inl k) x = fstk (Function.update S k x) i w t o := by
  funext j
  rcases j with j | j
  · by_cases h : j = k
    · subst h
      rw [Function.update_self]
      show x = Function.update S j x j
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show S j = Function.update S k x j
      rw [Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)]; cases j <;> rfl

theorem fstk_set_I (i' : List (Bool ⊕ Bool)) :
    Function.update (fstk S i w t o) (Sum.inr FX.I) i' = fstk S i' w t o := by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

theorem fstk_set_W (w' : List Bool) :
    Function.update (fstk S i w t o) (Sum.inr FX.W) w' = fstk S i w' t o := by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

theorem fstk_set_T (t' : List Bool) :
    Function.update (fstk S i w t o) (Sum.inr FX.T) t' = fstk S i w t' o := by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

theorem fstk_set_O (o' : List (Bool ⊕ Bool)) :
    Function.update (fstk S i w t o) (Sum.inr FX.O) o' = fstk S i w t o' := by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl

end fstk

abbrev FCfg1 (M : FinTM2) : Type := TM2.Cfg (FstΓ M) (FstΛ M) (Fstσ M)

def embF (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
    (o : List (Bool ⊕ Bool)) (c : TM2.Cfg M.Γ M.Λ M.σ) : FCfg1 M :=
  ⟨some (c.l.elim (Sum.inr FL.l3) Sum.inl), (c.var, b), fstk c.stk i w t o⟩

theorem simF (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
    (o : List (Bool ⊕ Bool)) (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ) (S : ∀ k, List (M.Γ k)) :
    TM2.stepAux (trF q) ((v, b) : Fstσ M) (fstk S i w t o) =
      embF b i w t o (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    have := ih v (Function.update S k (f v :: S k))
    rw [← fstk_set_M] at this
    exact this
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    have := ih (f v (S k).head?) (Function.update S k (S k).tail)
    rw [← fstk_set_M] at this
    exact this
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [trF, TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f => rfl
  | halt => rfl

theorem stepF (e₀ : Bool → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → Bool) (b : Option (Bool ⊕ Bool))
    (i : List (Bool ⊕ Bool)) (w t : List Bool) (o : List (Bool ⊕ Bool))
    (c c' : TM2.Cfg M.Γ M.Λ M.σ) (h : TM2.step M.m c = some c') :
    TM2.step (firstProg M e₀ e₁) (embF b i w t o c) = some (embF b i w t o c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (simF b i w t o (M.m l) v S)

end PEqualNP.Library.Machines

end

section

namespace PEqualNP.Library.Machines

open Turing

theorem iter_trans {σ : Type} (f : σ → Option σ) {a b : ℕ} {x y z : σ}
    (h₁ : (flip bind f)^[a] (some x) = some y) (h₂ : (flip bind f)^[b] (some y) = some z) :
    (flip bind f)^[b + a] (some x) = some z := by
  rw [Function.iterate_add_apply, h₁, h₂]

variable {M : FinTM2} (e₀ : Bool → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → Bool)

section fstk
variable (S : ∀ k, List (M.Γ k)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
  (o : List (Bool ⊕ Bool))
@[simp] theorem fstk_M (k : M.K) : fstk S i w t o (Sum.inl k) = S k := rfl
@[simp] theorem fstk_I : fstk S i w t o (Sum.inr FX.I) = i := rfl
@[simp] theorem fstk_W : fstk S i w t o (Sum.inr FX.W) = w := rfl
@[simp] theorem fstk_T : fstk S i w t o (Sum.inr FX.T) = t := rfl
@[simp] theorem fstk_O : fstk S i w t o (Sum.inr FX.O) = o := rfl
end fstk

variable (v : M.σ) (S : ∀ k, List (M.Γ k)) (w : List Bool) (o : List (Bool ⊕ Bool))

theorem f1_inl (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool)) (t : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l1), (v, b), fstk S (Sum.inl a :: i) w t o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr FL.l1), (v, some (Sum.inl a)), fstk S i w (a :: t) o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_I, fstk_set_T, isFst, bit]

theorem f1_inr (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool)) (t : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l1), (v, b), fstk S (Sum.inr a :: i) w t o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr FL.l1), (v, some (Sum.inr a)), fstk S i (a :: w) t o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_I, fstk_set_W, isFst, bit]

theorem f1_nil (b : Option (Bool ⊕ Bool)) (t : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l1), (v, b), fstk S [] w t o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr FL.l2), (v, none), fstk S [] w t o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_I]

theorem loop1 : ∀ (i : List (Bool ⊕ Bool)) (w t : List Bool) (b : Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (firstProg M e₀ e₁)))^[i.length + 1]
        (some (⟨some (Sum.inr FL.l1), (v, b), fstk S i w t o⟩ : FCfg1 M)) =
      some ⟨some (Sum.inr FL.l2), (v, none),
        fstk S [] ((i.filterMap Sum.getRight?).reverse ++ w)
          ((i.filterMap Sum.getLeft?).reverse ++ t) o⟩ := by
  intro i
  induction i with
  | nil => intro w t b; exact f1_nil e₀ e₁ v S w o b t
  | cons x i ih =>
    intro w t b
    rw [List.length_cons, Function.iterate_succ_apply]
    cases x with
    | inl a =>
      have e : flip bind (TM2.step (firstProg M e₀ e₁))
          (some (⟨some (Sum.inr FL.l1), (v, b), fstk S (Sum.inl a :: i) w t o⟩ : FCfg1 M)) =
          some ⟨some (Sum.inr FL.l1), (v, some (Sum.inl a)), fstk S i w (a :: t) o⟩ :=
        f1_inl e₀ e₁ v S w o b a i t
      rw [e, ih]; simp [List.filterMap_cons]
    | inr a =>
      have e : flip bind (TM2.step (firstProg M e₀ e₁))
          (some (⟨some (Sum.inr FL.l1), (v, b), fstk S (Sum.inr a :: i) w t o⟩ : FCfg1 M)) =
          some ⟨some (Sum.inr FL.l1), (v, some (Sum.inr a)), fstk S i (a :: w) t o⟩ :=
        f1_inr e₀ e₁ v S w o b a i t
      rw [e, ih]; simp [List.filterMap_cons]

theorem f2_cons (b : Option (Bool ⊕ Bool)) (a : Bool) (t : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l2), (v, b), fstk S [] w (a :: t) o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr FL.l2), (v, some (Sum.inl a)),
        fstk (Function.update S M.k₀ (e₀ a :: S M.k₀)) [] w t o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_T, fstk_set_M, bit]

theorem f2_nil (b : Option (Bool ⊕ Bool)) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l2), (v, b), fstk S [] w [] o⟩ : FCfg1 M) =
      some ⟨some (Sum.inl M.main), (v, none), fstk S [] w [] o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_T]

theorem loop2 : ∀ (t : List Bool) (S : ∀ k, List (M.Γ k)) (b : Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (firstProg M e₀ e₁)))^[t.length + 1]
        (some (⟨some (Sum.inr FL.l2), (v, b), fstk S [] w t o⟩ : FCfg1 M)) =
      some ⟨some (Sum.inl M.main), (v, none),
        fstk (Function.update S M.k₀ (t.reverse.map e₀ ++ S M.k₀)) [] w [] o⟩ := by
  intro t
  induction t with
  | nil =>
    intro S b
    have : Function.update S M.k₀ (([] : List Bool).reverse.map e₀ ++ S M.k₀) = S := by simp
    rw [this]
    exact f2_nil e₀ e₁ v S w o b
  | cons a t ih =>
    intro S b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M e₀ e₁))
        (some (⟨some (Sum.inr FL.l2), (v, b), fstk S [] w (a :: t) o⟩ : FCfg1 M)) =
        some ⟨some (Sum.inr FL.l2), (v, some (Sum.inl a)),
          fstk (Function.update S M.k₀ (e₀ a :: S M.k₀)) [] w t o⟩ := f2_cons e₀ e₁ v S w o b a t
    rw [e, ih]; simp

theorem f3_cons (b : Option (Bool ⊕ Bool)) (a : Bool) (w : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l3), (v, b), fstk S [] (a :: w) [] o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr FL.l3), (v, some (Sum.inl a)), fstk S [] w [] (Sum.inr a :: o)⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_W, fstk_set_O, bit]

theorem f3_nil (b : Option (Bool ⊕ Bool)) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l3), (v, b), fstk S [] [] [] o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr FL.l4), (v, none), fstk S [] [] [] o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_W]

theorem loop3 : ∀ (w : List Bool) (o : List (Bool ⊕ Bool)) (b : Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (firstProg M e₀ e₁)))^[w.length + 1]
        (some (⟨some (Sum.inr FL.l3), (v, b), fstk S [] w [] o⟩ : FCfg1 M)) =
      some ⟨some (Sum.inr FL.l4), (v, none), fstk S [] [] [] (w.reverse.map Sum.inr ++ o)⟩ := by
  intro w
  induction w with
  | nil => intro o b; exact f3_nil e₀ e₁ v S o b
  | cons a w ih =>
    intro o b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M e₀ e₁))
        (some (⟨some (Sum.inr FL.l3), (v, b), fstk S [] (a :: w) [] o⟩ : FCfg1 M)) =
        some ⟨some (Sum.inr FL.l3), (v, some (Sum.inl a)), fstk S [] w [] (Sum.inr a :: o)⟩ :=
      f3_cons e₀ e₁ v S o b a w
    rw [e, ih]; simp

theorem f4_cons (b : Option (Bool ⊕ Bool)) (y : M.Γ M.k₁) (m : List (M.Γ M.k₁)) (t : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l4), (v, b), fstk (Function.update S M.k₁ (y :: m)) [] [] t o⟩ :
          FCfg1 M) =
      some ⟨some (Sum.inr FL.l4), (v, some (Sum.inl (e₁ y))),
        fstk (Function.update S M.k₁ m) [] [] (e₁ y :: t) o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_T, fstk_set_M, bit]

theorem f4_nil (b : Option (Bool ⊕ Bool)) (t : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l4), (v, b), fstk (Function.update S M.k₁ []) [] [] t o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr FL.l5), (v, none), fstk (Function.update S M.k₁ []) [] [] t o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_M]

theorem loop4 : ∀ (m : List (M.Γ M.k₁)) (t : List Bool) (b : Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (firstProg M e₀ e₁)))^[m.length + 1]
        (some (⟨some (Sum.inr FL.l4), (v, b), fstk (Function.update S M.k₁ m) [] [] t o⟩ :
          FCfg1 M)) =
      some ⟨some (Sum.inr FL.l5), (v, none),
        fstk (Function.update S M.k₁ []) [] [] (m.reverse.map e₁ ++ t) o⟩ := by
  intro m
  induction m with
  | nil => intro t b; exact f4_nil e₀ e₁ v S o b t
  | cons y m ih =>
    intro t b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M e₀ e₁))
        (some (⟨some (Sum.inr FL.l4), (v, b), fstk (Function.update S M.k₁ (y :: m)) [] [] t o⟩ :
          FCfg1 M)) =
        some ⟨some (Sum.inr FL.l4), (v, some (Sum.inl (e₁ y))),
          fstk (Function.update S M.k₁ m) [] [] (e₁ y :: t) o⟩ := f4_cons e₀ e₁ v S o b y m t
    rw [e, ih]; simp

theorem f5_cons (b : Option (Bool ⊕ Bool)) (a : Bool) (t : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l5), (v, b), fstk S [] [] (a :: t) o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr FL.l5), (v, some (Sum.inl a)), fstk S [] [] t (Sum.inl a :: o)⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_T, fstk_set_O, bit]

theorem f5_nil (b : Option (Bool ⊕ Bool)) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l5), (v, b), fstk S [] [] [] o⟩ : FCfg1 M) =
      some ⟨none, (v, none), fstk S [] [] [] o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_T]

theorem loop5 : ∀ (t : List Bool) (o : List (Bool ⊕ Bool)) (b : Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (firstProg M e₀ e₁)))^[t.length + 1]
        (some (⟨some (Sum.inr FL.l5), (v, b), fstk S [] [] t o⟩ : FCfg1 M)) =
      some ⟨none, (v, none), fstk S [] [] [] (t.reverse.map Sum.inl ++ o)⟩ := by
  intro t
  induction t with
  | nil => intro o b; exact f5_nil e₀ e₁ v S o b
  | cons a t ih =>
    intro o b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M e₀ e₁))
        (some (⟨some (Sum.inr FL.l5), (v, b), fstk S [] [] (a :: t) o⟩ : FCfg1 M)) =
        some ⟨some (Sum.inr FL.l5), (v, some (Sum.inl a)), fstk S [] [] t (Sum.inl a :: o)⟩ :=
      f5_cons e₀ e₁ v S o b a t
    rw [e, ih]; simp

end PEqualNP.Library.Machines

end

section

namespace PEqualNP.Library.Machines

open Turing PEqualNP.Library

variable {M : FinTM2} (e₀ : Bool → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → Bool)

theorem fstk_nil : (fstk (fun _ => []) [] [] [] [] : ∀ k, List (FstΓ M k)) = fun _ => [] := by
  funext j; rcases j with j | (_ | _ | _ | _) <;> rfl

theorem fstk_nil_I (i : List (Bool ⊕ Bool)) :
    (fstk (fun _ => []) i [] [] [] : ∀ k, List (FstΓ M k)) =
      Function.update (fun _ => [] : ∀ k, List (FstΓ M k)) (Sum.inr FX.I) i :=
  (fstk_set_I (fun _ => []) [] [] [] [] i).symm.trans (by rw [fstk_nil])

theorem fstk_nil_O (o : List (Bool ⊕ Bool)) :
    (fstk (fun _ => []) [] [] [] o : ∀ k, List (FstΓ M k)) =
      Function.update (fun _ => [] : ∀ k, List (FstΓ M k)) (Sum.inr FX.O) o :=
  (fstk_set_O (fun _ => []) [] [] [] [] o).symm.trans (by rw [fstk_nil])

theorem embF_init (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
    (o : List (Bool ⊕ Bool)) (l : List (M.Γ M.k₀)) :
    embF b i w t o (initList M l) =
      (⟨some (Sum.inl M.main), (M.initialState, b),
        fstk (Function.update (fun _ => []) M.k₀ l) i w t o⟩ : FCfg1 M) := by
  rw [initList_eq]; rfl

theorem embF_halt (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
    (o : List (Bool ⊕ Bool)) (m : List (M.Γ M.k₁)) :
    embF b i w t o (haltList M m) =
      (⟨some (Sum.inr FL.l3), (M.initialState, b),
        fstk (Function.update (fun _ => []) M.k₁ m) i w t o⟩ : FCfg1 M) := by
  rw [haltList_eq]; rfl

theorem filterMap_const_none {γ δ : Type} (l : List γ) :
    l.filterMap (fun _ => (none : Option δ)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp

theorem encodePair_left (x w : List Bool) :
    (encodePair (x, w)).filterMap Sum.getLeft? = x := by
  have h1 : (Sum.getLeft? ∘ (Sum.inl : Bool → Bool ⊕ Bool) : Bool → Option Bool) = some := rfl
  have h2 : (Sum.getLeft? ∘ (Sum.inr : Bool → Bool ⊕ Bool) : Bool → Option Bool) = fun _ => none := rfl
  simp only [encodePair, List.filterMap_append, List.filterMap_map, h1, h2,
    List.filterMap_some, filterMap_const_none, List.append_nil]

theorem encodePair_right (x w : List Bool) :
    (encodePair (x, w)).filterMap Sum.getRight? = w := by
  have h1 : (Sum.getRight? ∘ (Sum.inl : Bool → Bool ⊕ Bool) : Bool → Option Bool) = fun _ => none := rfl
  have h2 : (Sum.getRight? ∘ (Sum.inr : Bool → Bool ⊕ Bool) : Bool → Option Bool) = some := rfl
  simp only [encodePair, List.filterMap_append, List.filterMap_map, h1, h2,
    List.filterMap_some, filterMap_const_none, List.nil_append]

theorem encodePair_length (x w : List Bool) :
    (encodePair (x, w)).length = x.length + w.length := by
  simp [encodePair]

theorem first_run (x w0 : List Bool) (m : List (M.Γ M.k₁)) (s : ℕ)
    (h : (flip bind (TM2.step M.m))^[s] (some (initList M (x.map e₀))) = some (haltList M m)) :
    ∃ n, n ≤ s + 2 * x.length + 2 * w0.length + 2 * m.length + 5 ∧
      (flip bind (TM2.step (firstProg M e₀ e₁)))^[n]
          (some (initList (firstM M e₀ e₁) (encodePair (x, w0)))) =
        some (haltList (firstM M e₀ e₁) (encodePair (m.map e₁, w0))) := by
  have q1 : (flip bind (TM2.step (firstProg M e₀ e₁)))^[(encodePair (x, w0)).length + 1]
      (some (initList (firstM M e₀ e₁) (encodePair (x, w0)))) =
      some (⟨some (Sum.inr FL.l2), (M.initialState, none),
        fstk (fun _ => []) [] w0.reverse x.reverse []⟩ : FCfg1 M) := by
    have := loop1 e₀ e₁ M.initialState (fun _ => []) [] (encodePair (x, w0)) [] [] none
    rw [encodePair_left, encodePair_right, List.append_nil, List.append_nil, fstk_nil_I] at this
    exact (congrArg (fun c => (flip bind (TM2.step (firstProg M e₀ e₁)))^[
      (encodePair (x, w0)).length + 1] (some c))
      (initList_eq (firstM M e₀ e₁) (encodePair (x, w0)))).trans this
  have q2 : (flip bind (TM2.step (firstProg M e₀ e₁)))^[x.reverse.length + 1]
      (some (⟨some (Sum.inr FL.l2), (M.initialState, none),
        fstk (fun _ => []) [] w0.reverse x.reverse []⟩ : FCfg1 M)) =
      some (embF none [] w0.reverse [] [] (initList M (x.map e₀))) := by
    have := loop2 e₀ e₁ M.initialState w0.reverse [] x.reverse (fun _ => []) none
    rw [embF_init]
    simpa using this
  have q3 := simulate (TM2.step M.m) (TM2.step (firstProg M e₀ e₁))
    (embF none [] w0.reverse [] []) (stepF e₀ e₁ none [] w0.reverse [] []) s _ _ h
  rw [embF_halt] at q3
  have q4 : (flip bind (TM2.step (firstProg M e₀ e₁)))^[w0.reverse.length + 1]
      (some (⟨some (Sum.inr FL.l3), (M.initialState, none),
        fstk (Function.update (fun _ => []) M.k₁ m) [] w0.reverse [] []⟩ : FCfg1 M)) =
      some (⟨some (Sum.inr FL.l4), (M.initialState, none),
        fstk (Function.update (fun _ => []) M.k₁ m) [] [] [] (w0.map Sum.inr)⟩ : FCfg1 M) := by
    have := loop3 e₀ e₁ M.initialState (Function.update (fun _ => []) M.k₁ m) w0.reverse [] none
    simpa using this
  have q5 : (flip bind (TM2.step (firstProg M e₀ e₁)))^[m.length + 1]
      (some (⟨some (Sum.inr FL.l4), (M.initialState, none),
        fstk (Function.update (fun _ => []) M.k₁ m) [] [] [] (w0.map Sum.inr)⟩ : FCfg1 M)) =
      some (⟨some (Sum.inr FL.l5), (M.initialState, none),
        fstk (fun _ => []) [] [] (m.reverse.map e₁) (w0.map Sum.inr)⟩ : FCfg1 M) := by
    have := loop4 e₀ e₁ M.initialState (fun _ => []) (w0.map Sum.inr) m [] none
    simpa using this
  have q6 : (flip bind (TM2.step (firstProg M e₀ e₁)))^[(m.reverse.map e₁).length + 1]
      (some (⟨some (Sum.inr FL.l5), (M.initialState, none),
        fstk (fun _ => []) [] [] (m.reverse.map e₁) (w0.map Sum.inr)⟩ : FCfg1 M)) =
      some (haltList (firstM M e₀ e₁) (encodePair (m.map e₁, w0))) := by
    have := loop5 e₀ e₁ M.initialState (fun _ => []) (m.reverse.map e₁) (w0.map Sum.inr) none
    rw [fstk_nil_O] at this
    refine this.trans (Eq.trans ?_
      (congrArg some (haltList_eq (firstM M e₀ e₁) (encodePair (m.map e₁, w0)))).symm)
    simp [encodePair]
    rfl
  refine ⟨_, ?_, iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ q1 q2) q3)
    q4) q5) q6⟩
  simp only [encodePair_length, List.length_reverse, List.length_map]
  omega

theorem first_polyTime (f : List Bool → List Bool)
    (c : TM2ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f) :
    Nonempty (TM2ComputableInPolyTime encodePair encodePair
      (fun p : List Bool × List Bool => (f p.1, p.2))) := by
  let e₀ : Bool → c.tm.Γ c.tm.k₀ := c.inputAlphabet.invFun
  let e₁ : c.tm.Γ c.tm.k₁ → Bool := c.outputAlphabet
  let T : Polynomial ℕ :=
    c.time + Polynomial.C 2 * (Polynomial.X + Polynomial.C (maxPush c.tm) * c.time) +
      Polynomial.C 2 * Polynomial.X + Polynomial.C 5
  have key : ∀ p : List Bool × List Bool, ∃ n, n ≤ T.eval (encodePair p).length ∧
      (flip bind (TM2.step (firstProg c.tm e₀ e₁)))^[n]
          (some (initList (firstM c.tm e₀ e₁) (encodePair p))) =
        some (haltList (firstM c.tm e₀ e₁) (encodePair (f p.1, p.2))) := by
    rintro ⟨x, w⟩
    have hs : ∃ s, s ≤ Polynomial.eval x.length c.time ∧
        (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm (x.map e₀))) =
          some (haltList c.tm (List.map c.outputAlphabet.invFun (f x))) :=
      ⟨(c.outputsFun x).steps, (c.outputsFun x).steps_le_m, (c.outputsFun x).evals_in_steps⟩
    obtain ⟨s, b1, h⟩ := hs
    obtain ⟨n, hn, hrun⟩ := first_run e₀ e₁ x w _ s h
    have hm : (List.map c.outputAlphabet.invFun (f x)).map e₁ = f x := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (f x)]
      exact List.map_congr_left fun y _ => c.outputAlphabet.right_inv y
    rw [hm] at hrun
    refine ⟨n, hn.trans ?_, hrun⟩
    have h' := h
    rw [haltList_eq, initList_eq] at h'
    have hlen := run_length c.tm c.tm.k₁ s _ _ h'
    simp only [Function.update_self, List.length_map] at hlen
    have hin : ((Function.update (fun _ => [] : ∀ k, List (c.tm.Γ k)) c.tm.k₀ (x.map e₀))
        c.tm.k₁).length ≤ x.length := by
      by_cases hk : c.tm.k₁ = c.tm.k₀
      · rw [hk, Function.update_self, List.length_map]
      · rw [Function.update_of_ne hk]; simp
    have b2 : Polynomial.eval x.length c.time ≤ Polynomial.eval (x.length + w.length) c.time :=
      eval_mono _ (by omega)
    have hmul : maxPush c.tm * s ≤
        maxPush c.tm * Polynomial.eval (x.length + w.length) c.time :=
      Nat.mul_le_mul_left _ (b1.trans b2)
    simp only [T, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, encodePair_length, List.length_map]
    omega
  exact ⟨{
    tm := firstM c.tm e₀ e₁
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := T
    outputsFun := fun p =>
      { steps := Classical.choose (key p)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          exact (congrArg (fun l => (flip bind (TM2.step (firstProg c.tm e₀ e₁)))^[
            Classical.choose (key p)] (some (initList (firstM c.tm e₀ e₁) l)))
            (hm _ (encodePair p))).trans ((Classical.choose_spec (key p)).2.trans
            (congrArg (fun l => some (haltList (firstM c.tm e₀ e₁) l))
              (hm _ (encodePair (f p.1, p.2))).symm))
        steps_le_m := (Classical.choose_spec (key p)).1 } }⟩

end PEqualNP.Library.Machines

end

section

namespace PEqualNP.Library.Machines

open PEqualNP.Library

private theorem filterMap_map_some {α β γ : Type} (h : α → β) (φ : β → Option γ) (g : α → γ)
    (hφ : ∀ a, φ (h a) = some (g a)) (l : List α) : (l.map h).filterMap φ = l.map g := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [hφ, ih]

private theorem filterMap_map_none {α β γ : Type} (h : α → β) (φ : β → Option γ)
    (hφ : ∀ a, φ (h a) = none) (l : List α) : (l.map h).filterMap φ = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [hφ, ih]

theorem cpt_comp {α β γ αΓ βΓ γΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {ec : γ → List γΓ} {f : α → β} {g : β → γ}
    (hf : PEqualNP.Library.ComputableInPolyTime ea eb f)
    (hg : PEqualNP.Library.ComputableInPolyTime eb ec g) :
    PEqualNP.Library.ComputableInPolyTime ea ec (fun a => g (f a)) := by
  obtain ⟨c1⟩ := hf
  obtain ⟨c2⟩ := hg
  exact comp_polyTime ea eb ec f g c1 c2

theorem cpt_swap :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      PEqualNP.Library.encodePair (fun p : List Bool × List Bool => (p.2, p.1)) := by
  refine twoPass_polyTime _ _ _
    (fun s : Bool ⊕ Bool => Sum.elim (fun _ => none) (fun b => some (Sum.inl b)) s)
    (fun s : Bool ⊕ Bool => Sum.elim (fun b => some (Sum.inr b)) (fun _ => none) s) ?_
  rintro ⟨x, w⟩
  simp only [encodePair, List.filterMap_append]
  rw [filterMap_map_none Sum.inl _ (fun _ => rfl) x,
    filterMap_map_some Sum.inr _ Sum.inl (fun _ => rfl) w,
    filterMap_map_some Sum.inl _ Sum.inr (fun _ => rfl) x,
    filterMap_map_none Sum.inr _ (fun _ => rfl) w]
  simp

theorem cpt_dup :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      PEqualNP.Library.encodePair (fun x : List Bool => (x, x)) := by
  refine twoPass_polyTime _ _ _
    (fun b : Bool => some (Sum.inl b)) (fun b : Bool => some (Sum.inr b)) ?_
  intro x
  have h1 := filterMap_map_some (fun b : Bool => b) (fun b : Bool => some (Sum.inl (β := Bool) b))
    Sum.inl (fun _ => rfl) x
  have h2 := filterMap_map_some (fun b : Bool => b) (fun b : Bool => some (Sum.inr (α := Bool) b))
    Sum.inr (fun _ => rfl) x
  simp only [List.map_id'] at h1 h2
  simp only [encodePair, h1, h2]

theorem cpt_fst :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x : List Bool => x) (fun p : List Bool × List Bool => p.1) := by
  refine filterMap_polyTime _ _ _
    (fun s : Bool ⊕ Bool => Sum.elim (fun b => some b) (fun _ => none) s) ?_
  rintro ⟨x, w⟩
  simp only [encodePair, List.filterMap_append]
  rw [filterMap_map_some Sum.inl _ (fun b => b) (fun _ => rfl) x,
    filterMap_map_none Sum.inr _ (fun _ => rfl) w]
  simp

theorem cpt_snd :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x : List Bool => x) (fun p : List Bool × List Bool => p.2) := by
  refine filterMap_polyTime _ _ _
    (fun s : Bool ⊕ Bool => Sum.elim (fun _ => none) (fun b => some b) s) ?_
  rintro ⟨x, w⟩
  simp only [encodePair, List.filterMap_append]
  rw [filterMap_map_none Sum.inl _ (fun _ => rfl) x,
    filterMap_map_some Sum.inr _ (fun b => b) (fun _ => rfl) w]
  simp

theorem cpt_append :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x : List Bool => x) (fun p : List Bool × List Bool => p.1 ++ p.2) := by
  refine filterMap_polyTime _ _ _
    (fun s : Bool ⊕ Bool => Sum.elim (fun b => some b) (fun b => some b) s) ?_
  rintro ⟨x, w⟩
  simp only [encodePair, List.filterMap_append]
  rw [filterMap_map_some Sum.inl _ (fun b => b) (fun _ => rfl) x,
    filterMap_map_some Sum.inr _ (fun b => b) (fun _ => rfl) w]
  simp

theorem cpt_first {f : List Bool → List Bool}
    (hf : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) f) :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      PEqualNP.Library.encodePair (fun p : List Bool × List Bool => (f p.1, p.2)) := by
  obtain ⟨c⟩ := hf
  exact first_polyTime f c

theorem cpt_second {g : List Bool → List Bool}
    (hg : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) g) :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      PEqualNP.Library.encodePair (fun p : List Bool × List Bool => (p.1, g p.2)) :=
  cpt_comp (cpt_comp cpt_swap (cpt_first hg)) cpt_swap

theorem cpt_pair {f g : List Bool → List Bool}
    (hf : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) f)
    (hg : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) g) :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      PEqualNP.Library.encodePair (fun x : List Bool => (f x, g x)) :=
  cpt_comp (cpt_comp cpt_dup (cpt_second hg)) (cpt_first hf)

theorem cpt_id :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) (fun x : List Bool => x) := by
  refine filterMap_polyTime _ _ _ (fun b : Bool => some b) ?_
  intro x
  have h := filterMap_map_some (fun b : Bool => b) (fun b : Bool => some b) (fun b => b)
    (fun _ => rfl) x
  simp only [List.map_id'] at h
  exact h.symm

end PEqualNP.Library.Machines

end

section

namespace PEqualNP.Library.Machines

open Turing

def fstRun {Γ₀ Γ₁ Q : Type} (δ : Q → Γ₀ → Q × Option Γ₁) (fin : Q → Option Γ₁) :
    Q → List Γ₀ → List Γ₁
  | q, [] => (fin q).toList
  | q, a :: l => (δ q a).2.toList ++ fstRun δ fin (δ q a).1 l

def fstRun2 {Γ₀ Γ₁ Q : Type} (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin : Q → Option Γ₁) :
    Q → List Γ₀ → List Γ₁
  | q, [] => (fin q).toList
  | q, a :: l => (δ q a).2.1.toList ++ (δ q a).2.2.toList ++ fstRun2 δ fin (δ q a).1 l

theorem fstRun_eq_fstRun2 {Γ₀ Γ₁ Q : Type} (δ : Q → Γ₀ → Q × Option Γ₁) (fin : Q → Option Γ₁)
    (q : Q) (l : List Γ₀) :
    fstRun δ fin q l = fstRun2 (fun q a => ((δ q a).1, (δ q a).2, none)) fin q l := by
  induction l generalizing q with
  | nil => rfl
  | cons a l ih => simp [fstRun, fstRun2, ih]

inductive TrK : Type
  | inp | tmp | out
  deriving DecidableEq

instance : Fintype TrK :=
  Fintype.ofList [.inp, .tmp, .out] (fun x => by cases x <;> simp)

variable {Γ₀ Γ₁ Q : Type}

abbrev TrΓ (Γ₀ Γ₁ Q : Type) : TrK → Type
  | .inp => Γ₀
  | .tmp => Q × Option Γ₀
  | .out => Γ₁

abbrev TrS (Γ₀ Q : Type) : Type := Q × Option Γ₀ × Bool

def trO1 (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin : Q → Option Γ₁) :
    Q × Option Γ₀ → Option Γ₁
  | (q, some a) => (δ q a).2.1
  | (q, none) => fin q

def trO2 (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) : Q × Option Γ₀ → Option Γ₁
  | (q, some a) => (δ q a).2.2
  | (_, none) => none

def trOut (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin : Q → Option Γ₁)
    (e : Q × Option Γ₀) : List Γ₁ :=
  (trO1 δ fin e).toList ++ (trO2 δ e).toList

def trTrace (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) : Q → List Γ₀ → List (Q × Option Γ₀)
  | q, [] => [(q, none)]
  | q, a :: l => (q, some a) :: trTrace δ (δ q a).1 l

theorem trTrace_length (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (q : Q) (l : List Γ₀) :
    (trTrace δ q l).length = l.length + 1 := by
  induction l generalizing q with
  | nil => rfl
  | cons a l ih => simp [trTrace, ih]

theorem trTrace_out (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin : Q → Option Γ₁) (q : Q)
    (l : List Γ₀) : (trTrace δ q l).flatMap (trOut δ fin) = fstRun2 δ fin q l := by
  induction l generalizing q with
  | nil => simp [trTrace, trOut, trO1, trO2, fstRun2]
  | cons a l ih => simp [trTrace, trOut, trO1, trO2, fstRun2, ih]

def trWrite (o : TrS Γ₀ Q → Option Γ₁) (d : Option Γ₁)
    (next : TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)) :
    TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q) :=
  .branch (fun s => (o s).isSome)
    (match d with
      | some dd => .push .out (fun s => (o s).getD dd) next
      | none => next)
    next

def trProg (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin : Q → Option Γ₁) (q₀ : Q)
    (d : Option Γ₁) : Bool → TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)
  | false =>
    .pop .inp (fun s o => (s.1, o, o.isSome))
      (.branch (fun s => s.2.2)
        (.push .tmp (fun s => (s.1, s.2.1))
          (.load (fun s => (match s.2.1 with
              | some a => (δ s.1 a).1
              | none => s.1, none, false))
            (.goto fun _ => false)))
        (.push .tmp (fun s => (s.1, none))
          (.load (fun _ => (q₀, none, false)) (.goto fun _ => true))))
  | true =>
    .pop .tmp (fun _ o => match o with
        | some e => (e.1, e.2, true)
        | none => (q₀, none, false))
      (.branch (fun s => s.2.2)
        (trWrite (fun s => trO2 δ (s.1, s.2.1)) d
          (trWrite (fun s => trO1 δ fin (s.1, s.2.1)) d (.goto fun _ => true)))
        .halt)

def trM [Fintype Γ₀] [Fintype Q] (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁)
    (fin : Q → Option Γ₁) (q₀ : Q) (d : Option Γ₁) : FinTM2 where
  K := TrK
  k₀ := .inp
  k₁ := .out
  Γ := TrΓ Γ₀ Γ₁ Q
  Λ := Bool
  main := false
  σ := TrS Γ₀ Q
  initialState := (q₀, none, false)
  Γk₀Fin := inferInstanceAs (Fintype Γ₀)
  m := trProg δ fin q₀ d

def trSt (l : List Γ₀) (t : List (Q × Option Γ₀)) (u : List Γ₁) : ∀ k, List (TrΓ Γ₀ Γ₁ Q k)
  | .inp => l
  | .tmp => t
  | .out => u

theorem trSt_set_inp (l l' : List Γ₀) (t : List (Q × Option Γ₀)) (u : List Γ₁) :
    Function.update (trSt l t u) .inp l' = trSt l' t u := by
  funext k; cases k <;> simp [trSt]

theorem trSt_set_tmp (l : List Γ₀) (t t' : List (Q × Option Γ₀)) (u : List Γ₁) :
    Function.update (trSt l t u) .tmp t' = trSt l t' u := by
  funext k; cases k <;> simp [trSt]

theorem trSt_set_out (l : List Γ₀) (t : List (Q × Option Γ₀)) (u u' : List Γ₁) :
    Function.update (trSt l t u) .out u' = trSt l t u' := by
  funext k; cases k <;> simp [trSt]

theorem trSt_start (l : List Γ₀) :
    (trSt l [] [] : ∀ k, List (TrΓ Γ₀ Γ₁ Q k)) =
      Function.update (fun _ => [] : ∀ k, List (TrΓ Γ₀ Γ₁ Q k)) .inp l := by
  funext k; cases k <;> simp [trSt]

theorem trSt_end (u : List Γ₁) :
    (trSt [] [] u : ∀ k, List (TrΓ Γ₀ Γ₁ Q k)) =
      Function.update (fun _ => [] : ∀ k, List (TrΓ Γ₀ Γ₁ Q k)) .out u := by
  funext k; cases k <;> simp [trSt]

abbrev TrCfg (Γ₀ Γ₁ Q : Type) : Type := TM2.Cfg (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)

theorem trWrite_stepAux (o : TrS Γ₀ Q → Option Γ₁) (d : Option Γ₁) (hd : ∀ _ : Γ₁, d ≠ none)
    (next : TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)) (s : TrS Γ₀ Q) (l : List Γ₀)
    (t : List (Q × Option Γ₀)) (u : List Γ₁) :
    TM2.stepAux (trWrite o d next) s (trSt l t u) =
      TM2.stepAux next s (trSt l t ((o s).toList ++ u)) := by
  cases ho : o s with
  | none => cases d <;> simp [trWrite, TM2.stepAux, ho]
  | some y =>
    cases d with
    | none => exact absurd rfl (hd y)
    | some dd => simp [trWrite, TM2.stepAux, ho, trSt, trSt_set_out]

variable (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin : Q → Option Γ₁) (q₀ : Q)
  (d : Option Γ₁)

theorem trA_cons (s : TrS Γ₀ Q) (a : Γ₀) (l : List Γ₀) (t : List (Q × Option Γ₀))
    (u : List Γ₁) :
    TM2.step (trProg δ fin q₀ d) (⟨some false, s, trSt (a :: l) t u⟩ : TrCfg Γ₀ Γ₁ Q) =
      some ⟨some false, ((δ s.1 a).1, none, false), trSt l ((s.1, some a) :: t) u⟩ := by
  simp [TM2.step, trProg, TM2.stepAux, trSt, trSt_set_inp, trSt_set_tmp]

theorem trA_nil (s : TrS Γ₀ Q) (t : List (Q × Option Γ₀)) (u : List Γ₁) :
    TM2.step (trProg δ fin q₀ d) (⟨some false, s, trSt [] t u⟩ : TrCfg Γ₀ Γ₁ Q) =
      some ⟨some true, (q₀, none, false), trSt [] ((s.1, none) :: t) u⟩ := by
  simp [TM2.step, trProg, TM2.stepAux, trSt, trSt_set_inp, trSt_set_tmp]

theorem trB_cons (hd : ∀ _ : Γ₁, d ≠ none) (s : TrS Γ₀ Q) (e : Q × Option Γ₀)
    (t : List (Q × Option Γ₀)) (u : List Γ₁) :
    TM2.step (trProg δ fin q₀ d) (⟨some true, s, trSt [] (e :: t) u⟩ : TrCfg Γ₀ Γ₁ Q) =
      some ⟨some true, (e.1, e.2, true), trSt [] t (trOut δ fin e ++ u)⟩ := by
  simp only [TM2.step, trProg, TM2.stepAux]
  have e1 : (trSt [] (e :: t) u : ∀ k, List (TrΓ Γ₀ Γ₁ Q k)) .tmp = e :: t := rfl
  rw [e1]
  simp only [List.head?_cons, List.tail_cons, Bool.cond_true]
  rw [trSt_set_tmp, trWrite_stepAux _ _ hd, trWrite_stepAux _ _ hd]
  simp [TM2.stepAux, trOut]

theorem trB_nil (s : TrS Γ₀ Q) (u : List Γ₁) :
    TM2.step (trProg δ fin q₀ d) (⟨some true, s, trSt [] [] u⟩ : TrCfg Γ₀ Γ₁ Q) =
      some ⟨none, (q₀, none, false), trSt [] [] u⟩ := by
  simp [TM2.step, trProg, TM2.stepAux, trSt, trSt_set_tmp]

theorem trLoopA (u : List Γ₁) :
    ∀ (l : List Γ₀) (t : List (Q × Option Γ₀)) (s : TrS Γ₀ Q),
      (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1]
          (some (⟨some false, s, trSt l t u⟩ : TrCfg Γ₀ Γ₁ Q)) =
        some ⟨some true, (q₀, none, false), trSt [] ((trTrace δ s.1 l).reverse ++ t) u⟩ := by
  intro l
  induction l with
  | nil => intro t s; exact trA_nil δ fin q₀ d s t u
  | cons a l ih =>
    intro t s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (trProg δ fin q₀ d))
        (some (⟨some false, s, trSt (a :: l) t u⟩ : TrCfg Γ₀ Γ₁ Q)) =
        some ⟨some false, ((δ s.1 a).1, none, false), trSt l ((s.1, some a) :: t) u⟩ :=
      trA_cons δ fin q₀ d s a l t u
    rw [e, ih]
    simp [trTrace]

theorem trLoopB (hd : ∀ _ : Γ₁, d ≠ none) :
    ∀ (t : List (Q × Option Γ₀)) (u : List Γ₁) (s : TrS Γ₀ Q),
      (flip bind (TM2.step (trProg δ fin q₀ d)))^[t.length + 1]
          (some (⟨some true, s, trSt [] t u⟩ : TrCfg Γ₀ Γ₁ Q)) =
        some ⟨none, (q₀, none, false), trSt [] [] (t.reverse.flatMap (trOut δ fin) ++ u)⟩ := by
  intro t
  induction t with
  | nil => intro u s; exact trB_nil δ fin q₀ d s u
  | cons e t ih =>
    intro u s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e' : flip bind (TM2.step (trProg δ fin q₀ d))
        (some (⟨some true, s, trSt [] (e :: t) u⟩ : TrCfg Γ₀ Γ₁ Q)) =
        some ⟨some true, (e.1, e.2, true), trSt [] t (trOut δ fin e ++ u)⟩ :=
      trB_cons δ fin q₀ d hd s e t u
    rw [e', ih]
    simp [List.flatMap_append]

theorem trM_run [Fintype Γ₀] [Fintype Q] (hd : ∀ _ : Γ₁, d ≠ none) (l : List Γ₀) :
    (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1 + 1 + (l.length + 1)]
        (some (initList (trM δ fin q₀ d) l)) =
      some (haltList (trM δ fin q₀ d) (fstRun2 δ fin q₀ l)) := by
  refine (congrArg (fun c => (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1 + 1 +
    (l.length + 1)] (some c)) (initList_eq (trM δ fin q₀ d) l)).trans
    (Eq.trans ?_ (congrArg some (haltList_eq (trM δ fin q₀ d) (fstRun2 δ fin q₀ l))).symm)
  show (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1 + 1 + (l.length + 1)]
    (some (⟨some false, (q₀, none, false), Function.update (fun _ => []) .inp l⟩ :
      TrCfg Γ₀ Γ₁ Q)) =
    some (⟨none, (q₀, none, false), Function.update (fun _ => []) .out (fstRun2 δ fin q₀ l)⟩ :
      TrCfg Γ₀ Γ₁ Q)
  have hA : (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1]
      (some (⟨some false, (q₀, none, false), trSt l [] []⟩ : TrCfg Γ₀ Γ₁ Q)) =
      some ⟨some true, (q₀, none, false), trSt [] (trTrace δ q₀ l).reverse []⟩ := by
    have := trLoopA δ fin q₀ d [] l [] (q₀, none, false)
    rw [List.append_nil] at this
    exact this
  have hB : (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1 + 1]
      (some (⟨some true, (q₀, none, false), trSt [] (trTrace δ q₀ l).reverse []⟩ :
        TrCfg Γ₀ Γ₁ Q)) =
      some ⟨none, (q₀, none, false), trSt [] [] (fstRun2 δ fin q₀ l)⟩ := by
    have := trLoopB δ fin q₀ d hd (trTrace δ q₀ l).reverse [] (q₀, none, false)
    rw [List.length_reverse, trTrace_length, List.reverse_reverse, trTrace_out,
      List.append_nil] at this
    exact this
  rw [Function.iterate_add_apply, ← trSt_start, hA, hB, trSt_end]

theorem fst2_polyTime {α β αΓ βΓ Q : Type} [Fintype αΓ] [Fintype Q] (ea : α → List αΓ)
    (eb : β → List βΓ) (f : α → β) (δ : Q → αΓ → Q × Option βΓ × Option βΓ)
    (fin : Q → Option βΓ) (q₀ : Q) (h : ∀ a, eb (f a) = fstRun2 δ fin q₀ (ea a)) :
    Nonempty (Turing.TM2ComputableInPolyTime ea eb f) := by
  classical
  let d : Option βΓ := if h : Nonempty βΓ then some (Classical.choice h) else none
  have hd : ∀ _ : βΓ, d ≠ none := by
    intro y
    have hn : Nonempty βΓ := ⟨y⟩
    simp [d, hn]
  exact ⟨{
    tm := trM δ fin q₀ d
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.C 2 * Polynomial.X + Polynomial.C 3
    outputsFun := fun a =>
      { steps := (ea a).length + 1 + 1 + ((ea a).length + 1)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have := trM_run δ fin q₀ d hd (ea a)
          exact (congrArg (fun l => (flip bind (TM2.step (trProg δ fin q₀ d)))^[(ea a).length +
            1 + 1 + ((ea a).length + 1)] (some (initList (trM δ fin q₀ d) l)))
            (hm αΓ (ea a))).trans
            (this.trans (congrArg (fun l => some (haltList (trM δ fin q₀ d) l))
              ((h a).symm.trans (hm βΓ (eb (f a))).symm)))
        steps_le_m := by
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X]
          omega } }⟩

theorem fst_polyTime {α β αΓ βΓ Q : Type} [Fintype αΓ] [Fintype Q] (ea : α → List αΓ)
    (eb : β → List βΓ) (f : α → β) (δ : Q → αΓ → Q × Option βΓ) (fin : Q → Option βΓ) (q₀ : Q)
    (h : ∀ a, eb (f a) = fstRun δ fin q₀ (ea a)) :
    Nonempty (Turing.TM2ComputableInPolyTime ea eb f) :=
  fst2_polyTime ea eb f (fun q a => ((δ q a).1, (δ q a).2, none)) fin q₀
    (fun a => (h a).trans (fstRun_eq_fstRun2 δ fin q₀ (ea a)))

end PEqualNP.Library.Machines

end

section

namespace PEqualNP.Library.Machines

open Turing

def pushList : List Bool → TM2.Stmt (fun _ : Unit => Bool) Unit Bool
  | [] => .halt
  | a :: l => .push () (fun _ => a) (pushList l)

def constListProg (l : List Bool) : Unit → TM2.Stmt (fun _ : Unit => Bool) Unit Bool :=
  fun _ => .pop () (fun _ o => o.isSome)
    (.branch (fun s => s)
      (.load (fun _ => false) (.goto fun _ => ()))
      (pushList l.reverse))

def constList (l : List Bool) : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Bool
  initialState := false
  m := constListProg l

abbrev CLCfg : Type := TM2.Cfg (fun _ : Unit => Bool) Unit Bool

theorem update_unit (S T : List Bool) :
    Function.update (fun _ : Unit => S) () T = fun _ => T := by
  funext k
  simp

theorem pushList_stepAux (l : List Bool) (v : Bool) (S : List Bool) :
    TM2.stepAux (pushList l) v (fun _ : Unit => S) =
      (⟨none, v, fun _ => l.reverse ++ S⟩ : CLCfg) := by
  induction l generalizing S with
  | nil => rfl
  | cons a l ih =>
    simp only [pushList, TM2.stepAux]
    rw [update_unit, ih]
    simp

theorem constList_cons (l : List Bool) (x : Bool) (a : List Bool) :
    TM2.step (constListProg l) (⟨some (), false, fun _ => x :: a⟩ : CLCfg) =
      some ⟨some (), false, fun _ => a⟩ := by
  simp only [TM2.step, constListProg, TM2.stepAux]
  rw [update_unit]
  simp

theorem constList_nil (l : List Bool) :
    TM2.step (constListProg l) (⟨some (), false, fun _ => []⟩ : CLCfg) =
      some ⟨none, false, fun _ => l⟩ := by
  simp only [TM2.step, constListProg, TM2.stepAux]
  rw [update_unit]
  simp only [List.head?_nil, Option.isSome_none, Bool.cond_false, List.tail_nil]
  rw [pushList_stepAux]
  simp

theorem constList_loop (l : List Bool) (a : List Bool) :
    (flip bind (TM2.step (constListProg l)))^[a.length + 1]
        (some (⟨some (), false, fun _ => a⟩ : CLCfg)) =
      some ⟨none, false, fun _ => l⟩ := by
  induction a with
  | nil => exact constList_nil l
  | cons x a ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (constListProg l))
        (some (⟨some (), false, fun _ => x :: a⟩ : CLCfg)) =
        some ⟨some (), false, fun _ => a⟩ := constList_cons l x a
    rw [e, ih]

theorem constList_run (l : List Bool) (a : List Bool) :
    (flip bind (TM2.step (constListProg l)))^[a.length + 1]
        (some (initList (constList l) a)) = some (haltList (constList l) l) := by
  refine (congrArg (fun c => (flip bind (TM2.step (constListProg l)))^[a.length + 1]
    (some c)) (initList_eq (constList l) a)).trans
    (Eq.trans ?_ (congrArg some (haltList_eq (constList l) l)).symm)
  show (flip bind (TM2.step (constListProg l)))^[a.length + 1]
    (some (⟨some (), false, Function.update (fun _ => []) () a⟩ : CLCfg)) =
    some (⟨none, false, Function.update (fun _ => []) () l⟩ : CLCfg)
  rw [update_unit, update_unit]
  exact constList_loop l a

theorem constList_polyTime (l : List Bool) :
    Nonempty (Turing.TM2ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) (fun _ : List Bool => l)) :=
  ⟨{
    tm := constList l
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.X + 1
    outputsFun := fun a =>
      { steps := a.length + 1
        evals_in_steps := by
          have hm : ∀ l : List Bool, List.map (Equiv.refl Bool).invFun l = l := fun l => by simp
          exact (congrArg (fun x => (flip bind (TM2.step (constListProg l)))^[a.length + 1]
            (some (initList (constList l) x))) (hm a)).trans
            ((constList_run l a).trans
              (congrArg (fun x => some (haltList (constList l) x)) (hm l).symm))
        steps_le_m := by simp } }⟩

end PEqualNP.Library.Machines

end

section

namespace PEqualNP.Library.Machines.Iter

open Turing

inductive IX
  | I | C | T | O
  deriving DecidableEq

instance : Fintype IX :=
  Fintype.ofList [IX.I, IX.C, IX.T, IX.O] (fun x => by cases x <;> simp)

inductive IL
  | l1 | l2 | l3 | l4 | l5 | l6
  deriving DecidableEq

instance : Fintype IL :=
  Fintype.ofList [IL.l1, IL.l2, IL.l3, IL.l4, IL.l5, IL.l6] (fun x => by cases x <;> simp)

variable (M : FinTM2)

abbrev ItΓ : M.K ⊕ IX → Type
  | Sum.inl k => M.Γ k
  | Sum.inr IX.I => Bool ⊕ Bool
  | Sum.inr IX.C => Bool
  | Sum.inr IX.T => Bool
  | Sum.inr IX.O => Bool

abbrev ItΛ : Type := M.Λ ⊕ IL

abbrev Itσ : Type := M.σ × Option (Bool ⊕ Bool)

variable {M}

def trI : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (ItΓ M) (ItΛ M) (Itσ M)
  | .push k f q => .push (Sum.inl k) (fun s => f s.1) (trI q)
  | .peek k f q => .peek (Sum.inl k) (fun s o => (f s.1 o, s.2)) (trI q)
  | .pop k f q => .pop (Sum.inl k) (fun s o => (f s.1 o, s.2)) (trI q)
  | .load a q => .load (fun s => (a s.1, s.2)) (trI q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1) (trI q₁) (trI q₂)
  | .goto f => .goto (fun s => Sum.inl (f s.1))
  | .halt => .goto (fun _ => Sum.inr IL.l4)

variable (M)

def iterProg (e₀ : Bool → M.Γ M.k₀) (d₀ : M.Γ M.k₀ → Bool) (e₁ : M.Γ M.k₁ → Bool) :
    ItΛ M → TM2.Stmt (ItΓ M) (ItΛ M) (Itσ M)
  | Sum.inl l => trI (M.m l)
  | Sum.inr IL.l1 =>
    .pop (Sum.inr IX.I) (fun s o => (s.1, o))
      (.branch (fun s => s.2.isSome)
        (.branch (fun s => isFst s.2)
          (.push (Sum.inr IX.T) (fun s => bit s.2) (.goto fun _ => Sum.inr IL.l1))
          (.push (Sum.inr IX.C) (fun s => bit s.2) (.goto fun _ => Sum.inr IL.l1)))
        (.goto fun _ => Sum.inr IL.l2))
  | Sum.inr IL.l2 =>
    .pop (Sum.inr IX.T) (fun s o => (s.1, o.map Sum.inl))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inl M.k₀) (fun s => e₀ (bit s.2)) (.goto fun _ => Sum.inr IL.l2))
        (.goto fun _ => Sum.inr IL.l3))
  | Sum.inr IL.l3 =>
    .pop (Sum.inr IX.C) (fun s o => (s.1, o.map Sum.inl))
      (.branch (fun s => s.2.isSome)
        (.goto fun _ => Sum.inl M.main)
        (.goto fun _ => Sum.inr IL.l5))
  | Sum.inr IL.l4 =>
    .pop (Sum.inl M.k₁) (fun s o => (s.1, o.map fun y => Sum.inl (e₁ y)))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr IX.T) (fun s => bit s.2) (.goto fun _ => Sum.inr IL.l4))
        (.goto fun _ => Sum.inr IL.l2))
  | Sum.inr IL.l5 =>
    .pop (Sum.inl M.k₀) (fun s o => (s.1, o.map fun y => Sum.inl (d₀ y)))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr IX.T) (fun s => bit s.2) (.goto fun _ => Sum.inr IL.l5))
        (.goto fun _ => Sum.inr IL.l6))
  | Sum.inr IL.l6 =>
    .pop (Sum.inr IX.T) (fun s o => (s.1, o.map Sum.inl))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr IX.O) (fun s => bit s.2) (.goto fun _ => Sum.inr IL.l6))
        .halt)

def iterM (e₀ : Bool → M.Γ M.k₀) (d₀ : M.Γ M.k₀ → Bool) (e₁ : M.Γ M.k₁ → Bool) : FinTM2 :=
  haveI := M.kFin
  haveI := M.ΛFin
  haveI := M.σFin
  { K := M.K ⊕ IX
    k₀ := Sum.inr IX.I
    k₁ := Sum.inr IX.O
    Γ := ItΓ M
    Λ := ItΛ M
    main := Sum.inr IL.l1
    σ := Itσ M
    initialState := (M.initialState, none)
    Γk₀Fin := inferInstanceAs (Fintype (Bool ⊕ Bool))
    m := iterProg M e₀ d₀ e₁ }

variable {M}

def istk (S : ∀ k, List (M.Γ k)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool) :
    ∀ k, List (ItΓ M k)
  | Sum.inl k => S k
  | Sum.inr IX.I => i
  | Sum.inr IX.C => cn
  | Sum.inr IX.T => t
  | Sum.inr IX.O => o

section istk

variable (S : ∀ k, List (M.Γ k)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool)

@[simp] theorem istk_M (k : M.K) : istk S i cn t o (Sum.inl k) = S k := rfl
@[simp] theorem istk_I : istk S i cn t o (Sum.inr IX.I) = i := rfl
@[simp] theorem istk_C : istk S i cn t o (Sum.inr IX.C) = cn := rfl
@[simp] theorem istk_T : istk S i cn t o (Sum.inr IX.T) = t := rfl
@[simp] theorem istk_O : istk S i cn t o (Sum.inr IX.O) = o := rfl

theorem istk_set_M (k : M.K) (x : List (M.Γ k)) :
    Function.update (istk S i cn t o) (Sum.inl k) x = istk (Function.update S k x) i cn t o := by
  funext j
  rcases j with j | j
  · by_cases h : j = k
    · subst h
      rw [Function.update_self]
      show x = Function.update S j x j
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show S j = Function.update S k x j
      rw [Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)]; cases j <;> rfl

theorem istk_set_I (i' : List (Bool ⊕ Bool)) :
    Function.update (istk S i cn t o) (Sum.inr IX.I) i' = istk S i' cn t o := by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

theorem istk_set_C (cn' : List Bool) :
    Function.update (istk S i cn t o) (Sum.inr IX.C) cn' = istk S i cn' t o := by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

theorem istk_set_T (t' : List Bool) :
    Function.update (istk S i cn t o) (Sum.inr IX.T) t' = istk S i cn t' o := by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

theorem istk_set_O (o' : List Bool) :
    Function.update (istk S i cn t o) (Sum.inr IX.O) o' = istk S i cn t o' := by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl

end istk

abbrev ICfg (M : FinTM2) : Type := TM2.Cfg (ItΓ M) (ItΛ M) (Itσ M)

def embI (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool)
    (c : TM2.Cfg M.Γ M.Λ M.σ) : ICfg M :=
  ⟨some (c.l.elim (Sum.inr IL.l4) Sum.inl), (c.var, b), istk c.stk i cn t o⟩

theorem simI (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool)
    (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ) (S : ∀ k, List (M.Γ k)) :
    TM2.stepAux (trI q) ((v, b) : Itσ M) (istk S i cn t o) =
      embI b i cn t o (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    have := ih v (Function.update S k (f v :: S k))
    rw [← istk_set_M] at this
    exact this
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    have := ih (f v (S k).head?) (Function.update S k (S k).tail)
    rw [← istk_set_M] at this
    exact this
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [trI, TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f => rfl
  | halt => rfl

theorem stepI (e₀ : Bool → M.Γ M.k₀) (d₀ : M.Γ M.k₀ → Bool) (e₁ : M.Γ M.k₁ → Bool)
    (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool)
    (c c' : TM2.Cfg M.Γ M.Λ M.σ) (h : TM2.step M.m c = some c') :
    TM2.step (iterProg M e₀ d₀ e₁) (embI b i cn t o c) = some (embI b i cn t o c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (simI b i cn t o (M.m l) v S)

theorem embI_init (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool)
    (l : List (M.Γ M.k₀)) :
    embI b i cn t o (initList M l) =
      (⟨some (Sum.inl M.main), (M.initialState, b),
        istk (Function.update (fun _ => []) M.k₀ l) i cn t o⟩ : ICfg M) := by
  rw [initList_eq]; rfl

theorem embI_halt (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool)
    (m : List (M.Γ M.k₁)) :
    embI b i cn t o (haltList M m) =
      (⟨some (Sum.inr IL.l4), (M.initialState, b),
        istk (Function.update (fun _ => []) M.k₁ m) i cn t o⟩ : ICfg M) := by
  rw [haltList_eq]; rfl

theorem istk_nil : (istk (fun _ => []) [] [] [] [] : ∀ k, List (ItΓ M k)) = fun _ => [] := by
  funext j; rcases j with j | (_ | _ | _ | _) <;> rfl

theorem istk_nil_I (i : List (Bool ⊕ Bool)) :
    (istk (fun _ => []) i [] [] [] : ∀ k, List (ItΓ M k)) =
      Function.update (fun _ => [] : ∀ k, List (ItΓ M k)) (Sum.inr IX.I) i :=
  (istk_set_I (fun _ => []) [] [] [] [] i).symm.trans (by rw [istk_nil])

theorem istk_nil_O (o : List Bool) :
    (istk (fun _ => []) [] [] [] o : ∀ k, List (ItΓ M k)) =
      Function.update (fun _ => [] : ∀ k, List (ItΓ M k)) (Sum.inr IX.O) o :=
  (istk_set_O (fun _ => []) [] [] [] [] o).symm.trans (by rw [istk_nil])

end PEqualNP.Library.Machines.Iter

end

section

namespace PEqualNP.Library.Machines.Iter

open Turing PEqualNP.Library

variable {M : FinTM2} (e₀ : Bool → M.Γ M.k₀) (d₀ : M.Γ M.k₀ → Bool) (e₁ : M.Γ M.k₁ → Bool)

variable (v : M.σ) (S : ∀ k, List (M.Γ k))

theorem i1_inl (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool))
    (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l1), (v, b), istk S (Sum.inl a :: i) cn t o⟩ : ICfg M) =
      some ⟨some (Sum.inr IL.l1), (v, some (Sum.inl a)), istk S i cn (a :: t) o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_I, istk_set_T, isFst, bit]

theorem i1_inr (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool))
    (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l1), (v, b), istk S (Sum.inr a :: i) cn t o⟩ : ICfg M) =
      some ⟨some (Sum.inr IL.l1), (v, some (Sum.inr a)), istk S i (a :: cn) t o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_I, istk_set_C, isFst, bit]

theorem i1_nil (b : Option (Bool ⊕ Bool)) (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l1), (v, b), istk S [] cn t o⟩ : ICfg M) =
      some ⟨some (Sum.inr IL.l2), (v, none), istk S [] cn t o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_I]

theorem iloop1 (o : List Bool) :
    ∀ (i : List (Bool ⊕ Bool)) (cn t : List Bool) (b : Option (Bool ⊕ Bool)),
    ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[i.length + 1]
        (some (⟨some (Sum.inr IL.l1), (v, b), istk S i cn t o⟩ : ICfg M)) =
      some ⟨some (Sum.inr IL.l2), (v, none),
        istk S [] ((i.filterMap Sum.getRight?).reverse ++ cn)
          ((i.filterMap Sum.getLeft?).reverse ++ t) o⟩ := by
  intro i
  induction i with
  | nil => intro cn t b; exact i1_nil e₀ d₀ e₁ v S b cn t o
  | cons x i ih =>
    intro cn t b
    rw [List.length_cons, Function.iterate_succ_apply]
    cases x with
    | inl a =>
      have e : (flip bind (TM2.step (iterProg M e₀ d₀ e₁)))
          (some (⟨some (Sum.inr IL.l1), (v, b), istk S (Sum.inl a :: i) cn t o⟩ : ICfg M)) =
          some ⟨some (Sum.inr IL.l1), (v, some (Sum.inl a)), istk S i cn (a :: t) o⟩ :=
        i1_inl e₀ d₀ e₁ v S b a i cn t o
      rw [e, ih]; simp [List.filterMap_cons]
    | inr a =>
      have e : (flip bind (TM2.step (iterProg M e₀ d₀ e₁)))
          (some (⟨some (Sum.inr IL.l1), (v, b), istk S (Sum.inr a :: i) cn t o⟩ : ICfg M)) =
          some ⟨some (Sum.inr IL.l1), (v, some (Sum.inr a)), istk S i (a :: cn) t o⟩ :=
        i1_inr e₀ d₀ e₁ v S b a i cn t o
      rw [e, ih]; simp [List.filterMap_cons]

theorem i2_cons (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool))
    (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l2), (v, b), istk S i cn (a :: t) o⟩ : ICfg M) =
      some ⟨some (Sum.inr IL.l2), (v, some (Sum.inl a)),
        istk (Function.update S M.k₀ (e₀ a :: S M.k₀)) i cn t o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_T, istk_set_M, bit]

theorem i2_nil (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l2), (v, b), istk S i cn [] o⟩ : ICfg M) =
      some ⟨some (Sum.inr IL.l3), (v, none), istk S i cn [] o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_T]

theorem iloop2 (i : List (Bool ⊕ Bool)) (cn o : List Bool) :
    ∀ (t : List Bool) (S : ∀ k, List (M.Γ k)) (b : Option (Bool ⊕ Bool)),
    ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[t.length + 1]
        (some (⟨some (Sum.inr IL.l2), (v, b), istk S i cn t o⟩ : ICfg M)) =
      some ⟨some (Sum.inr IL.l3), (v, none),
        istk (Function.update S M.k₀ (t.reverse.map e₀ ++ S M.k₀)) i cn [] o⟩ := by
  intro t
  induction t with
  | nil =>
    intro S b
    have : Function.update S M.k₀ (([] : List Bool).reverse.map e₀ ++ S M.k₀) = S := by simp
    rw [this]
    exact i2_nil e₀ d₀ e₁ v S b i cn o
  | cons a t ih =>
    intro S b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : (flip bind (TM2.step (iterProg M e₀ d₀ e₁)))
        (some (⟨some (Sum.inr IL.l2), (v, b), istk S i cn (a :: t) o⟩ : ICfg M)) =
        some ⟨some (Sum.inr IL.l2), (v, some (Sum.inl a)),
          istk (Function.update S M.k₀ (e₀ a :: S M.k₀)) i cn t o⟩ :=
      i2_cons e₀ d₀ e₁ v S b a i cn t o
    rw [e, ih]; simp

theorem i3_cons (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool))
    (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l3), (v, b), istk S i (a :: cn) t o⟩ : ICfg M) =
      some ⟨some (Sum.inl M.main), (v, some (Sum.inl a)), istk S i cn t o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_C]

theorem i3_nil (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l3), (v, b), istk S i [] t o⟩ : ICfg M) =
      some ⟨some (Sum.inr IL.l5), (v, none), istk S i [] t o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_C]

theorem i4_cons (b : Option (Bool ⊕ Bool)) (y : M.Γ M.k₁) (m : List (M.Γ M.k₁))
    (i : List (Bool ⊕ Bool)) (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l4), (v, b), istk (Function.update S M.k₁ (y :: m)) i cn t o⟩ :
          ICfg M) =
      some ⟨some (Sum.inr IL.l4), (v, some (Sum.inl (e₁ y))),
        istk (Function.update S M.k₁ m) i cn (e₁ y :: t) o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_T, istk_set_M, bit]

theorem i4_nil (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l4), (v, b), istk (Function.update S M.k₁ []) i cn t o⟩ : ICfg M) =
      some ⟨some (Sum.inr IL.l2), (v, none), istk (Function.update S M.k₁ []) i cn t o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_M]

theorem iloop4 (i : List (Bool ⊕ Bool)) (cn o : List Bool) :
    ∀ (m : List (M.Γ M.k₁)) (t : List Bool) (b : Option (Bool ⊕ Bool)),
    ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[m.length + 1]
        (some (⟨some (Sum.inr IL.l4), (v, b), istk (Function.update S M.k₁ m) i cn t o⟩ :
          ICfg M)) =
      some ⟨some (Sum.inr IL.l2), (v, none),
        istk (Function.update S M.k₁ []) i cn (m.reverse.map e₁ ++ t) o⟩ := by
  intro m
  induction m with
  | nil => intro t b; exact i4_nil e₀ d₀ e₁ v S b i cn t o
  | cons y m ih =>
    intro t b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : (flip bind (TM2.step (iterProg M e₀ d₀ e₁)))
        (some (⟨some (Sum.inr IL.l4), (v, b),
          istk (Function.update S M.k₁ (y :: m)) i cn t o⟩ : ICfg M)) =
        some ⟨some (Sum.inr IL.l4), (v, some (Sum.inl (e₁ y))),
          istk (Function.update S M.k₁ m) i cn (e₁ y :: t) o⟩ :=
      i4_cons e₀ d₀ e₁ v S b y m i cn t o
    rw [e, ih]; simp

theorem i5_cons (b : Option (Bool ⊕ Bool)) (y : M.Γ M.k₀) (m : List (M.Γ M.k₀))
    (i : List (Bool ⊕ Bool)) (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l5), (v, b), istk (Function.update S M.k₀ (y :: m)) i cn t o⟩ :
          ICfg M) =
      some ⟨some (Sum.inr IL.l5), (v, some (Sum.inl (d₀ y))),
        istk (Function.update S M.k₀ m) i cn (d₀ y :: t) o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_T, istk_set_M, bit]

theorem i5_nil (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l5), (v, b), istk (Function.update S M.k₀ []) i cn t o⟩ : ICfg M) =
      some ⟨some (Sum.inr IL.l6), (v, none), istk (Function.update S M.k₀ []) i cn t o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_M]

theorem iloop5 (i : List (Bool ⊕ Bool)) (cn o : List Bool) :
    ∀ (m : List (M.Γ M.k₀)) (t : List Bool) (b : Option (Bool ⊕ Bool)),
    ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[m.length + 1]
        (some (⟨some (Sum.inr IL.l5), (v, b), istk (Function.update S M.k₀ m) i cn t o⟩ :
          ICfg M)) =
      some ⟨some (Sum.inr IL.l6), (v, none),
        istk (Function.update S M.k₀ []) i cn (m.reverse.map d₀ ++ t) o⟩ := by
  intro m
  induction m with
  | nil => intro t b; exact i5_nil e₀ d₀ e₁ v S b i cn t o
  | cons y m ih =>
    intro t b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : (flip bind (TM2.step (iterProg M e₀ d₀ e₁)))
        (some (⟨some (Sum.inr IL.l5), (v, b),
          istk (Function.update S M.k₀ (y :: m)) i cn t o⟩ : ICfg M)) =
        some ⟨some (Sum.inr IL.l5), (v, some (Sum.inl (d₀ y))),
          istk (Function.update S M.k₀ m) i cn (d₀ y :: t) o⟩ :=
      i5_cons e₀ d₀ e₁ v S b y m i cn t o
    rw [e, ih]; simp

theorem i6_cons (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool))
    (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l6), (v, b), istk S i cn (a :: t) o⟩ : ICfg M) =
      some ⟨some (Sum.inr IL.l6), (v, some (Sum.inl a)), istk S i cn t (a :: o)⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_T, istk_set_O, bit]

theorem i6_nil (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l6), (v, b), istk S i cn [] o⟩ : ICfg M) =
      some ⟨none, (v, none), istk S i cn [] o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_T]

theorem iloop6 (i : List (Bool ⊕ Bool)) (cn : List Bool) :
    ∀ (t o : List Bool) (b : Option (Bool ⊕ Bool)),
    ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[t.length + 1]
        (some (⟨some (Sum.inr IL.l6), (v, b), istk S i cn t o⟩ : ICfg M)) =
      some ⟨none, (v, none), istk S i cn [] (t.reverse ++ o)⟩ := by
  intro t
  induction t with
  | nil => intro o b; exact i6_nil e₀ d₀ e₁ v S b i cn o
  | cons a t ih =>
    intro o b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : (flip bind (TM2.step (iterProg M e₀ d₀ e₁)))
        (some (⟨some (Sum.inr IL.l6), (v, b), istk S i cn (a :: t) o⟩ : ICfg M)) =
        some ⟨some (Sum.inr IL.l6), (v, some (Sum.inl a)), istk S i cn t (a :: o)⟩ :=
      i6_cons e₀ d₀ e₁ v S b a i cn t o
    rw [e, ih]; simp

theorem update_nil_nil (k : M.K) :
    Function.update (fun _ => [] : ∀ k, List (M.Γ k)) k [] = fun _ => [] :=
  Function.update_eq_self k (fun _ => [] : ∀ k, List (M.Γ k))

theorem main_loop (g : List Bool → List Bool) (k : ℕ) (p : Polynomial ℕ)
    (hk : ∀ y : List Bool, (g y).length ≤ y.length + k)
    (hd : ∀ a, d₀ (e₀ a) = a)
    (hrun : ∀ z : List Bool, ∃ (s : ℕ) (m : List (M.Γ M.k₁)), s ≤ p.eval z.length ∧
      (flip bind (TM2.step M.m))^[s] (some (initList M (z.map e₀))) = some (haltList M m) ∧
        m.map e₁ = g z) :
    ∀ (cn z : List Bool) (L : ℕ) (b : Option (Bool ⊕ Bool)), z.length + k * cn.length ≤ L →
      ∃ n, n ≤ cn.length * (p.eval L + 2 * L + 3) + 2 * L + 3 ∧
        ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[n]
            (some (⟨some (Sum.inr IL.l3), (M.initialState, b),
              istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] cn [] []⟩ : ICfg M)) =
          some ⟨none, (M.initialState, none),
            istk (fun _ => []) [] [] [] (g^[cn.length] z)⟩ := by
  intro cn
  induction cn with
  | nil =>
    intro z L b hL
    have hz : ((z.map e₀).reverse.map d₀).reverse = z := by
      rw [List.map_reverse, List.reverse_reverse, List.map_map]
      conv_rhs => rw [← List.map_id z]
      exact List.map_congr_left fun a _ => hd a
    have q1 : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[1]
        (some (⟨some (Sum.inr IL.l3), (M.initialState, b),
          istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] [] [] []⟩ : ICfg M)) =
        some ⟨some (Sum.inr IL.l5), (M.initialState, none),
          istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] [] [] []⟩ :=
      i3_nil e₀ d₀ e₁ M.initialState _ b [] [] []
    have q2 := iloop5 e₀ d₀ e₁ M.initialState (fun _ => []) [] [] [] (z.map e₀) [] none
    rw [update_nil_nil, List.append_nil] at q2
    have q3 := iloop6 e₀ d₀ e₁ M.initialState (fun _ => []) [] []
      ((z.map e₀).reverse.map d₀) [] none
    rw [List.append_nil, hz] at q3
    refine ⟨_, ?_, iter_trans _ (iter_trans _ q1 q2) q3⟩
    simp only [List.length_reverse, List.length_map, List.length_nil] at hL ⊢
    omega
  | cons a cn ih =>
    intro z L b hL
    obtain ⟨s, m, hs, hm, hmg⟩ := hrun z
    rw [List.length_cons] at hL
    have hgz : (g z).length ≤ z.length + k := hk z
    have hkk : k * (cn.length + 1) = k * cn.length + k := Nat.mul_succ _ _
    have hml : m.length = (g z).length := by rw [← hmg, List.length_map]
    have q1 : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[1]
        (some (⟨some (Sum.inr IL.l3), (M.initialState, b),
          istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] (a :: cn) [] []⟩ : ICfg M)) =
        some (embI (some (Sum.inl a)) [] cn [] [] (initList M (z.map e₀))) := by
      rw [embI_init]
      exact i3_cons e₀ d₀ e₁ M.initialState _ b a [] cn [] []
    have q2 := simulate (TM2.step M.m) (TM2.step (iterProg M e₀ d₀ e₁))
      (embI (some (Sum.inl a)) [] cn [] []) (stepI e₀ d₀ e₁ (some (Sum.inl a)) [] cn [] [])
      s _ _ hm
    rw [embI_halt] at q2
    have q3 := iloop4 e₀ d₀ e₁ M.initialState (fun _ => []) [] cn [] m [] (some (Sum.inl a))
    rw [update_nil_nil, List.append_nil, List.map_reverse, hmg] at q3
    have q4 := iloop2 e₀ d₀ e₁ M.initialState [] cn [] (g z).reverse (fun _ => []) none
    rw [List.append_nil, List.reverse_reverse] at q4
    obtain ⟨n, hn, q5⟩ := ih (g z) L none (by omega)
    have e : g^[(a :: cn).length] z = g^[cn.length] (g z) := Function.iterate_succ_apply g _ z
    rw [e]
    refine ⟨_, ?_, iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ q1 q2) q3) q4) q5⟩
    have hp : p.eval z.length ≤ p.eval L := eval_mono p (by omega)
    rw [List.length_reverse, List.length_cons, Nat.succ_mul]
    generalize cn.length * (p.eval L + 2 * L + 3) = A at hn ⊢
    omega

theorem iter_run (g : List Bool → List Bool) (k : ℕ) (p : Polynomial ℕ)
    (hk : ∀ y : List Bool, (g y).length ≤ y.length + k)
    (hd : ∀ a, d₀ (e₀ a) = a)
    (hrun : ∀ z : List Bool, ∃ (s : ℕ) (m : List (M.Γ M.k₁)), s ≤ p.eval z.length ∧
      (flip bind (TM2.step M.m))^[s] (some (initList M (z.map e₀))) = some (haltList M m) ∧
        m.map e₁ = g z)
    (y u : List Bool) (L : ℕ) (hL : y.length + k * u.length ≤ L) :
    ∃ n, n ≤ u.length * (p.eval L + 2 * L + 3) + 2 * L + 2 * y.length + u.length + 5 ∧
      ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[n] (some (initList (iterM M e₀ d₀ e₁) (encodePair (y, u)))) =
        some (haltList (iterM M e₀ d₀ e₁) (g^[u.length] y)) := by
  have q1 : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[(encodePair (y, u)).length + 1]
      (some (initList (iterM M e₀ d₀ e₁) (encodePair (y, u)))) =
      some (⟨some (Sum.inr IL.l2), (M.initialState, none),
        istk (fun _ => []) [] u.reverse y.reverse []⟩ : ICfg M) := by
    have := iloop1 e₀ d₀ e₁ M.initialState (fun _ => []) [] (encodePair (y, u)) [] [] none
    rw [encodePair_left, encodePair_right, List.append_nil, List.append_nil, istk_nil_I] at this
    exact (congrArg (fun c => ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[(encodePair (y, u)).length + 1] (some c))
      (initList_eq (iterM M e₀ d₀ e₁) (encodePair (y, u)))).trans this
  have q2 := iloop2 e₀ d₀ e₁ M.initialState [] u.reverse [] y.reverse (fun _ => []) none
  rw [List.append_nil, List.reverse_reverse] at q2
  obtain ⟨n, hn, q3⟩ := main_loop e₀ d₀ e₁ g k p hk hd hrun u.reverse y L none
    (by rw [List.length_reverse]; exact hL)
  rw [List.length_reverse] at hn q3
  rw [istk_nil_O] at q3
  have q3' : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[n]
      (some (⟨some (Sum.inr IL.l3), (M.initialState, none),
        istk (Function.update (fun _ => []) M.k₀ (y.map e₀)) [] u.reverse [] []⟩ : ICfg M)) =
      some (haltList (iterM M e₀ d₀ e₁) (g^[u.length] y)) :=
    q3.trans (congrArg some (haltList_eq (iterM M e₀ d₀ e₁) (g^[u.length] y))).symm
  refine ⟨_, ?_, iter_trans _ (iter_trans _ q1 q2) q3'⟩
  rw [encodePair_length, List.length_reverse]
  omega

theorem iter_polyTime (g : List Bool → List Bool)
    (c : Turing.TM2ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) g)
    (k : ℕ) (hk : ∀ y : List Bool, (g y).length ≤ y.length + k) :
    Nonempty (Turing.TM2ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x : List Bool => x)
      (fun p : List Bool × List Bool => g^[p.2.length] p.1)) := by
  let e₀ : Bool → c.tm.Γ c.tm.k₀ := c.inputAlphabet.invFun
  let d₀ : c.tm.Γ c.tm.k₀ → Bool := c.inputAlphabet
  let e₁ : c.tm.Γ c.tm.k₁ → Bool := c.outputAlphabet
  let W : Polynomial ℕ := Polynomial.X + Polynomial.C k * Polynomial.X
  let T : Polynomial ℕ :=
    Polynomial.X * (c.time.comp W + Polynomial.C 2 * W + Polynomial.C 3) +
      Polynomial.C 2 * W + Polynomial.C 3 * Polynomial.X + Polynomial.C 5
  have hd : ∀ a, d₀ (e₀ a) = a := fun a => c.inputAlphabet.right_inv a
  have hrun : ∀ z : List Bool, ∃ (s : ℕ) (m : List (c.tm.Γ c.tm.k₁)),
      s ≤ c.time.eval z.length ∧
      (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm (z.map e₀))) =
        some (haltList c.tm m) ∧ m.map e₁ = g z := by
    intro z
    refine ⟨(c.outputsFun z).steps, List.map c.outputAlphabet.invFun (g z),
      (c.outputsFun z).steps_le_m, (c.outputsFun z).evals_in_steps, ?_⟩
    rw [List.map_map]
    conv_rhs => rw [← List.map_id (g z)]
    exact List.map_congr_left fun y _ => c.outputAlphabet.right_inv y
  have key : ∀ q : List Bool × List Bool, ∃ n, n ≤ T.eval (encodePair q).length ∧
      (flip bind (TM2.step (iterProg c.tm e₀ d₀ e₁)))^[n]
          (some (initList (iterM c.tm e₀ d₀ e₁) (encodePair q))) =
        some (haltList (iterM c.tm e₀ d₀ e₁) (g^[q.2.length] q.1)) := by
    rintro ⟨y, u⟩
    have hku : k * u.length ≤ k * (y.length + u.length) := Nat.mul_le_mul_left _ (by omega)
    obtain ⟨n, hn, hr⟩ := iter_run e₀ d₀ e₁ g k c.time hk hd hrun y u
      (y.length + u.length + k * (y.length + u.length)) (by omega)
    refine ⟨n, hn.trans ?_, hr⟩
    simp only [T, W, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_comp, encodePair_length]
    have hmul : u.length * (Polynomial.eval (y.length + u.length + k * (y.length + u.length))
          c.time + 2 * (y.length + u.length + k * (y.length + u.length)) + 3) ≤
        (y.length + u.length) * (Polynomial.eval
          (y.length + u.length + k * (y.length + u.length)) c.time +
            2 * (y.length + u.length + k * (y.length + u.length)) + 3) :=
      Nat.mul_le_mul_right _ (by omega)
    generalize k * (y.length + u.length) = B at hmul ⊢
    omega
  exact ⟨{
    tm := iterM c.tm e₀ d₀ e₁
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := T
    outputsFun := fun q =>
      { steps := Classical.choose (key q)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          exact (congrArg (fun l => (flip bind (TM2.step (iterProg c.tm e₀ d₀ e₁)))^[
            Classical.choose (key q)] (some (initList (iterM c.tm e₀ d₀ e₁) l)))
            (hm _ (encodePair q))).trans ((Classical.choose_spec (key q)).2.trans
            (congrArg (fun l => some (haltList (iterM c.tm e₀ d₀ e₁) l))
              (hm _ (g^[q.2.length] q.1)).symm))
        steps_le_m := (Classical.choose_spec (key q)).1 } }⟩

end PEqualNP.Library.Machines.Iter

end

section

namespace PEqualNP.Library.Machines.Iter

open Turing PEqualNP.Library

variable {M : FinTM2} (e₀ : Bool → M.Γ M.k₀) (d₀ : M.Γ M.k₀ → Bool) (e₁ : M.Γ M.k₁ → Bool)

theorem main_loop_bdd (g : List Bool → List Bool) (p : Polynomial ℕ)
    (hd : ∀ a, d₀ (e₀ a) = a)
    (hrun : ∀ z : List Bool, ∃ (s : ℕ) (m : List (M.Γ M.k₁)), s ≤ p.eval z.length ∧
      (flip bind (TM2.step M.m))^[s] (some (initList M (z.map e₀))) = some (haltList M m) ∧
        m.map e₁ = g z) :
    ∀ (cn z : List Bool) (L : ℕ) (b : Option (Bool ⊕ Bool)),
      (∀ j ≤ cn.length, (g^[j] z).length ≤ L) →
      ∃ n, n ≤ cn.length * (p.eval L + 2 * L + 3) + 2 * L + 3 ∧
        ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[n]
            (some (⟨some (Sum.inr IL.l3), (M.initialState, b),
              istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] cn [] []⟩ : ICfg M)) =
          some ⟨none, (M.initialState, none),
            istk (fun _ => []) [] [] [] (g^[cn.length] z)⟩ := by
  intro cn
  induction cn with
  | nil =>
    intro z L b hL
    have hz : ((z.map e₀).reverse.map d₀).reverse = z := by
      rw [List.map_reverse, List.reverse_reverse, List.map_map]
      conv_rhs => rw [← List.map_id z]
      exact List.map_congr_left fun a _ => hd a
    have q1 : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[1]
        (some (⟨some (Sum.inr IL.l3), (M.initialState, b),
          istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] [] [] []⟩ : ICfg M)) =
        some ⟨some (Sum.inr IL.l5), (M.initialState, none),
          istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] [] [] []⟩ :=
      i3_nil e₀ d₀ e₁ M.initialState _ b [] [] []
    have q2 := iloop5 e₀ d₀ e₁ M.initialState (fun _ => []) [] [] [] (z.map e₀) [] none
    rw [update_nil_nil, List.append_nil] at q2
    have q3 := iloop6 e₀ d₀ e₁ M.initialState (fun _ => []) [] []
      ((z.map e₀).reverse.map d₀) [] none
    rw [List.append_nil, hz] at q3
    refine ⟨_, ?_, iter_trans _ (iter_trans _ q1 q2) q3⟩
    have hz0 : z.length ≤ L := hL 0 (Nat.zero_le _)
    simp only [List.length_reverse, List.length_map, List.length_nil] at hz0 ⊢
    omega
  | cons a cn ih =>
    intro z L b hL
    obtain ⟨s, m, hs, hm, hmg⟩ := hrun z
    rw [List.length_cons] at hL
    have hz0 : z.length ≤ L := hL 0 (Nat.zero_le _)
    have hgz : (g z).length ≤ L := hL 1 (by omega)
    have hml : m.length = (g z).length := by rw [← hmg, List.length_map]
    have q1 : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[1]
        (some (⟨some (Sum.inr IL.l3), (M.initialState, b),
          istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] (a :: cn) [] []⟩ : ICfg M)) =
        some (embI (some (Sum.inl a)) [] cn [] [] (initList M (z.map e₀))) := by
      rw [embI_init]
      exact i3_cons e₀ d₀ e₁ M.initialState _ b a [] cn [] []
    have q2 := simulate (TM2.step M.m) (TM2.step (iterProg M e₀ d₀ e₁))
      (embI (some (Sum.inl a)) [] cn [] []) (stepI e₀ d₀ e₁ (some (Sum.inl a)) [] cn [] [])
      s _ _ hm
    rw [embI_halt] at q2
    have q3 := iloop4 e₀ d₀ e₁ M.initialState (fun _ => []) [] cn [] m [] (some (Sum.inl a))
    rw [update_nil_nil, List.append_nil, List.map_reverse, hmg] at q3
    have q4 := iloop2 e₀ d₀ e₁ M.initialState [] cn [] (g z).reverse (fun _ => []) none
    rw [List.append_nil, List.reverse_reverse] at q4
    obtain ⟨n, hn, q5⟩ := ih (g z) L none (fun j hj => by
      have := hL (j + 1) (by omega)
      rwa [Function.iterate_succ_apply] at this)
    have e : g^[(a :: cn).length] z = g^[cn.length] (g z) := Function.iterate_succ_apply g _ z
    rw [e]
    refine ⟨_, ?_, iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ q1 q2) q3) q4) q5⟩
    have hp : p.eval z.length ≤ p.eval L := eval_mono p (by omega)
    rw [List.length_reverse, List.length_cons, Nat.succ_mul]
    generalize cn.length * (p.eval L + 2 * L + 3) = A at hn ⊢
    omega

theorem iter_run_bdd (g : List Bool → List Bool) (p : Polynomial ℕ)
    (hd : ∀ a, d₀ (e₀ a) = a)
    (hrun : ∀ z : List Bool, ∃ (s : ℕ) (m : List (M.Γ M.k₁)), s ≤ p.eval z.length ∧
      (flip bind (TM2.step M.m))^[s] (some (initList M (z.map e₀))) = some (haltList M m) ∧
        m.map e₁ = g z)
    (y u : List Bool) (L : ℕ) (hL : ∀ j ≤ u.length, (g^[j] y).length ≤ L) :
    ∃ n, n ≤ u.length * (p.eval L + 2 * L + 3) + 2 * L + 2 * y.length + u.length + 5 ∧
      ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[n] (some (initList (iterM M e₀ d₀ e₁) (encodePair (y, u)))) =
        some (haltList (iterM M e₀ d₀ e₁) (g^[u.length] y)) := by
  have q1 : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[(encodePair (y, u)).length + 1]
      (some (initList (iterM M e₀ d₀ e₁) (encodePair (y, u)))) =
      some (⟨some (Sum.inr IL.l2), (M.initialState, none),
        istk (fun _ => []) [] u.reverse y.reverse []⟩ : ICfg M) := by
    have := iloop1 e₀ d₀ e₁ M.initialState (fun _ => []) [] (encodePair (y, u)) [] [] none
    rw [encodePair_left, encodePair_right, List.append_nil, List.append_nil, istk_nil_I] at this
    exact (congrArg (fun c => ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[(encodePair (y, u)).length + 1] (some c))
      (initList_eq (iterM M e₀ d₀ e₁) (encodePair (y, u)))).trans this
  have q2 := iloop2 e₀ d₀ e₁ M.initialState [] u.reverse [] y.reverse (fun _ => []) none
  rw [List.append_nil, List.reverse_reverse] at q2
  obtain ⟨n, hn, q3⟩ := main_loop_bdd e₀ d₀ e₁ g p hd hrun u.reverse y L none
    (by rw [List.length_reverse]; exact hL)
  rw [List.length_reverse] at hn q3
  rw [istk_nil_O] at q3
  have q3' : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[n]
      (some (⟨some (Sum.inr IL.l3), (M.initialState, none),
        istk (Function.update (fun _ => []) M.k₀ (y.map e₀)) [] u.reverse [] []⟩ : ICfg M)) =
      some (haltList (iterM M e₀ d₀ e₁) (g^[u.length] y)) :=
    q3.trans (congrArg some (haltList_eq (iterM M e₀ d₀ e₁) (g^[u.length] y))).symm
  refine ⟨_, ?_, iter_trans _ (iter_trans _ q1 q2) q3'⟩
  rw [encodePair_length, List.length_reverse]
  omega

theorem iterate_length_measure (g : List Bool → List Bool) (m : List Bool → ℕ)
    (hm : ∀ y : List Bool, m (g y) ≤ m y)
    (hg : ∀ y : List Bool, (g y).length ≤ y.length + m y) (y : List Bool) :
    ∀ j : ℕ, m (g^[j] y) ≤ m y ∧ (g^[j] y).length ≤ y.length + j * m y := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', Nat.succ_mul]
    have h1 := hm (g^[j] y)
    have h2 := hg (g^[j] y)
    obtain ⟨i1, i2⟩ := ih
    generalize j * m y = A at i2 ⊢
    exact ⟨by omega, by omega⟩

theorem measure_arith (A B L V y u : ℕ) (hLV : L ≤ V) (hAB : A ≤ B) :
    A + 2 * L + 2 * y + u + 5 ≤ B + 2 * V + 3 * (y + u) + 5 := by
  omega

theorem iter_polyTime_measure (g : List Bool → List Bool)
    (c : Turing.TM2ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) g)
    (m : List Bool → ℕ) (a : ℕ)
    (hm : ∀ y : List Bool, m (g y) ≤ m y)
    (hg : ∀ y : List Bool, (g y).length ≤ y.length + m y)
    (ha : ∀ y : List Bool, m y ≤ a * y.length + a) :
    Nonempty (Turing.TM2ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x : List Bool => x) (fun p : List Bool × List Bool => g^[p.2.length] p.1)) := by
  let e₀ : Bool → c.tm.Γ c.tm.k₀ := c.inputAlphabet.invFun
  let d₀ : c.tm.Γ c.tm.k₀ → Bool := c.inputAlphabet
  let e₁ : c.tm.Γ c.tm.k₁ → Bool := c.outputAlphabet
  let W : Polynomial ℕ :=
    Polynomial.X + Polynomial.X * (Polynomial.C a * Polynomial.X + Polynomial.C a)
  let T : Polynomial ℕ :=
    Polynomial.X * (c.time.comp W + Polynomial.C 2 * W + Polynomial.C 3) +
      Polynomial.C 2 * W + Polynomial.C 3 * Polynomial.X + Polynomial.C 5
  have hd : ∀ a, d₀ (e₀ a) = a := fun a => c.inputAlphabet.right_inv a
  have hrun : ∀ z : List Bool, ∃ (s : ℕ) (m : List (c.tm.Γ c.tm.k₁)),
      s ≤ c.time.eval z.length ∧
      (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm (z.map e₀))) =
        some (haltList c.tm m) ∧ m.map e₁ = g z := by
    intro z
    refine ⟨(c.outputsFun z).steps, List.map c.outputAlphabet.invFun (g z),
      (c.outputsFun z).steps_le_m, (c.outputsFun z).evals_in_steps, ?_⟩
    rw [List.map_map]
    conv_rhs => rw [← List.map_id (g z)]
    exact List.map_congr_left fun y _ => c.outputAlphabet.right_inv y
  have key : ∀ q : List Bool × List Bool, ∃ n, n ≤ T.eval (encodePair q).length ∧
      (flip bind (TM2.step (iterProg c.tm e₀ d₀ e₁)))^[n]
          (some (initList (iterM c.tm e₀ d₀ e₁) (encodePair q))) =
        some (haltList (iterM c.tm e₀ d₀ e₁) (g^[q.2.length] q.1)) := by
    rintro ⟨y, u⟩
    have hL : ∀ j ≤ u.length,
        (g^[j] y).length ≤ y.length + u.length * (a * y.length + a) := by
      intro j hj
      have h1 := (iterate_length_measure g m hm hg y j).2
      have h2 : j * m y ≤ u.length * (a * y.length + a) := Nat.mul_le_mul hj (ha y)
      omega
    obtain ⟨n, hn, hr⟩ := iter_run_bdd e₀ d₀ e₁ g c.time hd hrun y u
      (y.length + u.length * (a * y.length + a)) hL
    have hLV : y.length + u.length * (a * y.length + a) ≤
        (y.length + u.length) + (y.length + u.length) * (a * (y.length + u.length) + a) :=
      Nat.add_le_add (by omega) (Nat.mul_le_mul (by omega)
        (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _))
    have hp := eval_mono c.time hLV
    have hmul : u.length * (Polynomial.eval (y.length + u.length * (a * y.length + a)) c.time +
          2 * (y.length + u.length * (a * y.length + a)) + 3) ≤
        (y.length + u.length) * (Polynomial.eval
          ((y.length + u.length) + (y.length + u.length) * (a * (y.length + u.length) + a))
            c.time +
            2 * ((y.length + u.length) +
              (y.length + u.length) * (a * (y.length + u.length) + a)) + 3) :=
      Nat.mul_le_mul (by omega) (by omega)
    refine ⟨n, hn.trans ?_, hr⟩
    simp only [T, W, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_comp, encodePair_length]
    exact measure_arith _ _ _ _ _ _ hLV hmul
  exact ⟨{
    tm := iterM c.tm e₀ d₀ e₁
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := T
    outputsFun := fun q =>
      { steps := Classical.choose (key q)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          exact (congrArg (fun l => (flip bind (TM2.step (iterProg c.tm e₀ d₀ e₁)))^[
            Classical.choose (key q)] (some (initList (iterM c.tm e₀ d₀ e₁) l)))
            (hm _ (encodePair q))).trans ((Classical.choose_spec (key q)).2.trans
            (congrArg (fun l => some (haltList (iterM c.tm e₀ d₀ e₁) l))
              (hm _ (g^[q.2.length] q.1)).symm))
        steps_le_m := (Classical.choose_spec (key q)).1 } }⟩

end PEqualNP.Library.Machines.Iter

end

section

namespace PEqualNP.Library.Machines.Gen

open Turing PEqualNP.Library.Machines

def gpair {A C : Type} (p : List A × List C) : List (A ⊕ C) :=
  p.1.map Sum.inl ++ p.2.map Sum.inr

inductive FX
  | I | W | TA | TB | O
  deriving DecidableEq

instance : Fintype FX :=
  Fintype.ofList [FX.I, FX.W, FX.TA, FX.TB, FX.O] (fun x => by cases x <;> simp)

inductive FL
  | l1 | l2 | l3 | l4 | l5
  deriving DecidableEq

instance : Fintype FL :=
  Fintype.ofList [FL.l1, FL.l2, FL.l3, FL.l4, FL.l5] (fun x => by cases x <;> simp)

variable (M : FinTM2) (A B C : Type)

abbrev FstΓ : M.K ⊕ FX → Type
  | Sum.inl k => M.Γ k
  | Sum.inr FX.I => A ⊕ C
  | Sum.inr FX.W => C
  | Sum.inr FX.TA => A
  | Sum.inr FX.TB => B
  | Sum.inr FX.O => B ⊕ C

abbrev FstΛ : Type := M.Λ ⊕ FL

abbrev Fstσ : Type := M.σ × Option (A ⊕ B ⊕ C)

variable {A B C}

def getA [Inhabited A] : Option (A ⊕ B ⊕ C) → A
  | some (Sum.inl a) => a
  | _ => default

def getB [Inhabited B] : Option (A ⊕ B ⊕ C) → B
  | some (Sum.inr (Sum.inl b)) => b
  | _ => default

def getC [Inhabited C] : Option (A ⊕ B ⊕ C) → C
  | some (Sum.inr (Sum.inr c)) => c
  | _ => default

def isA : Option (A ⊕ B ⊕ C) → Bool
  | some (Sum.inl _) => true
  | _ => false

def ofI : A ⊕ C → A ⊕ B ⊕ C
  | Sum.inl a => Sum.inl a
  | Sum.inr c => Sum.inr (Sum.inr c)

variable {M}
variable (A B C)

def trF : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (FstΓ M A B C) (FstΛ M) (Fstσ M A B C)
  | .push k f q => .push (Sum.inl k) (fun s => f s.1) (trF q)
  | .peek k f q => .peek (Sum.inl k) (fun s o => (f s.1 o, s.2)) (trF q)
  | .pop k f q => .pop (Sum.inl k) (fun s o => (f s.1 o, s.2)) (trF q)
  | .load a q => .load (fun s => (a s.1, s.2)) (trF q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1) (trF q₁) (trF q₂)
  | .goto f => .goto (fun s => Sum.inl (f s.1))
  | .halt => .goto (fun _ => Sum.inr FL.l3)

variable (M) {A B}
variable [Inhabited A] [Inhabited B] [Inhabited C]

def firstProg (e₀ : A → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → B) :
    FstΛ M → TM2.Stmt (FstΓ M A B C) (FstΛ M) (Fstσ M A B C)
  | Sum.inl l => trF A B C (M.m l)
  | Sum.inr FL.l1 =>
    .pop (Sum.inr FX.I) (fun s o => (s.1, o.map ofI))
      (.branch (fun s => s.2.isSome)
        (.branch (fun s => isA s.2)
          (.push (Sum.inr FX.TA) (fun s => getA s.2) (.goto fun _ => Sum.inr FL.l1))
          (.push (Sum.inr FX.W) (fun s => getC s.2) (.goto fun _ => Sum.inr FL.l1)))
        (.goto fun _ => Sum.inr FL.l2))
  | Sum.inr FL.l2 =>
    .pop (Sum.inr FX.TA) (fun s o => (s.1, o.map Sum.inl))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inl M.k₀) (fun s => e₀ (getA s.2)) (.goto fun _ => Sum.inr FL.l2))
        (.goto fun _ => Sum.inl M.main))
  | Sum.inr FL.l3 =>
    .pop (Sum.inr FX.W) (fun s o => (s.1, o.map fun c => Sum.inr (Sum.inr c)))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr FX.O) (fun s => Sum.inr (getC s.2)) (.goto fun _ => Sum.inr FL.l3))
        (.goto fun _ => Sum.inr FL.l4))
  | Sum.inr FL.l4 =>
    .pop (Sum.inl M.k₁) (fun s o => (s.1, o.map fun y => Sum.inr (Sum.inl (e₁ y))))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr FX.TB) (fun s => getB s.2) (.goto fun _ => Sum.inr FL.l4))
        (.goto fun _ => Sum.inr FL.l5))
  | Sum.inr FL.l5 =>
    .pop (Sum.inr FX.TB) (fun s o => (s.1, o.map fun b => Sum.inr (Sum.inl b)))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr FX.O) (fun s => Sum.inl (getB s.2)) (.goto fun _ => Sum.inr FL.l5))
        .halt)

def firstM [Fintype A] [Fintype B] [Fintype C] (e₀ : A → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → B) :
    FinTM2 :=
  haveI := M.kFin
  haveI := M.ΛFin
  haveI := M.σFin
  { K := M.K ⊕ FX
    k₀ := Sum.inr FX.I
    k₁ := Sum.inr FX.O
    Γ := FstΓ M A B C
    Λ := FstΛ M
    main := Sum.inr FL.l1
    σ := Fstσ M A B C
    initialState := (M.initialState, none)
    Γk₀Fin := inferInstanceAs (Fintype (A ⊕ C))
    m := firstProg M C e₀ e₁ }

omit [Inhabited A] [Inhabited B] [Inhabited C]
variable {M} {C}

def fstk (S : ∀ k, List (M.Γ k)) (i : List (A ⊕ C)) (w : List C) (ta : List A) (tb : List B)
    (o : List (B ⊕ C)) : ∀ k, List (FstΓ M A B C k)
  | Sum.inl k => S k
  | Sum.inr FX.I => i
  | Sum.inr FX.W => w
  | Sum.inr FX.TA => ta
  | Sum.inr FX.TB => tb
  | Sum.inr FX.O => o

section fstk

variable (S : ∀ k, List (M.Γ k)) (i : List (A ⊕ C)) (w : List C) (ta : List A) (tb : List B)
  (o : List (B ⊕ C))

@[simp] theorem fstk_M (k : M.K) : fstk S i w ta tb o (Sum.inl k) = S k := rfl
@[simp] theorem fstk_I : fstk S i w ta tb o (Sum.inr FX.I) = i := rfl
@[simp] theorem fstk_W : fstk S i w ta tb o (Sum.inr FX.W) = w := rfl
@[simp] theorem fstk_TA : fstk S i w ta tb o (Sum.inr FX.TA) = ta := rfl
@[simp] theorem fstk_TB : fstk S i w ta tb o (Sum.inr FX.TB) = tb := rfl
@[simp] theorem fstk_O : fstk S i w ta tb o (Sum.inr FX.O) = o := rfl

theorem fstk_set_M (k : M.K) (x : List (M.Γ k)) :
    Function.update (fstk S i w ta tb o) (Sum.inl k) x =
      fstk (Function.update S k x) i w ta tb o := by
  funext j
  rcases j with j | j
  · by_cases h : j = k
    · subst h
      rw [Function.update_self]
      show x = Function.update S j x j
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show S j = Function.update S k x j
      rw [Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)]; cases j <;> rfl

theorem fstk_set_I (i' : List (A ⊕ C)) :
    Function.update (fstk S i w ta tb o) (Sum.inr FX.I) i' = fstk S i' w ta tb o := by
  funext j
  rcases j with j | (_ | _ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  all_goals rw [Function.update_of_ne (by simp)]; rfl

theorem fstk_set_W (w' : List C) :
    Function.update (fstk S i w ta tb o) (Sum.inr FX.W) w' = fstk S i w' ta tb o := by
  funext j
  rcases j with j | (_ | _ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  all_goals rw [Function.update_of_ne (by simp)]; rfl

theorem fstk_set_TA (ta' : List A) :
    Function.update (fstk S i w ta tb o) (Sum.inr FX.TA) ta' = fstk S i w ta' tb o := by
  funext j
  rcases j with j | (_ | _ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  all_goals rw [Function.update_of_ne (by simp)]; rfl

theorem fstk_set_TB (tb' : List B) :
    Function.update (fstk S i w ta tb o) (Sum.inr FX.TB) tb' = fstk S i w ta tb' o := by
  funext j
  rcases j with j | (_ | _ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

theorem fstk_set_O (o' : List (B ⊕ C)) :
    Function.update (fstk S i w ta tb o) (Sum.inr FX.O) o' = fstk S i w ta tb o' := by
  funext j
  rcases j with j | (_ | _ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl

end fstk

variable (M A B C) in

abbrev FCfg : Type := TM2.Cfg (FstΓ M A B C) (FstΛ M) (Fstσ M A B C)

def embF (b : Option (A ⊕ B ⊕ C)) (i : List (A ⊕ C)) (w : List C) (ta : List A) (tb : List B)
    (o : List (B ⊕ C)) (c : TM2.Cfg M.Γ M.Λ M.σ) : FCfg M A B C :=
  ⟨some (c.l.elim (Sum.inr FL.l3) Sum.inl), (c.var, b), fstk c.stk i w ta tb o⟩

theorem simF (b : Option (A ⊕ B ⊕ C)) (i : List (A ⊕ C)) (w : List C) (ta : List A)
    (tb : List B) (o : List (B ⊕ C)) (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ)
    (S : ∀ k, List (M.Γ k)) :
    TM2.stepAux (trF A B C q) ((v, b) : Fstσ M A B C) (fstk S i w ta tb o) =
      embF b i w ta tb o (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    have := ih v (Function.update S k (f v :: S k))
    rw [← fstk_set_M] at this
    exact this
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    have := ih (f v (S k).head?) (Function.update S k (S k).tail)
    rw [← fstk_set_M] at this
    exact this
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [trF, TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f => rfl
  | halt => rfl

theorem stepF [Inhabited A] [Inhabited B] [Inhabited C] (e₀ : A → M.Γ M.k₀)
    (e₁ : M.Γ M.k₁ → B) (b : Option (A ⊕ B ⊕ C)) (i : List (A ⊕ C)) (w : List C)
    (ta : List A) (tb : List B) (o : List (B ⊕ C))
    (c c' : TM2.Cfg M.Γ M.Λ M.σ) (h : TM2.step M.m c = some c') :
    TM2.step (firstProg M C e₀ e₁) (embF b i w ta tb o c) = some (embF b i w ta tb o c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (simF b i w ta tb o (M.m l) v S)

end PEqualNP.Library.Machines.Gen

end

section

namespace PEqualNP.Library.Machines.Gen

open Turing PEqualNP.Library.Machines

theorem iter_trans {σ : Type} (f : σ → Option σ) {a b : ℕ} {x y z : σ}
    (h₁ : (flip bind f)^[a] (some x) = some y) (h₂ : (flip bind f)^[b] (some y) = some z) :
    (flip bind f)^[b + a] (some x) = some z := by
  rw [Function.iterate_add_apply, h₁, h₂]

variable {M : FinTM2} {A B C : Type} [Inhabited A] [Inhabited B] [Inhabited C]
  (e₀ : A → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → B)

variable (v : M.σ) (S : ∀ k, List (M.Γ k)) (w : List C) (o : List (B ⊕ C))

theorem f1_inl (b : Option (A ⊕ B ⊕ C)) (a : A) (i : List (A ⊕ C)) (t : List A)
    (tb : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l1), (v, b), fstk S (Sum.inl a :: i) w t tb o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inr FL.l1), (v, some (Sum.inl a)), fstk S i w (a :: t) tb o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_I, fstk_set_TA, isA, getA, ofI]

theorem f1_inr (b : Option (A ⊕ B ⊕ C)) (a : C) (i : List (A ⊕ C)) (t : List A)
    (tb : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l1), (v, b), fstk S (Sum.inr a :: i) w t tb o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inr FL.l1), (v, some (Sum.inr (Sum.inr a))),
        fstk S i (a :: w) t tb o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_I, fstk_set_W, isA, getC, ofI]

theorem f1_nil (b : Option (A ⊕ B ⊕ C)) (t : List A) (tb : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l1), (v, b), fstk S [] w t tb o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inr FL.l2), (v, none), fstk S [] w t tb o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_I]

theorem loop1 (tb : List B) : ∀ (i : List (A ⊕ C)) (w : List C) (t : List A)
    (b : Option (A ⊕ B ⊕ C)),
    (flip bind (TM2.step (firstProg M C e₀ e₁)))^[i.length + 1]
        (some (⟨some (Sum.inr FL.l1), (v, b), fstk S i w t tb o⟩ : FCfg M A B C)) =
      some ⟨some (Sum.inr FL.l2), (v, none),
        fstk S [] ((i.filterMap Sum.getRight?).reverse ++ w)
          ((i.filterMap Sum.getLeft?).reverse ++ t) tb o⟩ := by
  intro i
  induction i with
  | nil => intro w t b; exact f1_nil e₀ e₁ v S w o b t tb
  | cons x i ih =>
    intro w t b
    rw [List.length_cons, Function.iterate_succ_apply]
    cases x with
    | inl a =>
      have e : flip bind (TM2.step (firstProg M C e₀ e₁))
          (some (⟨some (Sum.inr FL.l1), (v, b), fstk S (Sum.inl a :: i) w t tb o⟩ :
            FCfg M A B C)) =
          some ⟨some (Sum.inr FL.l1), (v, some (Sum.inl a)), fstk S i w (a :: t) tb o⟩ :=
        f1_inl e₀ e₁ v S w o b a i t tb
      rw [e, ih]; simp [List.filterMap_cons]
    | inr a =>
      have e : flip bind (TM2.step (firstProg M C e₀ e₁))
          (some (⟨some (Sum.inr FL.l1), (v, b), fstk S (Sum.inr a :: i) w t tb o⟩ :
            FCfg M A B C)) =
          some ⟨some (Sum.inr FL.l1), (v, some (Sum.inr (Sum.inr a))),
            fstk S i (a :: w) t tb o⟩ :=
        f1_inr e₀ e₁ v S w o b a i t tb
      rw [e, ih]; simp [List.filterMap_cons]

theorem f2_cons (b : Option (A ⊕ B ⊕ C)) (a : A) (t : List A) (tb : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l2), (v, b), fstk S [] w (a :: t) tb o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inr FL.l2), (v, some (Sum.inl a)),
        fstk (Function.update S M.k₀ (e₀ a :: S M.k₀)) [] w t tb o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_TA, fstk_set_M, getA]

theorem f2_nil (b : Option (A ⊕ B ⊕ C)) (tb : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l2), (v, b), fstk S [] w [] tb o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inl M.main), (v, none), fstk S [] w [] tb o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_TA]

theorem loop2 (tb : List B) : ∀ (t : List A) (S : ∀ k, List (M.Γ k))
    (b : Option (A ⊕ B ⊕ C)),
    (flip bind (TM2.step (firstProg M C e₀ e₁)))^[t.length + 1]
        (some (⟨some (Sum.inr FL.l2), (v, b), fstk S [] w t tb o⟩ : FCfg M A B C)) =
      some ⟨some (Sum.inl M.main), (v, none),
        fstk (Function.update S M.k₀ (t.reverse.map e₀ ++ S M.k₀)) [] w [] tb o⟩ := by
  intro t
  induction t with
  | nil =>
    intro S b
    have : Function.update S M.k₀ (([] : List A).reverse.map e₀ ++ S M.k₀) = S := by simp
    rw [this]
    exact f2_nil e₀ e₁ v S w o b tb
  | cons a t ih =>
    intro S b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M C e₀ e₁))
        (some (⟨some (Sum.inr FL.l2), (v, b), fstk S [] w (a :: t) tb o⟩ : FCfg M A B C)) =
        some ⟨some (Sum.inr FL.l2), (v, some (Sum.inl a)),
          fstk (Function.update S M.k₀ (e₀ a :: S M.k₀)) [] w t tb o⟩ :=
      f2_cons e₀ e₁ v S w o b a t tb
    rw [e, ih]; simp

theorem f3_cons (b : Option (A ⊕ B ⊕ C)) (a : C) (w : List C) (ta : List A) (tb : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l3), (v, b), fstk S [] (a :: w) ta tb o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inr FL.l3), (v, some (Sum.inr (Sum.inr a))),
        fstk S [] w ta tb (Sum.inr a :: o)⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_W, fstk_set_O, getC]

theorem f3_nil (b : Option (A ⊕ B ⊕ C)) (ta : List A) (tb : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l3), (v, b), fstk S [] [] ta tb o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inr FL.l4), (v, none), fstk S [] [] ta tb o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_W]

theorem loop3 (ta : List A) (tb : List B) : ∀ (w : List C) (o : List (B ⊕ C))
    (b : Option (A ⊕ B ⊕ C)),
    (flip bind (TM2.step (firstProg M C e₀ e₁)))^[w.length + 1]
        (some (⟨some (Sum.inr FL.l3), (v, b), fstk S [] w ta tb o⟩ : FCfg M A B C)) =
      some ⟨some (Sum.inr FL.l4), (v, none),
        fstk S [] [] ta tb (w.reverse.map Sum.inr ++ o)⟩ := by
  intro w
  induction w with
  | nil => intro o b; exact f3_nil e₀ e₁ v S o b ta tb
  | cons a w ih =>
    intro o b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M C e₀ e₁))
        (some (⟨some (Sum.inr FL.l3), (v, b), fstk S [] (a :: w) ta tb o⟩ : FCfg M A B C)) =
        some ⟨some (Sum.inr FL.l3), (v, some (Sum.inr (Sum.inr a))),
          fstk S [] w ta tb (Sum.inr a :: o)⟩ :=
      f3_cons e₀ e₁ v S o b a w ta tb
    rw [e, ih]; simp

theorem f4_cons (b : Option (A ⊕ B ⊕ C)) (y : M.Γ M.k₁) (m : List (M.Γ M.k₁)) (ta : List A)
    (t : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l4), (v, b), fstk (Function.update S M.k₁ (y :: m)) [] [] ta t o⟩ :
          FCfg M A B C) =
      some ⟨some (Sum.inr FL.l4), (v, some (Sum.inr (Sum.inl (e₁ y)))),
        fstk (Function.update S M.k₁ m) [] [] ta (e₁ y :: t) o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_TB, fstk_set_M, getB]

theorem f4_nil (b : Option (A ⊕ B ⊕ C)) (ta : List A) (t : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l4), (v, b), fstk (Function.update S M.k₁ []) [] [] ta t o⟩ :
          FCfg M A B C) =
      some ⟨some (Sum.inr FL.l5), (v, none),
        fstk (Function.update S M.k₁ []) [] [] ta t o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_M]

theorem loop4 (ta : List A) : ∀ (m : List (M.Γ M.k₁)) (t : List B) (b : Option (A ⊕ B ⊕ C)),
    (flip bind (TM2.step (firstProg M C e₀ e₁)))^[m.length + 1]
        (some (⟨some (Sum.inr FL.l4), (v, b), fstk (Function.update S M.k₁ m) [] [] ta t o⟩ :
          FCfg M A B C)) =
      some ⟨some (Sum.inr FL.l5), (v, none),
        fstk (Function.update S M.k₁ []) [] [] ta (m.reverse.map e₁ ++ t) o⟩ := by
  intro m
  induction m with
  | nil => intro t b; exact f4_nil e₀ e₁ v S o b ta t
  | cons y m ih =>
    intro t b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M C e₀ e₁))
        (some (⟨some (Sum.inr FL.l4), (v, b),
          fstk (Function.update S M.k₁ (y :: m)) [] [] ta t o⟩ : FCfg M A B C)) =
        some ⟨some (Sum.inr FL.l4), (v, some (Sum.inr (Sum.inl (e₁ y)))),
          fstk (Function.update S M.k₁ m) [] [] ta (e₁ y :: t) o⟩ :=
      f4_cons e₀ e₁ v S o b y m ta t
    rw [e, ih]; simp

theorem f5_cons (b : Option (A ⊕ B ⊕ C)) (a : B) (ta : List A) (t : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l5), (v, b), fstk S [] [] ta (a :: t) o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inr FL.l5), (v, some (Sum.inr (Sum.inl a))),
        fstk S [] [] ta t (Sum.inl a :: o)⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_TB, fstk_set_O, getB]

theorem f5_nil (b : Option (A ⊕ B ⊕ C)) (ta : List A) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l5), (v, b), fstk S [] [] ta [] o⟩ : FCfg M A B C) =
      some ⟨none, (v, none), fstk S [] [] ta [] o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_TB]

theorem loop5 (ta : List A) : ∀ (t : List B) (o : List (B ⊕ C)) (b : Option (A ⊕ B ⊕ C)),
    (flip bind (TM2.step (firstProg M C e₀ e₁)))^[t.length + 1]
        (some (⟨some (Sum.inr FL.l5), (v, b), fstk S [] [] ta t o⟩ : FCfg M A B C)) =
      some ⟨none, (v, none), fstk S [] [] ta [] (t.reverse.map Sum.inl ++ o)⟩ := by
  intro t
  induction t with
  | nil => intro o b; exact f5_nil e₀ e₁ v S o b ta
  | cons a t ih =>
    intro o b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M C e₀ e₁))
        (some (⟨some (Sum.inr FL.l5), (v, b), fstk S [] [] ta (a :: t) o⟩ : FCfg M A B C)) =
        some ⟨some (Sum.inr FL.l5), (v, some (Sum.inr (Sum.inl a))),
          fstk S [] [] ta t (Sum.inl a :: o)⟩ :=
      f5_cons e₀ e₁ v S o b a ta t
    rw [e, ih]; simp

omit [Inhabited A] [Inhabited B] [Inhabited C] in
theorem fstk_nil :
    (fstk (fun _ => []) [] [] [] [] [] : ∀ k, List (FstΓ M A B C k)) = fun _ => [] := by
  funext j; rcases j with j | (_ | _ | _ | _ | _) <;> rfl

omit [Inhabited A] [Inhabited B] [Inhabited C] in
theorem fstk_nil_I (i : List (A ⊕ C)) :
    (fstk (fun _ => []) i [] [] [] [] : ∀ k, List (FstΓ M A B C k)) =
      Function.update (fun _ => [] : ∀ k, List (FstΓ M A B C k)) (Sum.inr FX.I) i :=
  (fstk_set_I (fun _ => []) [] [] [] [] [] i).symm.trans (by rw [fstk_nil])

omit [Inhabited A] [Inhabited B] [Inhabited C] in
theorem fstk_nil_O (o : List (B ⊕ C)) :
    (fstk (fun _ => []) [] [] [] [] o : ∀ k, List (FstΓ M A B C k)) =
      Function.update (fun _ => [] : ∀ k, List (FstΓ M A B C k)) (Sum.inr FX.O) o :=
  (fstk_set_O (fun _ => []) [] [] [] [] [] o).symm.trans (by rw [fstk_nil])

omit [Inhabited A] [Inhabited B] [Inhabited C] in
theorem embF_init (b : Option (A ⊕ B ⊕ C)) (i : List (A ⊕ C)) (w : List C) (ta : List A)
    (tb : List B) (o : List (B ⊕ C)) (l : List (M.Γ M.k₀)) :
    embF b i w ta tb o (initList M l) =
      (⟨some (Sum.inl M.main), (M.initialState, b),
        fstk (Function.update (fun _ => []) M.k₀ l) i w ta tb o⟩ : FCfg M A B C) := by
  rw [initList_eq]; rfl

omit [Inhabited A] [Inhabited B] [Inhabited C] in
theorem embF_halt (b : Option (A ⊕ B ⊕ C)) (i : List (A ⊕ C)) (w : List C) (ta : List A)
    (tb : List B) (o : List (B ⊕ C)) (m : List (M.Γ M.k₁)) :
    embF b i w ta tb o (haltList M m) =
      (⟨some (Sum.inr FL.l3), (M.initialState, b),
        fstk (Function.update (fun _ => []) M.k₁ m) i w ta tb o⟩ : FCfg M A B C) := by
  rw [haltList_eq]; rfl

theorem filterMap_const_none {γ δ : Type} (l : List γ) :
    l.filterMap (fun _ => (none : Option δ)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp

theorem gpair_left {A C : Type} (x : List A) (w : List C) :
    (gpair (x, w)).filterMap Sum.getLeft? = x := by
  have h1 : (Sum.getLeft? ∘ (Sum.inl : A → A ⊕ C) : A → Option A) = some := rfl
  have h2 : (Sum.getLeft? ∘ (Sum.inr : C → A ⊕ C) : C → Option A) = fun _ => none := rfl
  simp only [gpair, List.filterMap_append, List.filterMap_map, h1, h2,
    List.filterMap_some, filterMap_const_none, List.append_nil]

theorem gpair_right {A C : Type} (x : List A) (w : List C) :
    (gpair (x, w)).filterMap Sum.getRight? = w := by
  have h1 : (Sum.getRight? ∘ (Sum.inl : A → A ⊕ C) : A → Option C) = fun _ => none := rfl
  have h2 : (Sum.getRight? ∘ (Sum.inr : C → A ⊕ C) : C → Option C) = some := rfl
  simp only [gpair, List.filterMap_append, List.filterMap_map, h1, h2,
    List.filterMap_some, filterMap_const_none, List.nil_append]

theorem gpair_length {A C : Type} (x : List A) (w : List C) :
    (gpair (x, w)).length = x.length + w.length := by
  simp [gpair]

theorem first_run [Fintype A] [Fintype B] [Fintype C] (x : List A) (w0 : List C)
    (m : List (M.Γ M.k₁)) (s : ℕ)
    (h : (flip bind (TM2.step M.m))^[s] (some (initList M (x.map e₀))) = some (haltList M m)) :
    ∃ n, n ≤ s + 2 * x.length + 2 * w0.length + 2 * m.length + 5 ∧
      (flip bind (TM2.step (firstProg M C e₀ e₁)))^[n]
          (some (initList (firstM M C e₀ e₁) (gpair (x, w0)))) =
        some (haltList (firstM M C e₀ e₁) (gpair (m.map e₁, w0))) := by
  have q1 : (flip bind (TM2.step (firstProg M C e₀ e₁)))^[(gpair (x, w0)).length + 1]
      (some (initList (firstM M C e₀ e₁) (gpair (x, w0)))) =
      some (⟨some (Sum.inr FL.l2), (M.initialState, none),
        fstk (fun _ => []) [] w0.reverse x.reverse [] []⟩ : FCfg M A B C) := by
    have := loop1 e₀ e₁ M.initialState (fun _ => []) [] [] (gpair (x, w0)) [] [] none
    rw [gpair_left, gpair_right, List.append_nil, List.append_nil, fstk_nil_I] at this
    exact (congrArg (fun c => (flip bind (TM2.step (firstProg M C e₀ e₁)))^[
      (gpair (x, w0)).length + 1] (some c))
      (initList_eq (firstM M C e₀ e₁) (gpair (x, w0)))).trans this
  have q2 : (flip bind (TM2.step (firstProg M C e₀ e₁)))^[x.reverse.length + 1]
      (some (⟨some (Sum.inr FL.l2), (M.initialState, none),
        fstk (fun _ => []) [] w0.reverse x.reverse [] []⟩ : FCfg M A B C)) =
      some (embF none [] w0.reverse [] [] [] (initList M (x.map e₀))) := by
    have := loop2 e₀ e₁ M.initialState w0.reverse ([] : List (B ⊕ C)) [] x.reverse
      (fun _ => []) none
    rw [embF_init]
    simpa using this
  have q3 := simulate (TM2.step M.m) (TM2.step (firstProg M C e₀ e₁))
    (embF none [] w0.reverse [] [] []) (stepF e₀ e₁ none [] w0.reverse [] [] []) s _ _ h
  rw [embF_halt] at q3
  have q4 : (flip bind (TM2.step (firstProg M C e₀ e₁)))^[w0.reverse.length + 1]
      (some (⟨some (Sum.inr FL.l3), (M.initialState, none),
        fstk (Function.update (fun _ => []) M.k₁ m) [] w0.reverse [] [] []⟩ : FCfg M A B C)) =
      some (⟨some (Sum.inr FL.l4), (M.initialState, none),
        fstk (Function.update (fun _ => []) M.k₁ m) [] [] [] [] (w0.map Sum.inr)⟩ :
          FCfg M A B C) := by
    have := loop3 e₀ e₁ M.initialState (Function.update (fun _ => []) M.k₁ m) ([] : List A)
      ([] : List B) w0.reverse [] none
    simpa using this
  have q5 : (flip bind (TM2.step (firstProg M C e₀ e₁)))^[m.length + 1]
      (some (⟨some (Sum.inr FL.l4), (M.initialState, none),
        fstk (Function.update (fun _ => []) M.k₁ m) [] [] [] [] (w0.map Sum.inr)⟩ :
          FCfg M A B C)) =
      some (⟨some (Sum.inr FL.l5), (M.initialState, none),
        fstk (fun _ => []) [] [] [] (m.reverse.map e₁) (w0.map Sum.inr)⟩ : FCfg M A B C) := by
    have := loop4 e₀ e₁ M.initialState (fun _ => []) (w0.map Sum.inr) ([] : List A) m [] none
    simpa using this
  have q6 : (flip bind (TM2.step (firstProg M C e₀ e₁)))^[(m.reverse.map e₁).length + 1]
      (some (⟨some (Sum.inr FL.l5), (M.initialState, none),
        fstk (fun _ => []) [] [] [] (m.reverse.map e₁) (w0.map Sum.inr)⟩ : FCfg M A B C)) =
      some (haltList (firstM M C e₀ e₁) (gpair (m.map e₁, w0))) := by
    have := loop5 e₀ e₁ M.initialState (fun _ => []) ([] : List A) (m.reverse.map e₁)
      (w0.map Sum.inr) none
    rw [fstk_nil_O] at this
    refine this.trans (Eq.trans ?_
      (congrArg some (haltList_eq (firstM M C e₀ e₁) (gpair (m.map e₁, w0)))).symm)
    simp [gpair]
    rfl
  refine ⟨_, ?_, iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ q1 q2) q3)
    q4) q5) q6⟩
  simp only [gpair_length, List.length_reverse, List.length_map]
  omega

theorem first_polyTime {α β A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    [Inhabited A] [Inhabited B] [Inhabited C]
    (ea : α → List A) (eb : β → List B) (f : α → β)
    (c : Turing.TM2ComputableInPolyTime ea eb f) :
    Nonempty (Turing.TM2ComputableInPolyTime
      (fun p : α × List C => gpair (ea p.1, p.2))
      (fun p : β × List C => gpair (eb p.1, p.2))
      (fun p : α × List C => (f p.1, p.2))) := by
  let e₀ : A → c.tm.Γ c.tm.k₀ := fun a => c.inputAlphabet.invFun a
  let e₁ : c.tm.Γ c.tm.k₁ → B := fun y => c.outputAlphabet y
  let T : Polynomial ℕ :=
    c.time + Polynomial.C 2 * (Polynomial.X + Polynomial.C (maxPush c.tm) * c.time) +
      Polynomial.C 2 * Polynomial.X + Polynomial.C 5
  have key : ∀ p : α × List C, ∃ n, n ≤ T.eval (gpair (ea p.1, p.2)).length ∧
      (flip bind (TM2.step (firstProg c.tm C e₀ e₁)))^[n]
          (some (initList (firstM c.tm C e₀ e₁) (gpair (ea p.1, p.2)))) =
        some (haltList (firstM c.tm C e₀ e₁) (gpair (eb (f p.1), p.2))) := by
    rintro ⟨a, w⟩
    have hs : ∃ s, s ≤ Polynomial.eval (ea a).length c.time ∧
        (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm ((ea a).map e₀))) =
          some (haltList c.tm (List.map c.outputAlphabet.invFun (eb (f a)))) :=
      ⟨(c.outputsFun a).steps, (c.outputsFun a).steps_le_m, (c.outputsFun a).evals_in_steps⟩
    obtain ⟨s, b1, h⟩ := hs
    obtain ⟨n, hn, hrun⟩ := first_run (C := C) e₀ e₁ (ea a) w _ s h
    have hm : (List.map c.outputAlphabet.invFun (eb (f a))).map e₁ = eb (f a) := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (eb (f a))]
      exact List.map_congr_left fun y _ => c.outputAlphabet.right_inv y
    rw [hm] at hrun
    refine ⟨n, hn.trans ?_, hrun⟩
    have h' := h
    rw [haltList_eq, initList_eq] at h'
    have hlen := run_length c.tm c.tm.k₁ s _ _ h'
    simp only [Function.update_self, List.length_map] at hlen
    have hin : ((Function.update (fun _ => [] : ∀ k, List (c.tm.Γ k)) c.tm.k₀ ((ea a).map e₀))
        c.tm.k₁).length ≤ (ea a).length := by
      by_cases hk : c.tm.k₁ = c.tm.k₀
      · rw [hk, Function.update_self, List.length_map]
      · rw [Function.update_of_ne hk]; simp
    have b2 : Polynomial.eval (ea a).length c.time ≤
        Polynomial.eval ((ea a).length + w.length) c.time :=
      eval_mono _ (by omega)
    have hmul : maxPush c.tm * s ≤
        maxPush c.tm * Polynomial.eval ((ea a).length + w.length) c.time :=
      Nat.mul_le_mul_left _ (b1.trans b2)
    simp only [T, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, gpair_length, List.length_map]
    omega
  exact ⟨{
    tm := firstM c.tm C e₀ e₁
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := T
    outputsFun := fun p =>
      { steps := Classical.choose (key p)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          exact (congrArg (fun l => (flip bind (TM2.step (firstProg c.tm C e₀ e₁)))^[
            Classical.choose (key p)] (some (initList (firstM c.tm C e₀ e₁) l)))
            (hm _ (gpair (ea p.1, p.2)))).trans ((Classical.choose_spec (key p)).2.trans
            (congrArg (fun l => some (haltList (firstM c.tm C e₀ e₁) l))
              (hm _ (gpair (eb (f p.1), p.2))).symm))
        steps_le_m := (Classical.choose_spec (key p)).1 } }⟩

end PEqualNP.Library.Machines.Gen

end

section

namespace PEqualNP.Library.Universal

def un (n : ℕ) : List Bool := List.replicate n true

def pairB (a b : List Bool) : List Bool := un a.length ++ false :: (a ++ b)

def unpairB (s : List Bool) : List Bool × List Bool :=
  (((s.dropWhile id).tail).take (s.takeWhile id).length,
   ((s.dropWhile id).tail).drop (s.takeWhile id).length)

theorem unpairB_pairB (a b : List Bool) : unpairB (pairB a b) = (a, b) := by
  have h1 : (pairB a b).takeWhile id = un a.length := by
    simp [pairB, un]
  have h2 : (pairB a b).dropWhile id = false :: (a ++ b) := by
    simp [pairB, un]
  simp [unpairB, h1, h2, un]

end PEqualNP.Library.Universal

end

section

namespace PEqualNP.Library.Universal

open PEqualNP.Library PEqualNP.Library.Machines

private theorem cpt_congr {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

private theorem fm_elim {A B C : Type} (φl : A → Option C) (φr : B → Option C) (x : List A)
    (w : List B) :
    (x.map Sum.inl ++ w.map Sum.inr).filterMap (Sum.elim φl φr) =
      x.filterMap φl ++ w.filterMap φr := by
  have h1 : ∀ x : List A, (x.map Sum.inl).filterMap (Sum.elim φl φr) = x.filterMap φl := by
    intro x; induction x with
    | nil => rfl
    | cons a l ih => simp [List.filterMap_cons, ih]
  have h2 : ∀ w : List B, (w.map Sum.inr).filterMap (Sum.elim φl φr) = w.filterMap φr := by
    intro w; induction w with
    | nil => rfl
    | cons a l ih => simp [List.filterMap_cons, ih]
  rw [List.filterMap_append, h1, h2]

private theorem fm_some {A C : Type} (g : A → C) (l : List A) :
    l.filterMap (fun a => some (g a)) = l.map g := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

private theorem fm_none {A C : Type} (l : List A) :
    l.filterMap (fun _ : A => (none : Option C)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp

theorem cpt_pairB :
    ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => pairB p.1 p.2) := by
  have hA : ComputableInPolyTime encodePair encodePair
      (fun p : List Bool × List Bool => (p.1, p.1 ++ p.2)) := by
    refine twoPass_polyTime _ _ _
      (Sum.elim (fun b : Bool => some (Sum.inl b)) (fun _ : Bool => none))
      (Sum.elim (fun b : Bool => some (Sum.inr b)) (fun b : Bool => some (Sum.inr b))) ?_
    rintro ⟨x, w⟩
    simp only [encodePair]
    rw [fm_elim, fm_elim, fm_some, fm_some, fm_some, fm_none]
    simp
  have hU : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun a : List Bool => a.map (fun _ => true) ++ [false]) := by
    refine fst_polyTime _ _ _ (fun (_ : Unit) (_ : Bool) => ((), some true))
      (fun _ => some false) () ?_
    intro a
    induction a with
    | nil => rfl
    | cons b l ih =>
      simp only [fstRun, List.map_cons, List.cons_append, Option.toList_some] at ih ⊢
      rw [← ih]; rfl
  refine cpt_congr (cpt_comp (cpt_comp hA (cpt_first hU)) cpt_append) ?_
  rintro ⟨x, w⟩
  simp [pairB, un]

theorem cpt_ifEmpty :
    ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => if p.1 = [] then p.2 else []) := by
  obtain ⟨c⟩ := constList_polyTime []
  have hI := Iter.iter_polyTime (fun _ : List Bool => ([] : List Bool)) c 0 (by simp)
  refine cpt_congr (cpt_comp cpt_swap hI) ?_
  rintro ⟨x, w⟩
  cases x with
  | nil => simp
  | cons b l => simp [Function.iterate_succ_apply']

theorem cpt_ifNonempty :
    ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => if p.1 = [] then [] else p.2) := by
  have hneg : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => if x = [] then [true] else []) :=
    cpt_comp (cpt_pair cpt_id (constList_polyTime [true])) cpt_ifEmpty
  refine cpt_congr (cpt_comp (cpt_first hneg) cpt_ifEmpty) ?_
  rintro ⟨x, w⟩
  cases x with
  | nil => simp
  | cons b l => simp

theorem cpt_bitFlag {α αΓ : Type} {ea : α → List αΓ} {f : α → Bool}
    (hf : ComputableInPolyTime ea Computability.encodeBool f) :
    ComputableInPolyTime ea (fun x : List Bool => x) (fun a => if f a then [true] else []) := by
  have h : ComputableInPolyTime Computability.encodeBool (fun x : List Bool => x)
      (fun b : Bool => if b then [true] else []) := by
    refine filterMap_polyTime _ _ _ (fun b : Bool => if b then some true else none) ?_
    intro b
    cases b <;> simp [Computability.encodeBool]
  exact cpt_comp hf h

theorem cpt_pairG {α αΓ : Type} [Fintype αΓ] [Inhabited αΓ] {ea : α → List αΓ}
    {f g : α → List Bool}
    (hf : ComputableInPolyTime ea (fun x : List Bool => x) f)
    (hg : ComputableInPolyTime ea (fun x : List Bool => x) g) :
    ComputableInPolyTime ea encodePair (fun a => (f a, g a)) := by
  obtain ⟨cf⟩ := hf
  obtain ⟨cg⟩ := hg
  have s0 : ComputableInPolyTime ea (fun a : α => Gen.gpair (ea a, ea a)) (fun a : α => a) := by
    refine twoPass_polyTime _ _ _ (fun s => some (Sum.inl s)) (fun s => some (Sum.inr s)) ?_
    intro a
    simp only [Gen.gpair, fm_some]
  have s1 : ComputableInPolyTime (fun a : α => Gen.gpair (ea a, ea a))
      (fun a : α => Gen.gpair (f a, ea a)) (fun a : α => a) := by
    obtain ⟨c⟩ := Gen.first_polyTime (C := αΓ) ea (fun x : List Bool => x) f cf
    exact ⟨⟨c.toTM2ComputableAux, c.time, fun a => c.outputsFun (a, ea a)⟩⟩
  have s2 : ComputableInPolyTime (fun a : α => Gen.gpair (f a, ea a))
      (fun a : α => Gen.gpair (ea a, f a)) (fun a : α => a) := by
    refine twoPass_polyTime _ _ _
      (Sum.elim (fun _ : Bool => none) (fun c : αΓ => some (Sum.inl c)))
      (Sum.elim (fun b : Bool => some (Sum.inr b)) (fun _ : αΓ => none)) ?_
    intro a
    simp only [Gen.gpair]
    rw [fm_elim, fm_elim, fm_some, fm_some, fm_none, fm_none]
    simp
  have s3 : ComputableInPolyTime (fun a : α => Gen.gpair (ea a, f a))
      (fun a : α => Gen.gpair (g a, f a)) (fun a : α => a) := by
    obtain ⟨c⟩ := Gen.first_polyTime (C := Bool) ea (fun x : List Bool => x) g cg
    exact ⟨⟨c.toTM2ComputableAux, c.time, fun a => c.outputsFun (a, f a)⟩⟩
  have s4 : ComputableInPolyTime (fun a : α => Gen.gpair (g a, f a))
      encodePair (fun a : α => (f a, g a)) := by
    refine twoPass_polyTime _ _ _
      (Sum.elim (fun _ : Bool => none) (fun c : Bool => some (Sum.inl c)))
      (Sum.elim (fun b : Bool => some (Sum.inr b)) (fun _ : Bool => none)) ?_
    intro a
    simp only [Gen.gpair, encodePair]
    rw [fm_elim, fm_elim, fm_some, fm_some, fm_none, fm_none]
    simp
  exact cpt_comp (cpt_comp (cpt_comp (cpt_comp s0 s1) s2) s3) s4

private def encT (u : List Bool) : List Bool := u.flatMap (fun b => [true, b])

private def encF (v : List Bool) : List Bool := v.flatMap (fun b => [false, b])

private def twD : Bool → Bool → Bool × Option Bool
  | true, true => (true, some true)
  | _, _ => (false, none)

private theorem twD_run (l : List Bool) :
    fstRun twD (fun _ => none) false l = [] ∧
      fstRun twD (fun _ => none) true l = l.takeWhile id := by
  induction l with
  | nil => exact ⟨rfl, rfl⟩
  | cons b l ih => cases b <;> simp [fstRun, twD, ih.1, ih.2]

private def e0D : Bool → Bool → Bool × Option Bool × Option Bool
  | false, true => (false, none, none)
  | false, false => (true, none, none)
  | true, b => (true, some false, some b)

private theorem e0D_run_true (l : List Bool) :
    fstRun2 e0D (fun _ => none) true l = encF l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun2, e0D, encF, ih]

private theorem e0D_run_false (l : List Bool) :
    fstRun2 e0D (fun _ => none) false l = encF (l.dropWhile id).tail := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [fstRun2, e0D, ih, e0D_run_true]

private def mkD : Bool × Bool → Bool → (Bool × Bool) × Option Bool
  | (d, false), t => ((d || !t, true), some (t || !d))
  | (d, true), b => ((d, false), some b)

private def mk (l : List Bool) : List Bool := fstRun mkD (fun _ => none) (false, false) l

private theorem mkD_length (q : Bool × Bool) (l : List Bool) :
    (fstRun mkD (fun _ => none) q l).length = l.length := by
  induction l generalizing q with
  | nil => rfl
  | cons b l ih => obtain ⟨d, ph⟩ := q; cases ph <;> simp [fstRun, mkD, ih]

private theorem mkD_done (v : List Bool) :
    fstRun mkD (fun _ => none) (true, false) (encF v) = encF v := by
  induction v with
  | nil => rfl
  | cons b v ih => simp [fstRun, mkD, encF] at ih ⊢; exact ih

private theorem mkD_marked (u r : List Bool) :
    fstRun mkD (fun _ => none) (false, false) (encT u ++ r) =
      encT u ++ fstRun mkD (fun _ => none) (false, false) r := by
  induction u with
  | nil => rfl
  | cons b u ih => simp [fstRun, mkD, encT] at ih ⊢; exact ih

private theorem mk_nil (u : List Bool) : mk (encT u ++ encF []) = encT u ++ encF [] := by
  unfold mk; rw [mkD_marked]; rfl

private theorem mk_cons (u : List Bool) (b : Bool) (v : List Bool) :
    mk (encT u ++ encF (b :: v)) = encT (u ++ [b]) ++ encF v := by
  unfold mk
  rw [mkD_marked]
  have h : fstRun mkD (fun _ => none) (false, false) (encF (b :: v)) =
      true :: b :: encF v := by
    have h' := mkD_done v
    simp [fstRun, mkD, encF] at h' ⊢
    exact h'
  rw [h]
  simp [encT]

private theorem mk_iter (k : ℕ) : ∀ u t : List Bool,
    mk^[k] (encT u ++ encF t) = encT (u ++ t.take k) ++ encF (t.drop k) := by
  induction k with
  | zero => intro u t; simp
  | succ k ih =>
    intro u t
    rw [Function.iterate_succ_apply]
    cases t with
    | nil => rw [mk_nil, ih]; simp
    | cons b t => rw [mk_cons, ih]; simp

private def dcD : Option Bool → Bool → Option Bool × Option (Bool ⊕ Bool)
  | none, t => (some t, none)
  | some t, b => (none, some (if t then Sum.inl b else Sum.inr b))

private theorem dcD_F (v : List Bool) :
    fstRun dcD (fun _ => none) none (encF v) = v.map Sum.inr := by
  induction v with
  | nil => rfl
  | cons b v ih => simp [fstRun, dcD, encF] at ih ⊢; exact ih

private theorem dcD_T (u r : List Bool) :
    fstRun dcD (fun _ => none) none (encT u ++ r) =
      u.map Sum.inl ++ fstRun dcD (fun _ => none) none r := by
  induction u with
  | nil => rfl
  | cons b u ih => simp [fstRun, dcD, encT] at ih ⊢; exact ih

private def rawDec (l : List (Bool ⊕ Bool)) : List Bool × List Bool :=
  (l.filterMap Sum.getLeft?, l.filterMap Sum.getRight?)

private theorem rawDec_tagged (u v : List Bool) :
    rawDec (u.map Sum.inl ++ v.map Sum.inr) = (u, v) := by
  have h1 : ∀ x : List Bool, (x.map (Sum.inl (β := Bool))).filterMap Sum.getLeft? = x := by
    intro x; induction x with
    | nil => rfl
    | cons a l ih => exact congrArg (a :: ·) ih
  have h2 : ∀ x : List Bool, (x.map (Sum.inr (α := Bool))).filterMap Sum.getLeft? = [] := by
    intro x; induction x with
    | nil => rfl
    | cons a l ih => exact ih
  have h3 : ∀ x : List Bool, (x.map (Sum.inl (β := Bool))).filterMap Sum.getRight? = [] := by
    intro x; induction x with
    | nil => rfl
    | cons a l ih => exact ih
  have h4 : ∀ x : List Bool, (x.map (Sum.inr (α := Bool))).filterMap Sum.getRight? = x := by
    intro x; induction x with
    | nil => rfl
    | cons a l ih => exact congrArg (a :: ·) ih
  simp only [rawDec, List.filterMap_append, h1, h2, h3, h4, List.append_nil, List.nil_append]

theorem cpt_unpairB :
    ComputableInPolyTime (fun x : List Bool => x) encodePair unpairB := by
  have hTw : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => s.takeWhile id) :=
    fst_polyTime _ _ _ twD (fun _ => none) true (fun s => (twD_run s).2.symm)
  have hE0 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => encF (s.dropWhile id).tail) :=
    fst2_polyTime _ _ _ e0D (fun _ => none) false (fun s => (e0D_run_false s).symm)
  have hMk : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) mk :=
    fst_polyTime _ _ _ mkD (fun _ => none) (false, false) (fun _ => rfl)
  obtain ⟨cMk⟩ := hMk
  have hIt := Iter.iter_polyTime mk cMk 0 (fun y => by simp [mk, mkD_length])
  have hDc : ComputableInPolyTime (fun x : List Bool => x) (fun l : List (Bool ⊕ Bool) => l)
      (fun l : List Bool => fstRun dcD (fun _ => none) none l) :=
    fst_polyTime _ _ _ dcD (fun _ => none) none (fun _ => rfl)
  have hRaw : ComputableInPolyTime (fun l : List (Bool ⊕ Bool) => l) encodePair rawDec := by
    refine twoPass_polyTime _ _ _
      (fun s : Bool ⊕ Bool => (Sum.getLeft? s).map Sum.inl)
      (fun s : Bool ⊕ Bool => (Sum.getRight? s).map Sum.inr) ?_
    intro l
    simp only [rawDec, encodePair, List.map_filterMap]
  refine cpt_congr (cpt_comp (cpt_comp (cpt_comp (cpt_pair hE0 hTw) hIt) hDc) hRaw) ?_
  intro s
  have h := mk_iter (s.takeWhile id).length [] (s.dropWhile id).tail
  have e : encT [] ++ encF (s.dropWhile id).tail = encF (s.dropWhile id).tail := rfl
  rw [e] at h
  simp only [h, List.nil_append]
  rw [dcD_T, dcD_F, rawDec_tagged]
  rfl

theorem cpt_iterB (g : List Bool → List Bool)
    (hg : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) g)
    (m : List Bool → ℕ) (a : ℕ)
    (hm : ∀ y, m (g y) ≤ m y) (hgl : ∀ y, (g y).length ≤ y.length + m y)
    (ha : ∀ y, m y ≤ a * y.length + a) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => g^[(unpairB s).2.length] (unpairB s).1) := by
  obtain ⟨c⟩ := hg
  exact cpt_comp cpt_unpairB (Iter.iter_polyTime_measure g c m a hm hgl ha)

end PEqualNP.Library.Universal

end

section

namespace PEqualNP.Library.Universal

open PEqualNP.Library PEqualNP.Library.Machines

def hd (s : List Bool) : List Bool := s.takeWhile id

def dropN (s : List Bool) : List Bool := (s.dropWhile id).tail

def sel (f a b : List Bool) : List Bool := if f = [] then a else b

private theorem cptc {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

private def hdD : Bool → Bool → Bool × Option Bool
  | true, true => (true, some true)
  | _, _ => (false, none)

private theorem hdD_run (l : List Bool) :
    fstRun hdD (fun _ => none) false l = [] ∧
      fstRun hdD (fun _ => none) true l = l.takeWhile id := by
  induction l with
  | nil => exact ⟨rfl, rfl⟩
  | cons b l ih => cases b <;> simp [fstRun, hdD, ih.1, ih.2]

theorem cpt_hd :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) hd :=
  fst_polyTime _ _ _ hdD (fun _ => none) true (fun s => (hdD_run s).2.symm)

private def dnD : Bool → Bool → Bool × Option Bool
  | false, true => (false, none)
  | false, false => (true, none)
  | true, b => (true, some b)

private theorem dnD_true (l : List Bool) : fstRun dnD (fun _ => none) true l = l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, dnD, ih]

private theorem dnD_false (l : List Bool) :
    fstRun dnD (fun _ => none) false l = (l.dropWhile id).tail := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [fstRun, dnD, ih, dnD_true]

theorem cpt_dropN :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) dropN :=
  fst_polyTime _ _ _ dnD (fun _ => none) false (fun s => (dnD_false s).symm)

theorem cpt_const (l : List Bool) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun _ : List Bool => l) :=
  constList_polyTime l

theorem cpt_unpairB1 :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => (unpairB s).1) :=
  cptc (cpt_comp cpt_unpairB cpt_fst) (fun _ => rfl)

theorem cpt_unpairB2 :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => (unpairB s).2) :=
  cptc (cpt_comp cpt_unpairB cpt_snd) (fun _ => rfl)

theorem cpt_app2 {u v : List Bool → List Bool}
    (hu : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) u)
    (hv : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) v) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => u s ++ v s) :=
  cptc (cpt_comp (cpt_pair hu hv) cpt_append) (fun _ => rfl)

theorem cpt_pairB2 {u v : List Bool → List Bool}
    (hu : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) u)
    (hv : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) v) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => pairB (u s) (v s)) :=
  cptc (cpt_comp (cpt_pair hu hv) cpt_pairB) (fun _ => rfl)

theorem cpt_sel {f a b : List Bool → List Bool}
    (hf : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f)
    (ha : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) a)
    (hb : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) b) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => sel (f s) (a s) (b s)) := by
  have h1 := cpt_comp (cpt_pair hf ha) cpt_ifEmpty
  have h2 := cpt_comp (cpt_pair hf hb) cpt_ifNonempty
  refine cptc (cpt_app2 h1 h2) ?_
  intro s
  by_cases h : f s = [] <;> simp [sel, h]

end PEqualNP.Library.Universal

end

theorem aux370_findIdx_map {α β : Type} (f : α → β) (q : β → Bool) (l : List α) :
    (l.map f).findIdx q = l.findIdx (fun x => q (f x)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.findIdx_cons, ih]

theorem aux370_hd (k : ℕ) (a : List Bool) :
    (List.replicate k true ++ false :: a).takeWhile id = List.replicate k true := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ]

theorem aux370_drop (k : ℕ) (a : List Bool) :
    ((List.replicate k true ++ false :: a).dropWhile id).tail = a := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ]

theorem aux370_iter (g : List Bool → List Bool) (a : List Bool) (t : ℕ → Bool)
    (hg : ∀ i, g (List.replicate i true ++ false :: a) =
      if t i = true then List.replicate i true ++ false :: a
      else List.replicate (i + 1) true ++ false :: a) :
    ∀ (n i : ℕ), g^[n] (List.replicate i true ++ false :: a) =
      List.replicate (i + (List.range n).findIdx (fun j => t (i + j))) true ++ false :: a := by
  intro n
  induction n with
  | zero => intro i; simp
  | succ n ih =>
    intro i
    rw [Function.iterate_succ_apply, hg i, List.range_succ_eq_map, List.findIdx_cons,
      aux370_findIdx_map]
    by_cases h : t i = true
    · have hfix : g (List.replicate i true ++ false :: a) = List.replicate i true ++ false :: a := by
        rw [hg i, ite_eq_left h]
      rw [ite_eq_left h, Function.iterate_fixed hfix]
      simp [h]
    · rw [ite_eq_right h, ih (i + 1)]
      have h' : t i = false := by simpa using h
      have e : (fun j => t (i + 1 + j)) = (fun x => t (i + Nat.succ x)) := by
        funext j
        congr 1
        omega
      simp only [Nat.add_zero, h', e, Bool.false_eq_true, ↓reduceIte]
      congr 2
      omega

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal in
theorem PEqualNP.Outside.L_meta_370 : ∀ p cnt arg : List Bool → List Bool, PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) p → PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) cnt → PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) arg → PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (fun s => List.replicate ((List.range (cnt s).length).findIdx (fun i => !(p (List.replicate i true ++ false :: (List.replicate i true ++ arg s))).isEmpty)) true) := by
  intro p cnt arg hp hcnt harg
  have hq := cpt_app2 cpt_hd (cpt_app2 (cpt_const [false]) (cpt_app2 cpt_hd cpt_dropN))
  have hg := cpt_sel (cpt_comp hq hp) (cpt_app2 (cpt_const [true]) cpt_id) cpt_id
  have hit := cpt_iterB _ hg (fun _ => 1) 1 (fun _ => le_rfl)
    (by
      intro y
      simp only [sel]
      split_ifs <;> simp)
    (by intro y; omega)
  have hpk := cpt_pairB2 (cpt_app2 (cpt_const [false]) harg) hcnt
  have hall := cpt_comp (cpt_comp hpk hit) cpt_hd
  have key : ∀ s, hd ((fun y => sel (p (hd y ++ ([false] ++ (hd y ++ dropN y)))) ([true] ++ y) y)^[(unpairB (pairB ([false] ++ arg s) (cnt s))).2.length] (unpairB (pairB ([false] ++ arg s) (cnt s))).1) = List.replicate ((List.range (cnt s).length).findIdx (fun i => !(p (List.replicate i true ++ false :: (List.replicate i true ++ arg s))).isEmpty)) true := by
    intro s
    rw [unpairB_pairB]
    have h := aux370_iter (fun y => sel (p (hd y ++ ([false] ++ (hd y ++ dropN y)))) ([true] ++ y) y) (arg s)
      (fun i => !(p (List.replicate i true ++ false :: (List.replicate i true ++ arg s))).isEmpty)
      (by
        intro i
        simp only [hd, dropN, aux370_hd, aux370_drop, sel, List.singleton_append]
        by_cases h0 : p (List.replicate i true ++ false :: (List.replicate i true ++ arg s)) = []
        · simp [h0, List.replicate_succ]
        · simp [h0])
      (cnt s).length 0
    simp only [List.replicate_zero, List.nil_append, Nat.zero_add] at h
    simp only [List.singleton_append]
    simp only [List.singleton_append] at h
    rw [h]
    exact aux370_hd _ _
  obtain ⟨c⟩ := hall
  exact ⟨⟨c.toTM2ComputableAux, c.time, fun a => by have := c.outputsFun a; rw [← key a]; exact this⟩⟩
