import PEqualNP.Defs
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_378_aux

open Turing

private lemma iterate_none {α : Type} (f : α → Option α) (n : ℕ) :
    (flip bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

private lemma iter_trans {α : Type} {f : α → Option α} {n₁ n₂ : ℕ} {a b c : α}
    (h₁ : (flip bind f)^[n₁] (some a) = some b)
    (h₂ : (flip bind f)^[n₂] (some b) = some c) :
    (flip bind f)^[n₂ + n₁] (some a) = some c := by
  rw [Function.iterate_add_apply, h₁, h₂]

private lemma simulate {α β : Type} (f : α → Option α) (g : β → Option β) (emb : α → β)
    (h : ∀ c c', f c = some c' → g (emb c) = some (emb c')) :
    ∀ (n : ℕ) (a b : α), (flip bind f)^[n] (some a) = some b →
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

private def pushes {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type} :
    TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => pushes q + 1
  | .peek _ _ q => pushes q
  | .pop _ _ q => pushes q
  | .load _ q => pushes q
  | .branch _ q₁ q₂ => max (pushes q₁) (pushes q₂)
  | .goto _ => 0
  | .halt => 0

private lemma stepAux_length {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (k : K) :
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

private noncomputable def maxPush (tm : FinTM2) : ℕ :=
  (@Finset.univ tm.Λ tm.ΛFin).sup fun l => pushes (tm.m l)

private lemma step_length (tm : FinTM2) (c c' : TM2.Cfg tm.Γ tm.Λ tm.σ)
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

private lemma run_length (tm : FinTM2) (k : tm.K) :
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

private lemma initList_eq (tm : FinTM2) (s : List (tm.Γ tm.k₀)) :
    initList tm s =
      (⟨some tm.main, tm.initialState, Function.update (fun _ => []) tm.k₀ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ) := by
  unfold initList
  congr 1
  funext k
  by_cases h : k = tm.k₀
  · subst h; simp
  · simp [h]

private lemma haltList_eq (tm : FinTM2) (s : List (tm.Γ tm.k₁)) :
    haltList tm s =
      (⟨none, tm.initialState, Function.update (fun _ => []) tm.k₁ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ) := by
  unfold haltList
  congr 1
  funext k
  by_cases h : k = tm.k₁
  · subst h; simp
  · simp [h]

private lemma bits_succ (m : ℕ) :
    Nat.bits (m + 1) = decide ((m + 1) % 2 = 1) :: Nat.bits ((m + 1) / 2) := by
  have h1 : Nat.bit (decide ((m + 1) % 2 = 1)) ((m + 1) / 2) = m + 1 := by
    unfold Nat.bit
    by_cases h : (m + 1) % 2 = 1
    · simp [h]; omega
    · simp [h]; omega
  have h2 : (m + 1) / 2 = 0 → decide ((m + 1) % 2 = 1) = true := by
    intro hq
    simp only [decide_eq_true_eq]
    omega
  exact (congrArg Nat.bits h1.symm).trans (Nat.bits_append_bit _ _ h2)

private lemma bits_length_le : ∀ n : ℕ, (Nat.bits n).length ≤ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero => simp [Nat.zero_bits]
    | succ m =>
      rw [bits_succ, List.length_cons]
      have hlt : (m + 1) / 2 < m + 1 := by omega
      have := ih ((m + 1) / 2) hlt
      omega

section combined

variable (M1 M2 M3 : FinTM2)

abbrev MK : Type := Fin 5 ⊕ M1.K ⊕ M2.K ⊕ M3.K

abbrev MΓ : MK M1 M2 M3 → Type
  | Sum.inl _ => Bool
  | Sum.inr (Sum.inl k) => M1.Γ k
  | Sum.inr (Sum.inr (Sum.inl k)) => M2.Γ k
  | Sum.inr (Sum.inr (Sum.inr k)) => M3.Γ k

abbrev MΛ : Type := Fin 15 ⊕ M1.Λ ⊕ M2.Λ ⊕ M3.Λ

abbrev Mσ : Type := M1.σ × M2.σ × M3.σ × Option Bool × Bool

abbrev MCfg : Type := TM2.Cfg (MΓ M1 M2 M3) (MΛ M1 M2 M3) (Mσ M1 M2 M3)

variable {M1 M2 M3}

private abbrev setBuf (v : Mσ M1 M2 M3) (o : Option Bool) : Mσ M1 M2 M3 :=
  (v.1, v.2.1, v.2.2.1, o, v.2.2.2.2)

private abbrev setPh (v : Mσ M1 M2 M3) (p : Bool) : Mσ M1 M2 M3 :=
  (v.1, v.2.1, v.2.2.1, v.2.2.2.1, p)

private abbrev getBuf (v : Mσ M1 M2 M3) : Option Bool := v.2.2.2.1

private abbrev getPh (v : Mσ M1 M2 M3) : Bool := v.2.2.2.2

private def tr1 : TM2.Stmt M1.Γ M1.Λ M1.σ → TM2.Stmt (MΓ M1 M2 M3) (MΛ M1 M2 M3) (Mσ M1 M2 M3)
  | .push k f q => .push (Sum.inr (Sum.inl k)) (fun s => f s.1) (tr1 q)
  | .peek k f q => .peek (Sum.inr (Sum.inl k)) (fun s o => (f s.1 o, s.2)) (tr1 q)
  | .pop k f q => .pop (Sum.inr (Sum.inl k)) (fun s o => (f s.1 o, s.2)) (tr1 q)
  | .load a q => .load (fun s => (a s.1, s.2)) (tr1 q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1) (tr1 q₁) (tr1 q₂)
  | .goto f => .goto (fun s => Sum.inr (Sum.inl (f s.1)))
  | .halt => .goto (fun _ => Sum.inl 2)

private def tr2 : TM2.Stmt M2.Γ M2.Λ M2.σ → TM2.Stmt (MΓ M1 M2 M3) (MΛ M1 M2 M3) (Mσ M1 M2 M3)
  | .push k f q => .push (Sum.inr (Sum.inr (Sum.inl k))) (fun s => f s.2.1) (tr2 q)
  | .peek k f q => .peek (Sum.inr (Sum.inr (Sum.inl k))) (fun s o => (s.1, f s.2.1 o, s.2.2)) (tr2 q)
  | .pop k f q => .pop (Sum.inr (Sum.inr (Sum.inl k))) (fun s o => (s.1, f s.2.1 o, s.2.2)) (tr2 q)
  | .load a q => .load (fun s => (s.1, a s.2.1, s.2.2)) (tr2 q)
  | .branch f q₁ q₂ => .branch (fun s => f s.2.1) (tr2 q₁) (tr2 q₂)
  | .goto f => .goto (fun s => Sum.inr (Sum.inr (Sum.inl (f s.2.1))))
  | .halt => .goto (fun _ => Sum.inl 5)

private def tr3 : TM2.Stmt M3.Γ M3.Λ M3.σ → TM2.Stmt (MΓ M1 M2 M3) (MΛ M1 M2 M3) (Mσ M1 M2 M3)
  | .push k f q => .push (Sum.inr (Sum.inr (Sum.inr k))) (fun s => f s.2.2.1) (tr3 q)
  | .peek k f q => .peek (Sum.inr (Sum.inr (Sum.inr k))) (fun s o => (s.1, s.2.1, f s.2.2.1 o, s.2.2.2)) (tr3 q)
  | .pop k f q => .pop (Sum.inr (Sum.inr (Sum.inr k))) (fun s o => (s.1, s.2.1, f s.2.2.1 o, s.2.2.2)) (tr3 q)
  | .load a q => .load (fun s => (s.1, s.2.1, a s.2.2.1, s.2.2.2)) (tr3 q)
  | .branch f q₁ q₂ => .branch (fun s => f s.2.2.1) (tr3 q₁) (tr3 q₂)
  | .goto f => .goto (fun s => Sum.inr (Sum.inr (Sum.inr (f s.2.2.1))))
  | .halt => .goto (fun _ => Sum.inl 13)

variable (M1 M2 M3)

private def ctrl (i1 : Bool → M1.Γ M1.k₀) (i2 : Bool → M2.Γ M2.k₀) (i3 : Bool → M3.Γ M3.k₀) :
    Fin 15 → TM2.Stmt (MΓ M1 M2 M3) (MΛ M1 M2 M3) (Mσ M1 M2 M3)
  | ⟨0, _⟩ =>
    .pop (Sum.inl 0) (fun v o => setBuf v o)
      (.branch (fun v => (getBuf v).isSome)
        (.push (Sum.inl 2) (fun v => (getBuf v).getD false) (.goto fun _ => Sum.inl 0))
        (.goto fun _ => Sum.inl 1))
  | ⟨1, _⟩ =>
    .pop (Sum.inl 2) (fun v o => setBuf v o)
      (.branch (fun v => (getBuf v).isSome)
        (.push (Sum.inl 0) (fun v => (getBuf v).getD false)
          (.push (Sum.inr (Sum.inl M1.k₀)) (fun v => i1 ((getBuf v).getD false))
            (.goto fun _ => Sum.inl 1)))
        (.push (Sum.inl 1) (fun _ => false)
          (.push (Sum.inl 1) (fun _ => false)
            (.goto fun _ => Sum.inr (Sum.inl M1.main)))))
  | ⟨2, _⟩ =>
    .pop (Sum.inr (Sum.inl M1.k₁)) (fun v o => setBuf v (o.map fun _ => false))
      (.branch (fun v => (getBuf v).isSome)
        (.push (Sum.inl 2) (fun _ => false) (.goto fun _ => Sum.inl 2))
        (.goto fun _ => Sum.inl 6))
  | ⟨3, _⟩ =>
    .pop (Sum.inl 0) (fun v o => setBuf v o)
      (.branch (fun v => (getBuf v).isSome)
        (.push (Sum.inl 2) (fun v => (getBuf v).getD false) (.goto fun _ => Sum.inl 3))
        (.goto fun _ => Sum.inl 4))
  | ⟨4, _⟩ =>
    .pop (Sum.inl 2) (fun v o => setBuf v o)
      (.branch (fun v => (getBuf v).isSome)
        (.push (Sum.inl 0) (fun v => (getBuf v).getD false)
          (.push (Sum.inr (Sum.inr (Sum.inl M2.k₀))) (fun v => i2 ((getBuf v).getD false))
            (.goto fun _ => Sum.inl 4)))
        (.push (Sum.inl 1) (fun _ => false)
          (.goto fun _ => Sum.inr (Sum.inr (Sum.inl M2.main)))))
  | ⟨5, _⟩ =>
    .pop (Sum.inr (Sum.inr (Sum.inl M2.k₁))) (fun v o => setBuf v (o.map fun _ => false))
      (.branch (fun v => (getBuf v).isSome)
        (.push (Sum.inl 2) (fun _ => false) (.goto fun _ => Sum.inl 5))
        (.goto fun _ => Sum.inl 6))
  | ⟨6, _⟩ =>
    .pop (Sum.inl 2) (fun v o => setBuf v o)
      (.branch (fun v => (getBuf v).isSome)
        (.goto fun _ => Sum.inl 7)
        (.goto fun _ => Sum.inl 10))
  | ⟨7, _⟩ =>
    .pop (Sum.inl 2) (fun v o => setBuf v o)
      (.branch (fun v => (getBuf v).isSome)
        (.push (Sum.inl 3) (fun _ => false) (.goto fun _ => Sum.inl 8))
        (.push (Sum.inl 4) (fun _ => true) (.goto fun _ => Sum.inl 9)))
  | ⟨8, _⟩ =>
    .pop (Sum.inl 2) (fun v o => setBuf v o)
      (.branch (fun v => (getBuf v).isSome)
        (.goto fun _ => Sum.inl 7)
        (.push (Sum.inl 4) (fun _ => false) (.goto fun _ => Sum.inl 9)))
  | ⟨9, _⟩ =>
    .pop (Sum.inl 3) (fun v o => setBuf v o)
      (.branch (fun v => (getBuf v).isSome)
        (.push (Sum.inl 2) (fun _ => false) (.goto fun _ => Sum.inl 9))
        (.goto fun _ => Sum.inl 6))
  | ⟨10, _⟩ =>
    .pop (Sum.inl 4) (fun v o => setBuf v o)
      (.branch (fun v => (getBuf v).isSome)
        (.push (Sum.inl 1) (fun v => (getBuf v).getD false)
          (.push (Sum.inl 1) (fun _ => true)
            (.goto fun _ => Sum.inl 10)))
        (.push (Sum.inl 1) (fun _ => true)
          (.branch (fun v => getPh v)
            (.load (fun v => setPh v false) (.goto fun _ => Sum.inl 11))
            (.load (fun v => setPh v true) (.goto fun _ => Sum.inl 3)))))
  | ⟨11, _⟩ =>
    .pop (Sum.inl 0) (fun v o => setBuf v o)
      (.branch (fun v => (getBuf v).isSome)
        (.push (Sum.inl 2) (fun v => (getBuf v).getD false) (.goto fun _ => Sum.inl 11))
        (.goto fun _ => Sum.inl 12))
  | ⟨12, _⟩ =>
    .pop (Sum.inl 2) (fun v o => setBuf v o)
      (.branch (fun v => (getBuf v).isSome)
        (.push (Sum.inr (Sum.inr (Sum.inr M3.k₀))) (fun v => i3 ((getBuf v).getD false))
          (.goto fun _ => Sum.inl 12))
        (.goto fun _ => Sum.inr (Sum.inr (Sum.inr M3.main))))
  | ⟨13, _⟩ =>
    .pop (Sum.inr (Sum.inr (Sum.inr M3.k₁))) (fun v o => setBuf v (o.map fun _ => false))
      (.branch (fun v => (getBuf v).isSome)
        (.push (Sum.inl 1) (fun _ => true)
          (.push (Sum.inl 1) (fun _ => false)
            (.push (Sum.inl 1) (fun _ => true)
              (.goto fun _ => Sum.inl 14))))
        (.push (Sum.inl 1) (fun _ => false)
          (.push (Sum.inl 1) (fun _ => false)
            (.push (Sum.inl 1) (fun _ => true)
              .halt))))
  | ⟨14, _⟩ =>
    .pop (Sum.inr (Sum.inr (Sum.inr M3.k₁))) (fun v o => setBuf v (o.map fun _ => false))
      (.branch (fun v => (getBuf v).isSome)
        (.goto fun _ => Sum.inl 14)
        .halt)

private def prog (i1 : Bool → M1.Γ M1.k₀) (i2 : Bool → M2.Γ M2.k₀) (i3 : Bool → M3.Γ M3.k₀) :
    MΛ M1 M2 M3 → TM2.Stmt (MΓ M1 M2 M3) (MΛ M1 M2 M3) (Mσ M1 M2 M3)
  | Sum.inl c => ctrl M1 M2 M3 i1 i2 i3 c
  | Sum.inr (Sum.inl l) => tr1 (M1.m l)
  | Sum.inr (Sum.inr (Sum.inl l)) => tr2 (M2.m l)
  | Sum.inr (Sum.inr (Sum.inr l)) => tr3 (M3.m l)

private def comb (i1 : Bool → M1.Γ M1.k₀) (i2 : Bool → M2.Γ M2.k₀) (i3 : Bool → M3.Γ M3.k₀) : FinTM2 :=
  haveI := M1.kDecidableEq
  haveI := M2.kDecidableEq
  haveI := M3.kDecidableEq
  haveI := M1.kFin
  haveI := M2.kFin
  haveI := M3.kFin
  haveI := M1.ΛFin
  haveI := M2.ΛFin
  haveI := M3.ΛFin
  haveI := M1.σFin
  haveI := M2.σFin
  haveI := M3.σFin
  { K := MK M1 M2 M3
    k₀ := Sum.inl 0
    k₁ := Sum.inl 1
    Γ := MΓ M1 M2 M3
    Λ := MΛ M1 M2 M3
    main := Sum.inl 0
    σ := Mσ M1 M2 M3
    initialState := (M1.initialState, M2.initialState, M3.initialState, none, false)
    m := prog M1 M2 M3 i1 i2 i3 }

variable {M1 M2 M3}

private def mkAux (s0 s1 s2 s3 s4 : List Bool) : Fin 5 → List Bool
  | ⟨0, _⟩ => s0
  | ⟨1, _⟩ => s1
  | ⟨2, _⟩ => s2
  | ⟨3, _⟩ => s3
  | ⟨4, _⟩ => s4

private def mkStk (s0 s1 s2 s3 s4 : List Bool)
    (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k)) (S3 : ∀ k, List (M3.Γ k)) :
    ∀ k, List (MΓ M1 M2 M3 k)
  | Sum.inl j => mkAux s0 s1 s2 s3 s4 j
  | Sum.inr (Sum.inl k) => S1 k
  | Sum.inr (Sum.inr (Sum.inl k)) => S2 k
  | Sum.inr (Sum.inr (Sum.inr k)) => S3 k

private lemma mkStk_upd0 [DecidableEq (MK M1 M2 M3)] (s0 s0' s1 s2 s3 s4 : List Bool)
    (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k)) (S3 : ∀ k, List (M3.Γ k)) :
    Function.update (mkStk s0 s1 s2 s3 s4 S1 S2 S3) (Sum.inl 0) s0' =
      mkStk s0' s1 s2 s3 s4 S1 S2 S3 := by
  funext j
  rcases j with j | k | k | k
  · fin_cases j <;> simp [mkStk, mkAux]
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

private lemma mkStk_upd1 [DecidableEq (MK M1 M2 M3)] (s0 s1 s1' s2 s3 s4 : List Bool)
    (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k)) (S3 : ∀ k, List (M3.Γ k)) :
    Function.update (mkStk s0 s1 s2 s3 s4 S1 S2 S3) (Sum.inl 1) s1' =
      mkStk s0 s1' s2 s3 s4 S1 S2 S3 := by
  funext j
  rcases j with j | k | k | k
  · fin_cases j <;> simp [mkStk, mkAux]
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

private lemma mkStk_upd2 [DecidableEq (MK M1 M2 M3)] (s0 s1 s2 s2' s3 s4 : List Bool)
    (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k)) (S3 : ∀ k, List (M3.Γ k)) :
    Function.update (mkStk s0 s1 s2 s3 s4 S1 S2 S3) (Sum.inl 2) s2' =
      mkStk s0 s1 s2' s3 s4 S1 S2 S3 := by
  funext j
  rcases j with j | k | k | k
  · fin_cases j <;> simp [mkStk, mkAux]
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

private lemma mkStk_upd3 [DecidableEq (MK M1 M2 M3)] (s0 s1 s2 s3 s3' s4 : List Bool)
    (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k)) (S3 : ∀ k, List (M3.Γ k)) :
    Function.update (mkStk s0 s1 s2 s3 s4 S1 S2 S3) (Sum.inl 3) s3' =
      mkStk s0 s1 s2 s3' s4 S1 S2 S3 := by
  funext j
  rcases j with j | k | k | k
  · fin_cases j <;> simp [mkStk, mkAux]
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

private lemma mkStk_upd4 [DecidableEq (MK M1 M2 M3)] (s0 s1 s2 s3 s4 s4' : List Bool)
    (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k)) (S3 : ∀ k, List (M3.Γ k)) :
    Function.update (mkStk s0 s1 s2 s3 s4 S1 S2 S3) (Sum.inl 4) s4' =
      mkStk s0 s1 s2 s3 s4' S1 S2 S3 := by
  funext j
  rcases j with j | k | k | k
  · fin_cases j <;> simp [mkStk, mkAux]
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

private lemma mkStk_updS1 [DecidableEq (MK M1 M2 M3)] (s0 s1 s2 s3 s4 : List Bool)
    (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k)) (S3 : ∀ k, List (M3.Γ k))
    (k : M1.K) (x : List (M1.Γ k)) :
    Function.update (mkStk s0 s1 s2 s3 s4 S1 S2 S3) (Sum.inr (Sum.inl k)) x =
      mkStk s0 s1 s2 s3 s4 (Function.update S1 k x) S2 S3 := by
  funext j
  rcases j with j | j | j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · by_cases h : j = k
    · subst h
      rw [Function.update_self]
      show x = Function.update S1 j x j
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show S1 j = Function.update S1 k x j
      rw [Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

private lemma mkStk_updS2 [DecidableEq (MK M1 M2 M3)] (s0 s1 s2 s3 s4 : List Bool)
    (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k)) (S3 : ∀ k, List (M3.Γ k))
    (k : M2.K) (x : List (M2.Γ k)) :
    Function.update (mkStk s0 s1 s2 s3 s4 S1 S2 S3) (Sum.inr (Sum.inr (Sum.inl k))) x =
      mkStk s0 s1 s2 s3 s4 S1 (Function.update S2 k x) S3 := by
  funext j
  rcases j with j | j | j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · by_cases h : j = k
    · subst h
      rw [Function.update_self]
      show x = Function.update S2 j x j
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show S2 j = Function.update S2 k x j
      rw [Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)]; rfl

private lemma mkStk_updS3 [DecidableEq (MK M1 M2 M3)] (s0 s1 s2 s3 s4 : List Bool)
    (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k)) (S3 : ∀ k, List (M3.Γ k))
    (k : M3.K) (x : List (M3.Γ k)) :
    Function.update (mkStk s0 s1 s2 s3 s4 S1 S2 S3) (Sum.inr (Sum.inr (Sum.inr k))) x =
      mkStk s0 s1 s2 s3 s4 S1 S2 (Function.update S3 k x) := by
  funext j
  rcases j with j | j | j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · by_cases h : j = k
    · subst h
      rw [Function.update_self]
      show x = Function.update S3 j x j
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show S3 j = Function.update S3 k x j
      rw [Function.update_of_ne h]

private lemma mkStk_init [DecidableEq (MK M1 M2 M3)] (s : List Bool) :
    Function.update (fun _ => [] : ∀ k, List (MΓ M1 M2 M3 k)) (Sum.inl 0) s =
      mkStk s [] [] [] [] (fun _ => []) (fun _ => []) (fun _ => []) := by
  funext j
  rcases j with j | k | k | k
  · fin_cases j <;> simp [mkStk, mkAux]
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

private lemma mkStk_halt [DecidableEq (MK M1 M2 M3)] (o : List Bool) :
    Function.update (fun _ => [] : ∀ k, List (MΓ M1 M2 M3 k)) (Sum.inl 1) o =
      mkStk [] o [] [] [] (fun _ => []) (fun _ => []) (fun _ => []) := by
  funext j
  rcases j with j | k | k | k
  · fin_cases j <;> simp [mkStk, mkAux]
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

private def emb1 (s0 s1 s2 s3 s4 : List Bool) (w : M2.σ × M3.σ × Option Bool × Bool)
    (c : TM2.Cfg M1.Γ M1.Λ M1.σ) : MCfg M1 M2 M3 :=
  ⟨some (c.l.elim (Sum.inl 2) (fun l => Sum.inr (Sum.inl l))), (c.var, w),
    mkStk s0 s1 s2 s3 s4 c.stk (fun _ => []) (fun _ => [])⟩

private def emb2 (s0 s1 s2 s3 s4 : List Bool) (v1 : M1.σ) (w : M3.σ × Option Bool × Bool)
    (c : TM2.Cfg M2.Γ M2.Λ M2.σ) : MCfg M1 M2 M3 :=
  ⟨some (c.l.elim (Sum.inl 5) (fun l => Sum.inr (Sum.inr (Sum.inl l)))), (v1, c.var, w),
    mkStk s0 s1 s2 s3 s4 (fun _ => []) c.stk (fun _ => [])⟩

private def emb3 (s0 s1 s2 s3 s4 : List Bool) (v1 : M1.σ) (v2 : M2.σ) (w : Option Bool × Bool)
    (c : TM2.Cfg M3.Γ M3.Λ M3.σ) : MCfg M1 M2 M3 :=
  ⟨some (c.l.elim (Sum.inl 13) (fun l => Sum.inr (Sum.inr (Sum.inr l)))), (v1, v2, c.var, w),
    mkStk s0 s1 s2 s3 s4 (fun _ => []) (fun _ => []) c.stk⟩

private lemma sim1 [DecidableEq (MK M1 M2 M3)] (s0 s1 s2 s3 s4 : List Bool)
    (w : M2.σ × M3.σ × Option Bool × Bool) (q : TM2.Stmt M1.Γ M1.Λ M1.σ) (v : M1.σ)
    (S : ∀ k, List (M1.Γ k)) :
    TM2.stepAux (tr1 q) ((v, w) : Mσ M1 M2 M3)
      (mkStk s0 s1 s2 s3 s4 S (fun _ => []) (fun _ => [])) =
      emb1 s0 s1 s2 s3 s4 w (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    simp only [tr1, TM2.stepAux]
    rw [mkStk_updS1]
    exact ih v (Function.update S k (f v :: S k))
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    simp only [tr1, TM2.stepAux]
    rw [mkStk_updS1]
    exact ih (f v (S k).head?) (Function.update S k (S k).tail)
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [tr1, TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f => rfl
  | halt => rfl

private lemma sim2 [DecidableEq (MK M1 M2 M3)] (s0 s1 s2 s3 s4 : List Bool)
    (v1 : M1.σ) (w : M3.σ × Option Bool × Bool) (q : TM2.Stmt M2.Γ M2.Λ M2.σ) (v : M2.σ)
    (S : ∀ k, List (M2.Γ k)) :
    TM2.stepAux (tr2 q) ((v1, v, w) : Mσ M1 M2 M3)
      (mkStk s0 s1 s2 s3 s4 (fun _ => []) S (fun _ => [])) =
      emb2 s0 s1 s2 s3 s4 v1 w (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    simp only [tr2, TM2.stepAux]
    rw [mkStk_updS2]
    exact ih v (Function.update S k (f v :: S k))
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    simp only [tr2, TM2.stepAux]
    rw [mkStk_updS2]
    exact ih (f v (S k).head?) (Function.update S k (S k).tail)
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [tr2, TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f => rfl
  | halt => rfl

private lemma sim3 [DecidableEq (MK M1 M2 M3)] (s0 s1 s2 s3 s4 : List Bool)
    (v1 : M1.σ) (v2 : M2.σ) (w : Option Bool × Bool) (q : TM2.Stmt M3.Γ M3.Λ M3.σ) (v : M3.σ)
    (S : ∀ k, List (M3.Γ k)) :
    TM2.stepAux (tr3 q) ((v1, v2, v, w) : Mσ M1 M2 M3)
      (mkStk s0 s1 s2 s3 s4 (fun _ => []) (fun _ => []) S) =
      emb3 s0 s1 s2 s3 s4 v1 v2 w (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    simp only [tr3, TM2.stepAux]
    rw [mkStk_updS3]
    exact ih v (Function.update S k (f v :: S k))
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    simp only [tr3, TM2.stepAux]
    rw [mkStk_updS3]
    exact ih (f v (S k).head?) (Function.update S k (S k).tail)
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [tr3, TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f => rfl
  | halt => rfl

variable (i1 : Bool → M1.Γ M1.k₀) (i2 : Bool → M2.Γ M2.k₀) (i3 : Bool → M3.Γ M3.k₀)

private lemma step1 [DecidableEq (MK M1 M2 M3)] (s0 s1 s2 s3 s4 : List Bool)
    (w : M2.σ × M3.σ × Option Bool × Bool) (c c' : TM2.Cfg M1.Γ M1.Λ M1.σ)
    (h : TM2.step M1.m c = some c') :
    TM2.step (prog M1 M2 M3 i1 i2 i3) (emb1 s0 s1 s2 s3 s4 w c) =
      some (emb1 s0 s1 s2 s3 s4 w c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (sim1 s0 s1 s2 s3 s4 w (M1.m l) v S)

private lemma step2 [DecidableEq (MK M1 M2 M3)] (s0 s1 s2 s3 s4 : List Bool)
    (v1 : M1.σ) (w : M3.σ × Option Bool × Bool) (c c' : TM2.Cfg M2.Γ M2.Λ M2.σ)
    (h : TM2.step M2.m c = some c') :
    TM2.step (prog M1 M2 M3 i1 i2 i3) (emb2 s0 s1 s2 s3 s4 v1 w c) =
      some (emb2 s0 s1 s2 s3 s4 v1 w c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (sim2 s0 s1 s2 s3 s4 v1 w (M2.m l) v S)

private lemma step3 [DecidableEq (MK M1 M2 M3)] (s0 s1 s2 s3 s4 : List Bool)
    (v1 : M1.σ) (v2 : M2.σ) (w : Option Bool × Bool) (c c' : TM2.Cfg M3.Γ M3.Λ M3.σ)
    (h : TM2.step M3.m c = some c') :
    TM2.step (prog M1 M2 M3 i1 i2 i3) (emb3 s0 s1 s2 s3 s4 v1 v2 w c) =
      some (emb3 s0 s1 s2 s3 s4 v1 v2 w c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (sim3 s0 s1 s2 s3 s4 v1 v2 w (M3.m l) v S)

private lemma loop_copyB1 [DecidableEq (MK M1 M2 M3)] (v1 : M1.σ) (v2 : M2.σ) (v3 : M3.σ)
    (ph : Bool) (out : List Bool) :
    ∀ (l u : List Bool) (buf : Option Bool),
      (flip bind (TM2.step (prog M1 M2 M3 i1 i2 i3)))^[l.length + 1]
        (some (⟨some (Sum.inl 0), (v1, v2, v3, buf, ph),
          mkStk l out u [] [] (fun _ => []) (fun _ => []) (fun _ => [])⟩ : MCfg M1 M2 M3)) =
      some ⟨some (Sum.inl 1), (v1, v2, v3, none, ph),
        mkStk [] out (l.reverse ++ u) [] [] (fun _ => []) (fun _ => []) (fun _ => [])⟩ := by
  intro l
  induction l with
  | nil =>
    intro u buf
    show some _ = some _
    simp only [prog, ctrl, TM2.stepAux, setBuf, getBuf, mkStk, mkAux, List.head?_nil, List.tail_nil,
      Option.isSome_none, Bool.cond_false, List.reverse_nil, List.nil_append]
    rw [mkStk_upd0]
  | cons x l ih =>
    intro u buf
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (prog M1 M2 M3 i1 i2 i3))
        (some (⟨some (Sum.inl 0), (v1, v2, v3, buf, ph),
          mkStk (x :: l) out u [] [] (fun _ => []) (fun _ => []) (fun _ => [])⟩ : MCfg M1 M2 M3)) =
        some ⟨some (Sum.inl 0), (v1, v2, v3, some x, ph),
          mkStk l out (x :: u) [] [] (fun _ => []) (fun _ => []) (fun _ => [])⟩ := by
      show some _ = some _
      simp only [prog, ctrl, TM2.stepAux, setBuf, getBuf, mkStk, mkAux, List.head?_cons, List.tail_cons,
        Option.isSome_some, Bool.cond_true, Option.getD_some]
      rw [mkStk_upd0, mkStk_upd2]; rfl
    rw [e, ih]
    simp

private lemma loop_copyB2 [DecidableEq (MK M1 M2 M3)] (v1 : M1.σ) (v2 : M2.σ) (v3 : M3.σ)
    (ph : Bool) (out : List Bool) :
    ∀ (u r : List Bool) (acc1 : List (M1.Γ M1.k₀)) (buf : Option Bool),
      (flip bind (TM2.step (prog M1 M2 M3 i1 i2 i3)))^[u.length + 1]
        (some (⟨some (Sum.inl 1), (v1, v2, v3, buf, ph),
          mkStk r out u [] [] (Function.update (fun _ => []) M1.k₀ acc1)
            (fun _ => []) (fun _ => [])⟩ : MCfg M1 M2 M3)) =
      some ⟨some (Sum.inr (Sum.inl M1.main)), (v1, v2, v3, none, ph),
        mkStk (u.reverse ++ r) (false :: false :: out) [] [] []
          (Function.update (fun _ => []) M1.k₀ ((u.map i1).reverse ++ acc1))
          (fun _ => []) (fun _ => [])⟩ := by
  intro u
  induction u with
  | nil =>
    intro r acc1 buf
    show some _ = some _
    simp only [prog, ctrl, TM2.stepAux, setBuf, getBuf, mkStk, mkAux, List.head?_nil, List.tail_nil,
      Option.isSome_none, Bool.cond_false, List.reverse_nil, List.nil_append, List.map_nil]
    rw [mkStk_upd2, mkStk_upd1, mkStk_upd1]; rfl
  | cons x u ih =>
    intro r acc1 buf
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (prog M1 M2 M3 i1 i2 i3))
        (some (⟨some (Sum.inl 1), (v1, v2, v3, buf, ph),
          mkStk r out (x :: u) [] [] (Function.update (fun _ => []) M1.k₀ acc1)
            (fun _ => []) (fun _ => [])⟩ : MCfg M1 M2 M3)) =
        some ⟨some (Sum.inl 1), (v1, v2, v3, some x, ph),
          mkStk (x :: r) out u [] [] (Function.update (fun _ => []) M1.k₀ (i1 x :: acc1))
            (fun _ => []) (fun _ => [])⟩ := by
      show some _ = some _
      simp only [prog, ctrl, TM2.stepAux, setBuf, getBuf, mkStk, mkAux, List.head?_cons, List.tail_cons,
        Option.isSome_some, Bool.cond_true, Option.getD_some]
      rw [mkStk_upd2, mkStk_upd0, mkStk_updS1]
      simp only [mkStk, mkAux, Function.update_self, Function.update_idem]
    rw [e, ih]
    simp

private lemma loop_drainB [DecidableEq (MK M1 M2 M3)] (v1 : M1.σ) (v2 : M2.σ) (v3 : M3.σ)
    (ph : Bool) (s out : List Bool) :
    ∀ (l : List (M1.Γ M1.k₁)) (u : List Bool) (buf : Option Bool),
      (flip bind (TM2.step (prog M1 M2 M3 i1 i2 i3)))^[l.length + 1]
        (some (⟨some (Sum.inl 2), (v1, v2, v3, buf, ph),
          mkStk s out u [] [] (Function.update (fun _ => []) M1.k₁ l)
            (fun _ => []) (fun _ => [])⟩ : MCfg M1 M2 M3)) =
      some ⟨some (Sum.inl 6), (v1, v2, v3, none, ph),
        mkStk s out (List.replicate l.length false ++ u) [] []
          (fun _ => []) (fun _ => []) (fun _ => [])⟩ := by
  intro l
  induction l with
  | nil =>
    intro u buf
    show some _ = some _
    simp only [prog, ctrl, TM2.stepAux, setBuf, getBuf, mkStk, Function.update_self,
      List.head?_nil, List.tail_nil, Option.map_none, Option.isSome_none, Bool.cond_false,
      List.length_nil, List.replicate_zero, List.nil_append]
    rw [mkStk_updS1, Function.update_idem, Function.update_eq_self_iff.mpr rfl]
  | cons x l ih =>
    intro u buf
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (prog M1 M2 M3 i1 i2 i3))
        (some (⟨some (Sum.inl 2), (v1, v2, v3, buf, ph),
          mkStk s out u [] [] (Function.update (fun _ => []) M1.k₁ (x :: l))
            (fun _ => []) (fun _ => [])⟩ : MCfg M1 M2 M3)) =
        some ⟨some (Sum.inl 2), (v1, v2, v3, some false, ph),
          mkStk s out (false :: u) [] [] (Function.update (fun _ => []) M1.k₁ l)
            (fun _ => []) (fun _ => [])⟩ := by
      show some _ = some _
      simp only [prog, ctrl, TM2.stepAux, setBuf, getBuf, mkStk, Function.update_self,
        List.head?_cons, List.tail_cons, Option.map_some, Option.isSome_some, Bool.cond_true]
      rw [mkStk_updS1, Function.update_idem, mkStk_upd2]; rfl
    rw [e, ih]
    simp [List.replicate_succ', List.append_assoc]

private lemma loop_copyA1 [DecidableEq (MK M1 M2 M3)] (v1 : M1.σ) (v2 : M2.σ) (v3 : M3.σ)
    (ph : Bool) (out : List Bool) :
    ∀ (l u : List Bool) (buf : Option Bool),
      (flip bind (TM2.step (prog M1 M2 M3 i1 i2 i3)))^[l.length + 1]
        (some (⟨some (Sum.inl 3), (v1, v2, v3, buf, ph),
          mkStk l out u [] [] (fun _ => []) (fun _ => []) (fun _ => [])⟩ : MCfg M1 M2 M3)) =
      some ⟨some (Sum.inl 4), (v1, v2, v3, none, ph),
        mkStk [] out (l.reverse ++ u) [] [] (fun _ => []) (fun _ => []) (fun _ => [])⟩ := by
  intro l
  induction l with
  | nil =>
    intro u buf
    show some _ = some _
    simp only [prog, ctrl, TM2.stepAux, setBuf, getBuf, mkStk, mkAux, List.head?_nil, List.tail_nil,
      Option.isSome_none, Bool.cond_false, List.reverse_nil, List.nil_append]
    rw [mkStk_upd0]
  | cons x l ih =>
    intro u buf
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (prog M1 M2 M3 i1 i2 i3))
        (some (⟨some (Sum.inl 3), (v1, v2, v3, buf, ph),
          mkStk (x :: l) out u [] [] (fun _ => []) (fun _ => []) (fun _ => [])⟩ : MCfg M1 M2 M3)) =
        some ⟨some (Sum.inl 3), (v1, v2, v3, some x, ph),
          mkStk l out (x :: u) [] [] (fun _ => []) (fun _ => []) (fun _ => [])⟩ := by
      show some _ = some _
      simp only [prog, ctrl, TM2.stepAux, setBuf, getBuf, mkStk, mkAux, List.head?_cons, List.tail_cons,
        Option.isSome_some, Bool.cond_true, Option.getD_some]
      rw [mkStk_upd0, mkStk_upd2]; rfl
    rw [e, ih]
    simp

private lemma loop_copyA2 [DecidableEq (MK M1 M2 M3)] (v1 : M1.σ) (v2 : M2.σ) (v3 : M3.σ)
    (ph : Bool) (out : List Bool) :
    ∀ (u r : List Bool) (acc2 : List (M2.Γ M2.k₀)) (buf : Option Bool),
      (flip bind (TM2.step (prog M1 M2 M3 i1 i2 i3)))^[u.length + 1]
        (some (⟨some (Sum.inl 4), (v1, v2, v3, buf, ph),
          mkStk r out u [] [] (fun _ => [])
            (Function.update (fun _ => []) M2.k₀ acc2) (fun _ => [])⟩ : MCfg M1 M2 M3)) =
      some ⟨some (Sum.inr (Sum.inr (Sum.inl M2.main))), (v1, v2, v3, none, ph),
        mkStk (u.reverse ++ r) (false :: out) [] [] []
          (fun _ => []) (Function.update (fun _ => []) M2.k₀ ((u.map i2).reverse ++ acc2))
          (fun _ => [])⟩ := by
  intro u
  induction u with
  | nil =>
    intro r acc2 buf
    show some _ = some _
    simp only [prog, ctrl, TM2.stepAux, setBuf, getBuf, mkStk, mkAux, List.head?_nil, List.tail_nil,
      Option.isSome_none, Bool.cond_false, List.reverse_nil, List.nil_append, List.map_nil]
    rw [mkStk_upd2, mkStk_upd1]; rfl
  | cons x u ih =>
    intro r acc2 buf
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (prog M1 M2 M3 i1 i2 i3))
        (some (⟨some (Sum.inl 4), (v1, v2, v3, buf, ph),
          mkStk r out (x :: u) [] [] (fun _ => [])
            (Function.update (fun _ => []) M2.k₀ acc2) (fun _ => [])⟩ : MCfg M1 M2 M3)) =
        some ⟨some (Sum.inl 4), (v1, v2, v3, some x, ph),
          mkStk (x :: r) out u [] [] (fun _ => [])
            (Function.update (fun _ => []) M2.k₀ (i2 x :: acc2)) (fun _ => [])⟩ := by
      show some _ = some _
      simp only [prog, ctrl, TM2.stepAux, setBuf, getBuf, mkStk, mkAux, List.head?_cons, List.tail_cons,
        Option.isSome_some, Bool.cond_true, Option.getD_some]
      rw [mkStk_upd2, mkStk_upd0, mkStk_updS2]
      simp only [mkStk, mkAux, Function.update_self, Function.update_idem]
    rw [e, ih]
    simp

private lemma loop_drainA [DecidableEq (MK M1 M2 M3)] (v1 : M1.σ) (v2 : M2.σ) (v3 : M3.σ)
    (ph : Bool) (s out : List Bool) :
    ∀ (l : List (M2.Γ M2.k₁)) (u : List Bool) (buf : Option Bool),
      (flip bind (TM2.step (prog M1 M2 M3 i1 i2 i3)))^[l.length + 1]
        (some (⟨some (Sum.inl 5), (v1, v2, v3, buf, ph),
          mkStk s out u [] [] (fun _ => [])
            (Function.update (fun _ => []) M2.k₁ l) (fun _ => [])⟩ : MCfg M1 M2 M3)) =
      some ⟨some (Sum.inl 6), (v1, v2, v3, none, ph),
        mkStk s out (List.replicate l.length false ++ u) [] []
          (fun _ => []) (fun _ => []) (fun _ => [])⟩ := by
  intro l
  induction l with
  | nil =>
    intro u buf
    show some _ = some _
    simp only [prog, ctrl, TM2.stepAux, setBuf, getBuf, mkStk, Function.update_self,
      List.head?_nil, List.tail_nil, Option.map_none, Option.isSome_none, Bool.cond_false,
      List.length_nil, List.replicate_zero, List.nil_append]
    rw [mkStk_updS2, Function.update_idem, Function.update_eq_self_iff.mpr rfl]
  | cons x l ih =>
    intro u buf
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (prog M1 M2 M3 i1 i2 i3))
        (some (⟨some (Sum.inl 5), (v1, v2, v3, buf, ph),
          mkStk s out u [] [] (fun _ => [])
            (Function.update (fun _ => []) M2.k₁ (x :: l)) (fun _ => [])⟩ : MCfg M1 M2 M3)) =
        some ⟨some (Sum.inl 5), (v1, v2, v3, some false, ph),
          mkStk s out (false :: u) [] [] (fun _ => [])
            (Function.update (fun _ => []) M2.k₁ l) (fun _ => [])⟩ := by
      show some _ = some _
      simp only [prog, ctrl, TM2.stepAux, setBuf, getBuf, mkStk, Function.update_self,
        List.head?_cons, List.tail_cons, Option.map_some, Option.isSome_some, Bool.cond_true]
      rw [mkStk_updS2, Function.update_idem, mkStk_upd2]; rfl
    rw [e, ih]
    simp [List.replicate_succ', List.append_assoc]

private lemma loop_halve_inner [DecidableEq (MK M1 M2 M3)] (v1 : M1.σ) (v2 : M2.σ) (v3 : M3.σ)
    (ph : Bool) (s out : List Bool) :
    ∀ (u : List Bool),
      (∀ (v acc : List Bool) (buf : Option Bool),
        (flip bind (TM2.step (prog M1 M2 M3 i1 i2 i3)))^[u.length + 1]
          (some (⟨some (Sum.inl 7), (v1, v2, v3, buf, ph),
            mkStk s out u v acc (fun _ => []) (fun _ => []) (fun _ => [])⟩ : MCfg M1 M2 M3)) =
        some ⟨some (Sum.inl 9), (v1, v2, v3, none, ph),
          mkStk s out [] (List.replicate ((u.length + 1) / 2) false ++ v)
            (decide ((u.length + 1) % 2 = 1) :: acc)
            (fun _ => []) (fun _ => []) (fun _ => [])⟩) ∧
      (∀ (v acc : List Bool) (buf : Option Bool),
        (flip bind (TM2.step (prog M1 M2 M3 i1 i2 i3)))^[u.length + 1]
          (some (⟨some (Sum.inl 8), (v1, v2, v3, buf, ph),
            mkStk s out u v acc (fun _ => []) (fun _ => []) (fun _ => [])⟩ : MCfg M1 M2 M3)) =
        some ⟨some (Sum.inl 9), (v1, v2, v3, none, ph),
          mkStk s out [] (List.replicate (u.length / 2) false ++ v)
            (decide (u.length % 2 = 1) :: acc)
            (fun _ => []) (fun _ => []) (fun _ => [])⟩) := by
  intro u
  induction u with
  | nil =>
    constructor
    · intro v acc buf
      show some _ = some _
      simp only [prog, ctrl, TM2.stepAux, setBuf, getBuf, mkStk, mkAux, List.head?_nil, List.tail_nil,
        Option.isSome_none, Bool.cond_false, List.length_nil]
      rw [mkStk_upd2, mkStk_upd4]; rfl
    · intro v acc buf
      show some _ = some _
      simp only [prog, ctrl, TM2.stepAux, setBuf, getBuf, mkStk, mkAux, List.head?_nil, List.tail_nil,
        Option.isSome_none, Bool.cond_false, List.length_nil]
      rw [mkStk_upd2, mkStk_upd4]; rfl
  | cons x u ih =>
    constructor
    · intro v acc buf
      rw [List.length_cons, Function.iterate_succ_apply]
      have e : flip bind (TM2.step (prog M1 M2 M3 i1 i2 i3))
          (some (⟨some (Sum.inl 7), (v1, v2, v3, buf, ph),
            mkStk s out (x :: u) v acc (fun _ => []) (fun _ => []) (fun _ => [])⟩ : MCfg M1 M2 M3)) =
          some ⟨some (Sum.inl 8), (v1, v2, v3, some x, ph),
            mkStk s out u (false :: v) acc (fun _ => []) (fun _ => []) (fun _ => [])⟩ := by
        show some _ = some _
        simp only [prog, ctrl, TM2.stepAux, setBuf, getBuf, mkStk, mkAux, List.head?_cons, List.tail_cons,
          Option.isSome_some, Bool.cond_true]
        rw [mkStk_upd2, mkStk_upd3]; rfl
      rw [e, ih.2]
      have hdiv : (u.length + 1 + 1) / 2 = u.length / 2 + 1 := by omega
      have hmod : (u.length + 1 + 1) % 2 = u.length % 2 := by omega
      rw [hdiv, hmod, List.replicate_succ']
      simp [List.append_assoc]
    · intro v acc buf
      rw [List.length_cons, Function.iterate_succ_apply]
      have e : flip bind (TM2.step (prog M1 M2 M3 i1 i2 i3))
          (some (⟨some (Sum.inl 8), (v1, v2, v3, buf, ph),
            mkStk s out (x :: u) v acc (fun _ => []) (fun _ => []) (fun _ => [])⟩ : MCfg M1 M2 M3)) =
          some ⟨some (Sum.inl 7), (v1, v2, v3, some x, ph),
            mkStk s out u v acc (fun _ => []) (fun _ => []) (fun _ => [])⟩ := by
        show some _ = some _
        simp only [prog, ctrl, TM2.stepAux, setBuf, getBuf, mkStk, mkAux, List.head?_cons, List.tail_cons,
          Option.isSome_some, Bool.cond_true]
        rw [mkStk_upd2]
      rw [e, ih.1]

private lemma loop_restoreU [DecidableEq (MK M1 M2 M3)] (v1 : M1.σ) (v2 : M2.σ) (v3 : M3.σ)
    (ph : Bool) (s out acc : List Bool) :
    ∀ (v u : List Bool) (buf : Option Bool),
      (flip bind (TM2.step (prog M1 M2 M3 i1 i2 i3)))^[v.length + 1]
        (some (⟨some (Sum.inl 9), (v1, v2, v3, buf, ph),
          mkStk s out u v acc (fun _ => []) (fun _ => []) (fun _ => [])⟩ : MCfg M1 M2 M3)) =
      some ⟨some (Sum.inl 6), (v1, v2, v3, none, ph),
        mkStk s out (List.replicate v.length false ++ u) [] acc
          (fun _ => []) (fun _ => []) (fun _ => [])⟩ := by
  intro v
  induction v with
  | nil =>
    intro u buf
    show some _ = some _
    simp only [prog, ctrl, TM2.stepAux, setBuf, getBuf, mkStk, mkAux, List.head?_nil, List.tail_nil,
      Option.isSome_none, Bool.cond_false, List.length_nil, List.replicate_zero, List.nil_append]
    rw [mkStk_upd3]
  | cons x v ih =>
    intro u buf
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (prog M1 M2 M3 i1 i2 i3))
        (some (⟨some (Sum.inl 9), (v1, v2, v3, buf, ph),
          mkStk s out u (x :: v) acc (fun _ => []) (fun _ => []) (fun _ => [])⟩ : MCfg M1 M2 M3)) =
        some ⟨some (Sum.inl 9), (v1, v2, v3, some x, ph),
          mkStk s out (false :: u) v acc (fun _ => []) (fun _ => []) (fun _ => [])⟩ := by
      show some _ = some _
      simp only [prog, ctrl, TM2.stepAux, setBuf, getBuf, mkStk, mkAux, List.head?_cons, List.tail_cons,
        Option.isSome_some, Bool.cond_true]
      rw [mkStk_upd3, mkStk_upd2]; rfl
    rw [e, ih]
    simp [List.replicate_succ', List.append_assoc]

private lemma loop_halve [DecidableEq (MK M1 M2 M3)] (v1 : M1.σ) (v2 : M2.σ) (v3 : M3.σ)
    (ph : Bool) (s out : List Bool) :
    ∀ (m : ℕ) (u acc : List Bool) (buf : Option Bool),
      u.length = m →
      ∃ n, n ≤ 6 * m + 1 ∧
        (flip bind (TM2.step (prog M1 M2 M3 i1 i2 i3)))^[n]
          (some (⟨some (Sum.inl 6), (v1, v2, v3, buf, ph),
            mkStk s out u [] acc (fun _ => []) (fun _ => []) (fun _ => [])⟩ : MCfg M1 M2 M3)) =
        some ⟨some (Sum.inl 10), (v1, v2, v3, none, ph),
          mkStk s out [] [] ((Nat.bits m).reverse ++ acc)
            (fun _ => []) (fun _ => []) (fun _ => [])⟩ := by
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro u acc buf hu
    cases u with
    | nil =>
      subst hu
      refine ⟨1, by omega, ?_⟩
      show some _ = some _
      simp only [prog, ctrl, TM2.stepAux, setBuf, getBuf, mkStk, mkAux, List.head?_nil, List.tail_nil,
        Option.isSome_none, Bool.cond_false, List.length_nil, Nat.zero_bits, List.reverse_nil,
        List.nil_append]
      rw [mkStk_upd2]
    | cons x u =>
      have hm : m = u.length + 1 := hu.symm
      subst hm
      have step6 : (flip bind (TM2.step (prog M1 M2 M3 i1 i2 i3)))^[1]
          (some (⟨some (Sum.inl 6), (v1, v2, v3, buf, ph),
            mkStk s out (x :: u) [] acc (fun _ => []) (fun _ => []) (fun _ => [])⟩ : MCfg M1 M2 M3)) =
          some ⟨some (Sum.inl 7), (v1, v2, v3, some x, ph),
            mkStk s out u [] acc (fun _ => []) (fun _ => []) (fun _ => [])⟩ := by
        show some _ = some _
        simp only [prog, ctrl, TM2.stepAux, setBuf, getBuf, mkStk, mkAux, List.head?_cons, List.tail_cons,
          Option.isSome_some, Bool.cond_true]
        rw [mkStk_upd2]
      have h7 := (loop_halve_inner i1 i2 i3 v1 v2 v3 ph s out u).1 [] acc (some x)
      simp only [List.append_nil] at h7
      have h9 := loop_restoreU i1 i2 i3 v1 v2 v3 ph s out (decide ((u.length + 1) % 2 = 1) :: acc)
        (List.replicate ((u.length + 1) / 2) false) [] none
      simp only [List.length_replicate, List.append_nil] at h9
      obtain ⟨nr, hnr, hr⟩ := ih ((u.length + 1) / 2) (by omega)
        (List.replicate ((u.length + 1) / 2) false)
        (decide ((u.length + 1) % 2 = 1) :: acc) none (List.length_replicate)
      have q1 := iter_trans step6 h7
      have q2 := iter_trans q1 h9
      have q3 := iter_trans q2 hr
      refine ⟨nr + (((u.length + 1) / 2 + 1) + ((u.length + 1) + 1)), by omega, ?_⟩
      rw [bits_succ]
      simpa [List.append_assoc] using q3

private lemma loop_emit_false [DecidableEq (MK M1 M2 M3)] (v1 : M1.σ) (v2 : M2.σ) (v3 : M3.σ)
    (s : List Bool) :
    ∀ (acc out : List Bool) (buf : Option Bool),
      (flip bind (TM2.step (prog M1 M2 M3 i1 i2 i3)))^[acc.length + 1]
        (some (⟨some (Sum.inl 10), (v1, v2, v3, buf, false),
          mkStk s out [] [] acc (fun _ => []) (fun _ => []) (fun _ => [])⟩ : MCfg M1 M2 M3)) =
      some ⟨some (Sum.inl 3), (v1, v2, v3, none, true),
        mkStk s (true :: (acc.reverse.flatMap (fun b => [true, b]) ++ out)) [] [] []
          (fun _ => []) (fun _ => []) (fun _ => [])⟩ := by
  intro acc
  induction acc with
  | nil =>
    intro out buf
    show some _ = some _
    simp only [prog, ctrl, TM2.stepAux, setBuf, getBuf, setPh, getPh, mkStk, mkAux,
      List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false, List.reverse_nil,
      List.flatMap_nil, List.nil_append]
    rw [mkStk_upd4, mkStk_upd1]; rfl
  | cons d ds ih =>
    intro out buf
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (prog M1 M2 M3 i1 i2 i3))
        (some (⟨some (Sum.inl 10), (v1, v2, v3, buf, false),
          mkStk s out [] [] (d :: ds) (fun _ => []) (fun _ => []) (fun _ => [])⟩ : MCfg M1 M2 M3)) =
        some ⟨some (Sum.inl 10), (v1, v2, v3, some d, false),
          mkStk s (true :: d :: out) [] [] ds (fun _ => []) (fun _ => []) (fun _ => [])⟩ := by
      show some _ = some _
      simp only [prog, ctrl, TM2.stepAux, setBuf, getBuf, mkStk, mkAux, List.head?_cons, List.tail_cons,
        Option.isSome_some, Bool.cond_true, Option.getD_some]
      rw [mkStk_upd4, mkStk_upd1, mkStk_upd1]; rfl
    rw [e, ih]
    simp [List.flatMap_append, List.append_assoc]

private lemma loop_emit_true [DecidableEq (MK M1 M2 M3)] (v1 : M1.σ) (v2 : M2.σ) (v3 : M3.σ)
    (s : List Bool) :
    ∀ (acc out : List Bool) (buf : Option Bool),
      (flip bind (TM2.step (prog M1 M2 M3 i1 i2 i3)))^[acc.length + 1]
        (some (⟨some (Sum.inl 10), (v1, v2, v3, buf, true),
          mkStk s out [] [] acc (fun _ => []) (fun _ => []) (fun _ => [])⟩ : MCfg M1 M2 M3)) =
      some ⟨some (Sum.inl 11), (v1, v2, v3, none, false),
        mkStk s (true :: (acc.reverse.flatMap (fun b => [true, b]) ++ out)) [] [] []
          (fun _ => []) (fun _ => []) (fun _ => [])⟩ := by
  intro acc
  induction acc with
  | nil =>
    intro out buf
    show some _ = some _
    simp only [prog, ctrl, TM2.stepAux, setBuf, getBuf, setPh, getPh, mkStk, mkAux,
      List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false, Bool.cond_true,
      List.reverse_nil, List.flatMap_nil, List.nil_append]
    rw [mkStk_upd4, mkStk_upd1]; rfl
  | cons d ds ih =>
    intro out buf
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (prog M1 M2 M3 i1 i2 i3))
        (some (⟨some (Sum.inl 10), (v1, v2, v3, buf, true),
          mkStk s out [] [] (d :: ds) (fun _ => []) (fun _ => []) (fun _ => [])⟩ : MCfg M1 M2 M3)) =
        some ⟨some (Sum.inl 10), (v1, v2, v3, some d, true),
          mkStk s (true :: d :: out) [] [] ds (fun _ => []) (fun _ => []) (fun _ => [])⟩ := by
      show some _ = some _
      simp only [prog, ctrl, TM2.stepAux, setBuf, getBuf, mkStk, mkAux, List.head?_cons, List.tail_cons,
        Option.isSome_some, Bool.cond_true, Option.getD_some]
      rw [mkStk_upd4, mkStk_upd1, mkStk_upd1]; rfl
    rw [e, ih]
    simp [List.flatMap_append, List.append_assoc]

private lemma loop_moveFl1 [DecidableEq (MK M1 M2 M3)] (v1 : M1.σ) (v2 : M2.σ) (v3 : M3.σ)
    (ph : Bool) (out : List Bool) :
    ∀ (l u : List Bool) (buf : Option Bool),
      (flip bind (TM2.step (prog M1 M2 M3 i1 i2 i3)))^[l.length + 1]
        (some (⟨some (Sum.inl 11), (v1, v2, v3, buf, ph),
          mkStk l out u [] [] (fun _ => []) (fun _ => []) (fun _ => [])⟩ : MCfg M1 M2 M3)) =
      some ⟨some (Sum.inl 12), (v1, v2, v3, none, ph),
        mkStk [] out (l.reverse ++ u) [] [] (fun _ => []) (fun _ => []) (fun _ => [])⟩ := by
  intro l
  induction l with
  | nil =>
    intro u buf
    show some _ = some _
    simp only [prog, ctrl, TM2.stepAux, setBuf, getBuf, mkStk, mkAux, List.head?_nil, List.tail_nil,
      Option.isSome_none, Bool.cond_false, List.reverse_nil, List.nil_append]
    rw [mkStk_upd0]
  | cons x l ih =>
    intro u buf
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (prog M1 M2 M3 i1 i2 i3))
        (some (⟨some (Sum.inl 11), (v1, v2, v3, buf, ph),
          mkStk (x :: l) out u [] [] (fun _ => []) (fun _ => []) (fun _ => [])⟩ : MCfg M1 M2 M3)) =
        some ⟨some (Sum.inl 11), (v1, v2, v3, some x, ph),
          mkStk l out (x :: u) [] [] (fun _ => []) (fun _ => []) (fun _ => [])⟩ := by
      show some _ = some _
      simp only [prog, ctrl, TM2.stepAux, setBuf, getBuf, mkStk, mkAux, List.head?_cons, List.tail_cons,
        Option.isSome_some, Bool.cond_true, Option.getD_some]
      rw [mkStk_upd0, mkStk_upd2]; rfl
    rw [e, ih]
    simp

private lemma loop_moveFl2 [DecidableEq (MK M1 M2 M3)] (v1 : M1.σ) (v2 : M2.σ) (v3 : M3.σ)
    (ph : Bool) (out : List Bool) :
    ∀ (u : List Bool) (acc3 : List (M3.Γ M3.k₀)) (buf : Option Bool),
      (flip bind (TM2.step (prog M1 M2 M3 i1 i2 i3)))^[u.length + 1]
        (some (⟨some (Sum.inl 12), (v1, v2, v3, buf, ph),
          mkStk [] out u [] [] (fun _ => []) (fun _ => [])
            (Function.update (fun _ => []) M3.k₀ acc3)⟩ : MCfg M1 M2 M3)) =
      some ⟨some (Sum.inr (Sum.inr (Sum.inr M3.main))), (v1, v2, v3, none, ph),
        mkStk [] out [] [] [] (fun _ => []) (fun _ => [])
          (Function.update (fun _ => []) M3.k₀ ((u.map i3).reverse ++ acc3))⟩ := by
  intro u
  induction u with
  | nil =>
    intro acc3 buf
    show some _ = some _
    simp only [prog, ctrl, TM2.stepAux, setBuf, getBuf, mkStk, mkAux, List.head?_nil, List.tail_nil,
      Option.isSome_none, Bool.cond_false, List.map_nil, List.reverse_nil, List.nil_append]
    rw [mkStk_upd2]
  | cons x u ih =>
    intro acc3 buf
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (prog M1 M2 M3 i1 i2 i3))
        (some (⟨some (Sum.inl 12), (v1, v2, v3, buf, ph),
          mkStk [] out (x :: u) [] [] (fun _ => []) (fun _ => [])
            (Function.update (fun _ => []) M3.k₀ acc3)⟩ : MCfg M1 M2 M3)) =
        some ⟨some (Sum.inl 12), (v1, v2, v3, some x, ph),
          mkStk [] out u [] [] (fun _ => []) (fun _ => [])
            (Function.update (fun _ => []) M3.k₀ (i3 x :: acc3))⟩ := by
      show some _ = some _
      simp only [prog, ctrl, TM2.stepAux, setBuf, getBuf, mkStk, mkAux, List.head?_cons, List.tail_cons,
        Option.isSome_some, Bool.cond_true, Option.getD_some]
      rw [mkStk_upd2, mkStk_updS3]
      simp only [mkStk, Function.update_self, Function.update_idem]
    rw [e, ih]
    simp

private lemma loop_drainFl [DecidableEq (MK M1 M2 M3)] (v1 : M1.σ) (v2 : M2.σ) (v3 : M3.σ)
    (ph : Bool) (out : List Bool) :
    ∀ (l : List (M3.Γ M3.k₁)) (buf : Option Bool),
      (flip bind (TM2.step (prog M1 M2 M3 i1 i2 i3)))^[l.length + 1]
        (some (⟨some (Sum.inl 14), (v1, v2, v3, buf, ph),
          mkStk [] out [] [] [] (fun _ => []) (fun _ => [])
            (Function.update (fun _ => []) M3.k₁ l)⟩ : MCfg M1 M2 M3)) =
      some ⟨none, (v1, v2, v3, none, ph),
        mkStk [] out [] [] [] (fun _ => []) (fun _ => []) (fun _ => [])⟩ := by
  intro l
  induction l with
  | nil =>
    intro buf
    show some _ = some _
    simp only [prog, ctrl, TM2.stepAux, setBuf, getBuf, mkStk, Function.update_self,
      List.head?_nil, List.tail_nil, Option.map_none, Option.isSome_none, Bool.cond_false]
    rw [mkStk_updS3, Function.update_idem, Function.update_eq_self_iff.mpr rfl]
  | cons x l ih =>
    intro buf
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (prog M1 M2 M3 i1 i2 i3))
        (some (⟨some (Sum.inl 14), (v1, v2, v3, buf, ph),
          mkStk [] out [] [] [] (fun _ => []) (fun _ => [])
            (Function.update (fun _ => []) M3.k₁ (x :: l))⟩ : MCfg M1 M2 M3)) =
        some ⟨some (Sum.inl 14), (v1, v2, v3, some false, ph),
          mkStk [] out [] [] [] (fun _ => []) (fun _ => [])
            (Function.update (fun _ => []) M3.k₁ l)⟩ := by
      show some _ = some _
      simp only [prog, ctrl, TM2.stepAux, setBuf, getBuf, mkStk, Function.update_self,
        List.head?_cons, List.tail_cons, Option.map_some, Option.isSome_some, Bool.cond_true]
      rw [mkStk_updS3, Function.update_idem]
    rw [e, ih]

private lemma finish_fl [DecidableEq (MK M1 M2 M3)] (v1 : M1.σ) (v2 : M2.σ) (v3 : M3.σ)
    (out : List Bool) (l : List (M3.Γ M3.k₁)) :
    (flip bind (TM2.step (prog M1 M2 M3 i1 i2 i3)))^[l.length + 1]
      (some (⟨some (Sum.inl 13), (v1, v2, v3, none, false),
        mkStk [] out [] [] [] (fun _ => []) (fun _ => [])
          (Function.update (fun _ => []) M3.k₁ l)⟩ : MCfg M1 M2 M3)) =
    some ⟨none, (v1, v2, v3, none, false),
      mkStk [] (true :: false :: (!l.isEmpty) :: out) [] [] []
        (fun _ => []) (fun _ => []) (fun _ => [])⟩ := by
  cases l with
  | nil =>
    show some _ = some _
    simp only [prog, ctrl, TM2.stepAux, setBuf, getBuf, mkStk, Function.update_self,
      List.head?_nil, List.tail_nil, Option.map_none, Option.isSome_none, Bool.cond_false,
      List.isEmpty_nil, Bool.not_true]
    rw [mkStk_updS3, mkStk_upd1, mkStk_upd1, mkStk_upd1]
    simp only [mkStk, mkAux, Function.update_eq_self_iff.mpr rfl]
  | cons x l =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (prog M1 M2 M3 i1 i2 i3))
        (some (⟨some (Sum.inl 13), (v1, v2, v3, none, false),
          mkStk [] out [] [] [] (fun _ => []) (fun _ => [])
            (Function.update (fun _ => []) M3.k₁ (x :: l))⟩ : MCfg M1 M2 M3)) =
        some ⟨some (Sum.inl 14), (v1, v2, v3, some false, false),
          mkStk [] (true :: false :: true :: out) [] [] [] (fun _ => []) (fun _ => [])
            (Function.update (fun _ => []) M3.k₁ l)⟩ := by
      show some _ = some _
      simp only [prog, ctrl, TM2.stepAux, setBuf, getBuf, mkStk, Function.update_self,
        List.head?_cons, List.tail_cons, Option.map_some, Option.isSome_some, Bool.cond_true]
      rw [mkStk_updS3, mkStk_upd1, mkStk_upd1, mkStk_upd1]
      simp only [mkStk, mkAux, Function.update_idem]
    rw [e, loop_drainFl]
    simp

private lemma output_eq (fl_s a_s b_s : List Bool) :
    true :: PEqualNP.MetaComplexity.encodeGate
      (PEqualNP.CircuitLowerBounds.Gate.mk
        (if fl_s.isEmpty then PEqualNP.CircuitLowerBounds.GateOp.and
          else PEqualNP.CircuitLowerBounds.GateOp.or)
        [a_s.length, b_s.length]) =
    true :: false :: (!fl_s.isEmpty) :: true ::
      ((Nat.bits a_s.length).flatMap (fun b => [true, b]) ++
        false :: true ::
          ((Nat.bits b_s.length).flatMap (fun b => [true, b]) ++ [false, false])) := by
  unfold PEqualNP.MetaComplexity.encodeGate PEqualNP.CircuitLowerBounds.encodeList
    PEqualNP.CircuitLowerBounds.encodeNat
  cases h : fl_s.isEmpty <;>
    simp [PEqualNP.MetaComplexity.encodeGateOp, List.append_assoc]

private lemma comb_run (s : List Bool)
    (o1 : List (M1.Γ M1.k₁)) (o2 : List (M2.Γ M2.k₁)) (o3 : List (M3.Γ M3.k₁))
    (s1 s2 s3 : ℕ)
    (h1 : (flip bind (TM2.step M1.m))^[s1] (some (initList M1 (s.map i1))) = some (haltList M1 o1))
    (h2 : (flip bind (TM2.step M2.m))^[s2] (some (initList M2 (s.map i2))) = some (haltList M2 o2))
    (h3 : (flip bind (TM2.step M3.m))^[s3] (some (initList M3 (s.map i3))) = some (haltList M3 o3)) :
    ∃ n,
      n ≤ 6 * s.length + s1 + s2 + s3 + 8 * o1.length + 8 * o2.length + o3.length + 13 ∧
      o1.length ≤ s.length + maxPush M1 * s1 ∧
      o2.length ≤ s.length + maxPush M2 * s2 ∧
      o3.length ≤ s.length + maxPush M3 * s3 ∧
      (flip bind (TM2.step (comb M1 M2 M3 i1 i2 i3).m))^[n]
        (some (initList (comb M1 M2 M3 i1 i2 i3) s)) =
      some (haltList (comb M1 M2 M3 i1 i2 i3)
        (true :: false :: (!o3.isEmpty) :: true ::
          ((Nat.bits o2.length).flatMap (fun b => [true, b]) ++
            false :: true ::
              ((Nat.bits o1.length).flatMap (fun b => [true, b]) ++ [false, false])))) := by
  let _ := (comb M1 M2 M3 i1 i2 i3).kDecidableEq
  have hlen1 : o1.length ≤ s.length + maxPush M1 * s1 := by
    have := run_length M1 M1.k₁ s1 _ _ h1
    rw [haltList_eq, initList_eq] at this
    simp only [Function.update_self] at this
    refine this.trans (Nat.add_le_add_right ?_ _)
    by_cases h : M1.k₁ = M1.k₀
    · rw [h, Function.update_self, List.length_map]
    · rw [Function.update_of_ne h]; simp
  have hlen2 : o2.length ≤ s.length + maxPush M2 * s2 := by
    have := run_length M2 M2.k₁ s2 _ _ h2
    rw [haltList_eq, initList_eq] at this
    simp only [Function.update_self] at this
    refine this.trans (Nat.add_le_add_right ?_ _)
    by_cases h : M2.k₁ = M2.k₀
    · rw [h, Function.update_self, List.length_map]
    · rw [Function.update_of_ne h]; simp
  have hlen3 : o3.length ≤ s.length + maxPush M3 * s3 := by
    have := run_length M3 M3.k₁ s3 _ _ h3
    rw [haltList_eq, initList_eq] at this
    simp only [Function.update_self] at this
    refine this.trans (Nat.add_le_add_right ?_ _)
    by_cases h : M3.k₁ = M3.k₀
    · rw [h, Function.update_self, List.length_map]
    · rw [Function.update_of_ne h]; simp
  have p_cB1 := loop_copyB1 i1 i2 i3 M1.initialState M2.initialState M3.initialState false [] s [] none
  simp only [List.append_nil] at p_cB1
  have p_cB2 := loop_copyB2 i1 i2 i3 M1.initialState M2.initialState M3.initialState false [] s.reverse [] [] none
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil, List.map_reverse] at p_cB2
  rw [Function.update_eq_self_iff.mpr rfl] at p_cB2
  have p_M1 := simulate (TM2.step M1.m) (TM2.step (prog M1 M2 M3 i1 i2 i3))
    (emb1 s [false, false] [] [] [] (M2.initialState, M3.initialState, none, false))
    (step1 i1 i2 i3 s [false, false] [] [] [] _) s1 _ _ h1
  rw [initList_eq, haltList_eq] at p_M1
  have p_dB := loop_drainB i1 i2 i3 M1.initialState M2.initialState M3.initialState false s [false, false] o1 [] none
  simp only [List.append_nil] at p_dB
  obtain ⟨nh1, hnh1, p_h1⟩ := loop_halve i1 i2 i3 M1.initialState M2.initialState M3.initialState false s [false, false]
    o1.length (List.replicate o1.length false) [] none (List.length_replicate)
  simp only [List.append_nil] at p_h1
  have p_e1 := loop_emit_false i1 i2 i3 M1.initialState M2.initialState M3.initialState s
    (Nat.bits o1.length).reverse [false, false] none
  simp only [List.length_reverse, List.reverse_reverse] at p_e1
  let out1 := true :: ((Nat.bits o1.length).flatMap (fun b => [true, b]) ++ [false, false])
  have p_cA1 := loop_copyA1 i1 i2 i3 M1.initialState M2.initialState M3.initialState true out1 s [] none
  simp only [List.append_nil] at p_cA1
  have p_cA2 := loop_copyA2 i1 i2 i3 M1.initialState M2.initialState M3.initialState true out1 s.reverse [] [] none
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil, List.map_reverse] at p_cA2
  rw [Function.update_eq_self_iff.mpr rfl] at p_cA2
  have p_M2 := simulate (TM2.step M2.m) (TM2.step (prog M1 M2 M3 i1 i2 i3))
    (emb2 s (false :: out1) [] [] [] M1.initialState (M3.initialState, none, true))
    (step2 i1 i2 i3 s (false :: out1) [] [] [] _ _) s2 _ _ h2
  rw [initList_eq, haltList_eq] at p_M2
  have p_dA := loop_drainA i1 i2 i3 M1.initialState M2.initialState M3.initialState true s (false :: out1) o2 [] none
  simp only [List.append_nil] at p_dA
  obtain ⟨nh2, hnh2, p_h2⟩ := loop_halve i1 i2 i3 M1.initialState M2.initialState M3.initialState true s (false :: out1)
    o2.length (List.replicate o2.length false) [] none (List.length_replicate)
  simp only [List.append_nil] at p_h2
  have p_e2 := loop_emit_true i1 i2 i3 M1.initialState M2.initialState M3.initialState s
    (Nat.bits o2.length).reverse (false :: out1) none
  simp only [List.length_reverse, List.reverse_reverse] at p_e2
  let out2 := true :: ((Nat.bits o2.length).flatMap (fun b => [true, b]) ++ false :: out1)
  have p_mF1 := loop_moveFl1 i1 i2 i3 M1.initialState M2.initialState M3.initialState false out2 s [] none
  simp only [List.append_nil] at p_mF1
  have p_mF2 := loop_moveFl2 i1 i2 i3 M1.initialState M2.initialState M3.initialState false out2 s.reverse [] none
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil, List.map_reverse] at p_mF2
  rw [Function.update_eq_self_iff.mpr rfl] at p_mF2
  have p_M3 := simulate (TM2.step M3.m) (TM2.step (prog M1 M2 M3 i1 i2 i3))
    (emb3 [] out2 [] [] [] M1.initialState M2.initialState (none, false))
    (step3 i1 i2 i3 [] out2 [] [] [] _ _ _) s3 _ _ h3
  rw [initList_eq, haltList_eq] at p_M3
  have p_fin := finish_fl i1 i2 i3 M1.initialState M2.initialState M3.initialState out2 o3
  have q1 := iter_trans p_cB1 p_cB2
  have q2 := iter_trans q1 p_M1
  have q3 := iter_trans q2 p_dB
  have q4 := iter_trans q3 p_h1
  have q5 := iter_trans q4 p_e1
  have q6 := iter_trans q5 p_cA1
  have q7 := iter_trans q6 p_cA2
  have q8 := iter_trans q7 p_M2
  have q9 := iter_trans q8 p_dA
  have q10 := iter_trans q9 p_h2
  have q11 := iter_trans q10 p_e2
  have q12 := iter_trans q11 p_mF1
  have q13 := iter_trans q12 p_mF2
  have q14 := iter_trans q13 p_M3
  have q15 := iter_trans q14 p_fin
  have hb1 : (Nat.bits o1.length).length ≤ o1.length := bits_length_le o1.length
  have hb2 : (Nat.bits o2.length).length ≤ o2.length := bits_length_le o2.length
  refine ⟨o3.length + 1 + (s3 + (s.length + 1 + (s.length + 1 +
    ((Nat.bits o2.length).length + 1 + (nh2 + (o2.length + 1 + (s2 +
    (s.length + 1 + (s.length + 1 + ((Nat.bits o1.length).length + 1 +
    (nh1 + (o1.length + 1 + (s1 + (s.length + 1 + (s.length + 1))))))))))))))),
    by omega, hlen1, hlen2, hlen3, ?_⟩
  refine (congrArg (fun c => (flip bind (TM2.step (comb M1 M2 M3 i1 i2 i3).m))^[_] (some c))
    (initList_eq (comb M1 M2 M3 i1 i2 i3) s)).trans
    (Eq.trans ?_ (congrArg some (haltList_eq (comb M1 M2 M3 i1 i2 i3) _)).symm)
  change (flip bind (TM2.step (prog M1 M2 M3 i1 i2 i3)))^[_]
      (some (⟨some (Sum.inl 0), (M1.initialState, M2.initialState, M3.initialState, none, false),
        Function.update (fun _ => []) (Sum.inl 0) s⟩ : MCfg M1 M2 M3)) =
    some (⟨none, (M1.initialState, M2.initialState, M3.initialState, none, false),
      Function.update (fun _ => []) (Sum.inl 1) (true :: false :: (!o3.isEmpty) :: out2)⟩ : MCfg M1 M2 M3)
  rw [mkStk_init, mkStk_halt]
  exact q15

end combined

private lemma build_poly (fl a b : List Bool → List Bool)
    (c3 : TM2ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) fl)
    (c2 : TM2ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) a)
    (c1 : TM2ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) b) :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => true :: PEqualNP.MetaComplexity.encodeGate
        (PEqualNP.CircuitLowerBounds.Gate.mk
          (if (fl s).isEmpty then PEqualNP.CircuitLowerBounds.GateOp.and
            else PEqualNP.CircuitLowerBounds.GateOp.or)
          [(a s).length, (b s).length])) := by
  classical
  let M1 := c1.tm
  let M2 := c2.tm
  let M3 := c3.tm
  let i1 : Bool → M1.Γ M1.k₀ := c1.inputAlphabet.invFun
  let i2 : Bool → M2.Γ M2.k₀ := c2.inputAlphabet.invFun
  let i3 : Bool → M3.Γ M3.k₀ := c3.inputAlphabet.invFun
  let T : Polynomial ℕ :=
    Polynomial.C 23 * Polynomial.X +
    Polynomial.C (8 * maxPush M1 + 1) * c1.time +
    Polynomial.C (8 * maxPush M2 + 1) * c2.time +
    Polynomial.C (maxPush M3 + 1) * c3.time +
    Polynomial.C 13
  have key : ∀ s : List Bool, ∃ n, n ≤ T.eval s.length ∧
      (flip bind (TM2.step (comb M1 M2 M3 i1 i2 i3).m))^[n]
        (some (initList (comb M1 M2 M3 i1 i2 i3) (List.map (Equiv.refl Bool).invFun s))) =
      some (haltList (comb M1 M2 M3 i1 i2 i3)
        (List.map (Equiv.refl Bool).invFun
          (true :: PEqualNP.MetaComplexity.encodeGate
            (PEqualNP.CircuitLowerBounds.Gate.mk
              (if (fl s).isEmpty then PEqualNP.CircuitLowerBounds.GateOp.and
                else PEqualNP.CircuitLowerBounds.GateOp.or)
              [(a s).length, (b s).length])))) := by
    intro s
    have r1 := c1.outputsFun s
    have r2 := c2.outputsFun s
    have r3 := c3.outputsFun s
    obtain ⟨n, hn, hl1, hl2, hl3, hrun⟩ := comb_run i1 i2 i3 s
      (List.map c1.outputAlphabet.invFun (b s))
      (List.map c2.outputAlphabet.invFun (a s))
      (List.map c3.outputAlphabet.invFun (fl s))
      r1.steps r2.steps r3.steps r1.evals_in_steps r2.evals_in_steps r3.evals_in_steps
    have hlen1 : (List.map c1.outputAlphabet.invFun (b s)).length = (b s).length := List.length_map _
    have hlen2 : (List.map c2.outputAlphabet.invFun (a s)).length = (a s).length := List.length_map _
    have hemp3 : (List.map c3.outputAlphabet.invFun (fl s)).isEmpty = (fl s).isEmpty := by
      cases fl s <;> rfl
    rw [hlen1, hlen2, hemp3] at hrun
    refine ⟨n, ?_, ?_⟩
    · have b1 : r1.steps ≤ c1.time.eval s.length := r1.steps_le_m
      have b2 : r2.steps ≤ c2.time.eval s.length := r2.steps_le_m
      have b3 : r3.steps ≤ c3.time.eval s.length := r3.steps_le_m
      have hm1 : maxPush M1 * r1.steps ≤ maxPush M1 * c1.time.eval s.length :=
        Nat.mul_le_mul_left _ b1
      have hm2 : maxPush M2 * r2.steps ≤ maxPush M2 * c2.time.eval s.length :=
        Nat.mul_le_mul_left _ b2
      have hm3 : maxPush M3 * r3.steps ≤ maxPush M3 * c3.time.eval s.length :=
        Nat.mul_le_mul_left _ b3
      simp only [T, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
      omega
    · have hm : ∀ l : List Bool, List.map (Equiv.refl Bool).invFun l = l := fun l => by simp
      have h1' : (List.map (Equiv.refl Bool).invFun s : List Bool) = s := hm s
      have h2' : (List.map (Equiv.refl Bool).invFun
          (true :: PEqualNP.MetaComplexity.encodeGate
            (PEqualNP.CircuitLowerBounds.Gate.mk
              (if (fl s).isEmpty then PEqualNP.CircuitLowerBounds.GateOp.and
                else PEqualNP.CircuitLowerBounds.GateOp.or)
              [(a s).length, (b s).length])) : List Bool) =
          true :: false :: (!(fl s).isEmpty) :: true ::
            ((Nat.bits (a s).length).flatMap (fun b => [true, b]) ++
              false :: true ::
                ((Nat.bits (b s).length).flatMap (fun b => [true, b]) ++ [false, false])) :=
        (hm _).trans (output_eq (fl s) (a s) (b s))
      exact (congrArg (fun l : List Bool =>
        (flip bind (TM2.step (comb M1 M2 M3 i1 i2 i3).m))^[n]
          (some (initList (comb M1 M2 M3 i1 i2 i3) l))) h1').trans
        (hrun.trans (congrArg (fun l : List Bool =>
          some (haltList (comb M1 M2 M3 i1 i2 i3) l)) h2'.symm))
  exact ⟨{
    tm := comb M1 M2 M3 i1 i2 i3
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := T
    outputsFun := fun s =>
      ⟨⟨Classical.choose (key s), (Classical.choose_spec (key s)).2⟩,
        (Classical.choose_spec (key s)).1⟩ }⟩

end PEqualNP.Outside.L_meta_378_aux

theorem PEqualNP.Outside.L_meta_378 :
    ∀ fl a b : List Bool → List Bool, PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) fl → PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) a → PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) b → PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (fun s => true :: PEqualNP.MetaComplexity.encodeGate (PEqualNP.CircuitLowerBounds.Gate.mk (if (fl s).isEmpty then PEqualNP.CircuitLowerBounds.GateOp.and else PEqualNP.CircuitLowerBounds.GateOp.or) [(a s).length, (b s).length])) := by
  intro fl a b ⟨cfl⟩ ⟨ca⟩ ⟨cb⟩
  exact PEqualNP.Outside.L_meta_378_aux.build_poly fl a b cfl ca cb
