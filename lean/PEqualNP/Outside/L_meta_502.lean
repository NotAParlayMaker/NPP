import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Block502
open Turing
private lemma iterate_none {σ : Type} (f : σ → Option σ) (n : ℕ) :
    (flip bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih


private lemma simulate {σ τ : Type} (f : σ → Option σ) (g : τ → Option τ) (emb : σ → τ)
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


private def pushes : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => pushes q + 1
  | .peek _ _ q => pushes q
  | .pop _ _ q => pushes q
  | .load _ q => pushes q
  | .branch _ q₁ q₂ => max (pushes q₁) (pushes q₂)
  | .goto _ => 0
  | .halt => 0

private lemma stepAux_length (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (k : K) :
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

private lemma eval_mono (p : Polynomial ℕ) {x y : ℕ} (h : x ≤ y) : p.eval x ≤ p.eval y := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.eval_add, Polynomial.eval_add]; exact add_le_add hp hq
  | monomial d c =>
    rw [Polynomial.eval_monomial, Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)


variable (M : FinTM2)
private abbrev AΓ : M.K ⊕ Fin 6 → Type
  | .inl k => M.Γ k
  | .inr _ => Bool
private abbrev AΛ := M.Λ ⊕ Fin 12
private abbrev Aσ := M.σ × Option Bool
private abbrev Cfg := TM2.Cfg (AΓ M) (AΛ M) (Aσ M)
private abbrev St := TM2.Stmt (AΓ M) (AΛ M) (Aσ M)
private abbrev S0 := (k : M.K) → List (M.Γ k)
private abbrev allnil : S0 M := fun _ => []
private def stack (x : S0 M) (i c t d a o : List Bool) : (k : M.K ⊕ Fin 6) → List (AΓ M k)
  | .inl k => x k
  | .inr 0 => i
  | .inr 1 => c
  | .inr 2 => t
  | .inr 3 => d
  | .inr 4 => a
  | .inr 5 => o

variable {M}
private lemma setX (x : S0 M) (i c t d a o : List Bool) (k : M.K) (v : List (M.Γ k)) :
    Function.update (stack M x i c t d a o) (.inl k) v = stack M (Function.update x k v) i c t d a o := by
  funext j
  rcases j with j | j
  · by_cases h : j = k
    · subst j; simp [stack]
    · simp [stack, Function.update_of_ne, h]
  · rw [Function.update_of_ne (by simp)]; fin_cases j <;> rfl

private lemma seti (x : S0 M) (i c t d a o v : List Bool) :
    Function.update (stack M x i c t d a o) (.inr 0) v = stack M x v c t d a o := by
  funext k
  rcases k with k | k
  · rw [Function.update_of_ne (by simp)]; rfl
  · fin_cases k <;> simp [stack, Function.update]
private lemma setc (x : S0 M) (i c t d a o v : List Bool) :
    Function.update (stack M x i c t d a o) (.inr 1) v = stack M x i v t d a o := by
  funext k
  rcases k with k | k
  · rw [Function.update_of_ne (by simp)]; rfl
  · fin_cases k <;> simp [stack, Function.update]
private lemma sett (x : S0 M) (i c t d a o v : List Bool) :
    Function.update (stack M x i c t d a o) (.inr 2) v = stack M x i c v d a o := by
  funext k
  rcases k with k | k
  · rw [Function.update_of_ne (by simp)]; rfl
  · fin_cases k <;> simp [stack, Function.update]
private lemma setd (x : S0 M) (i c t d a o v : List Bool) :
    Function.update (stack M x i c t d a o) (.inr 3) v = stack M x i c t v a o := by
  funext k
  rcases k with k | k
  · rw [Function.update_of_ne (by simp)]; rfl
  · fin_cases k <;> simp [stack, Function.update]
private lemma seta (x : S0 M) (i c t d a o v : List Bool) :
    Function.update (stack M x i c t d a o) (.inr 4) v = stack M x i c t d v o := by
  funext k
  rcases k with k | k
  · rw [Function.update_of_ne (by simp)]; rfl
  · fin_cases k <;> simp [stack, Function.update]
private lemma seto (x : S0 M) (i c t d a o v : List Bool) :
    Function.update (stack M x i c t d a o) (.inr 5) v = stack M x i c t d a v := by
  funext k
  rcases k with k | k
  · rw [Function.update_of_ne (by simp)]; rfl
  · fin_cases k <;> simp [stack, Function.update]

private def tr : TM2.Stmt M.Γ M.Λ M.σ → St M
  | .push k f q => .push (.inl k) (fun s => f s.1) (tr q)
  | .peek k f q => .peek (.inl k) (fun s o => (f s.1 o, s.2)) (tr q)
  | .pop k f q => .pop (.inl k) (fun s o => (f s.1 o, s.2)) (tr q)
  | .load f q => .load (fun s => (f s.1, s.2)) (tr q)
  | .branch f u v => .branch (fun s => f s.1) (tr u) (tr v)
  | .goto f => .goto (fun s => .inl (f s.1))
  | .halt => .goto (fun _ => .inr 8)

private def jump (l : AΛ M) : St M := .load (fun s => (s.1,none)) (.goto (fun _ => l))
private def finish : St M := .load (fun s => (s.1,none)) .halt
private def pop (k : Fin 6) (q : St M) : St M :=
  .pop (.inr k) (fun s b => (s.1,b)) q
private def push (k : Fin 6) (b : Aσ M → Bool) (q : St M) : St M :=
  .push (.inr k) b q
private def bit : Aσ M → Bool := fun s => s.2.getD false
private def has : Aσ M → Bool := fun s => s.2.isSome

variable (M)
private def program (enc : Bool → M.Γ M.k₀) (dec : M.Γ M.k₁ → Bool) : AΛ M → St M
  | .inl l => tr (M.m l)
  | .inr 0 => pop 0 (push 1 bit (.branch bit (jump (.inr 1)) (jump (.inr 2))))
  | .inr 1 => pop 0 (push 1 bit (.branch bit (jump (.inr 1)) (jump (.inr 0))))
  | .inr 2 => pop 0 (.branch bit (jump (.inr 3)) (jump (.inr 10)))
  | .inr 3 => pop 0 (push 2 bit (.branch bit (jump (.inr 4)) (jump (.inr 5))))
  | .inr 4 => pop 0 (push 2 bit (.branch bit (jump (.inr 4)) (jump (.inr 3))))
  | .inr 5 => pop 2 (.branch has (.push (.inl M.k₀) (fun s => enc (bit s)) (jump (.inr 5))) (jump (.inr 6)))
  | .inr 6 => pop 1 (.branch has (push 3 bit (.push (.inl M.k₀) (fun s => enc (bit s)) (jump (.inr 6)))) (jump (.inr 7)))
  | .inr 7 => pop 3 (.branch has (push 1 bit (jump (.inr 7))) (jump (.inl M.main)))
  | .inr 8 => .pop (.inl M.k₁) (fun s v => (s.1,v.map dec)) (.branch has (push 4 bit (jump (.inr 8))) (jump (.inr 9)))
  | .inr 9 => pop 4 (jump (.inr 2))
  | .inr 10 => pop 1 (.branch has (jump (.inr 10)) (push 5 (fun _ => false) (jump (.inr 11))))
  | .inr 11 => pop 4 (.branch has (push 5 bit (jump (.inr 11))) finish)

private abbrev machine (enc : Bool → M.Γ M.k₀) (dec : M.Γ M.k₁ → Bool) : FinTM2 :=
  haveI := M.kFin
  haveI := M.ΛFin
  haveI := M.σFin
  { K := M.K ⊕ Fin 6
    k₀ := .inr 0
    k₁ := .inr 5
    Γ := AΓ M
    Λ := AΛ M
    main := .inr 0
    σ := Aσ M
    initialState := (M.initialState,none)
    Γk₀Fin := inferInstanceAs (Fintype Bool)
    m := program M enc dec }

private def cfg (l : Option (AΛ M)) (x : S0 M) (i c t d a o : List Bool) : Cfg M :=
  ⟨l, (M.initialState,none), stack M x i c t d a o⟩
private abbrev aux (l : Fin 12) : S0 M → List Bool → List Bool → List Bool → List Bool → List Bool → List Bool → Cfg M := cfg M (some (.inr l))

variable {M}
private def emb (i c t d a o : List Bool) (z : M.Cfg) : Cfg M :=
  ⟨some (z.l.elim (.inr 8) Sum.inl), (z.var,none), stack M z.stk i c t d a o⟩
private lemma sim (i c t d a o : List Bool) (q : M.Stmt) (v : M.σ) (x : S0 M) :
    TM2.stepAux (tr q) (v,none) (stack M x i c t d a o) = emb i c t d a o (TM2.stepAux q v x) := by
  induction q generalizing v x with
  | push k f q ih => exact (congrArg (TM2.stepAux (tr q) (v,none)) (setX x i c t d a o k _)).trans (ih _ _)
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    have h := ih (f v (x k).head?) (Function.update x k (x k).tail)
    rw [← setX] at h
    exact h
  | load f q ih => exact ih _ _
  | branch f p q hp hq => simp only [tr, TM2.stepAux]; cases f v <;> first | exact hp _ _ | exact hq _ _
  | goto => rfl
  | halt => rfl

variable (enc : Bool → M.Γ M.k₀) (dec : M.Γ M.k₁ → Bool)
private lemma simStep (i c t d a o : List Bool) (z w : M.Cfg) (h : TM2.step M.m z = some w) :
    TM2.step (program M enc dec) (emb i c t d a o z) = some (emb i c t d a o w) := by
  obtain ⟨l,v,x⟩ := z
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step] at h
    have hw := Option.some.inj h
    subst w
    exact congrArg some (sim i c t d a o (M.m l) v x)

private abbrev iter := flip bind (TM2.step (program M enc dec))
private abbrev path (n : ℕ) (u v : Cfg M) := (iter enc dec)^[n] (some u) = some v
private lemma chain {n m : ℕ} {u v w : Cfg M} (h : path enc dec n u v) (g : path enc dec m v w) :
    path enc dec (n+m) u w := by
  change (iter enc dec)^[n+m] (some u) = some w
  rw [Nat.add_comm, Function.iterate_add_apply, h]; exact g

private abbrev input (l : List (M.Γ M.k₀)) := Function.update (allnil M) M.k₀ l
private abbrev output (l : List (M.Γ M.k₁)) := Function.update (allnil M) M.k₁ l
private lemma nilupdate (k : M.K) : Function.update (allnil M) k [] = allnil M := by
  funext j
  by_cases h : j = k
  · subst j; simp
  · rw [Function.update_of_ne h]
private lemma q0true (x : S0 M)  (i c t d a o : List Bool) :
  path enc dec 1 (aux M 0 (x) (true :: i) (c) (t) (d) (a) (o)) (aux M 1 (x) (i) (true :: c) (t) (d) (a) (o)) := by
  simp [path, iter, flip, cfg, TM2.step, TM2.stepAux, program, pop, push, jump, bit, finish, stack, seti, setc]
private lemma q0false (x : S0 M)  (i c t d a o : List Bool) :
  path enc dec 1 (aux M 0 (x) (false :: i) (c) (t) (d) (a) (o)) (aux M 2 (x) (i) (false :: c) (t) (d) (a) (o)) := by
  simp [path, iter, flip, cfg, TM2.step, TM2.stepAux, program, pop, push, jump, bit, finish, stack, seti, setc]
private lemma q1true (x : S0 M)  (i c t d a o : List Bool) :
  path enc dec 1 (aux M 1 (x) (true :: i) (c) (t) (d) (a) (o)) (aux M 1 (x) (i) (true :: c) (t) (d) (a) (o)) := by
  simp [path, iter, flip, cfg, TM2.step, TM2.stepAux, program, pop, push, jump, bit, finish, stack, seti, setc]
private lemma q1false (x : S0 M)  (i c t d a o : List Bool) :
  path enc dec 1 (aux M 1 (x) (false :: i) (c) (t) (d) (a) (o)) (aux M 0 (x) (i) (false :: c) (t) (d) (a) (o)) := by
  simp [path, iter, flip, cfg, TM2.step, TM2.stepAux, program, pop, push, jump, bit, finish, stack, seti, setc]
private lemma q3true (x : S0 M)  (i c t d a o : List Bool) :
  path enc dec 1 (aux M 3 (x) (true :: i) (c) (t) (d) (a) (o)) (aux M 4 (x) (i) (c) (true :: t) (d) (a) (o)) := by
  simp [path, iter, flip, cfg, TM2.step, TM2.stepAux, program, pop, push, jump, bit, finish, stack, seti, sett]
private lemma q3false (x : S0 M)  (i c t d a o : List Bool) :
  path enc dec 1 (aux M 3 (x) (false :: i) (c) (t) (d) (a) (o)) (aux M 5 (x) (i) (c) (false :: t) (d) (a) (o)) := by
  simp [path, iter, flip, cfg, TM2.step, TM2.stepAux, program, pop, push, jump, bit, finish, stack, seti, sett]
private lemma q4true (x : S0 M)  (i c t d a o : List Bool) :
  path enc dec 1 (aux M 4 (x) (true :: i) (c) (t) (d) (a) (o)) (aux M 4 (x) (i) (c) (true :: t) (d) (a) (o)) := by
  simp [path, iter, flip, cfg, TM2.step, TM2.stepAux, program, pop, push, jump, bit, finish, stack, seti, sett]
private lemma q4false (x : S0 M)  (i c t d a o : List Bool) :
  path enc dec 1 (aux M 4 (x) (false :: i) (c) (t) (d) (a) (o)) (aux M 3 (x) (i) (c) (false :: t) (d) (a) (o)) := by
  simp [path, iter, flip, cfg, TM2.step, TM2.stepAux, program, pop, push, jump, bit, finish, stack, seti, sett]
private lemma q2true (x : S0 M)  (i c t d a o : List Bool) :
  path enc dec 1 (aux M 2 (x) (true :: i) (c) (t) (d) (a) (o)) (aux M 3 (x) (i) (c) (t) (d) (a) (o)) := by
  simp [path, iter, flip, cfg, TM2.step, TM2.stepAux, program, pop, push, jump, bit, finish, stack, seti]
private lemma q2false (x : S0 M)  (i c t d a o : List Bool) :
  path enc dec 1 (aux M 2 (x) (false :: i) (c) (t) (d) (a) (o)) (aux M 10 (x) (i) (c) (t) (d) (a) (o)) := by
  simp [path, iter, flip, cfg, TM2.step, TM2.stepAux, program, pop, push, jump, bit, finish, stack, seti]
private lemma q5cons  (xs : List (M.Γ M.k₀)) (b : Bool) (i c t d a o : List Bool) :
  path enc dec 1 (aux M 5 (input xs) (i) (c) (b :: t) (d) (a) (o)) (aux M 5 (input (enc b :: xs)) (i) (c) (t) (d) (a) (o)) := by
  simp [path, iter, flip, cfg, input, TM2.step, TM2.stepAux, program, pop, push, jump, bit, has, finish, stack, setX, sett, Function.update_idem]
private lemma q5nil  (xs : List (M.Γ M.k₀)) (i c _t d a o : List Bool) :
  path enc dec 1 (aux M 5 (input xs) (i) (c) ([]) (d) (a) (o)) (aux M 6 (input xs) (i) (c) ([]) (d) (a) (o)) := by
  simp [path, iter, flip, cfg, input, TM2.step, TM2.stepAux, program, pop, push, jump, bit, has, finish, stack, setX, sett, Function.update_idem]
private lemma q6cons  (xs : List (M.Γ M.k₀)) (b : Bool) (i c t d a o : List Bool) :
  path enc dec 1 (aux M 6 (input xs) (i) (b :: c) (t) (d) (a) (o)) (aux M 6 (input (enc b :: xs)) (i) (c) (t) (b :: d) (a) (o)) := by
  simp [path, iter, flip, cfg, input, TM2.step, TM2.stepAux, program, pop, push, jump, bit, has, finish, stack, setX, setc, setd, Function.update_idem]
private lemma q6nil  (xs : List (M.Γ M.k₀)) (i _c t d a o : List Bool) :
  path enc dec 1 (aux M 6 (input xs) (i) ([]) (t) (d) (a) (o)) (aux M 7 (input xs) (i) ([]) (t) (d) (a) (o)) := by
  simp [path, iter, flip, cfg, input, TM2.step, TM2.stepAux, program, pop, push, jump, bit, has, finish, stack, setX, setc, setd, Function.update_idem]
private lemma q7cons (x : S0 M) (b : Bool) (i c t d a o : List Bool) :
  path enc dec 1 (aux M 7 (x) (i) (c) (t) (b :: d) (a) (o)) (aux M 7 (x) (i) (b :: c) (t) (d) (a) (o)) := by
  simp [path, iter, flip, cfg, TM2.step, TM2.stepAux, program, pop, push, jump, bit, has, finish, stack, setc, setd]
private lemma q7nil (x : S0 M)  (i c t _d a o : List Bool) :
  path enc dec 1 (aux M 7 (x) (i) (c) (t) ([]) (a) (o)) (cfg M (some (.inl M.main)) (x) (i) (c) (t) ([]) (a) (o)) := by
  simp [path, iter, flip, cfg, TM2.step, TM2.stepAux, program, pop, push, jump, bit, has, finish, stack, setc, setd]
private lemma q8cons  (xs : List (M.Γ M.k₁)) (b : M.Γ M.k₁) (i c t d a o : List Bool) :
  path enc dec 1 (aux M 8 (output (b :: xs)) (i) (c) (t) (d) (a) (o)) (aux M 8 (output xs) (i) (c) (t) (d) (dec b :: a) (o)) := by
  simp [path, iter, flip, cfg, output, TM2.step, TM2.stepAux, program, pop, push, jump, bit, has, finish, stack, setX, seta, Function.update_idem]
private lemma q8nil   (i c t d a o : List Bool) :
  path enc dec 1 (aux M 8 (output ([] : List (M.Γ M.k₁))) (i) (c) (t) (d) (a) (o)) (aux M 9 (allnil M) (i) (c) (t) (d) (a) (o)) := by
  simp [path, iter, flip, cfg, output, TM2.step, TM2.stepAux, program, pop, push, jump, bit, has, finish, stack, setX, seta]
private lemma q9 (x : S0 M) (b : Bool) (i c t d a o : List Bool) :
  path enc dec 1 (aux M 9 (x) (i) (c) (t) (d) (b :: a) (o)) (aux M 2 (x) (i) (c) (t) (d) (a) (o)) := by
  simp [path, iter, flip, cfg, TM2.step, TM2.stepAux, program, pop, push, jump, bit, finish, stack, seta]
private lemma q10cons (x : S0 M) (b : Bool) (i c t d a o : List Bool) :
  path enc dec 1 (aux M 10 (x) (i) (b :: c) (t) (d) (a) (o)) (aux M 10 (x) (i) (c) (t) (d) (a) (o)) := by
  simp [path, iter, flip, cfg, TM2.step, TM2.stepAux, program, pop, push, jump, bit, has, finish, stack, setc, seto]
private lemma q10nil (x : S0 M)  (i _c t d a o : List Bool) :
  path enc dec 1 (aux M 10 (x) (i) ([]) (t) (d) (a) (o)) (aux M 11 (x) (i) ([]) (t) (d) (a) (false :: o)) := by
  simp [path, iter, flip, cfg, TM2.step, TM2.stepAux, program, pop, push, jump, bit, has, finish, stack, setc, seto]
private lemma q11cons (x : S0 M) (b : Bool) (i c t d a o : List Bool) :
  path enc dec 1 (aux M 11 (x) (i) (c) (t) (d) (b :: a) (o)) (aux M 11 (x) (i) (c) (t) (d) (a) (b :: o)) := by
  simp [path, iter, flip, cfg, TM2.step, TM2.stepAux, program, pop, push, jump, bit, has, finish, stack, seta, seto]
private lemma q11nil (x : S0 M)  (i c t d _a o : List Bool) :
  path enc dec 1 (aux M 11 (x) (i) (c) (t) (d) ([]) (o)) (cfg M none (x) (i) (c) (t) (d) ([]) (o)) := by
  simp [path, iter, flip, cfg, TM2.step, TM2.stepAux, program, pop, push, jump, bit, has, finish, stack, seta, seto]

private def unary (n : ℕ) := List.replicate n true ++ [false]
private abbrev tuple := PEqualNP.CircuitLowerBounds.encodeList unary
private abbrev payload (z : List (List ℕ)) := z.flatMap (fun t => true :: tuple t)
private abbrev many := PEqualNP.CircuitLowerBounds.encodeList tuple
private lemma tuple_nil : tuple [] = [false] := rfl
private lemma tuple_cons (n : ℕ) (ns : List ℕ) : tuple (n :: ns) = true :: (unary n ++ tuple ns) := by
  simp [PEqualNP.CircuitLowerBounds.encodeList, List.append_assoc]
private lemma many_payload (ts : List (List ℕ)) : many ts = payload ts ++ [false] := rfl
private lemma many_nil : many [] = [false] := rfl
private lemma many_cons (t : List ℕ) (ts : List (List ℕ)) : many (t :: ts) = true :: (tuple t ++ many ts) := by
  simp [PEqualNP.CircuitLowerBounds.encodeList, List.append_assoc]
private lemma unary_zero : unary 0 = [false] := rfl
private lemma unary_succ (n : ℕ) : unary (n+1) = true :: unary n := by simp [unary,List.replicate_succ]

private lemma unary1 (x : S0 M) (n : ℕ) (i c t d a o : List Bool) :
    path enc dec (unary n).length
      (aux M 1 (x) (unary n ++ i) (c) (t) (d) (a) (o))
      (aux M 0 (x) (i) ((unary n).reverse ++ c) (t) (d) (a) (o)) := by
  induction n generalizing c with
  | zero => simpa [unary_zero] using q1false enc dec x i c t d a o
  | succ n ih =>
    have u := q1true enc dec x (unary n ++ i) (c) (t) (d) (a) (o)
    have v := ih (true :: c)
    simpa [unary_succ, List.append_assoc, Nat.add_comm] using chain enc dec u v

private lemma parse0 (x : S0 M) (ns : List ℕ) (i c t d a o : List Bool) :
    path enc dec (tuple ns).length
      (aux M 0 (x) (tuple ns ++ i) (c) (t) (d) (a) (o))
      (aux M 2 (x) (i) ((tuple ns).reverse ++ c) (t) (d) (a) (o)) := by
  induction ns generalizing c with
  | nil => simpa [tuple_nil] using q0false enc dec x i c t d a o
  | cons n ns ih =>
    have u := q0true enc dec x (unary n ++ tuple ns ++ i) (c) (t) (d) (a) (o)
    have v := unary1 enc dec x n (tuple ns ++ i) (true :: c) (t) (d) (a) (o)
    have w := ih ((unary n).reverse ++ true :: c)
    simp only [List.append_assoc] at u
    simpa [tuple_cons, List.reverse_append, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      chain enc dec u (chain enc dec v w)

private lemma unary4 (x : S0 M) (n : ℕ) (i c t d a o : List Bool) :
    path enc dec (unary n).length
      (aux M 4 (x) (unary n ++ i) (c) (t) (d) (a) (o))
      (aux M 3 (x) (i) (c) ((unary n).reverse ++ t) (d) (a) (o)) := by
  induction n generalizing t with
  | zero => simpa [unary_zero] using q4false enc dec x i c t d a o
  | succ n ih =>
    have u := q4true enc dec x (unary n ++ i) (c) (t) (d) (a) (o)
    have v := ih (true :: t)
    simpa [unary_succ, List.append_assoc, Nat.add_comm] using chain enc dec u v

private lemma parse3 (x : S0 M) (ns : List ℕ) (i c t d a o : List Bool) :
    path enc dec (tuple ns).length
      (aux M 3 (x) (tuple ns ++ i) (c) (t) (d) (a) (o))
      (aux M 5 (x) (i) (c) ((tuple ns).reverse ++ t) (d) (a) (o)) := by
  induction ns generalizing t with
  | nil => simpa [tuple_nil] using q3false enc dec x i c t d a o
  | cons n ns ih =>
    have u := q3true enc dec x (unary n ++ tuple ns ++ i) (c) (t) (d) (a) (o)
    have v := unary4 enc dec x n (tuple ns ++ i) (c) (true :: t) (d) (a) (o)
    have w := ih ((unary n).reverse ++ true :: t)
    simp only [List.append_assoc] at u
    simpa [tuple_cons, List.reverse_append, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      chain enc dec u (chain enc dec v w)

private lemma loop5 (xs : List (M.Γ M.k₀)) (i c t d a o : List Bool) :
    path enc dec (t.length + 1)
      (aux M 5 (input xs) (i) (c) (t) (d) (a) (o))
      (aux M 6 (input (t.reverse.map enc ++ xs)) (i) (c) ([]) (d) (a) (o)) := by
  induction t generalizing xs with
  | nil => simpa using q5nil enc dec xs (i) (c) ([]) (d) (a) (o)
  | cons b t ih =>
    have u := q5cons enc dec xs b (i) (c) (t) (d) (a) (o)
    have v := ih (enc b :: xs)
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using chain enc dec u v

private lemma loop6 (xs : List (M.Γ M.k₀)) (i c t d a o : List Bool) :
    path enc dec (c.length + 1)
      (aux M 6 (input xs) (i) (c) (t) (d) (a) (o))
      (aux M 7 (input (c.reverse.map enc ++ xs)) (i) ([]) (t) (c.reverse ++ d) (a) (o)) := by
  induction c generalizing xs d with
  | nil => simpa using q6nil enc dec xs (i) ([]) (t) (d) (a) (o)
  | cons b c ih =>
    have u := q6cons enc dec xs b (i) (c) (t) (d) (a) (o)
    have v := ih (enc b :: xs) (b :: d)
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using chain enc dec u v

private lemma loop7 (x : S0 M) (i c t d a o : List Bool) :
    path enc dec (d.length + 1)
      (aux M 7 (x) (i) (c) (t) (d) (a) (o))
      (cfg M (some (.inl M.main)) (x) (i) (d.reverse ++ c) (t) ([]) (a) (o)) := by
  induction d generalizing c with
  | nil => simpa using q7nil enc dec x (i) (c) (t) ([]) (a) (o)
  | cons b d ih =>
    have u := q7cons enc dec x b (i) (c) (t) (d) (a) (o)
    have v := ih (b :: c)
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using chain enc dec u v

private lemma loop8 (xs : List (M.Γ M.k₁)) (i c t d a o : List Bool) :
    path enc dec (xs.length + 1)
      (aux M 8 (output xs) (i) (c) (t) (d) (a) (o))
      (aux M 9 (allnil M) (i) (c) (t) (d) (xs.reverse.map dec ++ a) (o)) := by
  induction xs generalizing a with
  | nil => simpa using q8nil enc dec  (i) (c) (t) (d) (a) (o)
  | cons b xs ih =>
    have u := q8cons enc dec xs b (i) (c) (t) (d) (a) (o)
    have v := ih (dec b :: a)
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using chain enc dec u v

private lemma loop10 (x : S0 M) (i c t d a o : List Bool) :
    path enc dec (c.length + 1)
      (aux M 10 (x) (i) (c) (t) (d) (a) (o))
      (aux M 11 (x) (i) ([]) (t) (d) (a) (false :: o)) := by
  induction c with
  | nil => simpa using q10nil enc dec x (i) ([]) (t) (d) (a) (o)
  | cons b c ih =>
    have u := q10cons enc dec x b (i) (c) (t) (d) (a) (o)
    have v := ih
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using chain enc dec u v

private lemma loop11 (x : S0 M) (i c t d a o : List Bool) :
    path enc dec (a.length + 1)
      (aux M 11 (x) (i) (c) (t) (d) (a) (o))
      (cfg M none (x) (i) (c) (t) (d) ([]) (a.reverse ++ o)) := by
  induction a generalizing o with
  | nil => simpa using q11nil enc dec x (i) (c) (t) (d) ([]) (o)
  | cons b a ih =>
    have u := q11cons enc dec x b (i) (c) (t) (d) (a) (o)
    have v := ih (b :: o)
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using chain enc dec u v
private abbrev inPair (p : List ℕ × List ℕ) := tuple p.1 ++ tuple p.2
private abbrev inList (p : List ℕ × List (List ℕ)) := tuple p.1 ++ many p.2
private abbrev cert (f : List ℕ × List ℕ → List (List ℕ)) := TM2ComputableInPolyTime inPair many f
private abbrev incoming {f} (c : cert f) : Bool → c.tm.Γ c.tm.k₀ := c.inputAlphabet.invFun
private abbrev outgoing {f} (c : cert f) : c.tm.Γ c.tm.k₁ → Bool := c.outputAlphabet

private lemma callMachine {f} (c : cert f) (p : List ℕ × List ℕ) (i a : List Bool) :
    ∃ s, s ≤ c.time.eval (inPair p).length ∧
      (many (f p)).length ≤ (inPair p).length + maxPush c.tm * s ∧
      path (incoming c) (outgoing c) s
        (cfg c.tm (some (.inl c.tm.main)) (input ((inPair p).map (incoming c))) i (tuple p.1).reverse [] [] a [])
        (aux c.tm 8 (output ((many (f p)).map c.outputAlphabet.invFun)) i (tuple p.1).reverse [] [] a []) := by
  obtain ⟨⟨s,he⟩,hs⟩ := c.outputsFun p
  have h : (flip bind (TM2.step c.tm.m))^[s]
      (some (initList c.tm ((inPair p).map (incoming c)))) =
        some (haltList c.tm ((many (f p)).map c.outputAlphabet.invFun)) := he
  have simh := simulate (TM2.step c.tm.m) (TM2.step (program c.tm (incoming c) (outgoing c)))
    (emb i (tuple p.1).reverse [] [] a []) (simStep (incoming c) (outgoing c) _ _ _ _ _ _)
    _ _ _ h
  have len := run_length c.tm c.tm.k₁ _ _ _ h
  rw [initList_eq, haltList_eq] at simh len
  refine ⟨s, hs, ?_, simh⟩
  simp only [Function.update_self, List.length_map] at len
  have hi : ((input ((inPair p).map (incoming c))) c.tm.k₁).length ≤ (inPair p).length := by
    by_cases he : c.tm.k₁ = c.tm.k₀
    · rw [he]; simp [input]
    · simp [input, Function.update_of_ne he]
  exact len.trans (Nat.add_le_add_right hi _)

private noncomputable abbrev outB {f} (c : cert f) (N : ℕ) := N + maxPush c.tm * c.time.eval N
private noncomputable abbrev stepB {f} (c : cert f) (N : ℕ) := 4*N + c.time.eval N + outB c N + 8

private lemma oneBlock {f} (c : cert f) (z t : List ℕ) (ts : List (List ℕ)) (a : List Bool) (N : ℕ)
    (hN : (tuple z).length + (tuple t).length ≤ N) :
    ∃ s, s ≤ stepB c N ∧ (payload (f (z,t))).length ≤ outB c N ∧
      path (incoming c) (outgoing c) s
        (aux c.tm 2 (allnil c.tm) (many (t::ts)) (tuple z).reverse [] [] a [])
        (aux c.tm 2 (allnil c.tm) (many ts) (tuple z).reverse [] [] ((payload (f (z,t))).reverse ++ a) []) := by
  let e := incoming c
  let g := outgoing c
  let x := allnil c.tm
  let i := many ts
  let v := (tuple z).reverse
  obtain ⟨s,hs,hl,hc⟩ := callMachine c (z,t) i a
  have h1 := q2true e g x (tuple t ++ i) v [] [] a []
  have h2 := parse3 e g x t i v [] [] a []
  have h3 := loop5 e g [] i v (tuple t).reverse [] a []
  have h4 := loop6 e g ((tuple t).map e) i v [] [] a []
  have h5 := loop7 e g (input ((inPair (z,t)).map e)) i [] [] (tuple z) a []
  have h7 := loop8 e g ((many (f (z,t))).map c.outputAlphabet.invFun) i v [] [] a []
  have h8 := q9 e g x false i v [] [] ((payload (f (z,t))).reverse ++ a) []
  simp only [List.append_nil] at h2 h3 h4 h5
  simp only [nilupdate, List.length_reverse, List.reverse_reverse] at h3
  simp only [v, List.reverse_reverse, List.length_reverse] at h4
  have hfg : ((many (f (z,t))).map c.outputAlphabet.invFun).reverse.map g = (many (f (z,t))).reverse := by
    rw [List.map_reverse, List.map_map]
    simp [g, outgoing, Function.comp_def]
  simp only [hfg, List.length_map] at h7
  have outrev : (many (f (z,t))).reverse = false :: (payload (f (z,t))).reverse := by
    rw [many_payload, List.reverse_append]; rfl
  rw [outrev, List.cons_append] at h7
  simp only [inPair, List.map_append] at h5 hc
  have h := chain e g h1 (chain e g h2 (chain e g h3 (chain e g h4
    (chain e g h5 (chain e g hc (chain e g h7 h8))))))
  have hN' : (inPair (z,t)).length ≤ N := by simpa [inPair] using hN
  have hP := hs.trans (eval_mono c.time hN')
  have ho : (many (f (z,t))).length ≤ outB c N :=
    hl.trans (Nat.add_le_add hN' (Nat.mul_le_mul_left _ hP))
  refine ⟨_, ?_, ?_, by simpa only [many_cons] using h⟩
  · exact show _ ≤ stepB c N from (by unfold stepB; omega)
  · rw [many_payload, List.length_append] at ho
    omega


private lemma walk {f} (c : cert f) (z : List ℕ) (ts : List (List ℕ)) (a : List Bool) (N : ℕ)
    (hN : (tuple z).length + (many ts).length ≤ N) :
    ∃ s, s ≤ ts.length * stepB c N ∧ (payload (ts.flatMap (fun t => f (z,t)))).length ≤ ts.length * outB c N ∧
      path (incoming c) (outgoing c) s
        (aux c.tm 2 (allnil c.tm) (many ts) (tuple z).reverse [] [] a [])
        (aux c.tm 2 (allnil c.tm) [false] (tuple z).reverse [] [] ((payload (ts.flatMap (fun t => f (z,t)))).reverse ++ a) []) := by
  induction ts generalizing a with
  | nil => exact ⟨0, by simp, by simp [payload], rfl⟩
  | cons t ts ih =>
    rw [many_cons, List.length_cons, List.length_append] at hN
    obtain ⟨k,hk,hb,h⟩ := oneBlock c z t ts a N (by omega)
    obtain ⟨j,hj,hd,g⟩ := ih ((payload (f (z,t))).reverse ++ a) (by omega)
    refine ⟨k+j, ?_, ?_, ?_⟩
    · rw [List.length_cons, Nat.succ_mul]; omega
    · simp only [List.flatMap_cons, payload, List.flatMap_append, List.length_append, List.length_cons, Nat.succ_mul]
      exact (Nat.add_le_add hb hd).trans (by omega)
    · simpa [payload,List.reverse_append,List.append_assoc] using chain (incoming c) (outgoing c) h g
private lemma count_le (ts : List (List ℕ)) : ts.length ≤ (many ts).length := by
  induction ts with
  | nil => simp
  | cons t ts ih => rw [many_cons, List.length_cons, List.length_cons, List.length_append]; omega

private lemma inStack (l : List Bool) :
    stack M (allnil M) l [] [] [] [] [] = (Function.update (fun _ => []) (.inr 0) l : (k : M.K ⊕ Fin 6) → List (AΓ M k)) := by
  funext k
  rcases k with k | k
  · rw [Function.update_of_ne (by simp)]; rfl
  · fin_cases k <;> simp [Function.update, stack]

private lemma outStack (l : List Bool) :
    stack M (allnil M) [] [] [] [] [] l = (Function.update (fun _ => []) (.inr 5) l : (k : M.K ⊕ Fin 6) → List (AΓ M k)) := by
  funext k
  rcases k with k | k
  · rw [Function.update_of_ne (by simp)]; rfl
  · fin_cases k <;> simp [Function.update, stack]

private noncomputable def budget {f} (c : cert f) : Polynomial ℕ :=
  let X := Polynomial.X
  let O := X + Polynomial.C (maxPush c.tm) * c.time
  let B := 4 * X + c.time + O + 8
  2 * X + X * B + X * O + 3

private lemma fullRun {f} (c : cert f) (z : List ℕ) (ts : List (List ℕ)) :
    ∃ n, n ≤ (budget c).eval (inList (z,ts)).length ∧
      (iter (incoming c) (outgoing c))^[n] (some (initList (machine c.tm (incoming c) (outgoing c)) (inList (z,ts)))) =
        some (haltList (machine c.tm (incoming c) (outgoing c)) (many (ts.flatMap (fun t => f (z,t))))) := by
  let N := (inList (z,ts)).length
  have hN : (tuple z).length + (many ts).length = N := List.length_append.symm
  have hc : ts.length ≤ N := (count_le ts).trans (by omega)
  let e := incoming c
  let g := outgoing c
  let x := allnil c.tm
  let w := payload (ts.flatMap (fun t => f (z,t)))
  let v := (tuple z).reverse
  obtain ⟨s,hs,hw,h⟩ := walk c z ts [] N hN.le
  have h0 := parse0 e g x z (many ts) [] [] [] [] []
  have he := q2false e g x [] v [] [] w.reverse []
  have hg := loop10 e g x [] v [] [] w.reverse []
  have hh := loop11 e g x [] [] [] [] w.reverse [false]
  simp only [List.append_nil] at h h0
  simp only [v, List.length_reverse] at hg
  simp only [List.length_reverse, List.reverse_reverse] at hh
  have run := chain e g h0 (chain e g h (chain e g he (chain e g hg hh)))
  have hs' := hs.trans (Nat.mul_le_mul_right (stepB c N) hc)
  have hw' : w.length ≤ N * outB c N := hw.trans (Nat.mul_le_mul_right _ hc)
  refine ⟨(tuple z).length + (s + (1 + ((tuple z).length + 1 + (w.length + 1)))), ?_, ?_⟩
  · change _ ≤ (budget c).eval N
    have hb : (budget c).eval N = 2*N + N*stepB c N + N*outB c N + 3 := by
      simp [budget, stepB, outB]
    rw [hb]
    omega
  · rw [initList_eq, haltList_eq]
    change (iter e g)^[_] (some _) = some _
    simpa only [path, cfg, x, inList, w, inStack, outStack, many_payload] using run

private lemma liftBlock (f : List ℕ × List ℕ → List (List ℕ)) (c : cert f) :
    PEqualNP.Library.ComputableInPolyTime inList many
      (fun p : List ℕ × List (List ℕ) => p.2.flatMap (fun t => f (p.1,t))) := by
  let m := machine c.tm (incoming c) (outgoing c)
  refine ⟨{ tm := m
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := Equiv.refl Bool
            time := budget c
            outputsFun := ?_ }⟩
  intro p
  obtain ⟨z,ts⟩ := p
  let h := fullRun c z ts
  refine { steps := Classical.choose h
           steps_le_m := (Classical.choose_spec h).1
           evals_in_steps := ?_ }
  have idmap (l : List Bool) : l.map (Equiv.refl Bool).invFun = l := by simp
  change (iter (incoming c) (outgoing c))^[_] (some (initList m (_ : List Bool))) = some (haltList m (_ : List Bool))
  rw [idmap, idmap]
  exact (Classical.choose_spec h).2

end PEqualNP.Outside.Block502

theorem PEqualNP.Outside.L_meta_502 : ∀ f : List ℕ × List ℕ → List (List ℕ), PEqualNP.Library.ComputableInPolyTime (fun p : List ℕ × List ℕ => PEqualNP.CircuitLowerBounds.encodeList (fun a : ℕ => List.replicate a true ++ [false]) p.1 ++ PEqualNP.CircuitLowerBounds.encodeList (fun a : ℕ => List.replicate a true ++ [false]) p.2) (PEqualNP.CircuitLowerBounds.encodeList (PEqualNP.CircuitLowerBounds.encodeList (fun a : ℕ => List.replicate a true ++ [false]))) f → PEqualNP.Library.ComputableInPolyTime (fun p : List ℕ × List (List ℕ) => PEqualNP.CircuitLowerBounds.encodeList (fun a : ℕ => List.replicate a true ++ [false]) p.1 ++ (PEqualNP.CircuitLowerBounds.encodeList (PEqualNP.CircuitLowerBounds.encodeList (fun a : ℕ => List.replicate a true ++ [false]))) p.2) (PEqualNP.CircuitLowerBounds.encodeList (PEqualNP.CircuitLowerBounds.encodeList (fun a : ℕ => List.replicate a true ++ [false]))) (fun p : List ℕ × List (List ℕ) => p.2.flatMap (fun t : List ℕ => f (p.1, t))) := by
  rintro f ⟨c⟩
  exact PEqualNP.Outside.Block502.liftBlock f c
