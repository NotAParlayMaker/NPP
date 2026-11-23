import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside

open Turing PEqualNP.Library

private theorem iterate_none {α : Type} (f : α → Option α) (n : ℕ) :
    (flip bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact ih

private theorem iter_trans {α : Type} (f : α → α) {m n : ℕ} {a b c : α}
    (h1 : f^[m] a = b) (h2 : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, h1, h2]

private theorem iter_step {α : Type} (f : α → Option α) {n : ℕ} {a b c : α}
    (h1 : f a = some b) (h2 : (flip bind f)^[n] (some b) = some c) :
    (flip bind f)^[n + 1] (some a) = some c := by
  rw [Function.iterate_succ_apply]
  change (flip bind f)^[n] (f a) = some c
  rw [h1]
  exact h2

private theorem simulate {α β : Type} (f : α → Option α) (g : β → Option β) (emb : α → β)
    (h : ∀ c c', f c = some c' → g (emb c) = some (emb c')) :
    ∀ (n : ℕ) (a b : α), (flip bind f)^[n] (some a) = some b →
      (flip bind g)^[n] (some (emb a)) = some (emb b) := by
  intro n
  induction n with
  | zero =>
    intro a b hab
    have : a = b := Option.some.inj hab
    rw [this]
    rfl
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

private def stmtPushes {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type} :
    TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => stmtPushes q + 1
  | .peek _ _ q => stmtPushes q
  | .pop _ _ q => stmtPushes q
  | .load _ q => stmtPushes q
  | .branch _ q₁ q₂ => max (stmtPushes q₁) (stmtPushes q₂)
  | .goto _ => 0
  | .halt => 0

private theorem stepAux_length {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (k : K) :
    ((TM2.stepAux q v S).stk k).length ≤ (S k).length + stmtPushes q := by
  induction q generalizing v S with
  | push k' f q ih =>
    simp only [TM2.stepAux, stmtPushes]
    refine (ih _ _).trans ?_
    by_cases h : k = k'
    · subst h
      rw [Function.update_self, List.length_cons]
      omega
    · rw [Function.update_of_ne h]
      omega
  | peek k' f q ih => exact ih _ _
  | pop k' f q ih =>
    simp only [TM2.stepAux, stmtPushes]
    refine (ih _ _).trans ?_
    by_cases h : k = k'
    · subst h
      rw [Function.update_self, List.length_tail]
      omega
    · rw [Function.update_of_ne h]
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [TM2.stepAux, stmtPushes]
    cases f v
    · exact (ih₂ v S).trans (by have := le_max_right (stmtPushes q₁) (stmtPushes q₂); omega)
    · exact (ih₁ v S).trans (by have := le_max_left (stmtPushes q₁) (stmtPushes q₂); omega)
  | goto f => simp [TM2.stepAux, stmtPushes]
  | halt => simp [TM2.stepAux, stmtPushes]

private noncomputable def maxPush (tm : FinTM2) : ℕ :=
  (@Finset.univ tm.Λ tm.ΛFin).sup fun l => stmtPushes (tm.m l)

private theorem step_length (tm : FinTM2) (c c' : TM2.Cfg tm.Γ tm.Λ tm.σ)
    (h : TM2.step tm.m c = some c') (k : tm.K) :
    (c'.stk k).length ≤ (c.stk k).length + maxPush tm := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    refine (stepAux_length _ _ _ _).trans ?_
    have : stmtPushes (tm.m l) ≤ maxPush tm :=
      Finset.le_sup (f := fun l => stmtPushes (tm.m l)) (@Finset.mem_univ tm.Λ tm.ΛFin l)
    simpa using this

private theorem run_length (tm : FinTM2) (k : tm.K) :
    ∀ (n : ℕ) (a b : TM2.Cfg tm.Γ tm.Λ tm.σ),
      (flip bind (TM2.step tm.m))^[n] (some a) = some b →
      (b.stk k).length ≤ (a.stk k).length + maxPush tm * n := by
  intro n
  induction n with
  | zero =>
    intro a b hab
    have : a = b := Option.some.inj hab
    rw [this]
    simp
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
      rw [Nat.mul_succ]
      omega

private theorem initList_eq (tm : FinTM2) (s : List (tm.Γ tm.k₀)) :
    initList tm s =
      (⟨some tm.main, tm.initialState, Function.update (fun _ => []) tm.k₀ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ) := by
  unfold initList
  congr 1
  funext k
  by_cases h : k = tm.k₀
  · subst h
    simp
  · simp [h]

private theorem haltList_eq (tm : FinTM2) (s : List (tm.Γ tm.k₁)) :
    haltList tm s =
      (⟨none, tm.initialState, Function.update (fun _ => []) tm.k₁ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ) := by
  unfold haltList
  congr 1
  funext k
  by_cases h : k = tm.k₁
  · subst h
    simp
  · simp [h]

private theorem eval_mono (p : Polynomial ℕ) {x y : ℕ} (h : x ≤ y) : p.eval x ≤ p.eval y := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.eval_add, Polynomial.eval_add]
    exact add_le_add hp hq
  | monomial d c =>
    rw [Polynomial.eval_monomial, Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)

private theorem output_length_le (f : List Bool → List Bool)
    (c : TM2ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f)
    (x : List Bool) :
    (f x).length ≤ x.length + maxPush c.tm * (c.outputsFun x).steps := by
  have h : (flip bind (TM2.step c.tm.m))^[(c.outputsFun x).steps]
      (some (initList c.tm (x.map c.inputAlphabet.invFun))) =
      some (haltList c.tm ((f x).map c.outputAlphabet.invFun)) :=
    (c.outputsFun x).evals_in_steps
  generalize (c.outputsFun x).steps = st at h ⊢
  rw [initList_eq, haltList_eq] at h
  have hlen := run_length c.tm c.tm.k₁ st _ _ h
  simp only [Function.update_self, List.length_map] at hlen
  have hin : ((Function.update (fun _ => [] : ∀ k, List (c.tm.Γ k)) c.tm.k₀
      (x.map c.inputAlphabet.invFun)) c.tm.k₁).length ≤ x.length := by
    by_cases hk : c.tm.k₁ = c.tm.k₀
    · rw [hk, Function.update_self, List.length_map]
    · rw [Function.update_of_ne hk]
      simp
  omega

private def findFrom (q : ℕ → Bool) (i : ℕ) : ℕ → ℕ
  | 0 => i
  | r + 1 => if q i then i else findFrom q (i + 1) r

private theorem findFrom_eq_findIdx_map (q : ℕ → Bool) (r : ℕ) :
    ∀ i : ℕ, ((List.range r).map (i + ·)).findIdx q + i = findFrom q i r := by
  induction r with
  | zero =>
    intro i
    simp [findFrom]
  | succ r ih =>
    intro i
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    have hmap : ((i + ·) ∘ Nat.succ) = (fun j => (i + 1) + j) := by
      funext j
      simp [Function.comp]
      omega
    rw [hmap, List.findIdx_cons, Nat.add_zero]
    simp only [findFrom]
    cases hq : q i with
    | true => simp
    | false =>
      have hih := ih (i + 1)
      simp only [Bool.false_eq_true, ↓reduceIte]
      omega

private theorem findFrom_zero (q : ℕ → Bool) (n : ℕ) :
    (List.range n).findIdx q = findFrom q 0 n := by
  have h := findFrom_eq_findIdx_map q n 0
  have hmap : (List.range n).map (0 + ·) = List.range n := by
    simp
  rw [hmap, Nat.add_zero] at h
  exact h

private abbrev MK (Mc Ma Mp : FinTM2) : Type := Mc.K ⊕ Ma.K ⊕ Mp.K ⊕ Fin 6

private abbrev MΓ (Mc Ma Mp : FinTM2) : MK Mc Ma Mp → Type
  | Sum.inl k => Mc.Γ k
  | Sum.inr (Sum.inl k) => Ma.Γ k
  | Sum.inr (Sum.inr (Sum.inl k)) => Mp.Γ k
  | Sum.inr (Sum.inr (Sum.inr _)) => Bool

private abbrev MΛ (Mc Ma Mp : FinTM2) : Type := Mc.Λ ⊕ Ma.Λ ⊕ Mp.Λ ⊕ Fin 15

private abbrev Mσ (Mc Ma Mp : FinTM2) : Type := Mc.σ × Ma.σ × Mp.σ × Option Bool

private abbrev MCfg (Mc Ma Mp : FinTM2) : Type :=
  TM2.Cfg (MΓ Mc Ma Mp) (MΛ Mc Ma Mp) (Mσ Mc Ma Mp)

private abbrev kI (Mc Ma Mp : FinTM2) : MK Mc Ma Mp := Sum.inr (Sum.inr (Sum.inr ⟨0, by decide⟩))
private abbrev kO (Mc Ma Mp : FinTM2) : MK Mc Ma Mp := Sum.inr (Sum.inr (Sum.inr ⟨1, by decide⟩))
private abbrev kR (Mc Ma Mp : FinTM2) : MK Mc Ma Mp := Sum.inr (Sum.inr (Sum.inr ⟨2, by decide⟩))
private abbrev kA (Mc Ma Mp : FinTM2) : MK Mc Ma Mp := Sum.inr (Sum.inr (Sum.inr ⟨3, by decide⟩))
private abbrev kB (Mc Ma Mp : FinTM2) : MK Mc Ma Mp := Sum.inr (Sum.inr (Sum.inr ⟨4, by decide⟩))
private abbrev kC (Mc Ma Mp : FinTM2) : MK Mc Ma Mp := Sum.inr (Sum.inr (Sum.inr ⟨5, by decide⟩))

private abbrev lbl (Mc Ma Mp : FinTM2) (n : Fin 15) : MΛ Mc Ma Mp :=
  Sum.inr (Sum.inr (Sum.inr n))

private def trC {Mc Ma Mp : FinTM2} :
    TM2.Stmt Mc.Γ Mc.Λ Mc.σ → TM2.Stmt (MΓ Mc Ma Mp) (MΛ Mc Ma Mp) (Mσ Mc Ma Mp)
  | .push k f q => .push (Sum.inl k) (fun s => f s.1) (trC q)
  | .peek k f q => .peek (Sum.inl k) (fun s o => (f s.1 o, s.2)) (trC q)
  | .pop k f q => .pop (Sum.inl k) (fun s o => (f s.1 o, s.2)) (trC q)
  | .load a q => .load (fun s => (a s.1, s.2)) (trC q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1) (trC q₁) (trC q₂)
  | .goto f => .goto (fun s => Sum.inl (f s.1))
  | .halt => .goto (fun _ => lbl Mc Ma Mp ⟨2, by decide⟩)

private def trA {Mc Ma Mp : FinTM2} :
    TM2.Stmt Ma.Γ Ma.Λ Ma.σ → TM2.Stmt (MΓ Mc Ma Mp) (MΛ Mc Ma Mp) (Mσ Mc Ma Mp)
  | .push k f q => .push (Sum.inr (Sum.inl k)) (fun s => f s.2.1) (trA q)
  | .peek k f q => .peek (Sum.inr (Sum.inl k)) (fun s o => (s.1, f s.2.1 o, s.2.2)) (trA q)
  | .pop k f q => .pop (Sum.inr (Sum.inl k)) (fun s o => (s.1, f s.2.1 o, s.2.2)) (trA q)
  | .load a q => .load (fun s => (s.1, a s.2.1, s.2.2)) (trA q)
  | .branch f q₁ q₂ => .branch (fun s => f s.2.1) (trA q₁) (trA q₂)
  | .goto f => .goto (fun s => Sum.inr (Sum.inl (f s.2.1)))
  | .halt => .goto (fun _ => lbl Mc Ma Mp ⟨4, by decide⟩)

private def trP {Mc Ma Mp : FinTM2} :
    TM2.Stmt Mp.Γ Mp.Λ Mp.σ → TM2.Stmt (MΓ Mc Ma Mp) (MΛ Mc Ma Mp) (Mσ Mc Ma Mp)
  | .push k f q => .push (Sum.inr (Sum.inr (Sum.inl k))) (fun s => f s.2.2.1) (trP q)
  | .peek k f q =>
      .peek (Sum.inr (Sum.inr (Sum.inl k))) (fun s o => (s.1, s.2.1, f s.2.2.1 o, s.2.2.2)) (trP q)
  | .pop k f q =>
      .pop (Sum.inr (Sum.inr (Sum.inl k))) (fun s o => (s.1, s.2.1, f s.2.2.1 o, s.2.2.2)) (trP q)
  | .load a q => .load (fun s => (s.1, s.2.1, a s.2.2.1, s.2.2.2)) (trP q)
  | .branch f q₁ q₂ => .branch (fun s => f s.2.2.1) (trP q₁) (trP q₂)
  | .goto f => .goto (fun s => Sum.inr (Sum.inr (Sum.inl (f s.2.2.1))))
  | .halt => .goto (fun _ => lbl Mc Ma Mp ⟨10, by decide⟩)

private def extraProg (Mc Ma Mp : FinTM2)
    (e0c : Bool → Mc.Γ Mc.k₀) (e0a : Bool → Ma.Γ Ma.k₀) (e1a : Ma.Γ Ma.k₁ → Bool)
    (e0p : Bool → Mp.Γ Mp.k₀) :
    Fin 15 → TM2.Stmt (MΓ Mc Ma Mp) (MΛ Mc Ma Mp) (Mσ Mc Ma Mp)
  | ⟨0, _⟩ =>
    .pop (kI Mc Ma Mp) (fun s o => (s.1, s.2.1, s.2.2.1, o))
      (.branch (fun s => s.2.2.2.isSome)
        (.push (kA Mc Ma Mp) (fun s => s.2.2.2.getD false)
          (.push (kB Mc Ma Mp) (fun s => s.2.2.2.getD false)
            (.goto (fun _ => lbl Mc Ma Mp ⟨0, by decide⟩))))
        (.goto (fun _ => lbl Mc Ma Mp ⟨1, by decide⟩)))
  | ⟨1, _⟩ =>
    .pop (kB Mc Ma Mp) (fun s o => (s.1, s.2.1, s.2.2.1, o))
      (.branch (fun s => s.2.2.2.isSome)
        (.push (Sum.inl Mc.k₀) (fun s => e0c (s.2.2.2.getD false))
          (.goto (fun _ => lbl Mc Ma Mp ⟨1, by decide⟩)))
        (.goto (fun _ => Sum.inl Mc.main)))
  | ⟨2, _⟩ =>
    .pop (Sum.inl Mc.k₁) (fun s o => (s.1, s.2.1, s.2.2.1, o.map (fun _ => true)))
      (.branch (fun s => s.2.2.2.isSome)
        (.push (kR Mc Ma Mp) (fun _ => true)
          (.goto (fun _ => lbl Mc Ma Mp ⟨2, by decide⟩)))
        (.goto (fun _ => lbl Mc Ma Mp ⟨3, by decide⟩)))
  | ⟨3, _⟩ =>
    .pop (kA Mc Ma Mp) (fun s o => (s.1, s.2.1, s.2.2.1, o))
      (.branch (fun s => s.2.2.2.isSome)
        (.push (Sum.inr (Sum.inl Ma.k₀)) (fun s => e0a (s.2.2.2.getD false))
          (.goto (fun _ => lbl Mc Ma Mp ⟨3, by decide⟩)))
        (.goto (fun _ => Sum.inr (Sum.inl Ma.main))))
  | ⟨4, _⟩ =>
    .pop (Sum.inr (Sum.inl Ma.k₁)) (fun s o => (s.1, s.2.1, s.2.2.1, o.map e1a))
      (.branch (fun s => s.2.2.2.isSome)
        (.push (kA Mc Ma Mp) (fun s => s.2.2.2.getD false)
          (.goto (fun _ => lbl Mc Ma Mp ⟨4, by decide⟩)))
        (.goto (fun _ => lbl Mc Ma Mp ⟨5, by decide⟩)))
  | ⟨5, _⟩ =>
    .pop (kR Mc Ma Mp) (fun s o => (s.1, s.2.1, s.2.2.1, o))
      (.branch (fun s => s.2.2.2.isSome)
        (.goto (fun _ => lbl Mc Ma Mp ⟨6, by decide⟩))
        (.goto (fun _ => lbl Mc Ma Mp ⟨13, by decide⟩)))
  | ⟨6, _⟩ =>
    .pop (kA Mc Ma Mp) (fun s o => (s.1, s.2.1, s.2.2.1, o))
      (.branch (fun s => s.2.2.2.isSome)
        (.push (Sum.inr (Sum.inr (Sum.inl Mp.k₀))) (fun s => e0p (s.2.2.2.getD false))
          (.push (kB Mc Ma Mp) (fun s => s.2.2.2.getD false)
            (.goto (fun _ => lbl Mc Ma Mp ⟨6, by decide⟩))))
        (.goto (fun _ => lbl Mc Ma Mp ⟨7, by decide⟩)))
  | ⟨7, _⟩ =>
    .pop (kB Mc Ma Mp) (fun s o => (s.1, s.2.1, s.2.2.1, o))
      (.branch (fun s => s.2.2.2.isSome)
        (.push (kA Mc Ma Mp) (fun s => s.2.2.2.getD false)
          (.goto (fun _ => lbl Mc Ma Mp ⟨7, by decide⟩)))
        (.goto (fun _ => lbl Mc Ma Mp ⟨8, by decide⟩)))
  | ⟨8, _⟩ =>
    .pop (kC Mc Ma Mp) (fun s o => (s.1, s.2.1, s.2.2.1, o))
      (.branch (fun s => s.2.2.2.isSome)
        (.push (Sum.inr (Sum.inr (Sum.inl Mp.k₀))) (fun _ => e0p true)
          (.push (kB Mc Ma Mp) (fun _ => true)
            (.goto (fun _ => lbl Mc Ma Mp ⟨8, by decide⟩))))
        (.push (Sum.inr (Sum.inr (Sum.inl Mp.k₀))) (fun _ => e0p false)
          (.goto (fun _ => lbl Mc Ma Mp ⟨9, by decide⟩))))
  | ⟨9, _⟩ =>
    .pop (kB Mc Ma Mp) (fun s o => (s.1, s.2.1, s.2.2.1, o))
      (.branch (fun s => s.2.2.2.isSome)
        (.push (Sum.inr (Sum.inr (Sum.inl Mp.k₀))) (fun _ => e0p true)
          (.push (kC Mc Ma Mp) (fun _ => true)
            (.goto (fun _ => lbl Mc Ma Mp ⟨9, by decide⟩))))
        (.goto (fun _ => Sum.inr (Sum.inr (Sum.inl Mp.main)))))
  | ⟨10, _⟩ =>
    .pop (Sum.inr (Sum.inr (Sum.inl Mp.k₁)))
      (fun s o => (s.1, s.2.1, s.2.2.1, o.map (fun _ => true)))
      (.branch (fun s => s.2.2.2.isSome)
        (.goto (fun _ => lbl Mc Ma Mp ⟨11, by decide⟩))
        (.push (kC Mc Ma Mp) (fun _ => true)
          (.goto (fun _ => lbl Mc Ma Mp ⟨5, by decide⟩))))
  | ⟨11, _⟩ =>
    .pop (Sum.inr (Sum.inr (Sum.inl Mp.k₁)))
      (fun s o => (s.1, s.2.1, s.2.2.1, o.map (fun _ => true)))
      (.branch (fun s => s.2.2.2.isSome)
        (.goto (fun _ => lbl Mc Ma Mp ⟨11, by decide⟩))
        (.goto (fun _ => lbl Mc Ma Mp ⟨12, by decide⟩)))
  | ⟨12, _⟩ =>
    .pop (kR Mc Ma Mp) (fun s o => (s.1, s.2.1, s.2.2.1, o))
      (.branch (fun s => s.2.2.2.isSome)
        (.goto (fun _ => lbl Mc Ma Mp ⟨12, by decide⟩))
        (.goto (fun _ => lbl Mc Ma Mp ⟨13, by decide⟩)))
  | ⟨13, _⟩ =>
    .pop (kA Mc Ma Mp) (fun s o => (s.1, s.2.1, s.2.2.1, o))
      (.branch (fun s => s.2.2.2.isSome)
        (.goto (fun _ => lbl Mc Ma Mp ⟨13, by decide⟩))
        (.goto (fun _ => lbl Mc Ma Mp ⟨14, by decide⟩)))
  | ⟨14, _⟩ =>
    .pop (kC Mc Ma Mp) (fun s o => (s.1, s.2.1, s.2.2.1, o))
      (.branch (fun s => s.2.2.2.isSome)
        (.push (kO Mc Ma Mp) (fun _ => true)
          (.goto (fun _ => lbl Mc Ma Mp ⟨14, by decide⟩)))
        .halt)

private def mainProg (Mc Ma Mp : FinTM2)
    (e0c : Bool → Mc.Γ Mc.k₀) (e0a : Bool → Ma.Γ Ma.k₀) (e1a : Ma.Γ Ma.k₁ → Bool)
    (e0p : Bool → Mp.Γ Mp.k₀) :
    MΛ Mc Ma Mp → TM2.Stmt (MΓ Mc Ma Mp) (MΛ Mc Ma Mp) (Mσ Mc Ma Mp)
  | Sum.inl l => trC (Mc.m l)
  | Sum.inr (Sum.inl l) => trA (Ma.m l)
  | Sum.inr (Sum.inr (Sum.inl l)) => trP (Mp.m l)
  | Sum.inr (Sum.inr (Sum.inr n)) => extraProg Mc Ma Mp e0c e0a e1a e0p n

private def mainM (Mc Ma Mp : FinTM2)
    (e0c : Bool → Mc.Γ Mc.k₀) (e0a : Bool → Ma.Γ Ma.k₀) (e1a : Ma.Γ Ma.k₁ → Bool)
    (e0p : Bool → Mp.Γ Mp.k₀) : FinTM2 :=
  haveI := Mc.kFin
  haveI := Ma.kFin
  haveI := Mp.kFin
  haveI := Mc.ΛFin
  haveI := Ma.ΛFin
  haveI := Mp.ΛFin
  haveI := Mc.σFin
  haveI := Ma.σFin
  haveI := Mp.σFin
  { K := MK Mc Ma Mp
    k₀ := kI Mc Ma Mp
    k₁ := kO Mc Ma Mp
    Γ := MΓ Mc Ma Mp
    Λ := MΛ Mc Ma Mp
    main := lbl Mc Ma Mp ⟨0, by decide⟩
    σ := Mσ Mc Ma Mp
    initialState := (Mc.initialState, Ma.initialState, Mp.initialState, none)
    Γk₀Fin := inferInstanceAs (Fintype Bool)
    m := mainProg Mc Ma Mp e0c e0a e1a e0p }

private def mstk {Mc Ma Mp : FinTM2}
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (sI sO sR sA sB sC : List Bool) : ∀ k, List (MΓ Mc Ma Mp k)
  | Sum.inl k => Sc k
  | Sum.inr (Sum.inl k) => Sa k
  | Sum.inr (Sum.inr (Sum.inl k)) => Sp k
  | Sum.inr (Sum.inr (Sum.inr ⟨0, _⟩)) => sI
  | Sum.inr (Sum.inr (Sum.inr ⟨1, _⟩)) => sO
  | Sum.inr (Sum.inr (Sum.inr ⟨2, _⟩)) => sR
  | Sum.inr (Sum.inr (Sum.inr ⟨3, _⟩)) => sA
  | Sum.inr (Sum.inr (Sum.inr ⟨4, _⟩)) => sB
  | Sum.inr (Sum.inr (Sum.inr ⟨5, _⟩)) => sC

private theorem mstk_set_c {Mc Ma Mp : FinTM2}
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (sI sO sR sA sB sC : List Bool) (k : Mc.K) (x : List (Mc.Γ k)) :
    Function.update (mstk Sc Sa Sp sI sO sR sA sB sC) (Sum.inl k) x =
      mstk (Function.update Sc k x) Sa Sp sI sO sR sA sB sC := by
  funext j
  rcases j with j | j | j | j
  · by_cases h : j = k
    · subst h
      rw [Function.update_self]
      show x = Function.update Sc j x j
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show Sc j = Function.update Sc k x j
      rw [Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; fin_cases j <;> rfl

private theorem mstk_set_a {Mc Ma Mp : FinTM2}
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (sI sO sR sA sB sC : List Bool) (k : Ma.K) (x : List (Ma.Γ k)) :
    Function.update (mstk Sc Sa Sp sI sO sR sA sB sC) (Sum.inr (Sum.inl k)) x =
      mstk Sc (Function.update Sa k x) Sp sI sO sR sA sB sC := by
  funext j
  rcases j with j | j | j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · by_cases h : j = k
    · subst h
      rw [Function.update_self]
      show x = Function.update Sa j x j
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show Sa j = Function.update Sa k x j
      rw [Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; fin_cases j <;> rfl

private theorem mstk_set_p {Mc Ma Mp : FinTM2}
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (sI sO sR sA sB sC : List Bool) (k : Mp.K) (x : List (Mp.Γ k)) :
    Function.update (mstk Sc Sa Sp sI sO sR sA sB sC) (Sum.inr (Sum.inr (Sum.inl k))) x =
      mstk Sc Sa (Function.update Sp k x) sI sO sR sA sB sC := by
  funext j
  rcases j with j | j | j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · by_cases h : j = k
    · subst h
      rw [Function.update_self]
      show x = Function.update Sp j x j
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show Sp j = Function.update Sp k x j
      rw [Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)]; fin_cases j <;> rfl

private theorem mstk_set_I {Mc Ma Mp : FinTM2}
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (sI sO sR sA sB sC x : List Bool) :
    Function.update (mstk Sc Sa Sp sI sO sR sA sB sC) (kI Mc Ma Mp) x =
      mstk Sc Sa Sp x sO sR sA sB sC := by
  funext j
  rcases j with j | j | j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · fin_cases j
    · rw [Function.update_self]; rfl
    all_goals rw [Function.update_of_ne (by simp [kI])]; rfl

private theorem mstk_set_O {Mc Ma Mp : FinTM2}
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (sI sO sR sA sB sC x : List Bool) :
    Function.update (mstk Sc Sa Sp sI sO sR sA sB sC) (kO Mc Ma Mp) x =
      mstk Sc Sa Sp sI x sR sA sB sC := by
  funext j
  rcases j with j | j | j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · fin_cases j
    · rw [Function.update_of_ne (by simp [kO])]; rfl
    · rw [Function.update_self]; rfl
    all_goals rw [Function.update_of_ne (by simp [kO])]; rfl

private theorem mstk_set_R {Mc Ma Mp : FinTM2}
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (sI sO sR sA sB sC x : List Bool) :
    Function.update (mstk Sc Sa Sp sI sO sR sA sB sC) (kR Mc Ma Mp) x =
      mstk Sc Sa Sp sI sO x sA sB sC := by
  funext j
  rcases j with j | j | j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · fin_cases j
    · rw [Function.update_of_ne (by simp [kR])]; rfl
    · rw [Function.update_of_ne (by simp [kR])]; rfl
    · rw [Function.update_self]; rfl
    all_goals rw [Function.update_of_ne (by simp [kR])]; rfl

private theorem mstk_set_A {Mc Ma Mp : FinTM2}
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (sI sO sR sA sB sC x : List Bool) :
    Function.update (mstk Sc Sa Sp sI sO sR sA sB sC) (kA Mc Ma Mp) x =
      mstk Sc Sa Sp sI sO sR x sB sC := by
  funext j
  rcases j with j | j | j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · fin_cases j
    · rw [Function.update_of_ne (by simp [kA])]; rfl
    · rw [Function.update_of_ne (by simp [kA])]; rfl
    · rw [Function.update_of_ne (by simp [kA])]; rfl
    · rw [Function.update_self]; rfl
    all_goals rw [Function.update_of_ne (by simp [kA])]; rfl

private theorem mstk_set_B {Mc Ma Mp : FinTM2}
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (sI sO sR sA sB sC x : List Bool) :
    Function.update (mstk Sc Sa Sp sI sO sR sA sB sC) (kB Mc Ma Mp) x =
      mstk Sc Sa Sp sI sO sR sA x sC := by
  funext j
  rcases j with j | j | j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · fin_cases j
    · rw [Function.update_of_ne (by simp [kB])]; rfl
    · rw [Function.update_of_ne (by simp [kB])]; rfl
    · rw [Function.update_of_ne (by simp [kB])]; rfl
    · rw [Function.update_of_ne (by simp [kB])]; rfl
    · rw [Function.update_self]; rfl
    · rw [Function.update_of_ne (by simp [kB])]; rfl

private theorem mstk_set_C {Mc Ma Mp : FinTM2}
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (sI sO sR sA sB sC x : List Bool) :
    Function.update (mstk Sc Sa Sp sI sO sR sA sB sC) (kC Mc Ma Mp) x =
      mstk Sc Sa Sp sI sO sR sA sB x := by
  funext j
  rcases j with j | j | j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · fin_cases j
    · rw [Function.update_of_ne (by simp [kC])]; rfl
    · rw [Function.update_of_ne (by simp [kC])]; rfl
    · rw [Function.update_of_ne (by simp [kC])]; rfl
    · rw [Function.update_of_ne (by simp [kC])]; rfl
    · rw [Function.update_of_ne (by simp [kC])]; rfl
    · rw [Function.update_self]; rfl

private theorem mstk_nil {Mc Ma Mp : FinTM2} :
    (mstk (Mc := Mc) (Ma := Ma) (Mp := Mp)
      (fun _ => []) (fun _ => []) (fun _ => []) [] [] [] [] [] []) = fun _ => [] := by
  funext j
  rcases j with j | j | j | j
  · rfl
  · rfl
  · rfl
  · fin_cases j <;> rfl

private theorem mstk_nil_I {Mc Ma Mp : FinTM2} (s : List Bool) :
    mstk (Mc := Mc) (Ma := Ma) (Mp := Mp)
      (fun _ => []) (fun _ => []) (fun _ => []) s [] [] [] [] [] =
      Function.update (fun _ => [] : ∀ k, List (MΓ Mc Ma Mp k)) (kI Mc Ma Mp) s :=
  (mstk_set_I (Mc := Mc) (Ma := Ma) (Mp := Mp)
    (fun _ => []) (fun _ => []) (fun _ => []) [] [] [] [] [] [] s).symm.trans
    (by rw [mstk_nil])

private theorem mstk_nil_O {Mc Ma Mp : FinTM2} (s : List Bool) :
    mstk (Mc := Mc) (Ma := Ma) (Mp := Mp)
      (fun _ => []) (fun _ => []) (fun _ => []) [] s [] [] [] [] =
      Function.update (fun _ => [] : ∀ k, List (MΓ Mc Ma Mp k)) (kO Mc Ma Mp) s :=
  (mstk_set_O (Mc := Mc) (Ma := Ma) (Mp := Mp)
    (fun _ => []) (fun _ => []) (fun _ => []) [] [] [] [] [] [] s).symm.trans
    (by rw [mstk_nil])

private def embC {Mc Ma Mp : FinTM2}
    (va : Ma.σ) (vp : Mp.σ) (ob : Option Bool)
    (Sa : ∀ k, List (Ma.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (sI sO sR sA sB sC : List Bool)
    (c : TM2.Cfg Mc.Γ Mc.Λ Mc.σ) : MCfg Mc Ma Mp :=
  ⟨some (c.l.elim (lbl Mc Ma Mp ⟨2, by decide⟩) Sum.inl),
    (c.var, va, vp, ob), mstk c.stk Sa Sp sI sO sR sA sB sC⟩

private def embA {Mc Ma Mp : FinTM2}
    (vc : Mc.σ) (vp : Mp.σ) (ob : Option Bool)
    (Sc : ∀ k, List (Mc.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (sI sO sR sA sB sC : List Bool)
    (c : TM2.Cfg Ma.Γ Ma.Λ Ma.σ) : MCfg Mc Ma Mp :=
  ⟨some (c.l.elim (lbl Mc Ma Mp ⟨4, by decide⟩) (fun l => Sum.inr (Sum.inl l))),
    (vc, c.var, vp, ob), mstk Sc c.stk Sp sI sO sR sA sB sC⟩

private def embP {Mc Ma Mp : FinTM2}
    (vc : Mc.σ) (va : Ma.σ) (ob : Option Bool)
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k))
    (sI sO sR sA sB sC : List Bool)
    (c : TM2.Cfg Mp.Γ Mp.Λ Mp.σ) : MCfg Mc Ma Mp :=
  ⟨some (c.l.elim (lbl Mc Ma Mp ⟨10, by decide⟩) (fun l => Sum.inr (Sum.inr (Sum.inl l)))),
    (vc, va, c.var, ob), mstk Sc Sa c.stk sI sO sR sA sB sC⟩

private theorem simC {Mc Ma Mp : FinTM2}
    (va : Ma.σ) (vp : Mp.σ) (ob : Option Bool)
    (Sa : ∀ k, List (Ma.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (sI sO sR sA sB sC : List Bool)
    (q : TM2.Stmt Mc.Γ Mc.Λ Mc.σ) (vc : Mc.σ) (Sc : ∀ k, List (Mc.Γ k)) :
    TM2.stepAux (trC (Ma := Ma) (Mp := Mp) q) ((vc, va, vp, ob) : Mσ Mc Ma Mp)
        (mstk Sc Sa Sp sI sO sR sA sB sC) =
      embC va vp ob Sa Sp sI sO sR sA sB sC (TM2.stepAux q vc Sc) := by
  induction q generalizing vc Sc with
  | push k f q ih =>
    have := ih vc (Function.update Sc k (f vc :: Sc k))
    rw [← mstk_set_c] at this
    exact this
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    have := ih (f vc (Sc k).head?) (Function.update Sc k (Sc k).tail)
    rw [← mstk_set_c] at this
    exact this
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [trC, TM2.stepAux]
    cases f vc
    · exact ih₂ vc Sc
    · exact ih₁ vc Sc
  | goto f => rfl
  | halt => rfl

private theorem stepC {Mc Ma Mp : FinTM2}
    (e0c : Bool → Mc.Γ Mc.k₀) (e0a : Bool → Ma.Γ Ma.k₀) (e1a : Ma.Γ Ma.k₁ → Bool)
    (e0p : Bool → Mp.Γ Mp.k₀)
    (va : Ma.σ) (vp : Mp.σ) (ob : Option Bool)
    (Sa : ∀ k, List (Ma.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (sI sO sR sA sB sC : List Bool)
    (c c' : TM2.Cfg Mc.Γ Mc.Λ Mc.σ) (h : TM2.step Mc.m c = some c') :
    TM2.step (mainProg Mc Ma Mp e0c e0a e1a e0p)
        (embC va vp ob Sa Sp sI sO sR sA sB sC c) =
      some (embC va vp ob Sa Sp sI sO sR sA sB sC c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (simC va vp ob Sa Sp sI sO sR sA sB sC (Mc.m l) v S)

private theorem simA {Mc Ma Mp : FinTM2}
    (vc : Mc.σ) (vp : Mp.σ) (ob : Option Bool)
    (Sc : ∀ k, List (Mc.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (sI sO sR sA sB sC : List Bool)
    (q : TM2.Stmt Ma.Γ Ma.Λ Ma.σ) (va : Ma.σ) (Sa : ∀ k, List (Ma.Γ k)) :
    TM2.stepAux (trA (Mc := Mc) (Mp := Mp) q) ((vc, va, vp, ob) : Mσ Mc Ma Mp)
        (mstk Sc Sa Sp sI sO sR sA sB sC) =
      embA vc vp ob Sc Sp sI sO sR sA sB sC (TM2.stepAux q va Sa) := by
  induction q generalizing va Sa with
  | push k f q ih =>
    have := ih va (Function.update Sa k (f va :: Sa k))
    rw [← mstk_set_a] at this
    exact this
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    have := ih (f va (Sa k).head?) (Function.update Sa k (Sa k).tail)
    rw [← mstk_set_a] at this
    exact this
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [trA, TM2.stepAux]
    cases f va
    · exact ih₂ va Sa
    · exact ih₁ va Sa
  | goto f => rfl
  | halt => rfl

private theorem stepA {Mc Ma Mp : FinTM2}
    (e0c : Bool → Mc.Γ Mc.k₀) (e0a : Bool → Ma.Γ Ma.k₀) (e1a : Ma.Γ Ma.k₁ → Bool)
    (e0p : Bool → Mp.Γ Mp.k₀)
    (vc : Mc.σ) (vp : Mp.σ) (ob : Option Bool)
    (Sc : ∀ k, List (Mc.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (sI sO sR sA sB sC : List Bool)
    (c c' : TM2.Cfg Ma.Γ Ma.Λ Ma.σ) (h : TM2.step Ma.m c = some c') :
    TM2.step (mainProg Mc Ma Mp e0c e0a e1a e0p)
        (embA vc vp ob Sc Sp sI sO sR sA sB sC c) =
      some (embA vc vp ob Sc Sp sI sO sR sA sB sC c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (simA vc vp ob Sc Sp sI sO sR sA sB sC (Ma.m l) v S)

private theorem simP {Mc Ma Mp : FinTM2}
    (vc : Mc.σ) (va : Ma.σ) (ob : Option Bool)
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k))
    (sI sO sR sA sB sC : List Bool)
    (q : TM2.Stmt Mp.Γ Mp.Λ Mp.σ) (vp : Mp.σ) (Sp : ∀ k, List (Mp.Γ k)) :
    TM2.stepAux (trP (Mc := Mc) (Ma := Ma) q) ((vc, va, vp, ob) : Mσ Mc Ma Mp)
        (mstk Sc Sa Sp sI sO sR sA sB sC) =
      embP vc va ob Sc Sa sI sO sR sA sB sC (TM2.stepAux q vp Sp) := by
  induction q generalizing vp Sp with
  | push k f q ih =>
    have := ih vp (Function.update Sp k (f vp :: Sp k))
    rw [← mstk_set_p] at this
    exact this
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    have := ih (f vp (Sp k).head?) (Function.update Sp k (Sp k).tail)
    rw [← mstk_set_p] at this
    exact this
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [trP, TM2.stepAux]
    cases f vp
    · exact ih₂ vp Sp
    · exact ih₁ vp Sp
  | goto f => rfl
  | halt => rfl

private theorem stepP {Mc Ma Mp : FinTM2}
    (e0c : Bool → Mc.Γ Mc.k₀) (e0a : Bool → Ma.Γ Ma.k₀) (e1a : Ma.Γ Ma.k₁ → Bool)
    (e0p : Bool → Mp.Γ Mp.k₀)
    (vc : Mc.σ) (va : Ma.σ) (ob : Option Bool)
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k))
    (sI sO sR sA sB sC : List Bool)
    (c c' : TM2.Cfg Mp.Γ Mp.Λ Mp.σ) (h : TM2.step Mp.m c = some c') :
    TM2.step (mainProg Mc Ma Mp e0c e0a e1a e0p)
        (embP vc va ob Sc Sa sI sO sR sA sB sC c) =
      some (embP vc va ob Sc Sa sI sO sR sA sB sC c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (simP vc va ob Sc Sa sI sO sR sA sB sC (Mp.m l) v S)

section loops

variable {Mc Ma Mp : FinTM2}
  (e0c : Bool → Mc.Γ Mc.k₀) (e0a : Bool → Ma.Γ Ma.k₀) (e1a : Ma.Γ Ma.k₁ → Bool)
  (e0p : Bool → Mp.Γ Mp.k₀)

private theorem loop0 (vc : Mc.σ) (va : Ma.σ) (vp : Mp.σ)
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (sO sR sC : List Bool) :
    ∀ (sI sA sB : List Bool) (ob : Option Bool),
      (flip bind (TM2.step (mainProg Mc Ma Mp e0c e0a e1a e0p)))^[sI.length + 1]
        (some ⟨some (lbl Mc Ma Mp ⟨0, by decide⟩), (vc, va, vp, ob),
          mstk Sc Sa Sp sI sO sR sA sB sC⟩) =
      some ⟨some (lbl Mc Ma Mp ⟨1, by decide⟩), (vc, va, vp, none),
        mstk Sc Sa Sp [] sO sR (sI.reverse ++ sA) (sI.reverse ++ sB) sC⟩ := by
  intro sI
  induction sI with
  | nil =>
    intro sA sB ob
    rw [List.length_nil, Function.iterate_one]
    dsimp only [flip, bind, Option.bind]
    simp only [TM2.step, mainProg, extraProg, TM2.stepAux, mstk, mstk_set_I,
      List.head?_nil, List.tail_nil, Option.isSome_none, List.reverse_nil, List.nil_append]
    rfl
  | cons x l ih =>
    intro sA sB ob
    rw [List.length_cons, Function.iterate_succ_apply]
    dsimp only [flip, bind, Option.bind]
    simp only [TM2.step, mainProg, extraProg, TM2.stepAux, mstk, mstk_set_I, mstk_set_A,
      mstk_set_B, List.head?_cons, List.tail_cons, Option.isSome_some, Option.getD_some]
    have h := ih (x :: sA) (x :: sB) (some x)
    simpa [List.reverse_cons, List.append_assoc] using h

private theorem loop1 (vc : Mc.σ) (va : Ma.σ) (vp : Mp.σ)
    (Sa : ∀ k, List (Ma.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (sI sO sR sA sC : List Bool) :
    ∀ (sB : List Bool) (mc0 : List (Mc.Γ Mc.k₀)) (ob : Option Bool),
      (flip bind (TM2.step (mainProg Mc Ma Mp e0c e0a e1a e0p)))^[sB.length + 1]
        (some ⟨some (lbl Mc Ma Mp ⟨1, by decide⟩), (vc, va, vp, ob),
          mstk (Function.update (fun _ => []) Mc.k₀ mc0) Sa Sp sI sO sR sA sB sC⟩) =
      some ⟨some (Sum.inl Mc.main), (vc, va, vp, none),
        mstk (Function.update (fun _ => []) Mc.k₀ (sB.reverse.map e0c ++ mc0))
          Sa Sp sI sO sR sA [] sC⟩ := by
  intro sB
  induction sB with
  | nil =>
    intro mc0 ob
    rw [List.length_nil, Function.iterate_one]
    dsimp only [flip, bind, Option.bind]
    simp only [TM2.step, mainProg, extraProg, TM2.stepAux, mstk, mstk_set_B,
      List.head?_nil, List.tail_nil, Option.isSome_none, List.reverse_nil, List.map_nil,
      List.nil_append]
    rfl
  | cons x l ih =>
    intro mc0 ob
    rw [List.length_cons, Function.iterate_succ_apply]
    dsimp only [flip, bind, Option.bind]
    simp only [TM2.step, mainProg, extraProg, TM2.stepAux, mstk, mstk_set_B, mstk_set_c,
      Function.update_self, Function.update_idem, List.head?_cons, List.tail_cons,
      Option.isSome_some, Option.getD_some]
    have h := ih (e0c x :: mc0) (some x)
    simpa [List.reverse_cons, List.map_append, List.append_assoc] using h

private theorem loop2 (vc : Mc.σ) (va : Ma.σ) (vp : Mp.σ)
    (Sa : ∀ k, List (Ma.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (sI sO sA sB sC : List Bool) :
    ∀ (mc1 : List (Mc.Γ Mc.k₁)) (r : ℕ) (ob : Option Bool),
      (flip bind (TM2.step (mainProg Mc Ma Mp e0c e0a e1a e0p)))^[mc1.length + 1]
        (some ⟨some (lbl Mc Ma Mp ⟨2, by decide⟩), (vc, va, vp, ob),
          mstk (Function.update (fun _ => []) Mc.k₁ mc1) Sa Sp
            sI sO (List.replicate r true) sA sB sC⟩) =
      some ⟨some (lbl Mc Ma Mp ⟨3, by decide⟩), (vc, va, vp, none),
        mstk (fun _ => []) Sa Sp sI sO (List.replicate (mc1.length + r) true) sA sB sC⟩ := by
  intro mc1
  induction mc1 with
  | nil =>
    intro r ob
    rw [List.length_nil, Function.iterate_one]
    dsimp only [flip, bind, Option.bind]
    have hu : Function.update (fun _ => [] : ∀ k, List (Mc.Γ k)) Mc.k₁ [] = fun _ => [] := by
      funext k
      by_cases h : k = Mc.k₁ <;> simp [h]
    simp only [TM2.step, mainProg, extraProg, TM2.stepAux, mstk, mstk_set_c,
      List.head?_nil, List.tail_nil, Option.map_none, Option.isSome_none, Nat.zero_add, hu]
    rfl
  | cons x l ih =>
    intro r ob
    rw [List.length_cons, Function.iterate_succ_apply]
    dsimp only [flip, bind, Option.bind]
    simp only [TM2.step, mainProg, extraProg, TM2.stepAux, mstk, mstk_set_c, mstk_set_R,
      Function.update_self, Function.update_idem, List.head?_cons, List.tail_cons,
      Option.map_some, Option.isSome_some]
    have h := ih (r + 1) (some true)
    have hrep : true :: List.replicate r true = List.replicate (r + 1) true := by
      simp [List.replicate_succ]
    rw [hrep]
    have heq : l.length + (r + 1) = l.length + 1 + r := by omega
    rw [heq] at h
    exact h

private theorem loop3 (vc : Mc.σ) (va : Ma.σ) (vp : Mp.σ)
    (Sc : ∀ k, List (Mc.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (sI sO sR sB sC : List Bool) :
    ∀ (sA : List Bool) (ma0 : List (Ma.Γ Ma.k₀)) (ob : Option Bool),
      (flip bind (TM2.step (mainProg Mc Ma Mp e0c e0a e1a e0p)))^[sA.length + 1]
        (some ⟨some (lbl Mc Ma Mp ⟨3, by decide⟩), (vc, va, vp, ob),
          mstk Sc (Function.update (fun _ => []) Ma.k₀ ma0) Sp sI sO sR sA sB sC⟩) =
      some ⟨some (Sum.inr (Sum.inl Ma.main)), (vc, va, vp, none),
        mstk Sc (Function.update (fun _ => []) Ma.k₀ (sA.reverse.map e0a ++ ma0))
          Sp sI sO sR [] sB sC⟩ := by
  intro sA
  induction sA with
  | nil =>
    intro ma0 ob
    rw [List.length_nil, Function.iterate_one]
    dsimp only [flip, bind, Option.bind]
    simp only [TM2.step, mainProg, extraProg, TM2.stepAux, mstk, mstk_set_A,
      List.head?_nil, List.tail_nil, Option.isSome_none, List.reverse_nil, List.map_nil,
      List.nil_append]
    rfl
  | cons x l ih =>
    intro ma0 ob
    rw [List.length_cons, Function.iterate_succ_apply]
    dsimp only [flip, bind, Option.bind]
    simp only [TM2.step, mainProg, extraProg, TM2.stepAux, mstk, mstk_set_A, mstk_set_a,
      Function.update_self, Function.update_idem, List.head?_cons, List.tail_cons,
      Option.isSome_some, Option.getD_some]
    have h := ih (e0a x :: ma0) (some x)
    simpa [List.reverse_cons, List.map_append, List.append_assoc] using h

private theorem loop4 (vc : Mc.σ) (va : Ma.σ) (vp : Mp.σ)
    (Sc : ∀ k, List (Mc.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (sI sO sR sB sC : List Bool) :
    ∀ (ma1 : List (Ma.Γ Ma.k₁)) (sA : List Bool) (ob : Option Bool),
      (flip bind (TM2.step (mainProg Mc Ma Mp e0c e0a e1a e0p)))^[ma1.length + 1]
        (some ⟨some (lbl Mc Ma Mp ⟨4, by decide⟩), (vc, va, vp, ob),
          mstk Sc (Function.update (fun _ => []) Ma.k₁ ma1) Sp sI sO sR sA sB sC⟩) =
      some ⟨some (lbl Mc Ma Mp ⟨5, by decide⟩), (vc, va, vp, none),
        mstk Sc (fun _ => []) Sp sI sO sR ((ma1.map e1a).reverse ++ sA) sB sC⟩ := by
  intro ma1
  induction ma1 with
  | nil =>
    intro sA ob
    rw [List.length_nil, Function.iterate_one]
    dsimp only [flip, bind, Option.bind]
    have hu : Function.update (fun _ => [] : ∀ k, List (Ma.Γ k)) Ma.k₁ [] = fun _ => [] := by
      funext k
      by_cases h : k = Ma.k₁ <;> simp [h]
    simp only [TM2.step, mainProg, extraProg, TM2.stepAux, mstk, mstk_set_a,
      List.head?_nil, List.tail_nil, Option.map_none, Option.isSome_none, List.map_nil,
      List.reverse_nil, List.nil_append, hu]
    rfl
  | cons x l ih =>
    intro sA ob
    rw [List.length_cons, Function.iterate_succ_apply]
    dsimp only [flip, bind, Option.bind]
    simp only [TM2.step, mainProg, extraProg, TM2.stepAux, mstk, mstk_set_a, mstk_set_A,
      Function.update_self, Function.update_idem, List.head?_cons, List.tail_cons,
      Option.map_some, Option.isSome_some, Option.getD_some]
    have h := ih (e1a x :: sA) (some (e1a x))
    simpa [List.reverse_cons, List.append_assoc] using h

private theorem loop6 (vc : Mc.σ) (va : Ma.σ) (vp : Mp.σ)
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k))
    (sI sO sR sC : List Bool) :
    ∀ (sA sB : List Bool) (mp0 : List (Mp.Γ Mp.k₀)) (ob : Option Bool),
      (flip bind (TM2.step (mainProg Mc Ma Mp e0c e0a e1a e0p)))^[sA.length + 1]
        (some ⟨some (lbl Mc Ma Mp ⟨6, by decide⟩), (vc, va, vp, ob),
          mstk Sc Sa (Function.update (fun _ => []) Mp.k₀ mp0) sI sO sR sA sB sC⟩) =
      some ⟨some (lbl Mc Ma Mp ⟨7, by decide⟩), (vc, va, vp, none),
        mstk Sc Sa (Function.update (fun _ => []) Mp.k₀ (sA.reverse.map e0p ++ mp0))
          sI sO sR [] (sA.reverse ++ sB) sC⟩ := by
  intro sA
  induction sA with
  | nil =>
    intro sB mp0 ob
    rw [List.length_nil, Function.iterate_one]
    dsimp only [flip, bind, Option.bind]
    simp only [TM2.step, mainProg, extraProg, TM2.stepAux, mstk, mstk_set_A,
      List.head?_nil, List.tail_nil, Option.isSome_none, List.reverse_nil, List.map_nil,
      List.nil_append]
    rfl
  | cons x l ih =>
    intro sB mp0 ob
    rw [List.length_cons, Function.iterate_succ_apply]
    dsimp only [flip, bind, Option.bind]
    simp only [TM2.step, mainProg, extraProg, TM2.stepAux, mstk, mstk_set_A, mstk_set_p,
      mstk_set_B, Function.update_self, Function.update_idem, List.head?_cons, List.tail_cons,
      Option.isSome_some, Option.getD_some]
    have h := ih (x :: sB) (e0p x :: mp0) (some x)
    simpa [List.reverse_cons, List.map_append, List.append_assoc] using h

private theorem loop7 (vc : Mc.σ) (va : Ma.σ) (vp : Mp.σ)
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (sI sO sR sC : List Bool) :
    ∀ (sB sA : List Bool) (ob : Option Bool),
      (flip bind (TM2.step (mainProg Mc Ma Mp e0c e0a e1a e0p)))^[sB.length + 1]
        (some ⟨some (lbl Mc Ma Mp ⟨7, by decide⟩), (vc, va, vp, ob),
          mstk Sc Sa Sp sI sO sR sA sB sC⟩) =
      some ⟨some (lbl Mc Ma Mp ⟨8, by decide⟩), (vc, va, vp, none),
        mstk Sc Sa Sp sI sO sR (sB.reverse ++ sA) [] sC⟩ := by
  intro sB
  induction sB with
  | nil =>
    intro sA ob
    rw [List.length_nil, Function.iterate_one]
    dsimp only [flip, bind, Option.bind]
    simp only [TM2.step, mainProg, extraProg, TM2.stepAux, mstk, mstk_set_B,
      List.head?_nil, List.tail_nil, Option.isSome_none, List.reverse_nil, List.nil_append]
    rfl
  | cons x l ih =>
    intro sA ob
    rw [List.length_cons, Function.iterate_succ_apply]
    dsimp only [flip, bind, Option.bind]
    simp only [TM2.step, mainProg, extraProg, TM2.stepAux, mstk, mstk_set_B, mstk_set_A,
      List.head?_cons, List.tail_cons, Option.isSome_some, Option.getD_some]
    have h := ih (x :: sA) (some x)
    simpa [List.reverse_cons, List.append_assoc] using h

private theorem loop8 (vc : Mc.σ) (va : Ma.σ) (vp : Mp.σ)
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k))
    (sI sO sR sA : List Bool) :
    ∀ (k m : ℕ) (mp0 : List (Mp.Γ Mp.k₀)) (ob : Option Bool),
      (flip bind (TM2.step (mainProg Mc Ma Mp e0c e0a e1a e0p)))^[k + 1]
        (some ⟨some (lbl Mc Ma Mp ⟨8, by decide⟩), (vc, va, vp, ob),
          mstk Sc Sa (Function.update (fun _ => []) Mp.k₀ mp0)
            sI sO sR sA (List.replicate m true) (List.replicate k true)⟩) =
      some ⟨some (lbl Mc Ma Mp ⟨9, by decide⟩), (vc, va, vp, none),
        mstk Sc Sa (Function.update (fun _ => []) Mp.k₀
            (e0p false :: (List.replicate k (e0p true) ++ mp0)))
          sI sO sR sA (List.replicate (k + m) true) []⟩ := by
  intro k
  induction k with
  | zero =>
    intro m mp0 ob
    rw [Nat.zero_add, Function.iterate_one]
    dsimp only [flip, bind, Option.bind]
    simp only [TM2.step, mainProg, extraProg, TM2.stepAux, mstk, mstk_set_C, mstk_set_p,
      Function.update_self, Function.update_idem, List.replicate_zero, List.head?_nil,
      List.tail_nil, Option.isSome_none, List.nil_append, Nat.zero_add]
    rfl
  | succ k ih =>
    intro m mp0 ob
    rw [Function.iterate_succ_apply]
    dsimp only [flip, bind, Option.bind]
    simp only [TM2.step, mainProg, extraProg, TM2.stepAux, mstk, mstk_set_C, mstk_set_p,
      mstk_set_B, Function.update_self, Function.update_idem, List.replicate_succ,
      List.head?_cons, List.tail_cons, Option.isSome_some]
    have h := ih (m + 1) (e0p true :: mp0) (some true)
    have hrepB : true :: List.replicate m true = List.replicate (m + 1) true := by
      simp [List.replicate_succ]
    rw [hrepB]
    have hkm : k + (m + 1) = k + 1 + m := by omega
    have hrepP : List.replicate k (e0p true) ++ e0p true :: mp0 =
        List.replicate (k + 1) (e0p true) ++ mp0 := by
      rw [List.replicate_succ', List.append_assoc, List.singleton_append]
    rw [hkm, hrepP] at h
    exact h

private theorem loop9 (vc : Mc.σ) (va : Ma.σ) (vp : Mp.σ)
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k))
    (sI sO sR sA : List Bool) :
    ∀ (k m : ℕ) (mp0 : List (Mp.Γ Mp.k₀)) (ob : Option Bool),
      (flip bind (TM2.step (mainProg Mc Ma Mp e0c e0a e1a e0p)))^[k + 1]
        (some ⟨some (lbl Mc Ma Mp ⟨9, by decide⟩), (vc, va, vp, ob),
          mstk Sc Sa (Function.update (fun _ => []) Mp.k₀ mp0)
            sI sO sR sA (List.replicate k true) (List.replicate m true)⟩) =
      some ⟨some (Sum.inr (Sum.inr (Sum.inl Mp.main))), (vc, va, vp, none),
        mstk Sc Sa (Function.update (fun _ => []) Mp.k₀
            (List.replicate k (e0p true) ++ mp0))
          sI sO sR sA [] (List.replicate (k + m) true)⟩ := by
  intro k
  induction k with
  | zero =>
    intro m mp0 ob
    rw [Nat.zero_add, Function.iterate_one]
    dsimp only [flip, bind, Option.bind]
    simp only [TM2.step, mainProg, extraProg, TM2.stepAux, mstk, mstk_set_B,
      List.replicate_zero, List.head?_nil, List.tail_nil, Option.isSome_none,
      List.nil_append, Nat.zero_add]
    rfl
  | succ k ih =>
    intro m mp0 ob
    rw [Function.iterate_succ_apply]
    dsimp only [flip, bind, Option.bind]
    simp only [TM2.step, mainProg, extraProg, TM2.stepAux, mstk, mstk_set_B, mstk_set_p,
      mstk_set_C, Function.update_self, Function.update_idem, List.replicate_succ,
      List.head?_cons, List.tail_cons, Option.isSome_some]
    have h := ih (m + 1) (e0p true :: mp0) (some true)
    have hrepC : true :: List.replicate m true = List.replicate (m + 1) true := by
      simp [List.replicate_succ]
    rw [hrepC]
    have hkm : k + (m + 1) = k + 1 + m := by omega
    have hrepP : List.replicate k (e0p true) ++ e0p true :: mp0 =
        List.replicate (k + 1) (e0p true) ++ mp0 := by
      rw [List.replicate_succ', List.append_assoc, List.singleton_append]
    rw [hkm, hrepP] at h
    exact h

private theorem loop11 (vc : Mc.σ) (va : Ma.σ) (vp : Mp.σ)
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k))
    (sI sO sR sA sB sC : List Bool) :
    ∀ (mp1 : List (Mp.Γ Mp.k₁)) (ob : Option Bool),
      (flip bind (TM2.step (mainProg Mc Ma Mp e0c e0a e1a e0p)))^[mp1.length + 1]
        (some ⟨some (lbl Mc Ma Mp ⟨11, by decide⟩), (vc, va, vp, ob),
          mstk Sc Sa (Function.update (fun _ => []) Mp.k₁ mp1) sI sO sR sA sB sC⟩) =
      some ⟨some (lbl Mc Ma Mp ⟨12, by decide⟩), (vc, va, vp, none),
        mstk Sc Sa (fun _ => []) sI sO sR sA sB sC⟩ := by
  intro mp1
  induction mp1 with
  | nil =>
    intro ob
    rw [List.length_nil, Function.iterate_one]
    dsimp only [flip, bind, Option.bind]
    have hu : Function.update (fun _ => [] : ∀ k, List (Mp.Γ k)) Mp.k₁ [] = fun _ => [] := by
      funext k
      by_cases h : k = Mp.k₁ <;> simp [h]
    simp only [TM2.step, mainProg, extraProg, TM2.stepAux, mstk, mstk_set_p,
      List.head?_nil, List.tail_nil, Option.map_none, Option.isSome_none, hu]
    rfl
  | cons x l ih =>
    intro ob
    rw [List.length_cons, Function.iterate_succ_apply]
    dsimp only [flip, bind, Option.bind]
    simp only [TM2.step, mainProg, extraProg, TM2.stepAux, mstk, mstk_set_p,
      Function.update_self, Function.update_idem, List.head?_cons, List.tail_cons,
      Option.map_some, Option.isSome_some]
    exact ih (some true)

private theorem loop12 (vc : Mc.σ) (va : Ma.σ) (vp : Mp.σ)
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (sI sO sA sB sC : List Bool) :
    ∀ (sR : List Bool) (ob : Option Bool),
      (flip bind (TM2.step (mainProg Mc Ma Mp e0c e0a e1a e0p)))^[sR.length + 1]
        (some ⟨some (lbl Mc Ma Mp ⟨12, by decide⟩), (vc, va, vp, ob),
          mstk Sc Sa Sp sI sO sR sA sB sC⟩) =
      some ⟨some (lbl Mc Ma Mp ⟨13, by decide⟩), (vc, va, vp, none),
        mstk Sc Sa Sp sI sO [] sA sB sC⟩ := by
  intro sR
  induction sR with
  | nil =>
    intro ob
    rw [List.length_nil, Function.iterate_one]
    dsimp only [flip, bind, Option.bind]
    simp only [TM2.step, mainProg, extraProg, TM2.stepAux, mstk, mstk_set_R,
      List.head?_nil, List.tail_nil, Option.isSome_none]
    rfl
  | cons x l ih =>
    intro ob
    rw [List.length_cons, Function.iterate_succ_apply]
    dsimp only [flip, bind, Option.bind]
    simp only [TM2.step, mainProg, extraProg, TM2.stepAux, mstk, mstk_set_R,
      List.head?_cons, List.tail_cons, Option.isSome_some]
    exact ih (some x)

private theorem loop13 (vc : Mc.σ) (va : Ma.σ) (vp : Mp.σ)
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (sI sO sR sB sC : List Bool) :
    ∀ (sA : List Bool) (ob : Option Bool),
      (flip bind (TM2.step (mainProg Mc Ma Mp e0c e0a e1a e0p)))^[sA.length + 1]
        (some ⟨some (lbl Mc Ma Mp ⟨13, by decide⟩), (vc, va, vp, ob),
          mstk Sc Sa Sp sI sO sR sA sB sC⟩) =
      some ⟨some (lbl Mc Ma Mp ⟨14, by decide⟩), (vc, va, vp, none),
        mstk Sc Sa Sp sI sO sR [] sB sC⟩ := by
  intro sA
  induction sA with
  | nil =>
    intro ob
    rw [List.length_nil, Function.iterate_one]
    dsimp only [flip, bind, Option.bind]
    simp only [TM2.step, mainProg, extraProg, TM2.stepAux, mstk, mstk_set_A,
      List.head?_nil, List.tail_nil, Option.isSome_none]
    rfl
  | cons x l ih =>
    intro ob
    rw [List.length_cons, Function.iterate_succ_apply]
    dsimp only [flip, bind, Option.bind]
    simp only [TM2.step, mainProg, extraProg, TM2.stepAux, mstk, mstk_set_A,
      List.head?_cons, List.tail_cons, Option.isSome_some]
    exact ih (some x)

private theorem loop14 (vc : Mc.σ) (va : Ma.σ) (vp : Mp.σ)
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (sI sR sA sB : List Bool) :
    ∀ (k m : ℕ) (ob : Option Bool),
      (flip bind (TM2.step (mainProg Mc Ma Mp e0c e0a e1a e0p)))^[k + 1]
        (some ⟨some (lbl Mc Ma Mp ⟨14, by decide⟩), (vc, va, vp, ob),
          mstk Sc Sa Sp sI (List.replicate m true) sR sA sB (List.replicate k true)⟩) =
      some ⟨none, (vc, va, vp, none),
        mstk Sc Sa Sp sI (List.replicate (k + m) true) sR sA sB []⟩ := by
  intro k
  induction k with
  | zero =>
    intro m ob
    rw [Nat.zero_add, Function.iterate_one]
    dsimp only [flip, bind, Option.bind]
    simp only [TM2.step, mainProg, extraProg, TM2.stepAux, mstk, mstk_set_C,
      List.replicate_zero, List.head?_nil, List.tail_nil, Option.isSome_none, Nat.zero_add]
    rfl
  | succ k ih =>
    intro m ob
    rw [Function.iterate_succ_apply]
    dsimp only [flip, bind, Option.bind]
    simp only [TM2.step, mainProg, extraProg, TM2.stepAux, mstk, mstk_set_C, mstk_set_O,
      List.replicate_succ, List.head?_cons, List.tail_cons, Option.isSome_some]
    have h := ih (m + 1) (some true)
    have hrepO : true :: List.replicate m true = List.replicate (m + 1) true := by
      simp [List.replicate_succ]
    rw [hrepO]
    have hkm : k + (m + 1) = k + 1 + m := by omega
    rw [hkm] at h
    exact h

end loops

theorem L_meta_370 :
    ∀ p cnt arg : List Bool → List Bool,
      PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) p →
      PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) cnt →
      PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) arg →
      PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
        (fun s => List.replicate ((List.range (cnt s).length).findIdx
          (fun i => !(p (List.replicate i true ++ false :: (List.replicate i true ++ arg s))).isEmpty)) true) := by
  intro p cnt arg ⟨cp⟩ ⟨cc⟩ ⟨ca⟩
  let Mc := cc.tm
  let Ma := ca.tm
  let Mp := cp.tm
  let e0c : Bool → Mc.Γ Mc.k₀ := cc.inputAlphabet.invFun
  let e0a : Bool → Ma.Γ Ma.k₀ := ca.inputAlphabet.invFun
  let e1a : Ma.Γ Ma.k₁ → Bool := ca.outputAlphabet
  let e0p : Bool → Mp.Γ Mp.k₀ := cp.inputAlphabet.invFun
  let M := mainM Mc Ma Mp e0c e0a e1a e0p
  let prog := mainProg Mc Ma Mp e0c e0a e1a e0p
  let Np : Polynomial ℕ := Polynomial.X + Polynomial.C (maxPush Mc) * cc.time
  let Ap : Polynomial ℕ := Polynomial.X + Polynomial.C (maxPush Ma) * ca.time
  let Xp : Polynomial ℕ := Polynomial.C 2 * Np + Polynomial.C 1 + Ap
  let SPp : Polynomial ℕ := cp.time.comp Xp
  let Poutp : Polynomial ℕ := Xp + Polynomial.C (maxPush Mp) * SPp
  let T : Polynomial ℕ :=
    Polynomial.C 3 * Polynomial.X + cc.time + Np + ca.time + Ap + Polynomial.C 5 +
      Np * (Polynomial.C 2 * Ap + Polynomial.C 2 * Np + SPp + Polynomial.C 6) +
      (Poutp + Ap + Polynomial.C 2 * Np + Polynomial.C 6)
  have key : ∀ s : List Bool, ∃ steps, steps ≤ T.eval s.length ∧
      (flip bind (TM2.step prog))^[steps] (some (initList M s)) =
        some (haltList M (List.replicate ((List.range (cnt s).length).findIdx
          (fun i => !(p (List.replicate i true ++ false :: (List.replicate i true ++ arg s))).isEmpty)) true)) := by
    intro s
    let n := (cnt s).length
    let a := arg s
    let q : ℕ → Bool := fun i =>
      !(p (List.replicate i true ++ false :: (List.replicate i true ++ a))).isEmpty
    have hsc : (cc.outputsFun s).steps ≤ cc.time.eval s.length := (cc.outputsFun s).steps_le_m
    have hn : n ≤ Np.eval s.length := by
      have h1 := output_length_le cnt cc s
      have h2 : maxPush Mc * (cc.outputsFun s).steps ≤ maxPush Mc * cc.time.eval s.length :=
        Nat.mul_le_mul_left _ hsc
      simp only [Np, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X]
      dsimp only [Mc, n] at h2 ⊢
      omega
    have hsa : (ca.outputsFun s).steps ≤ ca.time.eval s.length := (ca.outputsFun s).steps_le_m
    have ha : a.length ≤ Ap.eval s.length := by
      have h1 := output_length_le arg ca s
      have h2 : maxPush Ma * (ca.outputsFun s).steps ≤ maxPush Ma * ca.time.eval s.length :=
        Nat.mul_le_mul_left _ hsa
      simp only [Ap, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X]
      dsimp only [Ma, a] at h2 ⊢
      omega
    have hloop : ∀ r i : ℕ, i + r = n →
        ∃ t, t ≤ r * (2 * a.length + 2 * n + SPp.eval s.length + 6) +
            (Poutp.eval s.length + a.length + 2 * n + 6) ∧
          (flip bind (TM2.step prog))^[t]
            (some ⟨some (lbl Mc Ma Mp ⟨5, by decide⟩),
              (Mc.initialState, Ma.initialState, Mp.initialState, none),
              mstk (fun _ => []) (fun _ => []) (fun _ => [])
                [] [] (List.replicate r true) a.reverse [] (List.replicate i true)⟩) =
          some (haltList M (List.replicate (findFrom q i r) true)) := by
      intro r
      induction r with
      | zero =>
        intro i hir
        have q5 : TM2.step prog
            ⟨some (lbl Mc Ma Mp ⟨5, by decide⟩),
              (Mc.initialState, Ma.initialState, Mp.initialState, none),
              mstk (fun _ => []) (fun _ => []) (fun _ => [])
                [] [] (List.replicate 0 true) a.reverse [] (List.replicate i true)⟩ =
            some ⟨some (lbl Mc Ma Mp ⟨13, by decide⟩),
              (Mc.initialState, Ma.initialState, Mp.initialState, none),
              mstk (fun _ => []) (fun _ => []) (fun _ => [])
                [] [] [] a.reverse [] (List.replicate i true)⟩ := by
          simp only [prog, TM2.step, mainProg, extraProg, TM2.stepAux, mstk, mstk_set_R,
            List.replicate_zero, List.head?_nil, List.tail_nil, Option.isSome_none]
          rfl
        have q13 := loop13 e0c e0a e1a e0p
          Mc.initialState Ma.initialState Mp.initialState
          (fun _ => []) (fun _ => []) (fun _ => [])
          [] [] [] [] (List.replicate i true) a.reverse none
        have q14 := loop14 e0c e0a e1a e0p
          Mc.initialState Ma.initialState Mp.initialState
          (fun _ => []) (fun _ => []) (fun _ => [])
          [] [] [] [] i 0 none
        simp only [List.replicate_zero, Nat.add_zero] at q14
        have hrun := iter_step (TM2.step prog) q5 (iter_trans _ q13 q14)
        rw [mstk_nil_O] at hrun
        refine ⟨a.reverse.length + 1 + (i + 1) + 1, ?_, ?_⟩
        · simp only [List.length_reverse]
          omega
        · refine hrun.trans ?_
          exact (congrArg some (haltList_eq M (List.replicate i true))).symm
      | succ r ih =>
        intro i hir
        let xi : List Bool := List.replicate i true ++ false :: (List.replicate i true ++ a)
        have hxi_len : xi.length ≤ Xp.eval s.length := by
          simp only [xi, Xp, List.length_append, List.length_cons, List.length_replicate,
            Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
          omega
        have hspi : (cp.outputsFun xi).steps ≤ SPp.eval s.length := by
          have h1 := (cp.outputsFun xi).steps_le_m
          have h2 := eval_mono cp.time hxi_len
          rw [← Polynomial.eval_comp] at h2
          exact h1.trans h2
        have hpout : (p xi).length ≤ Poutp.eval s.length := by
          have h1 := output_length_le p cp xi
          have h2 : maxPush Mp * (cp.outputsFun xi).steps ≤ maxPush Mp * SPp.eval s.length :=
            Nat.mul_le_mul_left _ hspi
          simp only [Poutp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
          dsimp only [Mp] at h2 ⊢
          omega
        have q5 : TM2.step prog
            ⟨some (lbl Mc Ma Mp ⟨5, by decide⟩),
              (Mc.initialState, Ma.initialState, Mp.initialState, none),
              mstk (fun _ => []) (fun _ => []) (fun _ => [])
                [] [] (List.replicate (r + 1) true) a.reverse [] (List.replicate i true)⟩ =
            some ⟨some (lbl Mc Ma Mp ⟨6, by decide⟩),
              (Mc.initialState, Ma.initialState, Mp.initialState, some true),
              mstk (fun _ => []) (fun _ => []) (fun _ => [])
                [] [] (List.replicate r true) a.reverse [] (List.replicate i true)⟩ := by
          simp only [prog, TM2.step, mainProg, extraProg, TM2.stepAux, mstk, mstk_set_R,
            List.replicate_succ, List.head?_cons, List.tail_cons, Option.isSome_some]
          rfl
        have huMp0 : Function.update (fun _ => [] : ∀ k, List (Mp.Γ k)) Mp.k₀ [] = fun _ => [] := by
          funext k
          by_cases h : k = Mp.k₀ <;> simp [h]
        have q6 := loop6 e0c e0a e1a e0p
          Mc.initialState Ma.initialState Mp.initialState
          (fun _ => []) (fun _ => [])
          [] [] (List.replicate r true) (List.replicate i true) a.reverse [] [] (some true)
        rw [huMp0, List.reverse_reverse, List.append_nil, List.append_nil] at q6
        have q7 := loop7 e0c e0a e1a e0p
          Mc.initialState Ma.initialState Mp.initialState
          (fun _ => []) (fun _ => []) (Function.update (fun _ => []) Mp.k₀ (a.map e0p))
          [] [] (List.replicate r true) (List.replicate i true) a [] none
        rw [List.append_nil] at q7
        have q8 := loop8 e0c e0a e1a e0p
          Mc.initialState Ma.initialState Mp.initialState
          (fun _ => []) (fun _ => [])
          [] [] (List.replicate r true) a.reverse i 0 (a.map e0p) none
        simp only [List.replicate_zero, Nat.add_zero] at q8
        have q9 := loop9 e0c e0a e1a e0p
          Mc.initialState Ma.initialState Mp.initialState
          (fun _ => []) (fun _ => [])
          [] [] (List.replicate r true) a.reverse i 0
          (e0p false :: (List.replicate i (e0p true) ++ a.map e0p)) none
        simp only [List.replicate_zero, Nat.add_zero] at q9
        have hxi_map : List.replicate i (e0p true) ++
            e0p false :: (List.replicate i (e0p true) ++ a.map e0p) = xi.map e0p := by
          simp [xi, List.map_append, List.map_cons, List.map_replicate]
        rw [hxi_map] at q9
        have hsimP : (flip bind (TM2.step prog))^[(cp.outputsFun xi).steps]
            (some (embP Mc.initialState Ma.initialState none (fun _ => []) (fun _ => [])
              [] [] (List.replicate r true) a.reverse [] (List.replicate i true)
              ⟨some Mp.main, Mp.initialState, Function.update (fun _ => []) Mp.k₀ (xi.map e0p)⟩)) =
            some (embP Mc.initialState Ma.initialState none (fun _ => []) (fun _ => [])
              [] [] (List.replicate r true) a.reverse [] (List.replicate i true)
              ⟨none, Mp.initialState,
                Function.update (fun _ => []) Mp.k₁ ((p xi).map cp.outputAlphabet.invFun)⟩) := by
          have h0 := simulate (TM2.step Mp.m) (TM2.step prog)
            (embP Mc.initialState Ma.initialState none (fun _ => []) (fun _ => [])
              [] [] (List.replicate r true) a.reverse [] (List.replicate i true))
            (stepP e0c e0a e1a e0p Mc.initialState Ma.initialState none
              (fun _ => []) (fun _ => [])
              [] [] (List.replicate r true) a.reverse [] (List.replicate i true))
            (cp.outputsFun xi).steps _ _ (cp.outputsFun xi).evals_in_steps
          generalize (cp.outputsFun xi).steps = st at h0 ⊢
          rw [initList_eq, haltList_eq] at h0
          exact h0
        have qprep := iter_step (TM2.step prog) q5
          (iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ q6 q7) q8) q9) hsimP)
        cases hpxi : p xi with
        | nil =>
          have hqi : q i = false := by simp [q, xi, hpxi]
          have hfind : findFrom q i (r + 1) = findFrom q (i + 1) r := by
            simp [findFrom, hqi]
          have q10 : TM2.step prog
              (embP Mc.initialState Ma.initialState none (fun _ => []) (fun _ => [])
                [] [] (List.replicate r true) a.reverse [] (List.replicate i true)
                ⟨none, Mp.initialState,
                  Function.update (fun _ => []) Mp.k₁ ((p xi).map cp.outputAlphabet.invFun)⟩) =
              some ⟨some (lbl Mc Ma Mp ⟨5, by decide⟩),
                (Mc.initialState, Ma.initialState, Mp.initialState, none),
                mstk (fun _ => []) (fun _ => []) (fun _ => [])
                  [] [] (List.replicate r true) a.reverse [] (List.replicate (i + 1) true)⟩ := by
            have huMp1 : Function.update (fun _ => [] : ∀ k, List (Mp.Γ k)) Mp.k₁ [] = fun _ => [] := by
              funext k
              by_cases h : k = Mp.k₁ <;> simp [h]
            simp only [embP, Option.elim, hpxi, List.map_nil, huMp1, prog, TM2.step, mainProg,
              extraProg, TM2.stepAux, mstk, mstk_set_p, mstk_set_C, List.head?_nil, List.tail_nil,
              Option.map_none, Option.isSome_none, List.replicate_succ]
            rfl
          obtain ⟨t', ht', hrun'⟩ := ih (i + 1) (by omega)
          have hstep10 := iter_step (TM2.step prog) q10 hrun'
          have htot := iter_trans _ qprep hstep10
          rw [hfind]
          refine ⟨_, ?_, htot⟩
          simp only [List.length_reverse]
          have hmul : (r + 1) * (2 * a.length + 2 * n + SPp.eval s.length + 6) =
              r * (2 * a.length + 2 * n + SPp.eval s.length + 6) +
              (2 * a.length + 2 * n + SPp.eval s.length + 6) := by
            ring
          omega
        | cons b rest =>
          have hqi : q i = true := by simp [q, xi, hpxi]
          have hfind : findFrom q i (r + 1) = i := by
            simp [findFrom, hqi]
          have q10 : TM2.step prog
              (embP Mc.initialState Ma.initialState none (fun _ => []) (fun _ => [])
                [] [] (List.replicate r true) a.reverse [] (List.replicate i true)
                ⟨none, Mp.initialState,
                  Function.update (fun _ => []) Mp.k₁ ((p xi).map cp.outputAlphabet.invFun)⟩) =
              some ⟨some (lbl Mc Ma Mp ⟨11, by decide⟩),
                (Mc.initialState, Ma.initialState, Mp.initialState, some true),
                mstk (fun _ => []) (fun _ => [])
                  (Function.update (fun _ => []) Mp.k₁ (rest.map cp.outputAlphabet.invFun))
                  [] [] (List.replicate r true) a.reverse [] (List.replicate i true)⟩ := by
            simp only [embP, Option.elim, hpxi, List.map_cons, prog, TM2.step, mainProg, extraProg,
              TM2.stepAux, mstk, mstk_set_p, Function.update_self, Function.update_idem,
              List.head?_cons, List.tail_cons, Option.map_some, Option.isSome_some]
            rfl
          have q11 := loop11 e0c e0a e1a e0p
            Mc.initialState Ma.initialState Mp.initialState
            (fun _ => []) (fun _ => [])
            [] [] (List.replicate r true) a.reverse [] (List.replicate i true)
            (rest.map cp.outputAlphabet.invFun) (some true)
          have q12 := loop12 e0c e0a e1a e0p
            Mc.initialState Ma.initialState Mp.initialState
            (fun _ => []) (fun _ => []) (fun _ => [])
            [] [] a.reverse [] (List.replicate i true) (List.replicate r true) none
          have q13 := loop13 e0c e0a e1a e0p
            Mc.initialState Ma.initialState Mp.initialState
            (fun _ => []) (fun _ => []) (fun _ => [])
            [] [] [] [] (List.replicate i true) a.reverse none
          have q14 := loop14 e0c e0a e1a e0p
            Mc.initialState Ma.initialState Mp.initialState
            (fun _ => []) (fun _ => []) (fun _ => [])
            [] [] [] [] i 0 none
          simp only [List.replicate_zero, Nat.add_zero] at q14
          have hclean := iter_step (TM2.step prog) q10
            (iter_trans _ (iter_trans _ (iter_trans _ q11 q12) q13) q14)
          rw [mstk_nil_O] at hclean
          have htot := iter_trans _ qprep hclean
          rw [hfind]
          refine ⟨_, ?_, htot.trans (congrArg some (haltList_eq M (List.replicate i true))).symm⟩
          simp only [List.length_reverse, List.length_map, List.length_replicate]
          have hrest : rest.length ≤ Poutp.eval s.length := by
            rw [hpxi, List.length_cons] at hpout
            omega
          have hmul : 2 * a.length + 2 * n + SPp.eval s.length + 6 ≤
              (r + 1) * (2 * a.length + 2 * n + SPp.eval s.length + 6) := by
            exact Nat.le_mul_of_pos_left _ (Nat.succ_pos r)
          omega
    have q0 := loop0 e0c e0a e1a e0p
      Mc.initialState Ma.initialState Mp.initialState
      (fun _ => []) (fun _ => []) (fun _ => [])
      [] [] [] s [] [] none
    rw [List.append_nil, mstk_nil_I] at q0
    have q0' : (flip bind (TM2.step prog))^[s.length + 1] (some (initList M s)) =
        some ⟨some (lbl Mc Ma Mp ⟨1, by decide⟩),
          (Mc.initialState, Ma.initialState, Mp.initialState, none),
          mstk (fun _ => []) (fun _ => []) (fun _ => []) [] [] [] s.reverse s.reverse []⟩ :=
      (congrArg (fun c => (flip bind (TM2.step prog))^[s.length + 1] (some c))
        (initList_eq M s)).trans q0
    have huMc0 : Function.update (fun _ => [] : ∀ k, List (Mc.Γ k)) Mc.k₀ [] = fun _ => [] := by
      funext k
      by_cases h : k = Mc.k₀ <;> simp [h]
    have q1 := loop1 e0c e0a e1a e0p
      Mc.initialState Ma.initialState Mp.initialState
      (fun _ => []) (fun _ => [])
      [] [] [] s.reverse [] s.reverse [] none
    rw [huMc0, List.reverse_reverse, List.append_nil] at q1
    have hsimC : (flip bind (TM2.step prog))^[(cc.outputsFun s).steps]
        (some (embC Ma.initialState Mp.initialState none (fun _ => []) (fun _ => [])
          [] [] [] s.reverse [] []
          ⟨some Mc.main, Mc.initialState, Function.update (fun _ => []) Mc.k₀ (s.map e0c)⟩)) =
        some (embC Ma.initialState Mp.initialState none (fun _ => []) (fun _ => [])
          [] [] [] s.reverse [] []
          ⟨none, Mc.initialState,
            Function.update (fun _ => []) Mc.k₁ ((cnt s).map cc.outputAlphabet.invFun)⟩) := by
      have h0 := simulate (TM2.step Mc.m) (TM2.step prog)
        (embC Ma.initialState Mp.initialState none (fun _ => []) (fun _ => [])
          [] [] [] s.reverse [] [])
        (stepC e0c e0a e1a e0p Ma.initialState Mp.initialState none
          (fun _ => []) (fun _ => []) [] [] [] s.reverse [] [])
        (cc.outputsFun s).steps _ _ (cc.outputsFun s).evals_in_steps
      generalize (cc.outputsFun s).steps = st at h0 ⊢
      rw [initList_eq, haltList_eq] at h0
      exact h0
    have q2 := loop2 e0c e0a e1a e0p
      Mc.initialState Ma.initialState Mp.initialState
      (fun _ => []) (fun _ => [])
      [] [] s.reverse [] [] ((cnt s).map cc.outputAlphabet.invFun) 0 none
    simp only [List.replicate_zero, List.length_map, Nat.add_zero] at q2
    have huMa0 : Function.update (fun _ => [] : ∀ k, List (Ma.Γ k)) Ma.k₀ [] = fun _ => [] := by
      funext k
      by_cases h : k = Ma.k₀ <;> simp [h]
    have q3 := loop3 e0c e0a e1a e0p
      Mc.initialState Ma.initialState Mp.initialState
      (fun _ => []) (fun _ => [])
      [] [] (List.replicate n true) [] [] s.reverse [] none
    rw [huMa0, List.reverse_reverse, List.append_nil] at q3
    have hsimA : (flip bind (TM2.step prog))^[(ca.outputsFun s).steps]
        (some (embA Mc.initialState Mp.initialState none (fun _ => []) (fun _ => [])
          [] [] (List.replicate n true) [] [] []
          ⟨some Ma.main, Ma.initialState, Function.update (fun _ => []) Ma.k₀ (s.map e0a)⟩)) =
        some (embA Mc.initialState Mp.initialState none (fun _ => []) (fun _ => [])
          [] [] (List.replicate n true) [] [] []
          ⟨none, Ma.initialState,
            Function.update (fun _ => []) Ma.k₁ ((arg s).map ca.outputAlphabet.invFun)⟩) := by
      have h0 := simulate (TM2.step Ma.m) (TM2.step prog)
        (embA Mc.initialState Mp.initialState none (fun _ => []) (fun _ => [])
          [] [] (List.replicate n true) [] [] [])
        (stepA e0c e0a e1a e0p Mc.initialState Mp.initialState none
          (fun _ => []) (fun _ => []) [] [] (List.replicate n true) [] [] [])
        (ca.outputsFun s).steps _ _ (ca.outputsFun s).evals_in_steps
      generalize (ca.outputsFun s).steps = st at h0 ⊢
      rw [initList_eq, haltList_eq] at h0
      exact h0
    have q4 := loop4 e0c e0a e1a e0p
      Mc.initialState Ma.initialState Mp.initialState
      (fun _ => []) (fun _ => [])
      [] [] (List.replicate n true) [] [] ((arg s).map ca.outputAlphabet.invFun) [] none
    have hma_map : ((arg s).map ca.outputAlphabet.invFun).map e1a = a := by
      dsimp only [a]
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (arg s)]
      exact List.map_congr_left fun y _ => ca.outputAlphabet.right_inv y
    rw [hma_map, List.append_nil] at q4
    obtain ⟨t, ht, hrunLoop⟩ := hloop n 0 (Nat.zero_add n)
    simp only [List.replicate_zero] at hrunLoop
    have hfull := iter_trans _
      (iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _
        q0' q1) hsimC) q2) q3) hsimA) q4) hrunLoop
    rw [findFrom_zero q n]
    refine ⟨_, ?_, hfull⟩
    simp only [List.length_reverse, List.length_map]
    have hmul1 : n * (2 * a.length + 2 * n + SPp.eval s.length + 6) ≤
        Np.eval s.length * (2 * Ap.eval s.length + 2 * Np.eval s.length + SPp.eval s.length + 6) :=
      Nat.mul_le_mul hn (by omega)
    simp only [T, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
    dsimp only [n, a] at hn ha hmul1 ht ⊢
    omega
  exact ⟨{
    tm := M
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := T
    outputsFun := fun s =>
      { steps := Classical.choose (key s)
        evals_in_steps := by
          have hm : ∀ l : List Bool, List.map (Equiv.refl Bool).invFun l = l := fun l => by simp
          exact (congrArg (fun l => (flip bind (TM2.step prog))^[Classical.choose (key s)]
            (some (initList M l))) (hm s)).trans ((Classical.choose_spec (key s)).2.trans
            (congrArg (fun l => some (haltList M l)) (hm _).symm))
        steps_le_m := (Classical.choose_spec (key s)).1 } }⟩

end PEqualNP.Outside
