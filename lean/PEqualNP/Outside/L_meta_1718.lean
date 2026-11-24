import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1718

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run {α : Type} (f : Gate → List α → α) (gs : List Gate) (init : List α) : List α :=
  gs.foldl (fun acc g => acc ++ [f g acc]) init

theorem run_snoc {α : Type} (f : Gate → List α → α) (gs : List Gate) (g : Gate) (init : List α) :
    run f (gs ++ [g]) init = run f gs init ++ [f g (run f gs init)] := by
  simp [run, List.foldl_append]

theorem run_app {α : Type} (f : Gate → List α → α) (as bs : List Gate) (init : List α) :
    run f (as ++ bs) init = run f bs (run f as init) := by
  simp [run, List.foldl_append]

theorem run_len {α : Type} (f : Gate → List α → α) (gs : List Gate) (init : List α) :
    (run f gs init).length = init.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem run_pre {α : Type} (f : Gate → List α → α) (bs : List Gate) (init : List α) :
    ∃ t, run f bs init = init ++ t := by
  induction bs using List.reverseRecOn with
  | nil => exact ⟨[], by simp [run]⟩
  | append_singleton bs g ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨t ++ [f g (run f bs init)], ?_⟩
    rw [run_snoc, ← List.append_assoc, ← ht]

theorem run_stab {α : Type} (f : Gate → List α → α) (pre suf : List Gate) (init : List α) (d : α)
    (i : ℕ) (hi : i < init.length + pre.length) :
    (run f (pre ++ suf) init).getD i d = (run f pre init).getD i d := by
  rw [run_app]
  obtain ⟨t, ht⟩ := run_pre f suf (run f pre init)
  rw [ht, List.getD_append _ _ _ _ (by rw [run_len]; exact hi)]

theorem stab2 {α : Type} (f : Gate → List α → α) (gs pre : List Gate) (g : Gate) (suf : List Gate)
    (h : gs = pre ++ g :: suf) (init : List α) (d : α) (i : ℕ)
    (hi : i < init.length + pre.length) :
    (run f gs init).getD i d = (run f pre init).getD i d := by
  subst h
  exact run_stab f pre (g :: suf) init d i hi

theorem run_last {α : Type} (f : Gate → List α → α) (gs : List Gate) (g : Gate) (init : List α)
    (d : α) : (run f (gs ++ [g]) init).getD (init.length + gs.length) d = f g (run f gs init) := by
  rw [run_snoc, List.getD_append_right _ _ _ _ (by rw [run_len]), run_len, Nat.sub_self,
    List.getD_cons_zero]

def evf (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def dgf (g : Gate) (d : List ℕ) : ℕ := g.lineDegree d

def ini (n : ℕ) (M : Finset ℕ) : List ℕ := (List.range n).map fun i => if i ∈ M then 1 else 0

theorem ini_len (n : ℕ) (M : Finset ℕ) : (ini n M).length = n := by simp [ini]

theorem ev_and (g : Gate) (w : List Bool) (a b : ℕ) (ho : g.op = GateOp.and)
    (hi : g.inputs = [a, b]) : evf g w = (w.getD a false && w.getD b false) := by
  unfold evf; rw [ho, hi]; simp [GateOp.eval]

theorem ev_or (g : Gate) (w : List Bool) (a b : ℕ) (ho : g.op = GateOp.or)
    (hi : g.inputs = [a, b]) : evf g w = (w.getD a false || w.getD b false) := by
  unfold evf; rw [ho, hi]; simp [GateOp.eval]

theorem dg_and (g : Gate) (d : List ℕ) (a b : ℕ) (ho : g.op = GateOp.and)
    (hi : g.inputs = [a, b]) : dgf g d = d.getD a 0 + d.getD b 0 := by
  unfold dgf Gate.lineDegree
  rw [if_pos ho, hi]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

theorem dg_or (g : Gate) (d : List ℕ) (a b : ℕ) (ho : g.op = GateOp.or)
    (hi : g.inputs = [a, b]) : dgf g d = max (d.getD a 0) (d.getD b 0) := by
  have hne : ¬ g.op = GateOp.and := by rw [ho]; intro h; cases h
  unfold dgf Gate.lineDegree
  rw [if_neg hne, hi]
  simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
  omega

def P (n : ℕ) (iL iP : List ℕ) (pre : List Gate) (g : Gate) : Prop :=
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
  (∀ i ∈ g.inputs, i < n + pre.length) ∧
  (g.op = GateOp.and → (∃ i ∈ g.inputs, (run dgf pre iL).getD i 0 = 0) ∨
    (∀ h ∈ g.inputs, (run dgf pre iP).getD h 0 = 0))

def Good (n : ℕ) (iL iP : List ℕ) (gs : List Gate) : Prop :=
  ∀ (pre : List Gate) (g : Gate) (suf : List Gate), gs = pre ++ g :: suf → P n iL iP pre g

theorem Good_snoc_inv (n : ℕ) (iL iP : List ℕ) (gs : List Gate) (g : Gate)
    (H : Good n iL iP (gs ++ [g])) : Good n iL iP gs ∧ P n iL iP gs g := by
  refine ⟨?_, H gs g [] rfl⟩
  intro pre g' suf h
  exact H pre g' (suf ++ [g]) (by rw [h]; simp)

theorem Good_snoc (n : ℕ) (iL iP : List ℕ) (es : List Gate) (e : Gate)
    (hG : Good n iL iP es) (hP : P n iL iP es e) : Good n iL iP (es ++ [e]) := by
  intro pre g suf h
  rcases List.eq_nil_or_concat' suf with hs | ⟨s, a, hs⟩
  · subst hs
    obtain ⟨h1, h2⟩ := List.append_inj' h rfl
    have h3 : e = g := by simpa using h2
    subst h1; subst h3; exact hP
  · subst hs
    have h' : es ++ [e] = (pre ++ g :: s) ++ [a] := by rw [h]; simp
    obtain ⟨h1, _⟩ := List.append_inj' h' rfl
    exact hG pre g s h1

theorem dec (gs : List Gate) : ∀ (j : ℕ), j < gs.length →
    ∃ pre suf, gs = pre ++ gs.getD j ⟨GateOp.or, []⟩ :: suf ∧ pre.length = j := by
  induction gs with
  | nil => intro j hj; simp at hj
  | cons a t ih =>
    intro j hj
    cases j with
    | zero => exact ⟨[], t, rfl, rfl⟩
    | succ j =>
      obtain ⟨p, s, h1, h2⟩ := ih j (by simpa using hj)
      refine ⟨a :: p, s, ?_, by simp [h2]⟩
      rw [List.getD_cons_succ, List.cons_append]
      exact congrArg (List.cons a) h1

def Rel {ι : Type} (n : ℕ) (r f : ι → List Bool) (iL iP : List ℕ) (gs es : List Gate)
    (w : ℕ) : Prop :=
  (∃ b : Bool, ∀ p, (run evf gs (r p)).getD w false = b) ∨
  (∃ k, k < n + es.length ∧
    (∀ p, (run evf es (f p)).getD k false = (run evf gs (r p)).getD w false) ∧
    (run dgf es iL).getD k 0 ≤ (run dgf gs iL).getD w 0 ∧
    (run dgf es iP).getD k 0 ≤ (run dgf gs iP).getD w 0)

theorem Rel_extD {ι : Type} (n : ℕ) (r f : ι → List Bool) (iL iP : List ℕ)
    (hr : ∀ p, (r p).length = n) (hiL : iL.length = n) (hiP : iP.length = n)
    (gs es : List Gate) (g : Gate) (w : ℕ) (hw : w < n + gs.length)
    (h : Rel n r f iL iP gs es w) : Rel n r f iL iP (gs ++ [g]) es w := by
  have e1 : ∀ p, (run evf (gs ++ [g]) (r p)).getD w false = (run evf gs (r p)).getD w false :=
    fun p => run_stab evf gs [g] (r p) false w (by rw [hr]; exact hw)
  have e2 : (run dgf (gs ++ [g]) iL).getD w 0 = (run dgf gs iL).getD w 0 :=
    run_stab dgf gs [g] iL 0 w (by rw [hiL]; exact hw)
  have e3 : (run dgf (gs ++ [g]) iP).getD w 0 = (run dgf gs iP).getD w 0 :=
    run_stab dgf gs [g] iP 0 w (by rw [hiP]; exact hw)
  rcases h with ⟨b, hb⟩ | ⟨k, hk, hv, h1, h2⟩
  · exact Or.inl ⟨b, fun p => by rw [e1]; exact hb p⟩
  · exact Or.inr ⟨k, hk, fun p => by rw [e1]; exact hv p, by rw [e2]; exact h1,
      by rw [e3]; exact h2⟩

theorem Rel_extE {ι : Type} (n : ℕ) (r f : ι → List Bool) (iL iP : List ℕ)
    (hf : ∀ p, (f p).length = n) (hiL : iL.length = n) (hiP : iP.length = n)
    (gs es : List Gate) (e : Gate) (w : ℕ)
    (h : Rel n r f iL iP gs es w) : Rel n r f iL iP gs (es ++ [e]) w := by
  rcases h with ⟨b, hb⟩ | ⟨k, hk, hv, h1, h2⟩
  · exact Or.inl ⟨b, hb⟩
  · refine Or.inr ⟨k, by rw [List.length_append]; omega, fun p => ?_, ?_, ?_⟩
    · rw [run_stab evf es [e] (f p) false k (by rw [hf]; exact hk)]; exact hv p
    · rw [run_stab dgf es [e] iL 0 k (by rw [hiL]; exact hk)]; exact h1
    · rw [run_stab dgf es [e] iP 0 k (by rw [hiP]; exact hk)]; exact h2

theorem last_const {ι : Type} (n : ℕ) (r f : ι → List Bool) (iL iP : List ℕ)
    (hr : ∀ p, (r p).length = n) (gs es : List Gate) (g : Gate) (b : Bool)
    (h : ∀ p, evf g (run evf gs (r p)) = b) :
    Rel n r f iL iP (gs ++ [g]) es (n + gs.length) := by
  refine Or.inl ⟨b, fun p => ?_⟩
  have e := run_last evf gs g (r p) false
  rw [hr] at e
  rw [e]; exact h p

theorem last_copy {ι : Type} (n : ℕ) (r f : ι → List Bool) (iL iP : List ℕ)
    (hr : ∀ p, (r p).length = n) (hiL : iL.length = n) (hiP : iP.length = n)
    (gs es : List Gate) (g : Gate) (c : ℕ)
    (hc : Rel n r f iL iP gs es c)
    (hv : ∀ p, evf g (run evf gs (r p)) = (run evf gs (r p)).getD c false)
    (h1 : (run dgf gs iL).getD c 0 ≤ dgf g (run dgf gs iL))
    (h2 : (run dgf gs iP).getD c 0 ≤ dgf g (run dgf gs iP)) :
    Rel n r f iL iP (gs ++ [g]) es (n + gs.length) := by
  have e1 : ∀ p, (run evf (gs ++ [g]) (r p)).getD (n + gs.length) false
      = evf g (run evf gs (r p)) := by
    intro p
    have e := run_last evf gs g (r p) false
    rw [hr] at e; exact e
  have e2 : (run dgf (gs ++ [g]) iL).getD (n + gs.length) 0 = dgf g (run dgf gs iL) := by
    have e := run_last dgf gs g iL 0
    rw [hiL] at e; exact e
  have e3 : (run dgf (gs ++ [g]) iP).getD (n + gs.length) 0 = dgf g (run dgf gs iP) := by
    have e := run_last dgf gs g iP 0
    rw [hiP] at e; exact e
  rcases hc with ⟨b, hb⟩ | ⟨k, hk, hkv, k1, k2⟩
  · exact Or.inl ⟨b, fun p => by rw [e1, hv, hb]⟩
  · exact Or.inr ⟨k, hk, fun p => by rw [e1, hv, hkv], by rw [e2]; exact le_trans k1 h1,
      by rw [e3]; exact le_trans k2 h2⟩

theorem last_new {ι : Type} (n : ℕ) (r f : ι → List Bool) (iL iP : List ℕ)
    (hr : ∀ p, (r p).length = n) (hf : ∀ p, (f p).length = n)
    (hiL : iL.length = n) (hiP : iP.length = n)
    (gs es : List Gate) (g e : Gate)
    (hv : ∀ p, evf e (run evf es (f p)) = evf g (run evf gs (r p)))
    (h1 : dgf e (run dgf es iL) ≤ dgf g (run dgf gs iL))
    (h2 : dgf e (run dgf es iP) ≤ dgf g (run dgf gs iP)) :
    Rel n r f iL iP (gs ++ [g]) (es ++ [e]) (n + gs.length) := by
  refine Or.inr ⟨n + es.length, by rw [List.length_append, List.length_singleton]; omega,
    fun p => ?_, ?_, ?_⟩
  · have a1 := run_last evf gs g (r p) false
    have a2 := run_last evf es e (f p) false
    rw [hr] at a1; rw [hf] at a2
    rw [a1, a2]; exact hv p
  · have a1 := run_last dgf gs g iL 0
    have a2 := run_last dgf es e iL 0
    rw [hiL] at a1 a2
    rw [a1, a2]; exact h1
  · have a1 := run_last dgf gs g iP 0
    have a2 := run_last dgf es e iP 0
    rw [hiP] at a1 a2
    rw [a1, a2]; exact h2

theorem main {ι : Type} (n : ℕ) (r f : ι → List Bool) (iL iP : List ℕ)
    (hr : ∀ p, (r p).length = n) (hf : ∀ p, (f p).length = n)
    (hiL : iL.length = n) (hiP : iP.length = n)
    (hb : ∀ w < n, (∃ b : Bool, ∀ p, (r p).getD w false = b) ∨
      (∀ p, (f p).getD w false = (r p).getD w false)) :
    ∀ gs : List Gate, Good n iL iP gs → ∃ es : List Gate, Good n iL iP es ∧
      es.length ≤ gs.length ∧ ∀ w < n + gs.length, Rel n r f iL iP gs es w := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _
    refine ⟨[], ?_, le_refl _, ?_⟩
    · intro pre g suf h
      simp at h
    · intro w hw
      have hw' : w < n := by simpa using hw
      rcases hb w hw' with ⟨b, hb'⟩ | he
      · exact Or.inl ⟨b, fun p => hb' p⟩
      · exact Or.inr ⟨w, hw, fun p => he p, le_refl _, le_refl _⟩
  | append_singleton gs g ih =>
    intro HG
    obtain ⟨HGs, ⟨hop, hlen⟩, hrb, hkm⟩ := Good_snoc_inv n iL iP gs g HG
    obtain ⟨es, hE, hle, hrel⟩ := ih HGs
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
    have ha : a < n + gs.length := hrb a (by rw [hab]; simp)
    have hb2 : b < n + gs.length := hrb b (by rw [hab]; simp)
    have Ra := hrel a ha
    have Rb := hrel b hb2
    have old : ∀ es' : List Gate, (∀ w < n + gs.length, Rel n r f iL iP gs es' w) →
        Rel n r f iL iP (gs ++ [g]) es' (n + gs.length) →
        ∀ w < n + (gs ++ [g]).length, Rel n r f iL iP (gs ++ [g]) es' w := by
      intro es' h1 h2 w hw
      rw [List.length_append, List.length_singleton] at hw
      rcases Nat.lt_or_ge w (n + gs.length) with h | h
      · exact Rel_extD n r f iL iP hr hiL hiP gs es' g w h (h1 w h)
      · have hwe : w = n + gs.length := by omega
        rw [hwe]; exact h2
    have keep : Rel n r f iL iP (gs ++ [g]) es (n + gs.length) →
        ∃ es' : List Gate, Good n iL iP es' ∧ es'.length ≤ (gs ++ [g]).length ∧
          ∀ w < n + (gs ++ [g]).length, Rel n r f iL iP (gs ++ [g]) es' w := by
      intro h
      exact ⟨es, hE, by rw [List.length_append, List.length_singleton]; omega, old es hrel h⟩
    rcases hop with hop | hop
    · have hev : ∀ w : List Bool, evf g w = (w.getD a false && w.getD b false) :=
        fun w => ev_and g w a b hop hab
      have hdg : ∀ d : List ℕ, dgf g d = d.getD a 0 + d.getD b 0 :=
        fun d => dg_and g d a b hop hab
      rcases hrel a ha with ⟨ba, hca⟩ | ⟨ka, hka, hva, a1, a2⟩
      · cases ba with
        | false =>
          exact keep (last_const n r f iL iP hr gs es g false
            (fun p => by rw [hev, hca p, Bool.false_and]))
        | true =>
          exact keep (last_copy n r f iL iP hr hiL hiP gs es g b Rb
            (fun p => by rw [hev, hca p, Bool.true_and])
            (by rw [hdg]; omega) (by rw [hdg]; omega))
      · rcases hrel b hb2 with ⟨bb, hcb⟩ | ⟨kb, hkb, hvb, b1, b2⟩
        · cases bb with
          | false =>
            exact keep (last_const n r f iL iP hr gs es g false
              (fun p => by rw [hev, hcb p, Bool.and_false]))
          | true =>
            exact keep (last_copy n r f iL iP hr hiL hiP gs es g a Ra
              (fun p => by rw [hev, hcb p, Bool.and_true])
              (by rw [hdg]; omega) (by rw [hdg]; omega))
        · refine ⟨es ++ [⟨GateOp.and, [ka, kb]⟩], ?_, ?_, ?_⟩
          · apply Good_snoc n iL iP es _ hE
            unfold P
            refine ⟨⟨Or.inl rfl, rfl⟩, ?_, ?_⟩
            · intro i hi
              have hi' : i = ka ∨ i = kb := by simpa using hi
              rcases hi' with h | h
              · rw [h]; exact hka
              · rw [h]; exact hkb
            · intro _
              rcases hkm hop with ⟨i, hi, h0⟩ | hall
              · rw [hab] at hi
                have hi' : i = a ∨ i = b := by simpa using hi
                rcases hi' with h | h
                · rw [h] at h0
                  exact Or.inl ⟨ka, by simp, by omega⟩
                · rw [h] at h0
                  exact Or.inl ⟨kb, by simp, by omega⟩
              · have h0a := hall a (by rw [hab]; simp)
                have h0b := hall b (by rw [hab]; simp)
                refine Or.inr (fun h hh => ?_)
                have hh' : h = ka ∨ h = kb := by simpa using hh
                rcases hh' with e | e
                · rw [e]; omega
                · rw [e]; omega
          · rw [List.length_append, List.length_append, List.length_singleton,
              List.length_singleton]
            omega
          · apply old
            · intro w hw
              exact Rel_extE n r f iL iP hf hiL hiP gs es _ w (hrel w hw)
            · apply last_new n r f iL iP hr hf hiL hiP gs es g _
              · intro p
                rw [hev, ev_and ⟨GateOp.and, [ka, kb]⟩ _ ka kb rfl rfl, hva p, hvb p]
              · rw [hdg, dg_and ⟨GateOp.and, [ka, kb]⟩ _ ka kb rfl rfl]; omega
              · rw [hdg, dg_and ⟨GateOp.and, [ka, kb]⟩ _ ka kb rfl rfl]; omega
    · have hev : ∀ w : List Bool, evf g w = (w.getD a false || w.getD b false) :=
        fun w => ev_or g w a b hop hab
      have hdg : ∀ d : List ℕ, dgf g d = max (d.getD a 0) (d.getD b 0) :=
        fun d => dg_or g d a b hop hab
      rcases hrel a ha with ⟨ba, hca⟩ | ⟨ka, hka, hva, a1, a2⟩
      · cases ba with
        | true =>
          exact keep (last_const n r f iL iP hr gs es g true
            (fun p => by rw [hev, hca p, Bool.true_or]))
        | false =>
          exact keep (last_copy n r f iL iP hr hiL hiP gs es g b Rb
            (fun p => by rw [hev, hca p, Bool.false_or])
            (by rw [hdg]; exact le_max_right _ _) (by rw [hdg]; exact le_max_right _ _))
      · rcases hrel b hb2 with ⟨bb, hcb⟩ | ⟨kb, hkb, hvb, b1, b2⟩
        · cases bb with
          | true =>
            exact keep (last_const n r f iL iP hr gs es g true
              (fun p => by rw [hev, hcb p, Bool.or_true]))
          | false =>
            exact keep (last_copy n r f iL iP hr hiL hiP gs es g a Ra
              (fun p => by rw [hev, hcb p, Bool.or_false])
              (by rw [hdg]; exact le_max_left _ _) (by rw [hdg]; exact le_max_left _ _))
        · refine ⟨es ++ [⟨GateOp.or, [ka, kb]⟩], ?_, ?_, ?_⟩
          · apply Good_snoc n iL iP es _ hE
            unfold P
            refine ⟨⟨Or.inr rfl, rfl⟩, ?_, ?_⟩
            · intro i hi
              have hi' : i = ka ∨ i = kb := by simpa using hi
              rcases hi' with h | h
              · rw [h]; exact hka
              · rw [h]; exact hkb
            · intro h
              cases h
          · rw [List.length_append, List.length_append, List.length_singleton,
              List.length_singleton]
            omega
          · apply old
            · intro w hw
              exact Rel_extE n r f iL iP hf hiL hiP gs es _ w (hrel w hw)
            · apply last_new n r f iL iP hr hf hiL hiP gs es g _
              · intro p
                rw [hev, ev_or ⟨GateOp.or, [ka, kb]⟩ _ ka kb rfl rfl, hva p, hvb p]
              · rw [hdg, dg_or ⟨GateOp.or, [ka, kb]⟩ _ ka kb rfl rfl]; exact max_le_max a1 b1
              · rw [hdg, dg_or ⟨GateOp.or, [ka, kb]⟩ _ ka kb rfl rfl]; exact max_le_max a2 b2

theorem toGood (n : ℕ) (L Pm : Finset ℕ) (C : Circuit)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hrb : NestedCover.ReadsBack n C)
    (hkm : ∀ j < C.gates.length, (NestedCover.gateAt C j).op = GateOp.and →
      (∃ i ∈ (NestedCover.gateAt C j).inputs, (C.lineDegrees n L).getD i 0 = 0) ∨
      (∀ h ∈ (NestedCover.gateAt C j).inputs, (C.lineDegrees n Pm).getD h 0 = 0)) :
    Good n (ini n L) (ini n Pm) C.gates := by
  intro pre g suf h
  have hj : pre.length < C.gates.length := by
    rw [h, List.length_append, List.length_cons]; omega
  have hga : NestedCover.gateAt C pre.length = g := by
    unfold NestedCover.gateAt
    rw [h, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self, List.getD_cons_zero]
  have hin : ∀ i ∈ g.inputs, i < n + pre.length := by
    intro i hi
    exact hrb pre.length hj i (by rw [hga]; exact hi)
  have key : ∀ (M : Finset ℕ) (i : ℕ), i < n + pre.length →
      (C.lineDegrees n M).getD i 0 = (run dgf pre (ini n M)).getD i 0 := by
    intro M i hi
    exact stab2 dgf C.gates pre g suf h (ini n M) 0 i (by rw [ini_len]; exact hi)
  unfold P
  refine ⟨hg g (by rw [h]; simp), hin, ?_⟩
  intro hop
  rcases hkm pre.length hj (by rw [hga]; exact hop) with ⟨i, hi, h0⟩ | hall
  · rw [hga] at hi
    exact Or.inl ⟨i, hi, by rw [← key L i (hin i hi)]; exact h0⟩
  · refine Or.inr (fun i hi => ?_)
    rw [← key Pm i (hin i hi)]
    exact hall i (by rw [hga]; exact hi)

theorem fromGood (n : ℕ) (L Pm : Finset ℕ) (es : List Gate) (o : ℕ)
    (H : Good n (ini n L) (ini n Pm) es) :
    ((∀ g ∈ (Circuit.mk es o).gates,
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
      NestedCover.ReadsBack n (Circuit.mk es o)) ∧
    (∀ j < (Circuit.mk es o).gates.length,
      (NestedCover.gateAt (Circuit.mk es o) j).op = GateOp.and →
      (∃ i ∈ (NestedCover.gateAt (Circuit.mk es o) j).inputs,
        ((Circuit.mk es o).lineDegrees n L).getD i 0 = 0) ∨
      (∀ h ∈ (NestedCover.gateAt (Circuit.mk es o) j).inputs,
        ((Circuit.mk es o).lineDegrees n Pm).getD h 0 = 0)) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro g hg
    obtain ⟨s, t, h⟩ := List.append_of_mem hg
    obtain ⟨hA, _, _⟩ := H s g t h
    exact hA
  · intro j hj i hi
    obtain ⟨pre, suf, h1, h2⟩ := dec es j hj
    obtain ⟨_, hB, _⟩ := H pre _ suf h1
    have hlt := hB i hi
    rw [h2] at hlt; exact hlt
  · intro j hj hop
    obtain ⟨pre, suf, h1, h2⟩ := dec es j hj
    obtain ⟨_, hB, hC⟩ := H pre _ suf h1
    have key : ∀ (M : Finset ℕ) (i : ℕ), i < n + pre.length →
        ((Circuit.mk es o).lineDegrees n M).getD i 0 = (run dgf pre (ini n M)).getD i 0 := by
      intro M i hi
      exact stab2 dgf es pre _ suf h1 (ini n M) 0 i (by rw [ini_len]; exact hi)
    rcases hC hop with ⟨i, hi, h0⟩ | hall
    · exact Or.inl ⟨i, hi, by rw [key L i (hB i hi)]; exact h0⟩
    · exact Or.inr (fun i hi => by rw [key Pm i (hB i hi)]; exact hall i hi)

theorem ofFn_getD {m : ℕ} (x : Fin m → Bool) (i : ℕ) (hi : i < m) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

def rI (N : ℕ) (S W : Finset (Fin N)) (nu : Fin N → Bool)
    (p : (Fin N → Bool) × (Fin N → Bool)) : List Bool :=
  List.ofFn (Fin.append (fun u => decide (u ∈ S) && p.1 u) (fun t => if t ∈ W then p.2 t else nu t))

def fI (N : ℕ) (p : (Fin N → Bool) × (Fin N → Bool)) : List Bool :=
  List.ofFn (Fin.append p.1 p.2)

theorem base (N : ℕ) (S W : Finset (Fin N)) (nu : Fin N → Bool) :
    ∀ w < N + N, (∃ b : Bool, ∀ p, (rI N S W nu p).getD w false = b) ∨
      (∀ p, (fI N p).getD w false = (rI N S W nu p).getD w false) := by
  intro w hw
  have key : ∀ v : Fin (N + N),
      (∃ b : Bool, ∀ p : (Fin N → Bool) × (Fin N → Bool),
        Fin.append (fun u => decide (u ∈ S) && p.1 u)
          (fun t => if t ∈ W then p.2 t else nu t) v = b) ∨
      (∀ p : (Fin N → Bool) × (Fin N → Bool),
        Fin.append p.1 p.2 v = Fin.append (fun u => decide (u ∈ S) && p.1 u)
          (fun t => if t ∈ W then p.2 t else nu t) v) := by
    intro v
    refine Fin.addCases (fun i => ?_) (fun i => ?_) v
    · by_cases hi : i ∈ S
      · refine Or.inr (fun p => ?_)
        rw [Fin.append_left, Fin.append_left]
        simp [hi]
      · refine Or.inl ⟨false, fun p => ?_⟩
        rw [Fin.append_left]
        simp [hi]
    · by_cases hi : i ∈ W
      · refine Or.inr (fun p => ?_)
        rw [Fin.append_right, Fin.append_right]
        simp [hi]
      · refine Or.inl ⟨nu i, fun p => ?_⟩
        rw [Fin.append_right]
        simp [hi]
  rcases key ⟨w, hw⟩ with ⟨b, hb⟩ | he
  · refine Or.inl ⟨b, fun p => ?_⟩
    unfold rI
    rw [ofFn_getD _ w hw]
    exact hb p
  · refine Or.inr (fun p => ?_)
    unfold rI fI
    rw [ofFn_getD _ w hw, ofFn_getD _ w hw]
    exact he p

theorem rI_len (N : ℕ) (S W : Finset (Fin N)) (nu : Fin N → Bool)
    (p : (Fin N → Bool) × (Fin N → Bool)) : (rI N S W nu p).length = N + N := by
  simp [rI]

theorem fI_len (N : ℕ) (p : (Fin N → Bool) × (Fin N → Bool)) : (fI N p).length = N + N := by
  simp [fI]

theorem ev_oob (D : Circuit) (n : ℕ) (ho : n + D.gates.length ≤ D.output) (z : List Bool)
    (hz : z.length = n) : D.eval z = false := by
  show (run evf D.gates z).getD D.output false = false
  apply List.getD_eq_default
  rw [run_len, hz]; exact ho

end PEqualNP.Outside.L_meta_1718

theorem PEqualNP.Outside.L_meta_1718 : ∀ (N121 : ℕ) (D121 : PEqualNP.CircuitLowerBounds.Circuit) (S121 W121 : Finset (Fin N121)) (nu121 : Fin N121 → Bool), (∀ g121 ∈ D121.gates, (g121.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g121.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g121.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N121 + N121) D121 → (∀ j121 < D121.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D121 j121).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i121 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D121 j121).inputs, (D121.lineDegrees (N121 + N121) (Finset.Ico N121 (N121 + N121))).getD i121 0 = 0) ∨ (∀ h121 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D121 j121).inputs, (D121.lineDegrees (N121 + N121) (Finset.range N121)).getD h121 0 = 0)) → (∃ x121 y121 xa121 ya121 : Fin N121 → Bool, PEqualNP.MetaComplexity.circuitFun (N121 + N121) D121 (Fin.append (fun u121 => decide (u121 ∈ S121) && x121 u121) (fun t121 => if t121 ∈ W121 then y121 t121 else nu121 t121)) ≠ PEqualNP.MetaComplexity.circuitFun (N121 + N121) D121 (Fin.append (fun u121a => decide (u121a ∈ S121) && xa121 u121a) (fun t121a => if t121a ∈ W121 then ya121 t121a else nu121 t121a))) → ∃ E121 : PEqualNP.CircuitLowerBounds.Circuit, ((∀ g121a ∈ E121.gates, (g121a.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g121a.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g121a.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N121 + N121) E121) ∧ (∀ j121a < E121.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt E121 j121a).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i121a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt E121 j121a).inputs, (E121.lineDegrees (N121 + N121) (Finset.Ico N121 (N121 + N121))).getD i121a 0 = 0) ∨ (∀ h121a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt E121 j121a).inputs, (E121.lineDegrees (N121 + N121) (Finset.range N121)).getD h121a 0 = 0)) ∧ E121.size ≤ D121.size ∧ ∀ x121a y121a : Fin N121 → Bool, PEqualNP.MetaComplexity.circuitFun (N121 + N121) E121 (Fin.append x121a y121a) = PEqualNP.MetaComplexity.circuitFun (N121 + N121) D121 (Fin.append (fun u121b => decide (u121b ∈ S121) && x121a u121b) (fun t121b => if t121b ∈ W121 then y121a t121b else nu121 t121b)) := by
  intro N D S W nu hg hrb hkm hne
  have hG := PEqualNP.Outside.L_meta_1718.toGood (N + N) (Finset.Ico N (N + N)) (Finset.range N)
    D hg hrb hkm
  obtain ⟨es, hE, hle, hrel⟩ := PEqualNP.Outside.L_meta_1718.main (N + N)
    (PEqualNP.Outside.L_meta_1718.rI N S W nu) (PEqualNP.Outside.L_meta_1718.fI N)
    (PEqualNP.Outside.L_meta_1718.ini (N + N) (Finset.Ico N (N + N)))
    (PEqualNP.Outside.L_meta_1718.ini (N + N) (Finset.range N))
    (PEqualNP.Outside.L_meta_1718.rI_len N S W nu) (PEqualNP.Outside.L_meta_1718.fI_len N)
    (PEqualNP.Outside.L_meta_1718.ini_len _ _) (PEqualNP.Outside.L_meta_1718.ini_len _ _)
    (PEqualNP.Outside.L_meta_1718.base N S W nu) D.gates hG
  obtain ⟨x, y, xa, ya, hxy⟩ := hne
  rcases Nat.lt_or_ge D.output (N + N + D.gates.length) with ho | ho
  · rcases hrel D.output ho with ⟨b, hb⟩ | ⟨k, hk, hv, _, _⟩
    · exact absurd ((hb (x, y)).trans (hb (xa, ya)).symm) hxy
    · have hF := PEqualNP.Outside.L_meta_1718.fromGood (N + N) (Finset.Ico N (N + N))
        (Finset.range N) es k hE
      exact ⟨⟨es, k⟩, hF.1, hF.2, hle, fun x' y' => hv (x', y')⟩
  · exfalso
    apply hxy
    exact (PEqualNP.Outside.L_meta_1718.ev_oob D (N + N) ho _ (by simp)).trans
      (PEqualNP.Outside.L_meta_1718.ev_oob D (N + N) ho _ (by simp)).symm
