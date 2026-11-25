import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_13051

-- Lower bounds on binary gates by restriction, with a kernel search at the leaves. The live-set compression
-- (build, live, compress, live_card, live_separates, first_live, keepChoices) follows the merged L_meta_10916,
-- L_meta_8708, L_meta_8463 and L_meta_1449 (Apache-2.0).

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

section Prog
variable {ι κ : Type}

def K (S : (ι → Bool) → Prop) (w : ι → Bool) : Prop :=
  (∃ c : Bool, w = fun _ => c) ∨ S w ∨ S (fun x => !w x)

def ins (z : ι → Bool) (S : (ι → Bool) → Prop) : (ι → Bool) → Prop := fun w => w = z ∨ S w

def Run : ℕ → ((ι → Bool) → Prop) → (ι → Bool) → Prop
  | 0, S, f => K S f
  | t + 1, S, f => Run t S f ∨
      ∃ a b : ι → Bool, K S a ∧ K S b ∧ Run t (ins (fun x => a x && b x) S) f

theorem K_not {S : (ι → Bool) → Prop} {w : ι → Bool} (h : K S w) : K S (fun x => !w x) := by
  rcases h with ⟨c, rfl⟩ | h | h
  · exact Or.inl ⟨!c, rfl⟩
  · exact Or.inr (Or.inr (by simpa using h))
  · exact Or.inr (Or.inl h)

theorem K_ins {S : (ι → Bool) → Prop} {z w : ι → Bool} (h : K S w) : K (ins z S) w := by
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (Or.inr h))
  · exact Or.inr (Or.inr (Or.inr h))

theorem K_new {S : (ι → Bool) → Prop} (z : ι → Bool) : K (ins z S) z := Or.inr (Or.inl (Or.inl rfl))

theorem K_and {S : (ι → Bool) → Prop} {a b : ι → Bool} (ha : ∃ c, ∀ y, a y = c) (hb : K S b) :
    K S (fun y => a y && b y) := by
  obtain ⟨c, hc⟩ := ha
  cases c
  · exact Or.inl ⟨false, funext fun y => by simp [hc y]⟩
  · have : (fun y => a y && b y) = b := funext fun y => by simp [hc y]
    rw [this]; exact hb

theorem K_bind {S : (ι → Bool) → Prop} {S' : (κ → Bool) → Prop} (σ : κ → ι)
    (h : ∀ w, S w → K S' (fun y => w (σ y))) {w : ι → Bool} (hw : K S w) :
    K S' (fun y => w (σ y)) := by
  rcases hw with ⟨c, rfl⟩ | hw | hw
  · exact Or.inl ⟨c, rfl⟩
  · exact h w hw
  · have h2 := K_not (h _ hw)
    simpa using h2

theorem Run_map (σ : κ → ι) : ∀ (t : ℕ) (S : (ι → Bool) → Prop) (S' : (κ → Bool) → Prop)
    (f : ι → Bool), (∀ w, S w → K S' (fun y => w (σ y))) → Run t S f → Run t S' (fun y => f (σ y))
  | 0, _, _, _, h, hf => K_bind σ h hf
  | t + 1, S, S', f, h, hf => by
    rcases hf with hf | ⟨a, b, ha, hb, hf⟩
    · exact Or.inl (Run_map σ t S S' f h hf)
    · refine Or.inr ⟨_, _, K_bind σ h ha, K_bind σ h hb, Run_map σ t _ _ f ?_ hf⟩
      rintro w (rfl | hw)
      · exact K_new _
      · exact K_ins (h w hw)

theorem Run_le {t t' : ℕ} {S : (ι → Bool) → Prop} {f : ι → Bool} (h : t ≤ t') (hf : Run t S f) :
    Run t' S f := by
  induction h with
  | refl => exact hf
  | step _ ih => exact Or.inl ih

def Cl (σ : κ → ι) (p q r : ι) (S : (ι → Bool) → Prop) : Prop :=
  ∀ w, S w → w p ≠ w q → ∀ y, w (σ y) = w r

theorem Cl_K {σ : κ → ι} {p q r : ι} {S : (ι → Bool) → Prop} (h : Cl σ p q r S) {w : ι → Bool}
    (hw : K S w) (hd : w p ≠ w q) (y : κ) : w (σ y) = w r := by
  rcases hw with ⟨c, rfl⟩ | hw | hw
  · exact absurd rfl hd
  · exact h w hw hd y
  · have h2 := h _ hw (by simpa using hd) y
    simpa using h2

theorem and_dep {a b : ι → Bool} {p q : ι} (h : (a p && b p) ≠ (a q && b q)) :
    a p ≠ a q ∨ b p ≠ b q := by
  by_contra hc
  simp only [not_or, not_not] at hc
  exact h (by rw [hc.1, hc.2])

theorem kill1 (σ : κ → ι) (p q r : ι) : ∀ (t : ℕ) (S : (ι → Bool) → Prop) (S' : (κ → Bool) → Prop)
    (f : ι → Bool), Cl σ p q r S → (∀ w, S w → K S' (fun y => w (σ y))) → f p ≠ f q →
    (∃ y y', f (σ y) ≠ f (σ y')) → Run t S f → ∃ t', t' + 1 ≤ t ∧ Run t' S' (fun y => f (σ y))
  | 0, _, _, f, hc, _, hd, ⟨y, y', hn⟩, hf =>
    absurd ((Cl_K hc hf hd y).trans (Cl_K hc hf hd y').symm) hn
  | t + 1, S, S', f, hc, hm, hd, hn, hf => by
    rcases hf with hf | ⟨a, b, ha, hb, hf⟩
    · obtain ⟨t', ht, hr⟩ := kill1 σ p q r t S S' f hc hm hd hn hf
      exact ⟨t', by omega, hr⟩
    · by_cases hz : (a p && b p) ≠ (a q && b q)
      · have hk : K S' (fun y => a (σ y) && b (σ y)) := by
          rcases and_dep hz with h | h
          · exact K_and ⟨a r, Cl_K hc ha h⟩ (K_bind σ hm hb)
          · have e : (fun y => a (σ y) && b (σ y)) = fun y => b (σ y) && a (σ y) :=
              funext fun y => Bool.and_comm _ _
            rw [e]
            exact K_and ⟨b r, Cl_K hc hb h⟩ (K_bind σ hm ha)
        refine ⟨t, le_rfl, Run_map σ t _ S' f ?_ hf⟩
        rintro w (rfl | hw)
        · exact hk
        · exact hm w hw
      · obtain ⟨t', ht, hr⟩ := kill1 σ p q r t (ins (fun x => a x && b x) S)
          (ins (fun y => a (σ y) && b (σ y)) S') f
          (by
            rintro w (rfl | hw) hd2
            · exact absurd hd2 hz
            · exact hc w hw hd2)
          (by
            rintro w (rfl | hw)
            · exact K_new _
            · exact K_ins (hm w hw)) hd hn hf
        exact ⟨t' + 1, by omega, Or.inr ⟨_, _, K_bind σ hm ha, K_bind σ hm hb, hr⟩⟩

theorem kill2_dep (σ0 σ1 : κ → ι) (p q : ι) {t : ℕ} {S : (ι → Bool) → Prop}
    {S0 S1 : (κ → Bool) → Prop} {f a b : ι → Bool} (hc0 : Cl σ0 p q p S) (hc1 : Cl σ1 p q q S)
    (hm0 : ∀ w, S w → K S0 (fun y => w (σ0 y))) (hm1 : ∀ w, S w → K S1 (fun y => w (σ1 y)))
    (hd : f p ≠ f q) (hn0 : ∃ y y', f (σ0 y) ≠ f (σ0 y')) (hn1 : ∃ y y', f (σ1 y) ≠ f (σ1 y'))
    (ha : K S a) (hb : K S b) (hda : a p ≠ a q) (hf : Run t (ins (fun x => a x && b x) S) f) :
    ∃ t0 t1, Run t0 S0 (fun y => f (σ0 y)) ∧ Run t1 S1 (fun y => f (σ1 y)) ∧
      ((t0 + 2 ≤ t + 1 ∧ t1 + 1 ≤ t + 1) ∨ (t0 + 1 ≤ t + 1 ∧ t1 + 2 ≤ t + 1)) := by
  have k0 := Cl_K hc0 ha hda
  have k1 := Cl_K hc1 ha hda
  have hz0 : ∀ w, ins (fun x => a x && b x) S w → K S0 (fun y => w (σ0 y)) := by
    rintro w (rfl | hw)
    · exact K_and ⟨_, k0⟩ (K_bind σ0 hm0 hb)
    · exact hm0 w hw
  have hz1 : ∀ w, ins (fun x => a x && b x) S w → K S1 (fun y => w (σ1 y)) := by
    rintro w (rfl | hw)
    · exact K_and ⟨_, k1⟩ (K_bind σ1 hm1 hb)
    · exact hm1 w hw
  cases hap : a p
  · obtain ⟨t', ht, hr⟩ := kill1 σ0 p q p t _ S0 f (by
        rintro w (rfl | hw) hd2
        · intro y; simp [k0 y, hap]
        · exact hc0 w hw hd2) hz0 hd hn0 hf
    exact ⟨t', t, hr, Run_map σ1 t _ S1 f hz1 hf, Or.inl ⟨by omega, le_rfl⟩⟩
  · have haq : a q = false := by
      cases h : a q
      · rfl
      · exact absurd (hap.trans h.symm) hda
    obtain ⟨t', ht, hr⟩ := kill1 σ1 p q q t _ S1 f (by
        rintro w (rfl | hw) hd2
        · intro y; simp [k1 y, haq]
        · exact hc1 w hw hd2) hz1 hd hn1 hf
    exact ⟨t, t', Run_map σ0 t _ S0 f hz0 hf, hr, Or.inr ⟨le_rfl, by omega⟩⟩

theorem kill2 (σ0 σ1 : κ → ι) (p q : ι) : ∀ (t : ℕ) (S : (ι → Bool) → Prop)
    (S0 S1 : (κ → Bool) → Prop) (f : ι → Bool), Cl σ0 p q p S → Cl σ1 p q q S →
    (∀ w, S w → K S0 (fun y => w (σ0 y))) → (∀ w, S w → K S1 (fun y => w (σ1 y))) → f p ≠ f q →
    (∃ y y', f (σ0 y) ≠ f (σ0 y')) → (∃ y y', f (σ1 y) ≠ f (σ1 y')) → Run t S f →
    ∃ t0 t1, Run t0 S0 (fun y => f (σ0 y)) ∧ Run t1 S1 (fun y => f (σ1 y)) ∧
      ((t0 + 2 ≤ t ∧ t1 + 1 ≤ t) ∨ (t0 + 1 ≤ t ∧ t1 + 2 ≤ t))
  | 0, _, _, _, f, hc, _, _, _, hd, ⟨y, y', hn⟩, _, hf =>
    absurd ((Cl_K hc hf hd y).trans (Cl_K hc hf hd y').symm) hn
  | t + 1, S, S0, S1, f, hc0, hc1, hm0, hm1, hd, hn0, hn1, hf => by
    rcases hf with hf | ⟨a, b, ha, hb, hf⟩
    · obtain ⟨t0, t1, r0, r1, h⟩ := kill2 σ0 σ1 p q t S S0 S1 f hc0 hc1 hm0 hm1 hd hn0 hn1 hf
      exact ⟨t0, t1, r0, r1, by omega⟩
    · by_cases hz : (a p && b p) ≠ (a q && b q)
      · rcases and_dep hz with h | h
        · exact kill2_dep σ0 σ1 p q hc0 hc1 hm0 hm1 hd hn0 hn1 ha hb h hf
        · have e : (fun x => a x && b x) = fun x => b x && a x :=
            funext fun x => Bool.and_comm _ _
          rw [e] at hf
          exact kill2_dep σ0 σ1 p q hc0 hc1 hm0 hm1 hd hn0 hn1 hb ha h hf
      · obtain ⟨t0, t1, r0, r1, h⟩ := kill2 σ0 σ1 p q t (ins (fun x => a x && b x) S)
          (ins (fun y => a (σ0 y) && b (σ0 y)) S0) (ins (fun y => a (σ1 y) && b (σ1 y)) S1) f
          (by
            rintro w (rfl | hw) hd2
            · exact absurd hd2 hz
            · exact hc0 w hw hd2)
          (by
            rintro w (rfl | hw) hd2
            · exact absurd hd2 hz
            · exact hc1 w hw hd2)
          (by
            rintro w (rfl | hw)
            · exact K_new _
            · exact K_ins (hm0 w hw))
          (by
            rintro w (rfl | hw)
            · exact K_new _
            · exact K_ins (hm1 w hw)) hd hn0 hn1 hf
        exact ⟨t0 + 1, t1 + 1, Or.inr ⟨_, _, K_bind σ0 hm0 ha, K_bind σ0 hm0 hb, r0⟩,
          Or.inr ⟨_, _, K_bind σ1 hm1 ha, K_bind σ1 hm1 hb, r1⟩, by omega⟩

end Prog

section Rules
variable {n : ℕ}

abbrev BF (n : ℕ) := (Fin n → Bool) → Bool

def Vars (n : ℕ) : BF n → Prop := fun w => ∃ i : Fin n, w = fun x => x i

def LB (f : BF n) (b : ℕ) : Prop := ∀ t, Run t (Vars n) f → b ≤ t

def pt (n : ℕ) (c : ℕ) : Fin n → Bool := fun i => c.testBit i.val

def rs (f : BF n) (i : Fin n) (c : Bool) : BF n := fun x => f (Function.update x i c)

theorem vars_rs (i : Fin n) (c : Bool) (w : BF n) (hw : Vars n w) :
    K (Vars n) (fun x => w (Function.update x i c)) := by
  obtain ⟨j, rfl⟩ := hw
  by_cases h : j = i
  · subst h; exact Or.inl ⟨c, by simp⟩
  · exact Or.inr (Or.inl ⟨j, by simp [Function.update_of_ne h]⟩)

theorem vars_cl (i : Fin n) (c : Bool) (x : Fin n → Bool) :
    Cl (fun y => Function.update y i c) (Function.update x i false) (Function.update x i true)
      (Function.update x i c) (Vars n) := by
  rintro w ⟨j, rfl⟩ hd y
  by_cases h : j = i
  · subst h; simp
  · exact absurd (by simp [Function.update_of_ne h]) hd

theorem rule1 (f : BF n) (i : Fin n) (c : Bool) (b p y y' : ℕ)
    (hd : f (Function.update (pt n p) i false) ≠ f (Function.update (pt n p) i true))
    (hn : rs f i c (pt n y) ≠ rs f i c (pt n y')) (h : LB (rs f i c) b) : LB f (b + 1) := by
  intro t ht
  obtain ⟨t', h1, h2⟩ := kill1 _ _ _ _ t _ (Vars n) f (vars_cl i c (pt n p)) (vars_rs i c) hd
    ⟨_, _, hn⟩ ht
  have := h t' h2
  omega

theorem rule2 (f : BF n) (i : Fin n) (b p y y' u u' : ℕ)
    (hd : f (Function.update (pt n p) i false) ≠ f (Function.update (pt n p) i true))
    (hn0 : rs f i false (pt n y) ≠ rs f i false (pt n y'))
    (hn1 : rs f i true (pt n u) ≠ rs f i true (pt n u'))
    (h0 : LB (rs f i false) b) (h1 : LB (rs f i true) b) : LB f (b + 2) := by
  intro t ht
  obtain ⟨t0, t1, r0, r1, h⟩ := kill2 _ _ _ _ t _ (Vars n) (Vars n) f (vars_cl i false (pt n p))
    (vars_cl i true (pt n p)) (vars_rs i false) (vars_rs i true) hd ⟨_, _, hn0⟩ ⟨_, _, hn1⟩ ht
  have g0 := h0 t0 r0
  have g1 := h1 t1 r1
  omega

theorem LB_mono {f : BF n} {b b' : ℕ} (h : LB f b) (hb : b' ≤ b) : LB f b' :=
  fun t ht => hb.trans (h t ht)

theorem LB_perm (π : Fin n → Fin n) (f g : BF n) (hg : ∀ x, g x = f (fun i => x (π i))) {b : ℕ}
    (h : LB g b) : LB f b := by
  intro t ht
  apply h t
  have e : g = fun x => f (fun i => x (π i)) := funext hg
  rw [e]
  refine Run_map (fun (x : Fin n → Bool) (i : Fin n) => x (π i)) t _ _ f ?_ ht
  rintro w ⟨j, rfl⟩
  exact Or.inr (Or.inl ⟨π j, rfl⟩)

end Rules

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

def ops (a b : ℕ) : List ℕ := [a &&& b, a ||| b, a ^^^ (a &&& b), b ^^^ (a &&& b)]

abbrev bops (a b : ℕ) : Finset ℕ := (ops a b).toFinset

def sep (P m x : ℕ) : ℕ := Nat.land (Nat.xor (Nat.shiftRight x P) x) m

def cuts (P m : ℕ) (ws : List ℕ) : ℕ := ws.foldr (fun w v => Nat.lor (sep P m w) v) 0

def differs (P i w : ℕ) : Prop := w.testBit (P + i) ≠ w.testBit i

theorem ops_differs (P i a b z : ℕ) (hz : z ∈ bops a b) (hd : differs P i z) :
    differs P i a ∨ differs P i b := by
  simp only [bops, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha, hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, ha, hb]

theorem mask_bit (P i : ℕ) : (2 ^ P - 1).testBit i = decide (i < P) := Nat.testBit_two_pow_sub_one P i

theorem cuts_spec (P : ℕ) (ws : List ℕ) (i : ℕ) :
    (cuts P (2 ^ P - 1) ws).testBit i = true ↔ i < P ∧ ∃ w ∈ ws, differs P i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change ((((a >>> P) ^^^ a) &&& (2 ^ P - 1)) ||| cuts P (2 ^ P - 1) rest).testBit i = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftRight, mask_bit,
      Bool.and_eq_true, bx, decide_eq_true_eq, differs, List.mem_cons, exists_eq_or_imp]
    tauto

theorem cuts_full {P g : ℕ} (hg : ∀ i, i < P → differs P i g) {k : ℕ} {ws : List ℕ}
    (h : live bops g k ws.toFinset) : cuts P (2 ^ P - 1) ws = 2 ^ P - 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [mask_bit]
  by_cases hi : i < P
  · have hw := live_separates (differs P i) (hg i hi) (ops_differs P i) h
    simpa [hi] using (cuts_spec P ws i).mpr ⟨hi, by simpa using hw⟩
  · cases hb : (cuts P (2 ^ P - 1) ws).testBit i
    · simp [hi]
    · exact absurd ((cuts_spec P ws i).mp hb).1 hi

theorem ops_swap (a b : ℕ) : bops a b = bops b a := by
  ext z
  simp only [bops, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [Nat.and_comm a b, Nat.or_comm a b]
  tauto

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

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

def keepChoices (a b : ℕ) (r : List ℕ) : List (List ℕ) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List ℕ} {a b : ℕ} {needed : Finset ℕ}
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

theorem singleton_list {goal : ℕ} {ws : List ℕ} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) :
    ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

-- forces the kernel to evaluate a number before it goes on
def fz {β : Type} (n : ℕ) (f : ℕ → β) : β := Nat.casesOn n (f 0) (fun k => f (Nat.succ k))

theorem fz_eq {β : Type} (n : ℕ) (f : ℕ → β) : fz n f = f n := by cases n <;> rfl

def fzl {β : Type} : List ℕ → (List ℕ → β) → β
  | [], f => f []
  | a :: t, f => fz a fun a' => fzl t fun t' => f (a' :: t')

theorem fzl_eq {β : Type} : ∀ (l : List ℕ) (f : List ℕ → β), fzl l f = f l
  | [], f => rfl
  | a :: t, f => by simp [fzl, fz_eq, fzl_eq t]

def go (nx : ℕ → List ℕ → Bool) (e z : ℕ) (l : List ℕ) : Bool := fz z fun z => nx e (z :: l)

def tst (nx : ℕ → List ℕ → Bool) (v m e z : ℕ) (l : List ℕ) : Bool :=
  cond (Nat.beq v m) (go nx e z l) false

def t0 (P m base : ℕ) (nx : ℕ → List ℕ → Bool) (r : List ℕ) (z : ℕ) : Bool :=
  tst nx (Nat.lor (sep P m z) base) m 0 z r

def tE (P m base : ℕ) (nx : ℕ → List ℕ → Bool) (e a b : ℕ) (r : List ℕ) (z : ℕ) : Bool :=
  or (tst nx (Nat.lor (sep P m z) base) m (Nat.succ e) z r)
  (or (tst nx (Nat.lor (sep P m a) (Nat.lor (sep P m z) base)) m e z (a :: r))
  (or (tst nx (Nat.lor (sep P m b) (Nat.lor (sep P m z) base)) m e z (b :: r))
    (Nat.casesOn e false (fun e' =>
      tst nx (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m z) base))) m e' z
        (a :: b :: r)))))

def dsp (P m : ℕ) (nx : ℕ → List ℕ → Bool) (e a b base : ℕ) (r : List ℕ) : Bool :=
  Nat.casesOn e
    (or (t0 P m base nx r (Nat.land a b)) (or (t0 P m base nx r (Nat.lor a b))
      (or (t0 P m base nx r (Nat.xor a (Nat.land a b))) (t0 P m base nx r (Nat.xor b (Nat.land a b))))))
    (fun e => or (tE P m base nx e a b r (Nat.land a b)) (or (tE P m base nx e a b r (Nat.lor a b))
      (or (tE P m base nx e a b r (Nat.xor a (Nat.land a b)))
        (tE P m base nx e a b r (Nat.xor b (Nat.land a b))))))

def pall (P m : ℕ) (nx : ℕ → List ℕ → Bool) (e : ℕ) (ws : List ℕ) : Bool :=
  (pairs ws).any (fun q => dsp P m nx e q.1 q.2.1 (cuts P m q.2.2) q.2.2)

def n2 (P m : ℕ) (nx : ℕ → List ℕ → Bool) (e0 a b : ℕ) : Bool :=
  or (dsp P m nx e0 a b 0 [])
    (false)

def n3 (P m : ℕ) (nx : ℕ → List ℕ → Bool) (e0 a b c : ℕ) : Bool :=
  or (dsp P m nx e0 a b (Nat.lor (sep P m c) 0) [c])
    (or (dsp P m nx e0 a c (Nat.lor (sep P m b) 0) [b])
    (or (dsp P m nx e0 b c (Nat.lor (sep P m a) 0) [a])
    (false)))

def n4 (P m : ℕ) (nx : ℕ → List ℕ → Bool) (e0 a b c d : ℕ) : Bool :=
  or (dsp P m nx e0 a b (Nat.lor (sep P m c) (Nat.lor (sep P m d) 0)) [c, d])
    (or (dsp P m nx e0 a c (Nat.lor (sep P m b) (Nat.lor (sep P m d) 0)) [b, d])
    (or (dsp P m nx e0 a d (Nat.lor (sep P m b) (Nat.lor (sep P m c) 0)) [b, c])
    (or (dsp P m nx e0 b c (Nat.lor (sep P m a) (Nat.lor (sep P m d) 0)) [a, d])
    (or (dsp P m nx e0 b d (Nat.lor (sep P m a) (Nat.lor (sep P m c) 0)) [a, c])
    (or (dsp P m nx e0 c d (Nat.lor (sep P m a) (Nat.lor (sep P m b) 0)) [a, b])
    (false))))))

def n5 (P m : ℕ) (nx : ℕ → List ℕ → Bool) (e0 a b c d e : ℕ) : Bool :=
  or (dsp P m nx e0 a b (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m e) 0))) [c, d, e])
    (or (dsp P m nx e0 a c (Nat.lor (sep P m b) (Nat.lor (sep P m d) (Nat.lor (sep P m e) 0))) [b, d, e])
    (or (dsp P m nx e0 a d (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m e) 0))) [b, c, e])
    (or (dsp P m nx e0 a e (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m d) 0))) [b, c, d])
    (or (dsp P m nx e0 b c (Nat.lor (sep P m a) (Nat.lor (sep P m d) (Nat.lor (sep P m e) 0))) [a, d, e])
    (or (dsp P m nx e0 b d (Nat.lor (sep P m a) (Nat.lor (sep P m c) (Nat.lor (sep P m e) 0))) [a, c, e])
    (or (dsp P m nx e0 b e (Nat.lor (sep P m a) (Nat.lor (sep P m c) (Nat.lor (sep P m d) 0))) [a, c, d])
    (or (dsp P m nx e0 c d (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m e) 0))) [a, b, e])
    (or (dsp P m nx e0 c e (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m d) 0))) [a, b, d])
    (or (dsp P m nx e0 d e (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m c) 0))) [a, b, c])
    (false))))))))))

def n6 (P m : ℕ) (nx : ℕ → List ℕ → Bool) (e0 a b c d e f : ℕ) : Bool :=
  or (dsp P m nx e0 a b (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m e) (Nat.lor (sep P m f) 0)))) [c, d, e, f])
    (or (dsp P m nx e0 a c (Nat.lor (sep P m b) (Nat.lor (sep P m d) (Nat.lor (sep P m e) (Nat.lor (sep P m f) 0)))) [b, d, e, f])
    (or (dsp P m nx e0 a d (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m e) (Nat.lor (sep P m f) 0)))) [b, c, e, f])
    (or (dsp P m nx e0 a e (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m f) 0)))) [b, c, d, f])
    (or (dsp P m nx e0 a f (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m e) 0)))) [b, c, d, e])
    (or (dsp P m nx e0 b c (Nat.lor (sep P m a) (Nat.lor (sep P m d) (Nat.lor (sep P m e) (Nat.lor (sep P m f) 0)))) [a, d, e, f])
    (or (dsp P m nx e0 b d (Nat.lor (sep P m a) (Nat.lor (sep P m c) (Nat.lor (sep P m e) (Nat.lor (sep P m f) 0)))) [a, c, e, f])
    (or (dsp P m nx e0 b e (Nat.lor (sep P m a) (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m f) 0)))) [a, c, d, f])
    (or (dsp P m nx e0 b f (Nat.lor (sep P m a) (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m e) 0)))) [a, c, d, e])
    (or (dsp P m nx e0 c d (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m e) (Nat.lor (sep P m f) 0)))) [a, b, e, f])
    (or (dsp P m nx e0 c e (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m d) (Nat.lor (sep P m f) 0)))) [a, b, d, f])
    (or (dsp P m nx e0 c f (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m d) (Nat.lor (sep P m e) 0)))) [a, b, d, e])
    (or (dsp P m nx e0 d e (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m f) 0)))) [a, b, c, f])
    (or (dsp P m nx e0 d f (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m e) 0)))) [a, b, c, e])
    (or (dsp P m nx e0 e f (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m d) 0)))) [a, b, c, d])
    (false)))))))))))))))

def n7 (P m : ℕ) (nx : ℕ → List ℕ → Bool) (e0 a b c d e f h : ℕ) : Bool :=
  or (dsp P m nx e0 a b (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m e) (Nat.lor (sep P m f) (Nat.lor (sep P m h) 0))))) [c, d, e, f, h])
    (or (dsp P m nx e0 a c (Nat.lor (sep P m b) (Nat.lor (sep P m d) (Nat.lor (sep P m e) (Nat.lor (sep P m f) (Nat.lor (sep P m h) 0))))) [b, d, e, f, h])
    (or (dsp P m nx e0 a d (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m e) (Nat.lor (sep P m f) (Nat.lor (sep P m h) 0))))) [b, c, e, f, h])
    (or (dsp P m nx e0 a e (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m f) (Nat.lor (sep P m h) 0))))) [b, c, d, f, h])
    (or (dsp P m nx e0 a f (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m e) (Nat.lor (sep P m h) 0))))) [b, c, d, e, h])
    (or (dsp P m nx e0 a h (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m e) (Nat.lor (sep P m f) 0))))) [b, c, d, e, f])
    (or (dsp P m nx e0 b c (Nat.lor (sep P m a) (Nat.lor (sep P m d) (Nat.lor (sep P m e) (Nat.lor (sep P m f) (Nat.lor (sep P m h) 0))))) [a, d, e, f, h])
    (or (dsp P m nx e0 b d (Nat.lor (sep P m a) (Nat.lor (sep P m c) (Nat.lor (sep P m e) (Nat.lor (sep P m f) (Nat.lor (sep P m h) 0))))) [a, c, e, f, h])
    (or (dsp P m nx e0 b e (Nat.lor (sep P m a) (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m f) (Nat.lor (sep P m h) 0))))) [a, c, d, f, h])
    (or (dsp P m nx e0 b f (Nat.lor (sep P m a) (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m e) (Nat.lor (sep P m h) 0))))) [a, c, d, e, h])
    (or (dsp P m nx e0 b h (Nat.lor (sep P m a) (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m e) (Nat.lor (sep P m f) 0))))) [a, c, d, e, f])
    (or (dsp P m nx e0 c d (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m e) (Nat.lor (sep P m f) (Nat.lor (sep P m h) 0))))) [a, b, e, f, h])
    (or (dsp P m nx e0 c e (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m d) (Nat.lor (sep P m f) (Nat.lor (sep P m h) 0))))) [a, b, d, f, h])
    (or (dsp P m nx e0 c f (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m d) (Nat.lor (sep P m e) (Nat.lor (sep P m h) 0))))) [a, b, d, e, h])
    (or (dsp P m nx e0 c h (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m d) (Nat.lor (sep P m e) (Nat.lor (sep P m f) 0))))) [a, b, d, e, f])
    (or (dsp P m nx e0 d e (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m f) (Nat.lor (sep P m h) 0))))) [a, b, c, f, h])
    (or (dsp P m nx e0 d f (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m e) (Nat.lor (sep P m h) 0))))) [a, b, c, e, h])
    (or (dsp P m nx e0 d h (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m e) (Nat.lor (sep P m f) 0))))) [a, b, c, e, f])
    (or (dsp P m nx e0 e f (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m h) 0))))) [a, b, c, d, h])
    (or (dsp P m nx e0 e h (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m f) 0))))) [a, b, c, d, f])
    (or (dsp P m nx e0 f h (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m e) 0))))) [a, b, c, d, e])
    (false)))))))))))))))))))))

def n8 (P m : ℕ) (nx : ℕ → List ℕ → Bool) (e0 a b c d e f h i : ℕ) : Bool :=
  or (dsp P m nx e0 a b (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m e) (Nat.lor (sep P m f) (Nat.lor (sep P m h) (Nat.lor (sep P m i) 0)))))) [c, d, e, f, h, i])
    (or (dsp P m nx e0 a c (Nat.lor (sep P m b) (Nat.lor (sep P m d) (Nat.lor (sep P m e) (Nat.lor (sep P m f) (Nat.lor (sep P m h) (Nat.lor (sep P m i) 0)))))) [b, d, e, f, h, i])
    (or (dsp P m nx e0 a d (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m e) (Nat.lor (sep P m f) (Nat.lor (sep P m h) (Nat.lor (sep P m i) 0)))))) [b, c, e, f, h, i])
    (or (dsp P m nx e0 a e (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m f) (Nat.lor (sep P m h) (Nat.lor (sep P m i) 0)))))) [b, c, d, f, h, i])
    (or (dsp P m nx e0 a f (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m e) (Nat.lor (sep P m h) (Nat.lor (sep P m i) 0)))))) [b, c, d, e, h, i])
    (or (dsp P m nx e0 a h (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m e) (Nat.lor (sep P m f) (Nat.lor (sep P m i) 0)))))) [b, c, d, e, f, i])
    (or (dsp P m nx e0 a i (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m e) (Nat.lor (sep P m f) (Nat.lor (sep P m h) 0)))))) [b, c, d, e, f, h])
    (or (dsp P m nx e0 b c (Nat.lor (sep P m a) (Nat.lor (sep P m d) (Nat.lor (sep P m e) (Nat.lor (sep P m f) (Nat.lor (sep P m h) (Nat.lor (sep P m i) 0)))))) [a, d, e, f, h, i])
    (or (dsp P m nx e0 b d (Nat.lor (sep P m a) (Nat.lor (sep P m c) (Nat.lor (sep P m e) (Nat.lor (sep P m f) (Nat.lor (sep P m h) (Nat.lor (sep P m i) 0)))))) [a, c, e, f, h, i])
    (or (dsp P m nx e0 b e (Nat.lor (sep P m a) (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m f) (Nat.lor (sep P m h) (Nat.lor (sep P m i) 0)))))) [a, c, d, f, h, i])
    (or (dsp P m nx e0 b f (Nat.lor (sep P m a) (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m e) (Nat.lor (sep P m h) (Nat.lor (sep P m i) 0)))))) [a, c, d, e, h, i])
    (or (dsp P m nx e0 b h (Nat.lor (sep P m a) (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m e) (Nat.lor (sep P m f) (Nat.lor (sep P m i) 0)))))) [a, c, d, e, f, i])
    (or (dsp P m nx e0 b i (Nat.lor (sep P m a) (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m e) (Nat.lor (sep P m f) (Nat.lor (sep P m h) 0)))))) [a, c, d, e, f, h])
    (or (dsp P m nx e0 c d (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m e) (Nat.lor (sep P m f) (Nat.lor (sep P m h) (Nat.lor (sep P m i) 0)))))) [a, b, e, f, h, i])
    (or (dsp P m nx e0 c e (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m d) (Nat.lor (sep P m f) (Nat.lor (sep P m h) (Nat.lor (sep P m i) 0)))))) [a, b, d, f, h, i])
    (or (dsp P m nx e0 c f (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m d) (Nat.lor (sep P m e) (Nat.lor (sep P m h) (Nat.lor (sep P m i) 0)))))) [a, b, d, e, h, i])
    (or (dsp P m nx e0 c h (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m d) (Nat.lor (sep P m e) (Nat.lor (sep P m f) (Nat.lor (sep P m i) 0)))))) [a, b, d, e, f, i])
    (or (dsp P m nx e0 c i (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m d) (Nat.lor (sep P m e) (Nat.lor (sep P m f) (Nat.lor (sep P m h) 0)))))) [a, b, d, e, f, h])
    (or (dsp P m nx e0 d e (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m f) (Nat.lor (sep P m h) (Nat.lor (sep P m i) 0)))))) [a, b, c, f, h, i])
    (or (dsp P m nx e0 d f (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m e) (Nat.lor (sep P m h) (Nat.lor (sep P m i) 0)))))) [a, b, c, e, h, i])
    (or (dsp P m nx e0 d h (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m e) (Nat.lor (sep P m f) (Nat.lor (sep P m i) 0)))))) [a, b, c, e, f, i])
    (or (dsp P m nx e0 d i (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m e) (Nat.lor (sep P m f) (Nat.lor (sep P m h) 0)))))) [a, b, c, e, f, h])
    (or (dsp P m nx e0 e f (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m h) (Nat.lor (sep P m i) 0)))))) [a, b, c, d, h, i])
    (or (dsp P m nx e0 e h (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m f) (Nat.lor (sep P m i) 0)))))) [a, b, c, d, f, i])
    (or (dsp P m nx e0 e i (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m f) (Nat.lor (sep P m h) 0)))))) [a, b, c, d, f, h])
    (or (dsp P m nx e0 f h (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m e) (Nat.lor (sep P m i) 0)))))) [a, b, c, d, e, i])
    (or (dsp P m nx e0 f i (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m e) (Nat.lor (sep P m h) 0)))))) [a, b, c, d, e, h])
    (or (dsp P m nx e0 h i (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m e) (Nat.lor (sep P m f) 0)))))) [a, b, c, d, e, f])
    (false))))))))))))))))))))))))))))

def d8 (P m g : ℕ) (nx : ℕ → List ℕ → Bool) (e0 a b c d e f h i : ℕ) (l : List ℕ) : Bool :=
  List.casesOn l (n8 P m nx e0 a b c d e f h i) (fun y t => pall P m nx e0 (a :: b :: c :: d :: e :: f :: h :: i :: y :: t))

def d7 (P m g : ℕ) (nx : ℕ → List ℕ → Bool) (e0 a b c d e f h : ℕ) (l : List ℕ) : Bool :=
  List.casesOn l (n7 P m nx e0 a b c d e f h) (fun y t => d8 P m g nx e0 a b c d e f h y t)

def d6 (P m g : ℕ) (nx : ℕ → List ℕ → Bool) (e0 a b c d e f : ℕ) (l : List ℕ) : Bool :=
  List.casesOn l (n6 P m nx e0 a b c d e f) (fun y t => d7 P m g nx e0 a b c d e f y t)

def d5 (P m g : ℕ) (nx : ℕ → List ℕ → Bool) (e0 a b c d e : ℕ) (l : List ℕ) : Bool :=
  List.casesOn l (n5 P m nx e0 a b c d e) (fun y t => d6 P m g nx e0 a b c d e y t)

def d4 (P m g : ℕ) (nx : ℕ → List ℕ → Bool) (e0 a b c d : ℕ) (l : List ℕ) : Bool :=
  List.casesOn l (n4 P m nx e0 a b c d) (fun y t => d5 P m g nx e0 a b c d y t)

def d3 (P m g : ℕ) (nx : ℕ → List ℕ → Bool) (e0 a b c : ℕ) (l : List ℕ) : Bool :=
  List.casesOn l (n3 P m nx e0 a b c) (fun y t => d4 P m g nx e0 a b c y t)

def d2 (P m g : ℕ) (nx : ℕ → List ℕ → Bool) (e0 a b : ℕ) (l : List ℕ) : Bool :=
  List.casesOn l (n2 P m nx e0 a b) (fun y t => d3 P m g nx e0 a b y t)

def d1 (P m g : ℕ) (nx : ℕ → List ℕ → Bool) (e0 a : ℕ) (l : List ℕ) : Bool :=
  List.casesOn l (Nat.beq a g) (fun y t => d2 P m g nx e0 a y t)

theorem d1_eq (P m g : ℕ) (nx : ℕ → List ℕ → Bool) (e0 a b : ℕ) (t : List ℕ) :
    d1 P m g nx e0 a (b :: t) = pall P m nx e0 (a :: b :: t) := by
  rcases t with _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨h, _ | ⟨i, _ | ⟨j, t⟩⟩⟩⟩⟩⟩⟩
  all_goals rfl

def d0 (P m g : ℕ) (nx : ℕ → List ℕ → Bool) (e0 : ℕ) (l : List ℕ) : Bool :=
  List.casesOn l false (fun y t => d1 P m g nx e0 y t)

theorem d0_goal (P m g : ℕ) (nx : ℕ → List ℕ → Bool) (e0 : ℕ) : d0 P m g nx e0 [g] = true :=
  Nat.beq_refl g

theorem d0_pairs (P m g : ℕ) (nx : ℕ → List ℕ → Bool) (e0 : ℕ) (ws : List ℕ)
    (h : pall P m nx e0 ws = true) : d0 P m g nx e0 ws = true := by
  rcases ws with _ | ⟨a, _ | ⟨b, t⟩⟩
  · simp [pall, pairs] at h
  · simp [pall, pairs, singles] at h
  · change d1 P m g nx e0 a (b :: t) = true
    rw [d1_eq]; exact h

def optimized (P m g k : ℕ) : ℕ → List ℕ → Bool :=
  Nat.rec (fun _ ws => d0 P m g (fun _ _ => false) 0 ws) (fun _ nx e ws => d0 P m g nx e ws) k

theorem tst_true {nx : ℕ → List ℕ → Bool} {v m e z : ℕ} {l : List ℕ} (hv : v = m)
    (h : nx e (z :: l) = true) : tst nx v m e z l = true := by
  have hb : Nat.beq v m = true := by rw [hv]; exact Nat.beq_refl m
  unfold tst go
  rw [hb, fz_eq]
  exact h

theorem dispatch_complete {P m k extra : ℕ} {a b z : ℕ} {r kept : List ℕ}
    (next : ℕ → List ℕ → Bool)
    (hz : z ∈ bops a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts P m (z :: kept) = m) (ht : next (k - kept.length) (z :: kept) = true) :
    dsp P m next extra a b (cuts P m r) r = true := by
  have hz' : z = Nat.land a b ∨ z = Nat.lor a b ∨ z = Nat.xor a (Nat.land a b) ∨
      z = Nat.xor b (Nat.land a b) := by
    have h1 := hz
    simp only [bops, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at h1
    exact h1
  simp only [keepChoices, List.mem_cons, List.not_mem_nil, or_false] at hk
  have hc' : Nat.lor (sep P m z) (cuts P m kept) = m := hc
  rcases extra with _ | e
  · have hk0 : kept = r := by
      rcases hk with rfl | rfl | rfl | rfl
      · rfl
      all_goals (simp only [List.length_cons] at hn; omega)
    subst hk0
    have key : t0 P m (cuts P m kept) next kept z = true := by
      refine tst_true hc' ?_
      convert ht using 2; omega
    show or _ (or _ (or _ _)) = true
    rcases hz' with e1 | e1 | e1 | e1 <;> rw [e1] at key <;> rw [key] <;> simp
  · have key : tE P m (cuts P m r) next e a b r z = true := by
      unfold tE
      rcases hk with rfl | rfl | rfl | rfl
      · rw [tst_true hc' (by convert ht using 2; omega)]
        simp
      · rw [tst_true (v := Nat.lor (sep P m a) (Nat.lor (sep P m z) (cuts P m r))) (e := e)
          (by
            show sep P m a ||| (sep P m z ||| cuts P m r) = m
            have h2 : sep P m z ||| (sep P m a ||| cuts P m r) = m := hc'
            convert h2 using 1; ac_rfl)
          (by convert ht using 2; simp only [List.length_cons]; omega)]
        simp
      · rw [tst_true (v := Nat.lor (sep P m b) (Nat.lor (sep P m z) (cuts P m r))) (e := e)
          (by
            show sep P m b ||| (sep P m z ||| cuts P m r) = m
            have h2 : sep P m z ||| (sep P m b ||| cuts P m r) = m := hc'
            convert h2 using 1; ac_rfl)
          (by convert ht using 2; simp only [List.length_cons]; omega)]
        simp
      · rcases e with _ | e'
        · simp only [List.length_cons] at hn; omega
        · have h4 : tst next (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m z) (cuts P m r))))
              m e' z (a :: b :: r) = true :=
            tst_true (by
              show sep P m a ||| (sep P m b ||| (sep P m z ||| cuts P m r)) = m
              have h2 : sep P m z ||| (sep P m a ||| (sep P m b ||| cuts P m r)) = m := hc'
              convert h2 using 1; ac_rfl)
              (by convert ht using 2; simp only [List.length_cons]; omega)
          show or _ (or _ (or _ (tst next (Nat.lor (sep P m a) (Nat.lor (sep P m b)
            (Nat.lor (sep P m z) (cuts P m r)))) m e' z (a :: b :: r)))) = true
          rw [h4]; simp
    show or _ (or _ (or _ _)) = true
    rcases hz' with e1 | e1 | e1 | e1 <;> rw [e1] at key <;> rw [key] <;> simp

theorem optimized_complete {P g : ℕ} (hg : ∀ i, i < P → differs P i g) (n : ℕ) (ws : List ℕ)
    (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live bops g n ws.toFinset) :
    optimized P (2 ^ P - 1) g n extra ws = true := by
  induction n generalizing ws extra with
  | zero =>
    rw [singleton_list hn h]
    exact d0_goal P (2 ^ P - 1) g (fun _ _ => false) 0
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rw [singleton_list hn done]
      exact d0_goal P (2 ^ P - 1) g (optimized P (2 ^ P - 1) g k) extra
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have goz {a b : ℕ} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ bops a b) :
          dsp P (2 ^ P - 1) (optimized P (2 ^ P - 1) g k) extra a b (cuts P (2 ^ P - 1) r) r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live bops g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) _ hop hk (by omega) (by omega)
          (cuts_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      change d0 P (2 ^ P - 1) g (optimized P (2 ^ P - 1) g k) extra ws = true
      apply d0_pairs
      simp only [pall, List.any_eq_true]
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, goz hp hs hz⟩
      · exact ⟨(b, a, r), swap, goz (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm])
          (ops_swap a b ▸ hz)⟩

def search (P m g n : ℕ) (inputs : List ℕ) : Bool :=
  inputs.sublists.any fun ws => fzl ws fun ws =>
    cond (Nat.ble ws.length (n + 1)) (cond (Nat.beq (cuts P m ws) m)
      (fz (n + 1 - ws.length) fun e => optimized P m g n e ws) false) false
theorem search_complete {P g : ℕ} (hg : ∀ i, i < P → differs P i g) (n : ℕ) (inputs : List ℕ)
    (hn : inputs.Nodup) (h : build bops g n inputs.toFinset) :
    search P (2 ^ P - 1) g n inputs = true := by
  classical
  obtain ⟨s, hs, hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live bops g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  refine List.any_eq_true.mpr ⟨ws, List.mem_sublists.mpr (List.filter_sublist ..), ?_⟩
  have h1 : Nat.ble ws.length (n + 1) = true := Nat.ble_eq.mpr sz
  have h2 : Nat.beq (cuts P (2 ^ P - 1) ws) (2 ^ P - 1) = true := by
    rw [cuts_full hg hl']; exact Nat.beq_refl _
  rw [fzl_eq, h1, h2, fz_eq]
  exact optimized_complete hg n ws _ hnd (by omega) hl'

def enc {ρ : Type} (w : ρ → Bool) : List ρ → ℕ
  | [] => 0
  | p :: t => Nat.bit (w p) (enc w t)

theorem enc_testBit {ρ : Type} (w : ρ → Bool) : ∀ (l : List ρ) (j : ℕ),
    (enc w l).testBit j = (l.map w).getD j false
  | [], j => by simp [enc]
  | p :: t, 0 => by simp [enc]
  | p :: t, j + 1 => by simp [enc, Nat.testBit_bit_succ, enc_testBit w t j]

theorem enc_congr {ρ : Type} {w w' : ρ → Bool} (h : ∀ x, w x = w' x) (l : List ρ) :
    enc w l = enc w' l := by
  have : w = w' := funext h
  rw [this]

theorem enc_false {ρ : Type} (l : List ρ) : enc (fun _ : ρ => false) l = 0 := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [enc, ih]

theorem enc_op {ρ : Type} (o : Bool → Bool → Bool) (o' : ℕ → ℕ → ℕ) (h0 : o false false = false)
    (ho : ∀ a b i, (o' a b).testBit i = o (a.testBit i) (b.testBit i)) (a b : ρ → Bool)
    (l : List ρ) : enc (fun r => o (a r) (b r)) l = o' (enc a l) (enc b l) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [ho, enc_testBit, enc_testBit, enc_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega), h0]

section Code
variable {ρ : Type} (x0 : ρ) (pts : List ρ)

def code (w : ρ → Bool) : ℕ := enc (fun x => Bool.xor (w x) (w x0)) pts

theorem code_const (c : Bool) : code x0 pts (fun _ => c) = 0 := by
  unfold code
  rw [← enc_false pts]
  exact enc_congr (fun x => by simp) pts

theorem code_not (w : ρ → Bool) : code x0 pts (fun x => !w x) = code x0 pts w :=
  enc_congr (fun x => by
    show Bool.xor (!w x) (!w x0) = Bool.xor (w x) (w x0)
    cases w x <;> cases w x0 <;> rfl) pts

theorem code_and (a b : ρ → Bool) :
    code x0 pts (fun x => a x && b x) ∈ bops (code x0 pts a) (code x0 pts b) := by
  have e1 := enc_op (ρ := ρ) (fun p q => p && q) (· &&& ·) rfl (fun a b i => Nat.testBit_and a b i)
    (fun x => Bool.xor (a x) (a x0)) (fun x => Bool.xor (b x) (b x0)) pts
  have e2 := enc_op (ρ := ρ) (fun p q => p || q) (· ||| ·) rfl (fun a b i => Nat.testBit_or a b i)
    (fun x => Bool.xor (a x) (a x0)) (fun x => Bool.xor (b x) (b x0)) pts
  have e3 := enc_op (ρ := ρ) (fun p q => Bool.xor p (p && q)) (fun a b => a ^^^ (a &&& b)) rfl
    (fun a b i => by simp [Nat.testBit_and, Nat.testBit_xor])
    (fun x => Bool.xor (a x) (a x0)) (fun x => Bool.xor (b x) (b x0)) pts
  have e4 := enc_op (ρ := ρ) (fun p q => Bool.xor q (p && q)) (fun a b => b ^^^ (a &&& b)) rfl
    (fun a b i => by simp [Nat.testBit_and, Nat.testBit_xor])
    (fun x => Bool.xor (a x) (a x0)) (fun x => Bool.xor (b x) (b x0)) pts
  simp only [bops, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  unfold code
  cases ha : a x0 <;> cases hb : b x0
  · left
    rw [ha, hb] at e1
    rw [← e1]
    exact enc_congr (fun x => by simp only [ha, hb]; cases a x <;> cases b x <;> rfl) pts
  · right; right; left
    rw [ha, hb] at e3
    rw [← e3]
    exact enc_congr (fun x => by simp only [ha, hb]; cases a x <;> cases b x <;> rfl) pts
  · right; right; right
    rw [ha, hb] at e4
    rw [← e4]
    exact enc_congr (fun x => by simp only [ha, hb]; cases a x <;> cases b x <;> rfl) pts
  · right; left
    rw [ha, hb] at e2
    rw [← e2]
    exact enc_congr (fun x => by simp only [ha, hb]; cases a x <;> cases b x <;> rfl) pts

theorem bops_zero {b z : ℕ} (hz : z ∈ bops 0 b) : z = 0 ∨ z = b := by
  simp only [bops, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> simp

theorem bops_self {b z : ℕ} (hz : z ∈ bops b b) : z = 0 ∨ z = b := by
  simp only [bops, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> simp

theorem sim (f : ρ → Bool) (hf : code x0 pts f ≠ 0) : ∀ (t : ℕ) (S : (ρ → Bool) → Prop)
    (A : Finset ℕ), (∀ w, S w → code x0 pts w = 0 ∨ code x0 pts w ∈ A) → Run t S f →
    build bops (code x0 pts f) t A
  | 0, S, A, h, hr => by
    rcases hr with ⟨c, rfl⟩ | hr | hr
    · exact absurd (code_const x0 pts c) hf
    · exact (h f hr).resolve_left hf
    · have := h _ hr
      rw [code_not] at this
      exact this.resolve_left hf
  | t + 1, S, A, h, hr => by
    rcases hr with hr | ⟨a, b, ha, hb, hr⟩
    · exact Or.inl (sim f hf t S A h hr)
    · have hK : ∀ w, K S w → code x0 pts w = 0 ∨ code x0 pts w ∈ A := by
        intro w hw
        rcases hw with ⟨c, rfl⟩ | hw | hw
        · exact Or.inl (code_const x0 pts c)
        · exact h w hw
        · have := h _ hw
          rwa [code_not] at this
      have hmem := code_and x0 pts a b
      by_cases hz : code x0 pts (fun x => a x && b x) = 0 ∨ code x0 pts (fun x => a x && b x) ∈ A
      · refine Or.inl (sim f hf t _ A ?_ hr)
        rintro w (rfl | hw)
        · exact hz
        · exact h w hw
      · have ha' := hK a ha
        have hb' := hK b hb
        have haA : code x0 pts a ∈ A := by
          rcases ha' with h0 | h1
          · rw [h0] at hmem
            rcases bops_zero hmem with e | e
            · exact absurd (Or.inl e) hz
            · exact absurd (e ▸ hb') hz
          · exact h1
        have hbA : code x0 pts b ∈ A := by
          rcases hb' with h0 | h1
          · rw [h0, ops_swap] at hmem
            rcases bops_zero hmem with e | e
            · exact absurd (Or.inl e) hz
            · exact absurd (e ▸ ha') hz
          · exact h1
        have hne : code x0 pts a ≠ code x0 pts b := by
          intro e
          rw [e] at hmem
          rcases bops_self hmem with e2 | e2
          · exact hz (Or.inl e2)
          · exact hz (Or.inr (e2 ▸ hbA))
        refine Or.inr ⟨_, haA, _, hbA, hne, _, hmem, sim f hf t _ _ ?_ hr⟩
        rintro w (rfl | hw)
        · exact Or.inr (Finset.mem_insert_self _ _)
        · exact (h w hw).imp id (fun h => Finset.mem_insert_of_mem h)

end Code

def ptl (n : ℕ) (l : List ℕ) : List (Fin n → Bool) := l.map (pt n)

def ic (n : ℕ) (zs os : List ℕ) : List ℕ :=
  (List.finRange n).map fun i =>
    code (pt n (zs.headD 0)) (ptl n zs ++ ptl n os) fun x : Fin n → Bool => x i

def top (n : ℕ) (f : BF n) (zs os : List ℕ) (k : ℕ) : Bool :=
  fz zs.length fun P => fz (Nat.sub (Nat.pow 2 P) 1) fun m =>
  fzl (((ic n zs os).filter fun c => !Nat.beq c 0).dedup) fun inp =>
  fz (code (pt n (zs.headD 0)) (ptl n zs ++ ptl n os) f) fun g =>
  search P m g k inp

theorem base {n : ℕ} (f : BF n) (z1 : ℕ) (zt : List ℕ) (os : List ℕ) (k : ℕ)
    (hlen : os.length = (z1 :: zt).length)
    (hz : (z1 :: zt).all (fun c => !f (pt n c)) = true)
    (ho : os.all (fun c => f (pt n c)) = true)
    (h : top n f (z1 :: zt) os k = false) : LB f (k + 1) := by
  intro t ht
  by_contra hlt
  have hr := Run_le (show t ≤ k by omega) ht
  set zs := z1 :: zt with hzs
  set x0 := pt n (zs.headD 0) with hx0
  set pts := ptl n zs ++ ptl n os with hpts
  set P := zs.length with hP
  have hPpos : 0 < P := by simp [hP, hzs]
  have hz' : ∀ c ∈ zs, f (pt n c) = false := by
    intro c hc
    have := List.all_eq_true.mp hz c hc
    simpa using this
  have ho' : ∀ c ∈ os, f (pt n c) = true := fun c hc => List.all_eq_true.mp ho c hc
  have hfx0 : f x0 = false := hz' z1 (by simp [hzs])
  have hbit : ∀ i, i < P → (code x0 pts f).testBit i = false ∧
      (code x0 pts f).testBit (P + i) = true := by
    intro i hi
    have hl1 : i < zs.length := hi
    have hl2 : i < os.length := by omega
    unfold code
    rw [enc_testBit, enc_testBit, hpts, List.map_append]
    constructor
    · rw [List.getD_append _ _ _ _ (by simpa [ptl] using hl1),
        List.getD_eq_getElem _ _ (by simpa [ptl] using hl1)]
      simp [ptl, hfx0, hz' _ (List.getElem_mem hl1)]
    · rw [List.getD_append_right _ _ _ _ (by simp [ptl, hP])]
      have e2 : P + i - (List.map (fun x => f x ^^ f x0) (ptl n zs)).length = i := by
        simp [ptl, hP]
      rw [e2, List.getD_eq_getElem _ _ (by simpa [ptl] using hl2)]
      simp [ptl, hfx0, ho' _ (List.getElem_mem hl2)]
  have hg : ∀ i, i < P → differs P i (code x0 pts f) := by
    intro i hi
    unfold differs
    rw [(hbit i hi).1, (hbit i hi).2]
    decide
  have hne : code x0 pts f ≠ 0 := by
    intro e
    have := (hbit 0 hPpos).2
    rw [e] at this
    simp at this
  have hb := sim x0 pts f hne k (Vars n)
    (((ic n zs os).filter fun c => !Nat.beq c 0).dedup).toFinset (by
      rintro w ⟨i, rfl⟩
      by_cases h0 : code x0 pts (fun x => x i) = 0
      · exact Or.inl h0
      · right
        rw [List.mem_toFinset, List.mem_dedup, List.mem_filter]
        refine ⟨List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩, ?_⟩
        have : Nat.beq (code x0 pts fun x => x i) 0 = false := by
          cases hb : Nat.beq (code x0 pts fun x => x i) 0
          · rfl
          · exact absurd (Nat.eq_of_beq_eq_true hb) h0
        rw [this]; rfl) hr
  have hs := search_complete hg k _ (List.nodup_dedup _) hb
  simp only [top, fz_eq, fzl_eq] at h
  exact Bool.noConfusion (h.symm.trans hs)
def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true

def bc (gs : List Gate) : ℕ := (gs.filter isBinary).length

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

section Compile
variable {n : ℕ}

def rd (ws : List (BF n)) (i : ℕ) : BF n := fun x => (ws.map fun w => w x).getD i false

theorem rd_K {S : BF n → Prop} {ws : List (BF n)} (hw : ∀ w ∈ ws, K S w) (i : ℕ) :
    K S (rd ws i) := by
  by_cases h : i < ws.length
  · have : rd ws i = ws[i] := by
      funext x
      simp [rd, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
    rw [this]
    exact hw _ (List.getElem_mem h)
  · refine Or.inl ⟨false, ?_⟩
    funext x
    simp [rd, List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

theorem gate_run {S : BF n → Prop} {ws : List (BF n)} (hw : ∀ w ∈ ws, K S w) (g : Gate)
    (hg : legal g) (z : BF n)
    (hz : z = fun x => g.op.eval (g.inputs.map fun i => rd ws i x)) :
    K S z ∨ (isBinary g = true ∧ ∃ a b : BF n, K S a ∧ K S b ∧ K (ins (fun x => a x && b x) S) z) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  subst hz
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩
  · left
    rcases hop with rfl | rfl | rfl
    · exact Or.inl ⟨true, rfl⟩
    · exact Or.inl ⟨false, rfl⟩
    · exact Or.inl ⟨true, rfl⟩
  · left
    rcases hop with rfl | rfl | rfl
    · have e : (fun x => GateOp.eval .and ([i].map fun i => rd ws i x)) = rd ws i :=
        funext fun x => by simp [GateOp.eval]
      simp only [e]; exact rd_K hw i
    · have e : (fun x => GateOp.eval .or ([i].map fun i => rd ws i x)) = rd ws i :=
        funext fun x => by simp [GateOp.eval]
      simp only [e]; exact rd_K hw i
    · exact K_not (rd_K hw i)
  · rcases hop with rfl | rfl | rfl
    · right
      refine ⟨rfl, rd ws i, rd ws j, rd_K hw i, rd_K hw j, ?_⟩
      have e : (fun x => GateOp.eval .and ([i, j].map fun i => rd ws i x)) =
          fun x => rd ws i x && rd ws j x := funext fun x => by simp [GateOp.eval]
      simp only [e]; exact K_new _
    · right
      refine ⟨rfl, _, _, K_not (rd_K hw i), K_not (rd_K hw j), ?_⟩
      have e : (fun x => GateOp.eval .or ([i, j].map fun i => rd ws i x)) =
          fun x => !(!rd ws i x && !rd ws j x) := funext fun x => by simp [GateOp.eval]
      simp only [e]; exact K_not (K_new _)
    · left
      exact K_not (rd_K hw i)
  · simp at cap

theorem compile (out : ℕ) : ∀ (gs : List Gate) (ws : List (BF n)) (S : BF n → Prop),
    (∀ g ∈ gs, legal g) → (∀ w ∈ ws, K S w) →
    Run (bc gs) S (fun x => (gs.foldl step (ws.map fun w => w x)).getD out false)
  | [], ws, S, _, hw => rd_K hw out
  | g :: gs, ws, S, hg, hw => by
    set z : BF n := fun x => g.op.eval (g.inputs.map fun i => rd ws i x) with hz
    have hst : ∀ x, step (ws.map fun w => w x) g = (ws ++ [z]).map fun w => w x := by
      intro x
      simp [step, hz, rd]
    have hfold : (fun x => ((g :: gs).foldl step (ws.map fun w => w x)).getD out false) =
        fun x => (gs.foldl step ((ws ++ [z]).map fun w => w x)).getD out false := by
      funext x
      rw [List.foldl_cons, hst x]
    rw [hfold]
    have tail := fun S' h => compile out gs (ws ++ [z]) S' (fun g' h' => hg g' (by simp [h'])) h
    have ext : ∀ S' : BF n → Prop, (∀ w ∈ ws, K S' w) → K S' z → ∀ w ∈ ws ++ [z], K S' w := by
      intro S' h1 h2 w hm
      rcases List.mem_append.mp hm with hm | hm
      · exact h1 w hm
      · exact (List.mem_singleton.mp hm) ▸ h2
    have hle : bc gs ≤ bc (g :: gs) := by
      unfold bc
      rw [List.filter_cons]
      split <;> simp
    rcases gate_run hw g (hg g (by simp)) z hz with h | ⟨hb, a, b, ha, hb2, h⟩
    · exact Run_le hle (tail S (ext S hw h))
    · have hbc : bc (g :: gs) = bc gs + 1 := by simp [bc, hb]
      rw [hbc]
      exact Or.inr ⟨a, b, ha, hb2, tail _ (ext _ (fun w hm => K_ins (hw w hm)) h)⟩

theorem bound_of_LB (F : BF n) (b : ℕ) (h : LB F b) (gs : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin n → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = F x) : b ≤ bc gs := by
  apply h
  have hr := compile o gs (List.ofFn fun i : Fin n => fun x : Fin n → Bool => x i) (Vars n) hg (by
    intro w hw
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp hw
    exact Or.inr (Or.inl ⟨i, rfl⟩))
  have e : (fun x : Fin n → Bool => (gs.foldl step ((List.ofFn fun i : Fin n =>
      fun x : Fin n → Bool => x i).map fun w => w x)).getD o false) = F := by
    funext x
    rw [← he x, List.map_ofFn]
    rfl
  rw [e] at hr
  exact hr

end Compile

def F : BF 6 := fun x => Nat.testBit (4278124202 * 2 ^ 32 + 4277075626) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def Fq : BF 6 := fun x => Nat.testBit (4278124202 * 2 ^ 32 + 4277075626)
  ((if x 0 = true then 1 else 0) + (if x 1 = true then 2 else 0) + (if x 2 = true then 4 else 0) + (if x 3 = true then 8 else 0) + (if x 4 = true then 16 else 0) + (if x 5 = true then 32 else 0))

theorem Fq_eq (x : Fin 6 → Bool) : Fq x = F x := by
  unfold F Fq
  rw [Fin.sum_univ_six]
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0 : LB Fq 5 := base Fq 0 [2, 2, 2, 4, 4, 6, 6, 6, 8, 8, 8, 16, 16, 20, 20, 20, 20, 24, 24, 24, 32, 34, 34, 34, 36, 36, 36, 38, 38, 38, 40, 40, 40, 48, 48, 48, 56, 56, 56, 2, 4, 6, 2, 6, 24, 20, 6, 6, 34, 36, 38, 34, 20, 38, 56, 56, 38, 38]
  [1, 3, 10, 18, 5, 12, 7, 14, 22, 9, 10, 12, 17, 18, 21, 22, 28, 52, 25, 26, 28, 33, 35, 42, 50, 37, 44, 52, 39, 46, 54, 41, 42, 44, 49, 50, 52, 57, 58, 60, 11, 13, 15, 19, 23, 27, 29, 30, 31, 43, 45, 47, 51, 53, 55, 59, 61, 62, 63] 4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def wg : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [4, 7]⟩, ⟨.or, [8, 3]⟩, ⟨.and, [9, 6]⟩, ⟨.or, [10, 0]⟩], 11⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wok : ∀ x : Fin 6 → Bool, wg.eval (List.ofFn x) = Fq x := by decide +kernel

theorem solve (s : ℕ) (hs : HasCircuitSize 6 F s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = F x := by
  obtain ⟨C, fits, size, computes⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : bc C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, mem, by simp [isBinary, op]⟩
    have hb := bound_of_LB Fq 5 b0 C.gates C.output fits (fun x => (computes x).trans (Fq_eq x).symm)
    refine ⟨wg, by simp [Monotone2, wg], ?_, fun x => (wok x).trans (Fq_eq x)⟩
    change 6 ≤ s
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := fits g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hasNot ⟨g, mem, eq⟩).elim)), cap⟩

end PEqualNP.Outside.L_meta_13051

theorem PEqualNP.Outside.L_meta_13051 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124202 * 2 ^ 32 + 4277075626) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124202 * 2 ^ 32 + 4277075626) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_13051.solve
