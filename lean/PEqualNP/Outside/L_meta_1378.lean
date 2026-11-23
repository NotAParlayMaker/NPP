import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1378_aux

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def val {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (run gates (List.ofFn x)).getD w false

lemma eval_eq_val {n : ℕ} (gates : List Gate) (w : ℕ) (x : Fin n → Bool) :
    Circuit.eval ⟨gates, w⟩ (List.ofFn x) = val gates x w :=
  rfl

lemma input_val {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (p : Fin n) :
    val gates x p.val = x p := by
  unfold val
  have hp : p.val < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_val {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : val gates x w = false := by
  unfold val
  exact List.getD_eq_default _ _ (by simpa [run_length] using hw)

lemma gate_val {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (j : Fin gates.length) :
    let g := gates.get j
    val gates x (n + j.val) = g.op.eval (g.inputs.map fun r => if r < n + j.val then val gates x r else false) := by
  let g := gates.get j
  let earlier := run (gates.take j.val) (List.ofFn x)
  have hj : j.val < gates.length := j.isLt
  have plen : earlier.length = n + j.val := by
    simp [earlier, run_length]
  have split : run gates (List.ofFn x) = run (g :: gates.drop (j.val + 1)) earlier := by
    rw [run_split gates (List.ofFn x) j.val, List.drop_eq_getElem_cons hj]
    rfl
  have read (r : ℕ) : earlier.getD r false = if r < n + j.val then val gates x r else false := by
    by_cases hr : r < n + j.val
    · rw [ite_eq_left hr]
      unfold val
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  unfold val
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]
  rfl

def fset {n m : ℕ} (S : Fin m → Finset (Fin n)) (w : Fin m) (x : Fin n → Bool) : Bool :=
  decide (∃ v ∈ S w, x v = true)

lemma fset_zero {n m : ℕ} (S : Fin m → Finset (Fin n)) (w : Fin m) :
    fset S w (fun _ => false) = false := by
  simp [fset]

lemma fset_single {n m : ℕ} (S : Fin m → Finset (Fin n)) (w : Fin m) (p : Fin n) :
    fset S w (fun v => decide (v = p)) = decide (p ∈ S w) := by
  simp [fset]

lemma exists_diff {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hcard : ∀ i : Fin m, 3 ≤ (S i).card)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    {w₁ w₂ : Fin m} (hne : w₁ ≠ w₂) :
    ∃ p ∈ S w₁, p ∉ S w₂ := by
  by_contra! hsub
  have h1 : S w₁ ∩ S w₂ = S w₁ := Finset.inter_eq_left.mpr hsub
  have h2 := hinter w₁ w₂ hne
  rw [h1] at h2
  have h3 := hcard w₁
  omega

lemma exists_ne_mem {n : ℕ} {A : Finset (Fin n)} (hA : 3 ≤ A.card) (r : ℕ) :
    ∃ p ∈ A, p.val ≠ r := by
  by_contra! hall
  have hsub : A.image Fin.val ⊆ {r} := by
    intro k hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_singleton.mpr (hall p hp)
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective A Fin.val_injective, Finset.card_singleton] at h1
  omega

lemma exists_two_mem {n : ℕ} {A : Finset (Fin n)} (hA : 2 ≤ A.card) :
    ∃ p₁ ∈ A, ∃ p₂ ∈ A, p₁ ≠ p₂ :=
  Finset.one_lt_card.mp (by omega)

def TagNeg {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (w : Fin m) (k : Fin gates.length) : Prop :=
  ∀ x : Fin n → Bool, val gates x (n + k.val) = !(fset S w x)

def TagSub2 {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (w : Fin m) (k : Fin gates.length) : Prop :=
  (∀ x : Fin n → Bool, val gates x (n + k.val) = true → fset S w x = true) ∧
  (∃ p₁ ∈ S w, ∃ p₂ ∈ S w, p₁ ≠ p₂ ∧
    val gates (fun v => decide (v = p₁)) (n + k.val) = true ∧
    val gates (fun v => decide (v = p₂)) (n + k.val) = true)

def TagSupOnly {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (w : Fin m) (k : Fin gates.length) : Prop :=
  (∀ x : Fin n → Bool, fset S w x = true → val gates x (n + k.val) = true) ∧
  (∀ w' : Fin m, w' ≠ w → ∃ x : Fin n → Bool, fset S w' x = true ∧ val gates x (n + k.val) = false)

def Tag {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (w : Fin m) (k : Fin gates.length) : Prop :=
  TagNeg S gates w k ∨ TagSub2 S gates w k ∨ TagSupOnly S gates w k

lemma tag_unique {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (hcard : ∀ i : Fin m, 3 ≤ (S i).card)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    {w₁ w₂ : Fin m} {k : Fin gates.length}
    (h1 : Tag S gates w₁ k) (h2 : Tag S gates w₂ k) : w₁ = w₂ := by
  by_contra hne
  have neg_vs_sub : ∀ {a b : Fin m}, TagNeg S gates a k → TagSub2 S gates b k → False := by
    intro a b hn hs
    have h0 := hn (fun _ => false)
    rw [fset_zero] at h0
    have hf := hs.1 (fun _ => false) h0
    rw [fset_zero] at hf
    exact Bool.false_ne_true hf
  have neg_vs_sup : ∀ {a b : Fin m}, a ≠ b → TagNeg S gates a k → TagSupOnly S gates b k → False := by
    intro a b hab hn hs
    obtain ⟨p, hpA, _⟩ := exists_diff S hcard hinter hab
    obtain ⟨q, hqB, _⟩ := exists_diff S hcard hinter hab.symm
    let x : Fin n → Bool := fun v => decide (v = p ∨ v = q)
    have ha : fset S a x = true := decide_eq_true ⟨p, hpA, by simp [x]⟩
    have hb : fset S b x = true := decide_eq_true ⟨q, hqB, by simp [x]⟩
    have hnt := hn x
    rw [ha] at hnt
    have hst := hs.1 x hb
    rw [hnt] at hst
    exact Bool.false_ne_true hst
  have sub_vs_sup : ∀ {a b : Fin m}, a ≠ b → TagSub2 S gates a k → TagSupOnly S gates b k → False := by
    intro a b hab hsub hsup
    obtain ⟨p, hpB, hpA⟩ := exists_diff S hcard hinter hab.symm
    let x : Fin n → Bool := fun v => decide (v = p)
    have hb : fset S b x = true := by rw [fset_single]; exact decide_eq_true hpB
    have ha : fset S a x = true := hsub.1 x (hsup.1 x hb)
    rw [fset_single, decide_eq_true_eq] at ha
    exact hpA ha
  rcases h1 with hn1 | hs1 | hu1 <;> rcases h2 with hn2 | hs2 | hu2
  · obtain ⟨p, hp1, hp2⟩ := exists_diff S hcard hinter hne
    let x : Fin n → Bool := fun v => decide (v = p)
    have e1 := hn1 x
    have e2 := hn2 x
    rw [fset_single, decide_eq_true hp1] at e1
    rw [fset_single, decide_eq_false hp2] at e2
    rw [e1] at e2
    exact Bool.false_ne_true e2
  · exact neg_vs_sub hn1 hs2
  · exact neg_vs_sup hne hn1 hu2
  · exact neg_vs_sub hn2 hs1
  · obtain ⟨p₁, hp₁, p₂, hp₂, hpne, hv₁, hv₂⟩ := hs1.2
    have hm1 : p₁ ∈ S w₂ := by
      have := hs2.1 _ hv₁
      rwa [fset_single, decide_eq_true_eq] at this
    have hm2 : p₂ ∈ S w₂ := by
      have := hs2.1 _ hv₂
      rwa [fset_single, decide_eq_true_eq] at this
    have hsub : ({p₁, p₂} : Finset (Fin n)) ⊆ S w₁ ∩ S w₂ := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hp₁, hm1⟩
      · exact Finset.mem_inter.mpr ⟨hp₂, hm2⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_pair hpne] at hc
    have := hinter w₁ w₂ hne
    omega
  · exact sub_vs_sup hne hs1 hu2
  · exact neg_vs_sup (Ne.symm hne) hn2 hu1
  · exact sub_vs_sup (Ne.symm hne) hs2 hu1
  · obtain ⟨x, hx2, hxf⟩ := hu1.2 w₂ (Ne.symm hne)
    have hxt := hu2.1 x hx2
    rw [hxf] at hxt
    exact Bool.false_ne_true hxt

lemma main {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hcard : ∀ i : Fin m, 3 ≤ (S i).card)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gates : List Gate) (out : Fin m → ℕ)
    (hG : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hout : ∀ (w : Fin m) (x : Fin n → Bool),
      Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) :
    2 * m ≤ gates.length := by
  classical
  have hout_val : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = fset S w x :=
    fun w x => hout w x
  have hout_gate : ∀ w : Fin m, ∃ k : Fin gates.length, out w = n + k.val := by
    intro w
    have hge : n ≤ out w := by
      by_contra! hlt
      obtain ⟨p, hp, hpne⟩ := exists_ne_mem (hcard w) (out w)
      have hv := hout_val w (fun v => decide (v = p))
      rw [fset_single, decide_eq_true hp] at hv
      have hi := input_val gates (fun v => decide (v = p)) ⟨out w, hlt⟩
      change val gates (fun v => decide (v = p)) (out w) = decide (⟨out w, hlt⟩ = p) at hi
      rw [hv] at hi
      have heq : (⟨out w, hlt⟩ : Fin n) = p := of_decide_eq_true hi.symm
      exact hpne (congrArg Fin.val heq).symm
    have hlt : out w < n + gates.length := by
      by_contra! hle
      obtain ⟨p, hp, _⟩ := exists_ne_mem (hcard w) 0
      have hv := hout_val w (fun v => decide (v = p))
      rw [missing_val gates _ _ hle, fset_single, decide_eq_true hp] at hv
      exact Bool.false_ne_true hv
    exact ⟨⟨out w - n, by omega⟩, by dsimp; omega⟩
  choose g hg using hout_gate
  have hg_val : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (n + (g w).val) = fset S w x := by
    intro w x
    rw [← hg w]
    exact hout_val w x
  have hg_inj : Function.Injective g := by
    intro w₁ w₂ heq
    by_contra hne
    obtain ⟨p, hp1, hp2⟩ := exists_diff S hcard hinter hne
    have e1 := hg_val w₁ (fun v => decide (v = p))
    have e2 := hg_val w₂ (fun v => decide (v = p))
    rw [heq] at e1
    rw [fset_single, decide_eq_true hp1] at e1
    rw [fset_single, decide_eq_false hp2] at e2
    rw [e1] at e2
    exact Bool.false_ne_true e2.symm
  have hex_tag : ∀ w : Fin m, ∃ k : Fin gates.length, k.val < (g w).val ∧ Tag S gates w k := by
    intro w
    let G := gates.get (g w)
    have hGmem : G ∈ gates := List.get_mem gates (g w)
    obtain ⟨hop, hlen⟩ := hG G hGmem
    let eff (r : ℕ) (x : Fin n → Bool) : Bool := if r < n + (g w).val then val gates x r else false
    have hform : ∀ x : Fin n → Bool, fset S w x = G.op.eval (G.inputs.map fun r => eff r x) := by
      intro x
      rw [← hg_val w x]
      exact gate_val gates x (g w)
    have hnot_case : ∀ u : ℕ, (∀ x, fset S w x = !(eff u x)) →
        ∃ k : Fin gates.length, k.val < (g w).val ∧ Tag S gates w k := by
      intro u hu
      have hult : u < n + (g w).val := by
        by_contra! hge
        have h0 := hu (fun _ => false)
        have h1 : eff u (fun _ => false) = false := by simp [eff, show ¬ u < n + (g w).val by omega]
        obtain ⟨p, hp, _⟩ := exists_ne_mem (hcard w) 0
        have hp' := hu (fun v => decide (v = p))
        have h2 : eff u (fun v => decide (v = p)) = false := by
          simp [eff, show ¬ u < n + (g w).val by omega]
        rw [fset_single, decide_eq_true hp, h2] at hp'
        rw [fset_zero, h1] at h0
        exact Bool.false_ne_true (h0.trans hp'.symm)
      have huge : n ≤ u := by
        by_contra! hlt
        have h0 := hu (fun _ => false)
        have h1 : eff u (fun _ => false) = false := by
          simp only [eff, ite_eq_left hult]
          exact input_val gates (fun _ => false) ⟨u, hlt⟩
        rw [fset_zero, h1] at h0
        exact Bool.false_ne_true h0
      refine ⟨⟨u - n, by omega⟩, by dsimp; omega, Or.inl ?_⟩
      intro x
      have hx := hu x
      have he : eff u x = val gates x (n + (u - n)) := by
        simp only [eff, ite_eq_left hult]
        congr 1
        omega
      rw [he] at hx
      cases hb : val gates x (n + (u - n)) <;> rw [hb] at hx <;> simp [hx]
    have hsub2_case : ∀ u : ℕ,
        (∀ x, eff u x = true → fset S w x = true) →
        (∃ p₁ ∈ S w, ∃ p₂ ∈ S w, p₁ ≠ p₂ ∧
          eff u (fun v => decide (v = p₁)) = true ∧ eff u (fun v => decide (v = p₂)) = true) →
        ∃ k : Fin gates.length, k.val < (g w).val ∧ Tag S gates w k := by
      intro u hsound ⟨p₁, hp₁, p₂, hp₂, hpne, hv₁, hv₂⟩
      have hult : u < n + (g w).val := by
        by_contra! hge
        simp [eff, show ¬ u < n + (g w).val by omega] at hv₁
      have huge : n ≤ u := by
        by_contra! hlt
        simp only [eff, ite_eq_left hult] at hv₁ hv₂
        have i1 := input_val gates (fun v => decide (v = p₁)) ⟨u, hlt⟩
        have i2 := input_val gates (fun v => decide (v = p₂)) ⟨u, hlt⟩
        change val gates _ u = decide (⟨u, hlt⟩ = p₁) at i1
        change val gates _ u = decide (⟨u, hlt⟩ = p₂) at i2
        rw [hv₁] at i1
        rw [hv₂] at i2
        have e1 : (⟨u, hlt⟩ : Fin n) = p₁ := of_decide_eq_true i1.symm
        have e2 : (⟨u, hlt⟩ : Fin n) = p₂ := of_decide_eq_true i2.symm
        exact hpne (e1.symm.trans e2)
      have heq : n + (u - n) = u := by omega
      refine ⟨⟨u - n, by omega⟩, by dsimp; omega, Or.inr (Or.inl ⟨?_, ?_⟩)⟩
      · intro x hx
        apply hsound x
        simp only [eff, ite_eq_left hult]
        rwa [heq] at hx
      · refine ⟨p₁, hp₁, p₂, hp₂, hpne, ?_, ?_⟩
        · simp only [eff, ite_eq_left hult] at hv₁
          rwa [heq]
        · simp only [eff, ite_eq_left hult] at hv₂
          rwa [heq]
    have hsup_case : ∀ u : ℕ,
        (∀ x, fset S w x = true → eff u x = true) →
        (∀ w' : Fin m, w' ≠ w → ∃ x : Fin n → Bool, fset S w' x = true ∧ eff u x = false) →
        ∃ k : Fin gates.length, k.val < (g w).val ∧ Tag S gates w k := by
      intro u hsup hnotother
      have hult : u < n + (g w).val := by
        by_contra! hge
        obtain ⟨p, hp, _⟩ := exists_ne_mem (hcard w) 0
        have hfp : fset S w (fun v => decide (v = p)) = true := by
          rw [fset_single]; exact decide_eq_true hp
        have hu := hsup _ hfp
        simp [eff, show ¬ u < n + (g w).val by omega] at hu
      have huge : n ≤ u := by
        by_contra! hlt
        obtain ⟨p, hp, hpne⟩ := exists_ne_mem (hcard w) u
        have hfp : fset S w (fun v => decide (v = p)) = true := by
          rw [fset_single]; exact decide_eq_true hp
        have hu := hsup _ hfp
        simp only [eff, ite_eq_left hult] at hu
        have hi := input_val gates (fun v => decide (v = p)) ⟨u, hlt⟩
        change val gates _ u = decide (⟨u, hlt⟩ = p) at hi
        rw [hu] at hi
        have heq : (⟨u, hlt⟩ : Fin n) = p := of_decide_eq_true hi.symm
        exact hpne (congrArg Fin.val heq).symm
      have heq : n + (u - n) = u := by omega
      refine ⟨⟨u - n, by omega⟩, by dsimp; omega, Or.inr (Or.inr ⟨?_, ?_⟩)⟩
      · intro x hx
        have hu := hsup x hx
        simp only [eff, ite_eq_left hult] at hu
        rwa [heq]
      · intro w' hw'
        obtain ⟨x, hxw', hxu⟩ := hnotother w' hw'
        simp only [eff, ite_eq_left hult] at hxu
        exact ⟨x, hxw', by rwa [heq]⟩
    cases hin : G.inputs with
    | nil =>
      obtain ⟨p, hp, _⟩ := exists_ne_mem (hcard w) 0
      have h0 := hform (fun _ => false)
      have h1 := hform (fun v => decide (v = p))
      rw [hin, fset_zero] at h0
      rw [hin, fset_single, decide_eq_true hp] at h1
      exact absurd (h0.trans h1.symm) Bool.false_ne_true
    | cons u rest =>
      cases rest with
      | nil =>
        rcases hop with hop | hop | hop
        · have heq : ∀ x, fset S w x = eff u x := by
            intro x
            have hx := hform x
            simpa [hin, hop, GateOp.eval] using hx
          obtain ⟨p₁, hp₁, p₂, hp₂, hpne⟩ := exists_two_mem (A := S w) (by have := hcard w; omega)
          refine hsub2_case u (fun x hx => by rw [heq]; exact hx)
            ⟨p₁, hp₁, p₂, hp₂, hpne, ?_, ?_⟩
          · rw [← heq, fset_single]; exact decide_eq_true hp₁
          · rw [← heq, fset_single]; exact decide_eq_true hp₂
        · have heq : ∀ x, fset S w x = eff u x := by
            intro x
            have hx := hform x
            simpa [hin, hop, GateOp.eval] using hx
          obtain ⟨p₁, hp₁, p₂, hp₂, hpne⟩ := exists_two_mem (A := S w) (by have := hcard w; omega)
          refine hsub2_case u (fun x hx => by rw [heq]; exact hx)
            ⟨p₁, hp₁, p₂, hp₂, hpne, ?_, ?_⟩
          · rw [← heq, fset_single]; exact decide_eq_true hp₁
          · rw [← heq, fset_single]; exact decide_eq_true hp₂
        · refine hnot_case u (fun x => ?_)
          have hx := hform x
          simpa [hin, hop, GateOp.eval] using hx
      | cons v tail =>
        cases tail with
        | nil =>
          rcases hop with hop | hop | hop
          · have heq : ∀ x, fset S w x = (eff u x && eff v x) := by
              intro x
              have hx := hform x
              simpa [hin, hop, GateOp.eval] using hx
            have hu_sup : ∀ x, fset S w x = true → eff u x = true := by
              intro x hx
              rw [heq] at hx
              exact (Bool.and_eq_true _ _).mp hx |>.1
            have hv_sup : ∀ x, fset S w x = true → eff v x = true := by
              intro x hx
              rw [heq] at hx
              exact (Bool.and_eq_true _ _).mp hx |>.2
            by_cases hu : ∀ w' : Fin m, w' ≠ w → ∃ x : Fin n → Bool, fset S w' x = true ∧ eff u x = false
            · exact hsup_case u hu_sup hu
            · push Not at hu
              obtain ⟨w₁, hw₁, hu₁⟩ := hu
              have hv : ∀ w' : Fin m, w' ≠ w → ∃ x : Fin n → Bool, fset S w' x = true ∧ eff v x = false := by
                intro w₂ hw₂
                by_contra! hv₂
                obtain ⟨p, hp1, hpnw⟩ := exists_diff S hcard hinter hw₁
                obtain ⟨q, hq2, hqnw⟩ := exists_diff S hcard hinter hw₂
                let x : Fin n → Bool := fun r => decide (r = p ∨ r = q)
                have hfw1 : fset S w₁ x = true := decide_eq_true ⟨p, hp1, by simp [x]⟩
                have hfw2 : fset S w₂ x = true := decide_eq_true ⟨q, hq2, by simp [x]⟩
                have hux : eff u x = true := by
                  have := hu₁ x hfw1
                  simpa using this
                have hvx : eff v x = true := by
                  have := hv₂ x hfw2
                  simpa using this
                have hfw : fset S w x = true := by
                  rw [heq, hux, hvx]
                  rfl
                obtain ⟨r, hrw, hrx⟩ := of_decide_eq_true hfw
                simp only [x, decide_eq_true_eq] at hrx
                rcases hrx with rfl | rfl
                · exact hpnw hrw
                · exact hqnw hrw
              exact hsup_case v hv_sup hv
          · have heq : ∀ x, fset S w x = (eff u x || eff v x) := by
              intro x
              have hx := hform x
              simpa [hin, hop, GateOp.eval] using hx
            have hu_sub : ∀ x, eff u x = true → fset S w x = true := by
              intro x hx
              rw [heq, hx]
              rfl
            have hv_sub : ∀ x, eff v x = true → fset S w x = true := by
              intro x hx
              rw [heq, hx]
              simp
            let Au := (S w).filter (fun p => eff u (fun r => decide (r = p)) = true)
            let Av := (S w).filter (fun p => eff v (fun r => decide (r = p)) = true)
            have hcov : S w ⊆ Au ∪ Av := by
              intro p hp
              have hfp : fset S w (fun r => decide (r = p)) = true := by
                rw [fset_single]; exact decide_eq_true hp
              rw [heq, Bool.or_eq_true] at hfp
              rcases hfp with h | h
              · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, h⟩)
              · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, h⟩)
            have hsum := (Finset.card_le_card hcov).trans (Finset.card_union_le Au Av)
            have hcw := hcard w
            by_cases hAu : 2 ≤ Au.card
            · obtain ⟨p₁, hp₁, p₂, hp₂, hpne⟩ := exists_two_mem hAu
              have h1 := Finset.mem_filter.mp hp₁
              have h2 := Finset.mem_filter.mp hp₂
              exact hsub2_case u hu_sub ⟨p₁, h1.1, p₂, h2.1, hpne, h1.2, h2.2⟩
            · have hAv : 2 ≤ Av.card := by omega
              obtain ⟨p₁, hp₁, p₂, hp₂, hpne⟩ := exists_two_mem hAv
              have h1 := Finset.mem_filter.mp hp₁
              have h2 := Finset.mem_filter.mp hp₂
              exact hsub2_case v hv_sub ⟨p₁, h1.1, p₂, h2.1, hpne, h1.2, h2.2⟩
          · refine hnot_case u (fun x => ?_)
            have hx := hform x
            simpa [hin, hop, GateOp.eval] using hx
        | cons _ _ =>
          rw [hin] at hlen
          simp at hlen
  choose h hh_lt hh_tag using hex_tag
  have hh_inj : Function.Injective h := by
    intro w₁ w₂ heq
    exact tag_unique S gates hcard hinter (hh_tag w₁) (heq ▸ hh_tag w₂)
  have hdisj : Disjoint (Finset.univ.image g) (Finset.univ.image h) := by
    rw [Finset.disjoint_left]
    intro k hkg hkh
    obtain ⟨w₁, _, rfl⟩ := Finset.mem_image.mp hkg
    obtain ⟨w₂, _, hk2⟩ := Finset.mem_image.mp hkh
    by_cases hw : w₁ = w₂
    · subst hw
      have hlt := hh_lt w₁
      rw [hk2] at hlt
      exact lt_irrefl _ hlt
    · rcases hk2 ▸ hh_tag w₂ with hn | hs | hu
      · have h0 := hn (fun _ => false)
        rw [hg_val w₁, fset_zero, fset_zero] at h0
        exact Bool.false_ne_true h0
      · obtain ⟨p₁, hp₁, p₂, hp₂, hpne, hv₁, hv₂⟩ := hs.2
        rw [hg_val w₁, fset_single, decide_eq_true_eq] at hv₁ hv₂
        have hsub : ({p₁, p₂} : Finset (Fin n)) ⊆ S w₁ ∩ S w₂ := by
          intro v hv
          simp only [Finset.mem_insert, Finset.mem_singleton] at hv
          rcases hv with rfl | rfl
          · exact Finset.mem_inter.mpr ⟨hv₁, hp₁⟩
          · exact Finset.mem_inter.mpr ⟨hv₂, hp₂⟩
        have hc := Finset.card_le_card hsub
        rw [Finset.card_pair hpne] at hc
        have := hinter w₁ w₂ hw
        omega
      · obtain ⟨x, hx1, hxf⟩ := hu.2 w₁ hw
        rw [hg_val w₁] at hxf
        rw [hx1] at hxf
        exact Bool.false_ne_true hxf.symm
  have hle : (Finset.univ.image g ∪ Finset.univ.image h).card ≤
      (Finset.univ : Finset (Fin gates.length)).card :=
    Finset.card_le_card (Finset.subset_univ _)
  rw [Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ hg_inj,
      Finset.card_image_of_injective _ hh_inj,
      Finset.card_univ, Finset.card_univ, Fintype.card_fin, Fintype.card_fin] at hle
  omega

end PEqualNP.Outside.L_meta_1378_aux

theorem PEqualNP.Outside.L_meta_1378 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), 2 ≤ m → (∀ i : Fin m, 3 ≤ (S i).card) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) → 2 * m ≤ gates.length := by
  intro n m S _ hcard hinter gates out hG hout
  exact PEqualNP.Outside.L_meta_1378_aux.main S hcard hinter gates out hG hout
