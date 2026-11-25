import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5505

open PEqualNP.CircuitLowerBounds

def Ops {α : Type} (S : Set (α → Bool)) : Set (α → Bool) :=
  {g | ∃ a ∈ S, ∃ b ∈ S, g = (fun x => a x && b x) ∨ g = (fun x => a x || b x) ∨
    g = (fun x => !a x)}

def Chain {α : Type} : Set (α → Bool) → List (α → Bool) → Prop
  | _, [] => True
  | S, g :: L => g ∈ Ops S ∧ Chain (insert g S) L

lemma chain_cons {α : Type} (S : Set (α → Bool)) (g : α → Bool) (L : List (α → Bool)) :
    Chain S (g :: L) ↔ g ∈ Ops S ∧ Chain (insert g S) L := Iff.rfl

lemma ops_mono {α : Type} {S S' : Set (α → Bool)} (h : S ⊆ S') : Ops S ⊆ Ops S' := by
  rintro g ⟨a, ha, b, hb, hf⟩
  exact ⟨a, h ha, b, h hb, hf⟩

lemma chain_mono {α : Type} : ∀ (L : List (α → Bool)) (S S' : Set (α → Bool)), S ⊆ S' →
    Chain S L → Chain S' L := by
  intro L
  induction L with
  | nil => intro S S' _ _; exact True.intro
  | cons g L ih =>
    intro S S' h hc
    obtain ⟨h1, h2⟩ := (chain_cons _ _ _).1 hc
    exact (chain_cons _ _ _).2 ⟨ops_mono h h1, ih _ _ (Set.insert_subset_insert h) h2⟩

lemma chain_comp {α β : Type} (ι : β → α) : ∀ (L : List (α → Bool)) (S : Set (α → Bool)),
    Chain S L →
      Chain ((fun b : α → Bool => fun x => b (ι x)) '' S)
        (L.map (fun b : α → Bool => fun x => b (ι x))) := by
  intro L
  induction L with
  | nil => intro S _; exact True.intro
  | cons g L ih =>
    intro S hc
    obtain ⟨hg, hL⟩ := (chain_cons _ _ _).1 hc
    rw [List.map_cons]
    refine (chain_cons _ _ _).2 ⟨?_, ?_⟩
    · obtain ⟨a, ha, b, hb, hf⟩ := hg
      refine ⟨fun x => a (ι x), Set.mem_image_of_mem _ ha, fun x => b (ι x),
        Set.mem_image_of_mem _ hb, ?_⟩
      rcases hf with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · have h := ih _ hL
      rwa [Set.image_insert_eq] at h

lemma and_case {α : Type} (S : Set (α → Bool)) (hF : (fun _ => false) ∈ S)
    (hT : (fun _ => true) ∈ S) (a b a' b' : α → Bool) (ha : a ∈ S) (hb : b ∈ S)
    (ea : a' = a ∨ a' = (fun _ => false) ∨ a' = (fun _ => true))
    (eb : b' = b ∨ b' = (fun _ => false) ∨ b' = (fun _ => true)) :
    (fun x => a' x && b' x) ∈ S ∨ (a' = a ∧ b' = b) := by
  rcases ea with rfl | rfl | rfl <;> rcases eb with rfl | rfl | rfl
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl (Set.mem_of_eq_of_mem (by funext x; simp) hF)
  · exact Or.inl (Set.mem_of_eq_of_mem (by funext x; simp) ha)
  · exact Or.inl (Set.mem_of_eq_of_mem (by funext x; simp) hF)
  · exact Or.inl (Set.mem_of_eq_of_mem (by funext x; simp) hF)
  · exact Or.inl (Set.mem_of_eq_of_mem (by funext x; simp) hF)
  · exact Or.inl (Set.mem_of_eq_of_mem (by funext x; simp) hb)
  · exact Or.inl (Set.mem_of_eq_of_mem (by funext x; simp) hF)
  · exact Or.inl (Set.mem_of_eq_of_mem (by funext x; simp) hT)

lemma or_case {α : Type} (S : Set (α → Bool)) (hF : (fun _ => false) ∈ S)
    (hT : (fun _ => true) ∈ S) (a b a' b' : α → Bool) (ha : a ∈ S) (hb : b ∈ S)
    (ea : a' = a ∨ a' = (fun _ => false) ∨ a' = (fun _ => true))
    (eb : b' = b ∨ b' = (fun _ => false) ∨ b' = (fun _ => true)) :
    (fun x => a' x || b' x) ∈ S ∨ (a' = a ∧ b' = b) := by
  rcases ea with rfl | rfl | rfl <;> rcases eb with rfl | rfl | rfl
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl (Set.mem_of_eq_of_mem (by funext x; simp) ha)
  · exact Or.inl (Set.mem_of_eq_of_mem (by funext x; simp) hT)
  · exact Or.inl (Set.mem_of_eq_of_mem (by funext x; simp) hb)
  · exact Or.inl (Set.mem_of_eq_of_mem (by funext x; simp) hF)
  · exact Or.inl (Set.mem_of_eq_of_mem (by funext x; simp) hT)
  · exact Or.inl (Set.mem_of_eq_of_mem (by funext x; simp) hT)
  · exact Or.inl (Set.mem_of_eq_of_mem (by funext x; simp) hT)
  · exact Or.inl (Set.mem_of_eq_of_mem (by funext x; simp) hT)

lemma not_case {α : Type} (S : Set (α → Bool)) (hF : (fun _ => false) ∈ S)
    (hT : (fun _ => true) ∈ S) (a a' : α → Bool)
    (ea : a' = a ∨ a' = (fun _ => false) ∨ a' = (fun _ => true)) :
    (fun x => !a' x) ∈ S ∨ a' = a := by
  rcases ea with rfl | rfl | rfl
  · exact Or.inr rfl
  · exact Or.inl (Set.mem_of_eq_of_mem (by funext x; simp) hT)
  · exact Or.inl (Set.mem_of_eq_of_mem (by funext x; simp) hF)

lemma elim {α : Type} (ι : α → α) : ∀ (L : List (α → Bool)) (S : Set (α → Bool)),
    (fun _ => false) ∈ S → (fun _ => true) ∈ S →
    (∀ b ∈ S, (fun x => b (ι x)) = b ∨ (fun x => b (ι x)) = (fun _ => false) ∨
      (fun x => b (ι x)) = (fun _ => true)) →
    Chain S L → ∀ h : α → Bool, h ∈ L → (fun x => h (ι x)) ≠ h →
    ∃ L' : List (α → Bool), L'.length + 1 ≤ L.length ∧ Chain S L' ∧
      ((fun x => h (ι x)) ∈ S ∨ (fun x => h (ι x)) ∈ L') := by
  intro L
  induction L with
  | nil => intro S _ _ _ _ h hh _; simp at hh
  | cons g L ih =>
    intro S hF hT hst hc h hh hne
    obtain ⟨hg, hL⟩ := (chain_cons _ _ _).1 hc
    have himg : ∀ b ∈ S, (fun x => b (ι x)) ∈ S := by
      intro b hb
      rcases hst b hb with e | e | e
      · rw [e]; exact hb
      · rw [e]; exact hF
      · rw [e]; exact hT
    by_cases hinv : (fun x => g (ι x)) = g
    · have hst' : ∀ b ∈ insert g S, (fun x => b (ι x)) = b ∨
          (fun x => b (ι x)) = (fun _ => false) ∨ (fun x => b (ι x)) = (fun _ => true) := by
        intro b hb
        rcases Set.mem_insert_iff.1 hb with e | hb
        · rw [e]; exact Or.inl hinv
        · exact hst b hb
      rcases List.mem_cons.1 hh with e | hh'
      · rw [e] at hne; exact absurd hinv hne
      · obtain ⟨L', h1, h2, h3⟩ := ih (insert g S) (Set.mem_insert_of_mem _ hF)
          (Set.mem_insert_of_mem _ hT) hst' hL h hh' hne
        refine ⟨g :: L', by simp only [List.length_cons]; omega,
          (chain_cons _ _ _).2 ⟨hg, h2⟩, ?_⟩
        rcases h3 with h3 | h3
        · rcases Set.mem_insert_iff.1 h3 with e | h3
          · exact Or.inr (List.mem_cons.2 (Or.inl e))
          · exact Or.inl h3
        · exact Or.inr (List.mem_cons.2 (Or.inr h3))
    · have hgS : (fun x => g (ι x)) ∈ S := by
        obtain ⟨a, ha, b, hb, hf⟩ := hg
        rcases hf with rfl | rfl | rfl
        · rcases and_case S hF hT a b (fun x => a (ι x)) (fun x => b (ι x)) ha hb
            (hst a ha) (hst b hb) with h1 | ⟨h1, h2⟩
          · exact h1
          · exfalso
            apply hinv
            funext x
            have e1 : a (ι x) = a x := congrFun h1 x
            have e2 : b (ι x) = b x := congrFun h2 x
            show (a (ι x) && b (ι x)) = (a x && b x)
            rw [e1, e2]
        · rcases or_case S hF hT a b (fun x => a (ι x)) (fun x => b (ι x)) ha hb
            (hst a ha) (hst b hb) with h1 | ⟨h1, h2⟩
          · exact h1
          · exfalso
            apply hinv
            funext x
            have e1 : a (ι x) = a x := congrFun h1 x
            have e2 : b (ι x) = b x := congrFun h2 x
            show (a (ι x) || b (ι x)) = (a x || b x)
            rw [e1, e2]
        · rcases not_case S hF hT a (fun x => a (ι x)) (hst a ha) with h1 | h1
          · exact h1
          · exfalso
            apply hinv
            funext x
            have e1 : a (ι x) = a x := congrFun h1 x
            show (!a (ι x)) = !a x
            rw [e1]
      refine ⟨L.map (fun b : α → Bool => fun x => b (ι x)), by simp, ?_, ?_⟩
      · refine chain_mono _ _ _ ?_ (chain_comp ι L _ hL)
        rintro y ⟨b, hb, rfl⟩
        rcases Set.mem_insert_iff.1 hb with e | hb
        · rw [e]; exact hgS
        · exact himg b hb
      · rcases List.mem_cons.1 hh with e | hh'
        · rw [e]; exact Or.inl hgS
        · exact Or.inr (List.mem_map.2 ⟨h, hh', rfl⟩)

def gfn {n : ℕ} (W : List ((Fin n → Bool) → Bool)) (g : Gate) : (Fin n → Bool) → Bool :=
  fun x => g.op.eval (g.inputs.map fun i => (W.getD i (fun _ => false)) x)

lemma getD_map_app {β : Type} (W : List (β → Bool)) (x : β) : ∀ i : ℕ,
    (W.map (fun h => h x)).getD i false = (W.getD i (fun _ => false)) x := by
  induction W with
  | nil => intro i; simp
  | cons h t ih =>
    intro i
    cases i with
    | zero => simp
    | succ k => simpa using ih k

lemma wires_eq {n : ℕ} (gs : List Gate) : ∀ (W : List ((Fin n → Bool) → Bool))
    (x : Fin n → Bool),
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (W.map (fun h => h x)) =
      (gs.foldl (fun W g => W ++ [gfn W g]) W).map (fun h => h x) := by
  induction gs with
  | nil => intro W x; rfl
  | cons g gs ih =>
    intro W x
    have e : (fun i => (W.map (fun h => h x)).getD i false) =
        (fun i => (W.getD i (fun _ => false)) x) := funext (getD_map_app W x)
    simp only [List.foldl_cons]
    rw [← ih (W ++ [gfn W g]) x, List.map_append, List.map_cons, List.map_nil, e]
    rfl

lemma gfn_mem {n : ℕ} (S : Set ((Fin n → Bool) → Bool)) (hF : (fun _ => false) ∈ S)
    (hT : (fun _ => true) ∈ S) (W : List ((Fin n → Bool) → Bool)) (hW : ∀ h ∈ W, h ∈ S)
    (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) : gfn W g ∈ Ops S := by
  have hget : ∀ i : ℕ, W.getD i (fun _ => false) ∈ S := by
    intro i
    by_cases hi : i < W.length
    · rw [List.getD_eq_getElem _ _ hi]; exact hW _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]; exact hF
  obtain ⟨op, inputs⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k, rest⟩⟩⟩
  · rcases hop with rfl | rfl | rfl
    · exact ⟨_, hT, _, hT, Or.inl (by funext x; simp [gfn, GateOp.eval])⟩
    · exact ⟨_, hF, _, hF, Or.inr (Or.inl (by funext x; simp [gfn, GateOp.eval]))⟩
    · exact ⟨_, hF, _, hF, Or.inr (Or.inr (by funext x; simp [gfn, GateOp.eval]))⟩
  · rcases hop with rfl | rfl | rfl
    · exact ⟨_, hget i, _, hget i, Or.inl (by funext x; simp [gfn, GateOp.eval])⟩
    · exact ⟨_, hget i, _, hget i, Or.inr (Or.inl (by funext x; simp [gfn, GateOp.eval]))⟩
    · exact ⟨_, hget i, _, hget i, Or.inr (Or.inr (by funext x; simp [gfn, GateOp.eval]))⟩
  · rcases hop with rfl | rfl | rfl
    · exact ⟨_, hget i, _, hget j, Or.inl (by funext x; simp [gfn, GateOp.eval])⟩
    · exact ⟨_, hget i, _, hget j, Or.inr (Or.inl (by funext x; simp [gfn, GateOp.eval]))⟩
    · exact ⟨_, hget i, _, hget i, Or.inr (Or.inr (by funext x; simp [gfn, GateOp.eval]))⟩
  · simp at hlen

lemma chain_of_gates {n : ℕ} : ∀ (gs : List Gate) (S : Set ((Fin n → Bool) → Bool))
    (W : List ((Fin n → Bool) → Bool)),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) →
    (fun _ => false) ∈ S → (fun _ => true) ∈ S → (∀ h ∈ W, h ∈ S) →
    ∃ L : List ((Fin n → Bool) → Bool), L.length = gs.length ∧ Chain S L ∧
      ∀ h ∈ gs.foldl (fun W g => W ++ [gfn W g]) W, h ∈ S ∨ h ∈ L := by
  intro gs
  induction gs with
  | nil =>
    intro S W _ _ _ hW
    exact ⟨[], rfl, True.intro, fun h hh => Or.inl (hW h hh)⟩
  | cons g gs ih =>
    intro S W hg hF hT hW
    have hg0 := hg g (List.mem_cons.2 (Or.inl rfl))
    have hgm := gfn_mem S hF hT W hW g hg0.1 hg0.2
    obtain ⟨L, h1, h2, h3⟩ := ih (insert (gfn W g) S) (W ++ [gfn W g])
      (fun g' hg' => hg g' (List.mem_cons.2 (Or.inr hg')))
      (Set.mem_insert_of_mem _ hF) (Set.mem_insert_of_mem _ hT)
      (by
        intro h hh
        rcases List.mem_append.1 hh with hh | hh
        · exact Set.mem_insert_of_mem _ (hW h hh)
        · rw [List.mem_singleton.1 hh]; exact Set.mem_insert _ _)
    refine ⟨gfn W g :: L, by simp [h1], (chain_cons _ _ _).2 ⟨hgm, h2⟩, ?_⟩
    intro h hh
    rw [List.foldl_cons] at hh
    rcases h3 h hh with h4 | h4
    · rcases Set.mem_insert_iff.1 h4 with e | h4
      · exact Or.inr (List.mem_cons.2 (Or.inl e))
      · exact Or.inl h4
    · exact Or.inr (List.mem_cons.2 (Or.inr h4))

def fE (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) ||
    (x 1 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 3) || (x 2 && x 4) ||
    (x 2 && x 5)

def upd (i : Fin 6) (x : Fin 6 → Bool) : Fin 6 → Bool := fun j => if j = i then false else x j

def B6 : Set ((Fin 6 → Bool) → Bool) :=
  {h | h = (fun _ => false) ∨ h = (fun _ => true) ∨ ∃ i : Fin 6, h = fun x => x i}

lemma f6 : (fun _ => false) ∈ B6 := Or.inl rfl

lemma t6 : (fun _ => true) ∈ B6 := Or.inr (Or.inl rfl)

lemma v6 (i : Fin 6) : (fun x : Fin 6 → Bool => x i) ∈ B6 := Or.inr (Or.inr ⟨i, rfl⟩)

def vars6 : List ((Fin 6 → Bool) → Bool) := List.ofFn (fun i : Fin 6 => fun x : Fin 6 → Bool => x i)

lemma stable6 (i : Fin 6) : ∀ b ∈ B6, (fun x => b (upd i x)) = b ∨
    (fun x => b (upd i x)) = (fun _ => false) ∨ (fun x => b (upd i x)) = (fun _ => true) := by
  rintro b (rfl | rfl | ⟨j, rfl⟩)
  · exact Or.inl rfl
  · exact Or.inl rfl
  · by_cases hj : j = i
    · right; left; funext x; simp [upd, hj]
    · left; funext x; simp [upd, hj]

lemma step6 (i : Fin 6) (L : List ((Fin 6 → Bool) → Bool)) (h : (Fin 6 → Bool) → Bool)
    (hc : Chain B6 L) (hm : h ∈ B6 ∨ h ∈ L)
    (hne : (fun x => h (upd i x)) ≠ h) (hnF : (fun x => h (upd i x)) ≠ (fun _ => false))
    (hnT : (fun x => h (upd i x)) ≠ (fun _ => true)) :
    ∃ L' : List ((Fin 6 → Bool) → Bool), L'.length + 1 ≤ L.length ∧ Chain B6 L' ∧
      ((fun x => h (upd i x)) ∈ B6 ∨ (fun x => h (upd i x)) ∈ L') := by
  rcases hm with hm | hm
  · rcases stable6 i h hm with e | e | e
    · exact absurd e hne
    · exact absurd e hnF
    · exact absurd e hnT
  · exact elim (upd i) L B6 f6 t6 (stable6 i) hc h hm hne

def pA : Fin 6 → Bool := fun j => decide (j = 0 ∨ j = 1)

def pZ : Fin 6 → Bool := fun _ => false

def p15 : Fin 6 → Bool := fun j => decide (j = 1 ∨ j = 5)

def p14 : Fin 6 → Bool := fun j => decide (j = 1 ∨ j = 4)

def p23 : Fin 6 → Bool := fun j => decide (j = 2 ∨ j = 3)

lemma ne1 : (fun x => fE (upd 5 x)) ≠ fE :=
  fun e => absurd (congrFun e p15) (by decide)

lemma nF1 : (fun x => fE (upd 5 x)) ≠ (fun _ => false) :=
  fun e => absurd (congrFun e pA) (by decide)

lemma nT1 : (fun x => fE (upd 5 x)) ≠ (fun _ => true) :=
  fun e => absurd (congrFun e pZ) (by decide)

lemma ne2 : (fun x => fE (upd 5 (upd 4 x))) ≠ (fun x => fE (upd 5 x)) :=
  fun e => absurd (congrFun e p14) (by decide)

lemma nF2 : (fun x => fE (upd 5 (upd 4 x))) ≠ (fun _ => false) :=
  fun e => absurd (congrFun e pA) (by decide)

lemma nT2 : (fun x => fE (upd 5 (upd 4 x))) ≠ (fun _ => true) :=
  fun e => absurd (congrFun e pZ) (by decide)

lemma ne3 : (fun x => fE (upd 5 (upd 4 (upd 2 x)))) ≠ (fun x => fE (upd 5 (upd 4 x))) :=
  fun e => absurd (congrFun e p23) (by decide)

lemma nF3 : (fun x => fE (upd 5 (upd 4 (upd 2 x)))) ≠ (fun _ => false) :=
  fun e => absurd (congrFun e pA) (by decide)

lemma nT3 : (fun x => fE (upd 5 (upd 4 (upd 2 x)))) ≠ (fun _ => true) :=
  fun e => absurd (congrFun e pZ) (by decide)

def idx (p : Bool × Bool × Bool) : ℕ :=
  (if p.1 then 1 else 0) + (if p.2.1 then 2 else 0) + (if p.2.2 then 4 else 0)

def dec (m : ℕ) : Bool × Bool × Bool → Bool := fun p => m.testBit (idx p)

def emb (p : Bool × Bool × Bool) : Fin 6 → Bool :=
  fun j => if j = 0 then p.1 else if j = 1 then p.2.1 else if j = 3 then p.2.2 else false

def cands (T : List ℕ) : List ℕ :=
  T.flatMap fun a => (255 ^^^ a) :: T.flatMap fun b => [a &&& b, a ||| b]

def reach : ℕ → List ℕ → Bool
  | 0, T => T.contains 232
  | k + 1, T => T.contains 232 || (cands T).any fun g => reach k (g :: T)

lemma reach_false : reach 3 [0, 255, 170, 204, 240] = false := by decide +kernel

lemma dec_inj (m : ℕ) (hm : m < 256) (h : dec m = dec 232) : m = 232 := by
  have key : ∀ m : ℕ, m < 256 →
      (∀ u v w : Bool, m.testBit (idx (u, v, w)) = (232).testBit (idx (u, v, w))) →
      m = 232 := by
    decide +kernel
  exact key m hm (fun u v w => congrFun h (u, v, w))

lemma h255 (p : Bool × Bool × Bool) : (255).testBit (idx p) = true := by
  obtain ⟨u, v, w⟩ := p
  cases u <;> cases v <;> cases w <;> decide

lemma reach_sound : ∀ (L : List (Bool × Bool × Bool → Bool))
    (S : Set (Bool × Bool × Bool → Bool)) (T : List ℕ) (k : ℕ), L.length ≤ k →
    (∀ h ∈ S, ∃ m ∈ T, m < 256 ∧ h = dec m) → Chain S L → (dec 232 ∈ S ∨ dec 232 ∈ L) →
    reach k T = true := by
  intro L
  induction L with
  | nil =>
    intro S T k _ hS _ hm
    have h232 : 232 ∈ T := by
      rcases hm with hm | hm
      · obtain ⟨m, hmT, hlt, he⟩ := hS _ hm
        have e := dec_inj m hlt he.symm
        rw [e] at hmT
        exact hmT
      · simp at hm
    cases k with
    | zero => simp [reach, h232]
    | succ k => simp [reach, h232]
  | cons g L ih =>
    intro S T k hk hS hc hm
    obtain ⟨hg, hL⟩ := (chain_cons _ _ _).1 hc
    cases k with
    | zero => simp at hk
    | succ k =>
      have key : ∃ mg ∈ cands T, mg < 256 ∧ g = dec mg := by
        obtain ⟨a, ha, b, hb, hf⟩ := hg
        obtain ⟨ma, hma, hla, rfl⟩ := hS a ha
        obtain ⟨mb, hmb, hlb, rfl⟩ := hS b hb
        have hla' : ma < 2 ^ 8 := by norm_num; exact hla
        have hlb' : mb < 2 ^ 8 := by norm_num; exact hlb
        rcases hf with rfl | rfl | rfl
        · refine ⟨ma &&& mb, ?_, lt_of_le_of_lt Nat.and_le_left hla, ?_⟩
          · exact List.mem_flatMap.2 ⟨ma, hma, List.mem_cons.2 (Or.inr
              (List.mem_flatMap.2 ⟨mb, hmb, List.mem_cons.2 (Or.inl rfl)⟩))⟩
          · funext p; simp [dec, Nat.testBit_land]
        · refine ⟨ma ||| mb, ?_, ?_, ?_⟩
          · exact List.mem_flatMap.2 ⟨ma, hma, List.mem_cons.2 (Or.inr
              (List.mem_flatMap.2 ⟨mb, hmb,
                List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))⟩))⟩
          · have h := Nat.or_lt_two_pow hla' hlb'
            norm_num at h
            exact h
          · funext p; simp [dec, Nat.testBit_lor]
        · refine ⟨255 ^^^ ma, ?_, ?_, ?_⟩
          · exact List.mem_flatMap.2 ⟨ma, hma, List.mem_cons.2 (Or.inl rfl)⟩
          · have h := Nat.xor_lt_two_pow (show 255 < 2 ^ 8 by norm_num) hla'
            norm_num at h
            exact h
          · funext p; simp [dec, Nat.testBit_xor, h255]
      obtain ⟨mg, hmg, hlg, rfl⟩ := key
      have hrec : reach k (mg :: T) = true := by
        refine ih (insert (dec mg) S) (mg :: T) k (by simpa using hk) ?_ hL ?_
        · intro h hh
          rcases Set.mem_insert_iff.1 hh with e | hh
          · exact ⟨mg, List.mem_cons.2 (Or.inl rfl), hlg, e⟩
          · obtain ⟨m, hm1, hm2, hm3⟩ := hS h hh
            exact ⟨m, List.mem_cons.2 (Or.inr hm1), hm2, hm3⟩
        · rcases hm with hm | hm
          · exact Or.inl (Set.mem_insert_of_mem _ hm)
          · rcases List.mem_cons.1 hm with e | hm
            · exact Or.inl (by rw [e]; exact Set.mem_insert _ _)
            · exact Or.inr hm
      simp only [reach, Bool.or_eq_true, List.any_eq_true]
      exact Or.inr ⟨mg, hmg, hrec⟩

lemma base3 : ∀ h ∈ ((fun b : (Fin 6 → Bool) → Bool => fun p => b (emb p)) '' B6),
    ∃ m ∈ [0, 255, 170, 204, 240], m < 256 ∧ h = dec m := by
  rintro h ⟨b, hb, rfl⟩
  rcases hb with rfl | rfl | ⟨j, rfl⟩
  · exact ⟨0, by simp, by norm_num,
      by funext ⟨u, v, w⟩; cases u <;> cases v <;> cases w <;> decide⟩
  · exact ⟨255, by simp, by norm_num,
      by funext ⟨u, v, w⟩; cases u <;> cases v <;> cases w <;> decide⟩
  · fin_cases j
    · exact ⟨170, by simp, by norm_num,
        by funext ⟨u, v, w⟩; cases u <;> cases v <;> cases w <;> decide⟩
    · exact ⟨204, by simp, by norm_num,
        by funext ⟨u, v, w⟩; cases u <;> cases v <;> cases w <;> decide⟩
    · exact ⟨0, by simp, by norm_num,
        by funext ⟨u, v, w⟩; cases u <;> cases v <;> cases w <;> decide⟩
    · exact ⟨240, by simp, by norm_num,
        by funext ⟨u, v, w⟩; cases u <;> cases v <;> cases w <;> decide⟩
    · exact ⟨0, by simp, by norm_num,
        by funext ⟨u, v, w⟩; cases u <;> cases v <;> cases w <;> decide⟩
    · exact ⟨0, by simp, by norm_num,
        by funext ⟨u, v, w⟩; cases u <;> cases v <;> cases w <;> decide⟩

lemma target3 : (fun p => fE (upd 5 (upd 4 (upd 2 (emb p))))) = dec 232 := by
  funext ⟨u, v, w⟩
  cases u <;> cases v <;> cases w <;> decide

lemma main (t : ℕ) (h : PEqualNP.MetaComplexity.HasCircuitSize 6 fE t) : 7 ≤ t := by
  obtain ⟨C, hFan, hsize, hev⟩ := h
  obtain ⟨L0, hl0, hc0, hm0⟩ := chain_of_gates C.gates B6 vars6 hFan f6 t6 (by
    intro h hh
    rw [vars6, List.mem_ofFn] at hh
    obtain ⟨i, rfl⟩ := hh
    exact v6 i)
  have e : fE = (C.gates.foldl (fun W g => W ++ [gfn W g]) vars6).getD C.output
      (fun _ => false) := by
    funext x
    have h2 : List.ofFn x = vars6.map (fun h => h x) := by
      simp [vars6, List.map_ofFn, Function.comp_def]
    rw [← hev x]
    show (C.gates.foldl _ (List.ofFn x)).getD C.output false = _
    rw [h2, wires_eq, getD_map_app]
  have hfE : fE ∈ B6 ∨ fE ∈ L0 := by
    by_cases ho : C.output < (C.gates.foldl (fun W g => W ++ [gfn W g]) vars6).length
    · rw [e, List.getD_eq_getElem _ _ ho]
      exact hm0 _ (List.getElem_mem ho)
    · rw [e, List.getD_eq_default _ _ (by omega)]
      exact Or.inl f6
  obtain ⟨L1, hl1, hc1, hm1⟩ := step6 5 L0 fE hc0 hfE ne1 nF1 nT1
  obtain ⟨L2, hl2, hc2, hm2⟩ := step6 4 L1 _ hc1 hm1 ne2 nF2 nT2
  obtain ⟨L3, hl3, hc3, hm3⟩ := step6 2 L2 _ hc2 hm2 ne3 nF3 nT3
  have hc3' := chain_comp emb L3 B6 hc3
  have hm3' : dec 232 ∈ ((fun b : (Fin 6 → Bool) → Bool => fun p => b (emb p)) '' B6) ∨
      dec 232 ∈ L3.map (fun b : (Fin 6 → Bool) → Bool => fun p => b (emb p)) := by
    rw [← target3]
    rcases hm3 with hm3 | hm3
    · exact Or.inl ⟨_, hm3, rfl⟩
    · exact Or.inr (List.mem_map.2 ⟨_, hm3, rfl⟩)
  by_contra hlt
  have hsz : C.size = C.gates.length := rfl
  have hk : (L3.map (fun b : (Fin 6 → Bool) → Bool => fun p => b (emb p))).length ≤ 3 := by
    rw [List.length_map]
    omega
  have hr := reach_sound _ _ [0, 255, 170, 204, 240] 3 hk base3 hc3' hm3'
  rw [reach_false] at hr
  exact Bool.false_ne_true hr

end PEqualNP.Outside.L_meta_5505

theorem PEqualNP.Outside.L_meta_5505 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 3) || (x 2 && x 4) || (x 2 && x 5)) t → 7 ≤ t := by
  intro t h
  exact PEqualNP.Outside.L_meta_5505.main t h
