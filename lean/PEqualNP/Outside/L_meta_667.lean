import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_667_aux

-- Circuit values on one or two selected points. The wire evaluation lemmas follow L_meta_616.
open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_step_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_append_left_lt (w t : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_self (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp

lemma getD_ge_len (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

lemma foldl_step_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (step w g).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (step w g) hlt]
    exact getD_append_left_lt w _ i hi

lemma foldl_step_getD_ge (gs : List Gate) (w : List Bool) (i : ℕ) (hi : w.length + gs.length ≤ i) :
    (gs.foldl step w).getD i false = false := by
  apply getD_ge_len
  rw [foldl_step_len]
  exact hi

lemma foldl_step_gate (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate) (hj : gs[j]? = some g) :
    (gs.foldl step w).getD (w.length + j) false =
      g.op.eval (g.inputs.map fun i => if i < w.length + j then (gs.foldl step w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g0 gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      rw [Nat.add_zero, List.foldl_cons]
      have hlt : w.length < (step w g0).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [foldl_step_getD_lt gs (step w g0) w.length hlt]
      have hself : (step w g0).getD w.length false = g0.op.eval (g0.inputs.map fun i => w.getD i false) :=
        getD_append_self w _
      rw [hself]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · have hilt : i < (step w g0).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]
          omega
        simp only [hi, ↓reduceIte, foldl_step_getD_lt gs (step w g0) i hilt]
        exact (getD_append_left_lt w _ i hi).symm
      · simp only [hi, ↓reduceIte]
        exact getD_ge_len w i (Nat.le_of_not_lt hi)
    | succ j' =>
      simp only [List.getElem?_cons_succ] at hj
      have hlen : (step w g0).length + j' = w.length + (j' + 1) := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [List.foldl_cons, ← hlen]
      exact ih (step w g0) j' hj

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl step x := rfl

lemma wires_gate_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hj : C.gates[j]? = some g) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      g.op.eval (g.inputs.map fun i => if i < n + j then (C.wires (List.ofFn x)).getD i false else false) := by
  have h := foldl_step_gate C.gates (List.ofFn x) j g hj
  simpa only [List.length_ofFn, ← wires_eq_foldl] using h

lemma ofFn_getD_lt {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (List.ofFn x).getD w false = x ⟨w, hw⟩ := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some]

lemma wires_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (C.wires (List.ofFn x)).getD w false = x ⟨w, hw⟩ := by
  rw [wires_eq_foldl, foldl_step_getD_lt C.gates (List.ofFn x) w (by simp [hw]), ofFn_getD_lt]

lemma wires_oob {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    (C.wires (List.ofFn x)).getD w false = false := by
  rw [wires_eq_foldl]
  exact foldl_step_getD_ge C.gates (List.ofFn x) w (by simp [hw])

lemma gateOp_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (f1 f2 : ℕ → Bool) (hle : ∀ i ∈ l, f1 i = true → f2 i = true) :
    op.eval (l.map f1) = true → op.eval (l.map f2) = true := by
  rcases hop with rfl | rfl
  · intro h
    change (l.map f1).all id = true at h
    change (l.map f2).all id = true
    rw [List.all_eq_true] at h ⊢
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact hle i hi (h _ (List.mem_map_of_mem hi))
  · intro h
    change (l.map f1).any id = true at h
    change (l.map f2).any id = true
    rw [List.any_eq_true] at h ⊢
    obtain ⟨b, hb, hbt⟩ := h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact ⟨f2 i, List.mem_map_of_mem hi, hle i hi hbt⟩

lemma wires_mono {n : ℕ} (C : Circuit) (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ u, x u = true → y u = true) :
    ∀ w : ℕ, (C.wires (List.ofFn x)).getD w false = true → (C.wires (List.ofFn y)).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw1 : w < n
    · rw [wires_input C x w hw1, wires_input C y w hw1]
      exact hxy ⟨w, hw1⟩
    · by_cases hw2 : n + C.gates.length ≤ w
      · rw [wires_oob C x w hw2]
        intro h; exact absurd h (by decide)
      · have hjlt : w - n < C.gates.length := by omega
        set j := w - n
        have hwj : w = n + j := by omega
        have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
        have hgop : (C.gates[j]'hjlt).op = GateOp.and ∨ (C.gates[j]'hjlt).op = GateOp.or := by
          simpa using (hmono _ (List.mem_of_getElem? hg)).1
        rw [hwj, wires_gate_ofFn C x j _ hg, wires_gate_ofFn C y j _ hg]
        apply gateOp_mono _ hgop
        intro i _ hi
        by_cases hilt : i < n + j
        · simp only [hilt, ↓reduceIte] at hi ⊢
          exact ih i (by omega) hi
        · simp only [hilt, ↓reduceIte] at hi
          exact absurd hi (by decide)

def wireV (gs : List Gate) (w : ℕ) (x : Fin 13 → Bool) :=
  ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD w false

def one (p i : Fin 13) : Bool := decide (i = p)

def two (p q i : Fin 13) : Bool := decide (i = p ∨ i = q)

def Sg (gs : List Gate) (w : ℕ) := Finset.univ.filter (fun p => wireV gs w (one p))

def Pg (gs : List Gate) (w : ℕ) (p q : Fin 13) := wireV gs w (two p q) = true

def semOk (gs : List Gate) := ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma semMono (gs : List Gate) (hg : semOk gs) (w : ℕ) (p q : Fin 13) :
    p ∈ Sg gs w ∨ q ∈ Sg gs w → Pg gs w p q := by
  have hm : PEqualNP.MetaComplexity.Monotone2 ⟨gs,0⟩ := by
    intro g h
    simpa using hg g h
  simp only [Sg, Finset.mem_filter, Finset.mem_univ, true_and]
  rintro (h | h)
  · apply wires_mono ⟨gs,0⟩ hm (one p) (two p q) _ w h
    intro i hi
    simpa [two] using Or.inl (b := i=q) (by simpa [one] using hi : i=p)
  · apply wires_mono ⟨gs,0⟩ hm (one q) (two p q) _ w h
    intro i hi
    simpa [two] using Or.inr (a := i=p) (by simpa [one] using hi : i=q)

lemma semInput (gs : List Gate) (w : ℕ) (h : 2 ≤ (Sg gs w).card) : 13 ≤ w := by
  by_contra! hw
  have eq : Sg gs w = {⟨w,hw⟩} := by
    ext p
    simp only [Sg,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
    change (((⟨gs,0⟩ : Circuit).wires (List.ofFn (one p))).getD w false = true) ↔ _
    rw [wires_input _ _ _ hw]
    simp only [one,decide_eq_true_eq]
    exact eq_comm
  simp [eq] at h

def Normal (gs : List Gate) (w : ℕ) :=
  (∃ c : Bool, ∀ x, wireV gs w x = c) ∨
    ∃ a b, a < w ∧ b < w ∧
      ((∀ x, wireV gs w x = (wireV gs a x || wireV gs b x)) ∨
       (∀ x, wireV gs w x = (wireV gs a x && wireV gs b x)))

lemma semNormal (gs : List Gate) (hok : semOk gs) (w : ℕ)
    (lo : 13 ≤ w) (hi : w < 13+gs.length) : Normal gs w := by
  let j := w - 13
  have hj : j < gs.length := by dsimp [j]; omega
  let g := gs[j]
  have hjg : gs[j]? = some g := List.getElem?_eq_getElem hj
  obtain ⟨hop,hsize⟩ := hok g (List.mem_of_getElem? hjg)
  have e : 13 + j = w := by dsimp [j]; omega
  have ev (x) : wireV gs w x = g.op.eval
      (g.inputs.map (fun i => if i < w then wireV gs i x else false)) := by
    have h := wires_gate_ofFn (n:=13) (⟨gs,0⟩ : Circuit) x j g hjg
    simpa only [wireV,e] using h
  have copy (a) (ha : a < w) (hv : ∀ x, wireV gs w x = wireV gs a x) : Normal gs w :=
    Or.inr ⟨a,a,ha,ha,Or.inl (fun x => by simp [hv x])⟩
  rcases h : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c,l⟩⟩⟩
  · rcases hop with h1 | h1
    · exact Or.inl ⟨true, fun x => by simpa [h,h1,GateOp.eval] using ev x⟩
    · exact Or.inl ⟨false, fun x => by simpa [h,h1,GateOp.eval] using ev x⟩
  · by_cases ha : a < w
    · apply copy a ha; intro x; rcases hop with h1 | h1 <;>
        simpa [h,h1,ha,GateOp.eval] using ev x
    · apply Or.inl; refine ⟨false, fun x => ?_⟩; rcases hop with h1 | h1 <;>
        simpa [h,h1,ha,GateOp.eval] using ev x
  · by_cases ha : a < w <;> by_cases hb : b < w
    · refine Or.inr ⟨a,b,ha,hb,?_⟩
      rcases hop with h1 | h1
      · exact Or.inr (fun x => by simpa [h,h1,ha,hb,GateOp.eval] using ev x)
      · exact Or.inl (fun x => by simpa [h,h1,ha,hb,GateOp.eval] using ev x)
    · rcases hop with h1 | h1
      · exact Or.inl ⟨false,fun x => by simpa [h,h1,ha,hb,GateOp.eval] using ev x⟩
      · exact copy a ha (fun x => by simpa [h,h1,ha,hb,GateOp.eval] using ev x)
    · rcases hop with h1 | h1
      · exact Or.inl ⟨false,fun x => by simpa [h,h1,ha,hb,GateOp.eval] using ev x⟩
      · exact copy b hb (fun x => by simpa [h,h1,ha,hb,GateOp.eval] using ev x)
    · apply Or.inl; refine ⟨false, fun x => ?_⟩; rcases hop with h1 | h1 <;>
        simpa [h,h1,ha,hb,GateOp.eval] using ev x
  · simp [h] at hsize

lemma semGate (gs : List Gate) (hg : semOk gs) (w : ℕ)
    (hlo : 2 ≤ (Sg gs w).card) (hut : (Sg gs w).card < 13) (hw : w < 13+gs.length) :
    13 ≤ w ∧ ∃ a b, a<w ∧ b<w ∧
      ((Sg gs w = Sg gs a ∪ Sg gs b ∧ ∀ p q, Pg gs w p q ↔ Pg gs a p q ∨ Pg gs b p q) ∨
       (Sg gs w = Sg gs a ∩ Sg gs b ∧ ∀ p q, Pg gs w p q ↔ Pg gs a p q ∧ Pg gs b p q)) := by
  have hi := semInput gs w hlo
  refine ⟨hi,?_⟩
  rcases semNormal gs hg w hi hw with ⟨c,h⟩ | ⟨a,b,ha,hb,h | h⟩
  · cases c
    · simp [Sg,h] at hlo
    · simp [Sg,h] at hut
  · refine ⟨a,b,ha,hb,Or.inl ⟨?_,?_⟩⟩
    · ext p; simp [Sg,h]
    · intro p q; simp [Pg,h]
  · refine ⟨a,b,ha,hb,Or.inr ⟨?_,?_⟩⟩
    · ext p; simp [Sg,h]
    · intro p q; simp [Pg,h]

def light (x : Fin 13 → Bool) :=
  ∀ i j k : Fin 13, x i=true → x j=true → x k=true → i=j ∨ j=k ∨ i=k

lemma oneLight (p : Fin 13) : light (one p) := by
  intro i j k hi hj hk
  simp only [one, decide_eq_true_eq] at hi hj hk
  exact Or.inl (hi.trans hj.symm)

lemma twoLight (p q : Fin 13) : light (two p q) := by
  intro i j k hi hj hk
  simp only [two, decide_eq_true_eq] at hi hj hk
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> rcases hk with rfl | rfl <;> simp

lemma semRoot (gs : List Gate) (w : ℕ) (L : Finset (Fin 13)) (hne : L.Nonempty)
    (ht : ∀ x : Fin 13 → Bool, light x →
      Circuit.eval ⟨gs,w⟩ (List.ofFn x) = decide (∃ v ∈ L, x v = true)) :
    w < 13 + gs.length ∧ Sg gs w = L ∧
      ∀ p q : Fin 13, p ∉ L → q ∉ L → ¬ Pg gs w p q := by
  have ho (p : Fin 13) : wireV gs w (one p) = decide (p ∈ L) := by
    have hh := ht (one p) (oneLight p)
    change wireV gs w (one p) = _ at hh
    simpa only [one,decide_eq_true_eq,exists_eq_right] using hh
  have hs : Sg gs w = L := by
    ext p
    simp [Sg,ho]
  refine ⟨?_,hs,?_⟩
  · by_contra! hn
    obtain ⟨p,hp⟩ := hne
    have hh := ho p
    change ((⟨gs,0⟩ : Circuit).wires (List.ofFn (one p))).getD w false = _ at hh
    rw [wires_oob _ _ _ hn] at hh
    simp [hp] at hh
  · intro p q hp hq h
    have hh := ht (two p q) (twoLight p q)
    change wireV gs w (two p q) = _ at hh
    change wireV gs w (two p q) = true at h
    rw [hh,decide_eq_true_eq] at h
    obtain ⟨v,hv,hb⟩ := h
    simp only [two,decide_eq_true_eq] at hb
    rcases hb with rfl | rfl
    · exact hp hv
    · exact hq hv

-- A line with only two private wires forces three larger supports with disjoint excess.
def privateWires (N : ℕ) (S : ℕ → Finset (Fin 13)) (L : Finset (Fin 13)) : Finset ℕ :=
  (Finset.range N).filter fun w => 2 ≤ (S w).card ∧ S w ⊆ L

def pairLow (P : ℕ → Fin 13 → Fin 13 → Prop) (L : Finset (Fin 13)) (w : ℕ) : Prop :=
  ∀ p q, p ∉ L → q ∉ L → ¬ P w p q

def WireSteps (N : ℕ) (S : ℕ → Finset (Fin 13)) (P : ℕ → Fin 13 → Fin 13 → Prop) : Prop :=
  ∀ w, 2 ≤ (S w).card → (S w).card < 13 → w < N → 13 ≤ w ∧
    ∃ a b : ℕ, a < w ∧ b < w ∧
      ((S w = S a ∪ S b ∧ ∀ p q, P w p q ↔ P a p q ∨ P b p q) ∨
       (S w = S a ∩ S b ∧ ∀ p q, P w p q ↔ P a p q ∧ P b p q))

lemma memPrivate {N w : ℕ} {S : ℕ → Finset (Fin 13)} {L : Finset (Fin 13)} :
    w ∈ privateWires N S L ↔ w < N ∧ 2 ≤ (S w).card ∧ S w ⊆ L := by
  simp [privateWires]

lemma lowAndOperand {S : ℕ → Finset (Fin 13)} {P : ℕ → Fin 13 → Fin 13 → Prop}
    {L : Finset (Fin 13)} {w a b : ℕ}
    (hm : ∀ v i j, i ∈ S v ∨ j ∈ S v → P v i j)
    (hand : ∀ p q, P w p q ↔ P a p q ∧ P b p q) (hlow : pairLow P L w) :
    S a ⊆ L ∨ S b ⊆ L := by
  by_contra! h
  obtain ⟨i, hia, hiL⟩ := Finset.not_subset.mp h.1
  obtain ⟨j, hjb, hjL⟩ := Finset.not_subset.mp h.2
  exact hlow i j hiL hjL ((hand i j).2 ⟨hm a i j (.inl hia), hm b i j (.inr hjb)⟩)

lemma privatePred {N : ℕ} {S : ℕ → Finset (Fin 13)} {P : ℕ → Fin 13 → Fin 13 → Prop}
    {L : Finset (Fin 13)} (hl : L.card = 4) (hs : WireSteps N S P)
    (hm : ∀ v i j, i ∈ S v ∨ j ∈ S v → P v i j) {w : ℕ} (hw : w < N)
    (hsize : 3 ≤ (S w).card) (hsub : S w ⊆ L) (hlow : pairLow P L w) :
    ∃ v < w, v ∈ privateWires N S L := by
  have hbound := Finset.card_le_card hsub
  obtain ⟨_,a,b,ha,hb,hcases⟩ := hs w (by omega) (by omega) hw
  rcases hcases with ⟨hu, _⟩ | ⟨hi, hp⟩
  · have hsum := Finset.card_union_le (S a) (S b)
    rw [← hu] at hsum
    rcases le_or_gt 2 (S a).card with h | h
    · exact ⟨a, ha, memPrivate.2 ⟨by omega, h, fun i hia => hsub (hu ▸ Finset.mem_union_left _ hia)⟩⟩
    · exact ⟨b, hb, memPrivate.2 ⟨by omega, by omega, fun i hib => hsub (hu ▸ Finset.mem_union_right _ hib)⟩⟩
  · rcases lowAndOperand hm hp hlow with h | h
    · have he : S w ⊆ S a := hi ▸ Finset.inter_subset_left
      have := Finset.card_le_card he
      exact ⟨a, ha, memPrivate.2 ⟨by omega, by omega, h⟩⟩
    · have he : S w ⊆ S b := hi ▸ Finset.inter_subset_right
      have := Finset.card_le_card he
      exact ⟨b, hb, memPrivate.2 ⟨by omega, by omega, h⟩⟩

lemma threePrivate {s : Finset ℕ} {x y z : ℕ} (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ s)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : 3 ≤ s.card := by
  have h : ({x,y,z} : Finset ℕ) ⊆ s := by
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl <;> assumption
  simpa [hxy,hxz,hyz] using Finset.card_le_card h

lemma classifyLine {N : ℕ} (S : ℕ → Finset (Fin 13)) (P : ℕ → Fin 13 → Fin 13 → Prop)
    (L : Finset (Fin 13)) (hl : L.card = 4) (hs : WireSteps N S P)
    (hm : ∀ v i j, i ∈ S v ∨ j ∈ S v → P v i j)
    (hg : ∀ v, 2 ≤ (S v).card → v < N → 13 ≤ v)
    (o : ℕ) (hon : o < N) (ho : S o = L) (hlow : pairLow P L o) :
    2 ≤ (privateWires N S L).card ∧ ((privateWires N S L).card ≤ 2 →
      ∃ a b c : ℕ, 13 ≤ a ∧ a < N ∧ 13 ≤ b ∧ b < N ∧ 13 ≤ c ∧ c < N ∧
        L ⊂ S a ∧ L ⊂ S b ∧ L ⊂ S c ∧ Disjoint (S a \ L) (S b \ L) ∧
        Disjoint (S a \ L) (S c \ L) ∧ Disjoint (S b \ L) (S c \ L)) := by
  classical
  have h4 : (S o).card = 4 := ho ▸ hl
  have hop : o ∈ privateWires N S L := memPrivate.2 ⟨hon, by omega, ho.le⟩
  obtain ⟨e,heo,hep⟩ := privatePred hl hs hm hon (by omega) ho.le hlow
  constructor
  · have h : ({e,o} : Finset ℕ) ⊆ privateWires N S L := by
      intro i hi
      simp only [Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with rfl | rfl <;> assumption
    simpa [ne_of_lt heo] using Finset.card_le_card h
  intro hweak
  have unique : ∀ v < o, v ∈ privateWires N S L → v = e := by
    intro v hvo hv
    by_contra hne
    have := threePrivate hv hep hop hne (ne_of_lt hvo) (ne_of_lt heo)
    omega
  have noneBefore : ∀ v < e, v ∉ privateWires N S L := by
    intro v hve hv
    have := unique v (lt_trans hve heo) hv
    omega
  obtain ⟨_,r,t,hr,ht,hrule⟩ := hs o (by omega) (by omega) hon
  rcases hrule with ⟨hu,hpair⟩ | ⟨hi,hpair⟩
  · have hsr : S r ⊆ L := fun i h => ho ▸ hu ▸ Finset.mem_union_left _ h
    have hst : S t ⊆ L := fun i h => ho ▸ hu ▸ Finset.mem_union_right _ h
    have hsmall (z : ℕ) (hz : z < o) (hsub : S z ⊆ L) (hzlow : pairLow P L z) : (S z).card ≤ 2 := by
      by_contra! h
      have hze := unique z hz (memPrivate.2 ⟨by omega,by omega,hsub⟩)
      obtain ⟨v,hvz,hv⟩ := privatePred hl hs hm (lt_trans hz hon) (by omega) hsub hzlow
      exact noneBefore v (by omega) hv
    have h1 := hsmall r hr hsr (fun i j hiL hjL h => hlow i j hiL hjL ((hpair i j).2 (.inl h)))
    have h2 := hsmall t ht hst (fun i j hiL hjL h => hlow i j hiL hjL ((hpair i j).2 (.inr h)))
    have hsum := Finset.card_union_le (S r) (S t)
    rw [← hu] at hsum
    have hre := unique r hr (memPrivate.2 ⟨by omega,by omega,hsr⟩)
    have hte := unique t ht (memPrivate.2 ⟨by omega,by omega,hst⟩)
    rw [show t = r by omega, Finset.union_self] at hu
    rw [hu] at h4
    omega
  · have rh : L ⊆ S r := ho ▸ hi ▸ Finset.inter_subset_left
    have th : L ⊆ S t := ho ▸ hi ▸ Finset.inter_subset_right
    have doAnd (c : ℕ) (hc : c < o) (ec : S e = L) (lc : L ⊆ S c)
        (ev : ∀ p q, P o p q ↔ P e p q ∧ P c p q) :
        ∃ a b d : ℕ, 13 ≤ a ∧ a < N ∧ 13 ≤ b ∧ b < N ∧ 13 ≤ d ∧ d < N ∧
          L ⊂ S a ∧ L ⊂ S b ∧ L ⊂ S d ∧ Disjoint (S a \ L) (S b \ L) ∧
          Disjoint (S a \ L) (S d \ L) ∧ Disjoint (S b \ L) (S d \ L) := by
      have he4 : (S e).card = 4 := ec ▸ hl
      obtain ⟨_,a,b,ha,hb,hrules⟩ := hs e (by omega) (by omega) (by omega)
      rcases hrules with ⟨hu,_⟩ | ⟨hu,hab⟩
      · have hsum := Finset.card_union_le (S a) (S b)
        rw [← hu] at hsum
        have limited (v : ℕ) (hv : v < e) (hh : S v ⊆ L) : (S v).card < 2 := by
          by_contra! h
          exact noneBefore v hv (memPrivate.2 ⟨by omega,h,hh⟩)
        have h1 := limited a ha (fun i h => ec ▸ hu ▸ Finset.mem_union_left _ h)
        have h2 := limited b hb (fun i h => ec ▸ hu ▸ Finset.mem_union_right _ h)
        omega
      · have la : L ⊆ S a := ec ▸ hu ▸ Finset.inter_subset_left
        have lb : L ⊆ S b := ec ▸ hu ▸ Finset.inter_subset_right
        have size (v : ℕ) (h : L ⊆ S v) : 2 ≤ (S v).card := by have := Finset.card_le_card h; omega
        have nsa : ¬S a ⊆ L := fun h => noneBefore a ha (memPrivate.2 ⟨by omega,size a la,h⟩)
        have nsb : ¬S b ⊆ L := fun h => noneBefore b hb (memPrivate.2 ⟨by omega,size b lb,h⟩)
        obtain ⟨i,hia,hiL⟩ := Finset.not_subset.mp nsa
        obtain ⟨j,hjb,hjL⟩ := Finset.not_subset.mp nsb
        have falsePair (p q : Fin 13) (h1 : p ∈ S a) (h2 : q ∈ S b) (h3 : p ∉ L) (h4' : q ∉ L) : ¬ P c p q := by
          intro hh
          exact hlow p q h3 h4' ((ev p q).2 ⟨(hab p q).2 ⟨hm a p q (.inl h1),hm b p q (.inr h2)⟩,hh⟩)
        have nsc : ¬S c ⊆ L := by
          intro h
          have ce := unique c hc (memPrivate.2 ⟨by omega,size c lc,h⟩)
          subst c
          exact falsePair i j hia hjb hiL hjL ((hab i j).2 ⟨hm a i j (.inl hia),hm b i j (.inr hjb)⟩)
        refine ⟨a,b,c,hg a (size a la) (by omega),by omega,hg b (size b lb) (by omega),by omega,
          hg c (size c lc) (by omega),by omega,lt_of_le_not_ge la nsa,lt_of_le_not_ge lb nsb,
          lt_of_le_not_ge lc nsc,Finset.disjoint_left.mpr ?_,Finset.disjoint_left.mpr ?_,Finset.disjoint_left.mpr ?_⟩
        · intro p h1 h2
          exact (Finset.mem_sdiff.mp h1).2 (ec ▸ hu ▸ Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp h1).1,(Finset.mem_sdiff.mp h2).1⟩)
        · intro p h1 h2
          exact falsePair p j (Finset.mem_sdiff.mp h1).1 hjb (Finset.mem_sdiff.mp h1).2 hjL (hm c p j (.inl (Finset.mem_sdiff.mp h2).1))
        · intro p h1 h2
          exact falsePair i p hia (Finset.mem_sdiff.mp h1).1 hiL (Finset.mem_sdiff.mp h1).2 (hm c i p (.inr (Finset.mem_sdiff.mp h2).1))
    rcases lowAndOperand hm hpair hlow with h | h
    · have rr : S r = L := Finset.Subset.antisymm h rh
      have re := unique r hr (memPrivate.2 ⟨by omega, by rw [rr,hl]; decide,h⟩)
      subst r
      exact doAnd t ht rr th hpair
    · have tt : S t = L := Finset.Subset.antisymm h th
      have te := unique t ht (memPrivate.2 ⟨by omega, by rw [tt,hl]; decide,h⟩)
      subst t
      exact doAnd r hr tt rh (fun i j => (hpair i j).trans and_comm)

-- The thirteen lines each have four points and distinct lines meet at one point.
def planeLine (w : Fin 13) : Finset (Fin 13) :=
  ({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + w)

lemma line_card : ∀ w, (planeLine w).card = 4 := by decide

set_option maxHeartbeats 2000000 in
lemma intersection_card : ∀ w u, w ≠ u → (planeLine w ∩ planeLine u).card = 1 := by
  decide

lemma extras_three {w u : Fin 13} {Z : Finset (Fin 13)} (hwu : w ≠ u)
    (hu : planeLine u ⊆ Z) : 3 ≤ (Z \ planeLine w).card := by
  have h := Finset.card_sdiff_add_card_inter (planeLine u) (planeLine w)
  rw [intersection_card u w hwu.symm, line_card] at h
  have hs : planeLine u \ planeLine w ⊆ Z \ planeLine w := by
    intro p hp
    exact Finset.mem_sdiff.mpr ⟨hu (Finset.mem_sdiff.mp hp).1, (Finset.mem_sdiff.mp hp).2⟩
  have := Finset.card_le_card hs
  omega

lemma triple_large {w u v : Fin 13} (hwu : w ≠ u) (hwv : w ≠ v) (huv : u ≠ v) :
    9 ≤ ((planeLine w ∪ planeLine u) ∪ planeLine v).card := by
  have h₁ := Finset.card_union_add_card_inter (planeLine w) (planeLine u)
  rw [intersection_card w u hwu, line_card, line_card] at h₁
  have h₂ := Finset.card_union_add_card_inter (planeLine w ∪ planeLine u) (planeLine v)
  have h₃ : ((planeLine w ∪ planeLine u) ∩ planeLine v).card ≤ 2 := by
    rw [Finset.union_inter_distrib_right]
    calc
      _ ≤ _ := Finset.card_union_le _ _
      _ = 2 := by rw [intersection_card w v hwv, intersection_card u v huv]
  rw [line_card] at h₂
  omega

lemma small_support_few_lines (Z : Finset (Fin 13)) (hZ : Z.card ≤ 7)
    (T : Finset (Fin 13)) (ht : ∀ w ∈ T, planeLine w ⊆ Z) : T.card ≤ 2 := by
  by_contra! h
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
  have herase := Finset.card_erase_of_mem hw
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (by omega : 1 < (T.erase w).card)
  obtain ⟨huw, hut⟩ := Finset.mem_erase.mp hu
  obtain ⟨hvw, hvt⟩ := Finset.mem_erase.mp hv
  have hsub := Finset.union_subset (Finset.union_subset (ht w hw) (ht u hut)) (ht v hvt)
  have := Finset.card_le_card hsub
  have := triple_large huw.symm hvw.symm huv
  omega

def supply (L : Finset (Fin 13)) (S : ℕ → Finset (Fin 13)) (U T : Finset ℕ) : Prop :=
  T ⊆ U ∧ (∀ g ∈ T, L ⊂ S g) ∧
    ∀ g ∈ T, ∀ h ∈ T, g ≠ h → Disjoint (S g \ L) (S h \ L)

lemma three_supply {L : Finset (Fin 13)} {S : ℕ → Finset (Fin 13)} {U : Finset ℕ}
    {a b c : ℕ} (au : a ∈ U) (bu : b ∈ U) (cu : c ∈ U)
    (ha : L ⊂ S a) (hb : L ⊂ S b) (hc : L ⊂ S c)
    (ab : Disjoint (S a \ L) (S b \ L)) (ac : Disjoint (S a \ L) (S c \ L))
    (bc : Disjoint (S b \ L) (S c \ L)) :
    ∃ T : Finset ℕ, T.card = 3 ∧ supply L S U T := by
  have different {i j : ℕ} (hi : L ⊂ S i) (hd : Disjoint (S i \ L) (S j \ L)) : i ≠ j := by
    rintro rfl
    have he := Finset.sdiff_nonempty_of_card_lt_card (Finset.card_lt_card hi)
    obtain ⟨p,hp⟩ := he
    exact Finset.disjoint_left.mp hd hp hp
  have ab' := different ha ab
  have ac' := different ha ac
  have bc' := different hb bc
  refine ⟨{a,b,c}, by simp [ab', ac', bc'], ?_, ?_, ?_⟩
  · intro g hg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl | rfl <;> assumption
  · intro g hg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl | rfl <;> assumption
  · intro g hg h hh hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg hh
    rcases hg with rfl | rfl | rfl <;> rcases hh with rfl | rfl | rfl <;>
      first | exact (hn rfl).elim | assumption | apply Disjoint.symm; assumption

lemma supply_capacity (S : ℕ → Finset (Fin 13)) (U : Finset ℕ) (B : Fin 13 → Finset ℕ)
    (good : ∀ w, supply (planeLine w) S U (B w)) (w : Fin 13) (sz : (B w).card = 3)
    (shared : ∀ g ∈ B w, ∃ v : Fin 13, v ≠ w ∧ g ∈ B v) (g : ℕ) (hg : g ∈ B w) :
    ((Finset.univ : Finset (Fin 13)).filter (fun v => g ∈ B v)).card ≤ 2 := by
  have large (i : ℕ) (hi : i ∈ B w) : 3 ≤ (S i \ planeLine w).card := by
    obtain ⟨v, hv, hiv⟩ := shared i hi
    exact extras_three hv.symm ((good v).2.1 i hiv).le
  have he := Finset.card_erase_of_mem hg
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < ((B w).erase g).card)
  obtain ⟨hag, haw⟩ := Finset.mem_erase.mp ha
  obtain ⟨hbg, hbw⟩ := Finset.mem_erase.mp hb
  let ex := fun i => S i \ planeLine w
  have hd := (good w).2.2
  have hj : Disjoint (ex g ∪ ex a) (ex b) := Finset.disjoint_union_left.mpr
    ⟨hd g hg b hbw hbg.symm, hd a haw b hbw hab⟩
  have hbound : ((ex g ∪ ex a) ∪ ex b).card ≤ (Finset.univ \ planeLine w).card := by
    apply Finset.card_le_card
    have sub (i : ℕ) : ex i ⊆ Finset.univ \ planeLine w := by
      intro p hp
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hp).2⟩
    exact Finset.union_subset (Finset.union_subset (sub g) (sub a)) (sub b)
  rw [Finset.card_union_of_disjoint hj,
      Finset.card_union_of_disjoint (hd g hg a haw hag.symm)] at hbound
  have hu := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (planeLine w))
  have hgsize := Finset.card_sdiff_add_card_eq_card ((good w).2.1 g hg).le
  rw [line_card] at hu hgsize
  simp only [Finset.card_univ, Fintype.card_fin] at hu
  have hla := large a haw
  have hlb := large b hbw
  dsimp [ex] at hbound
  apply small_support_few_lines (S g) (by omega)
  intro v hv
  exact ((good v).2.1 g (Finset.mem_filter.mp hv).2).le

-- Each line receives six credits and a gate supplies at most two.
lemma count_gates (U : Finset ℕ) (P B : Fin 13 → Finset ℕ)
    (pU : ∀ w, P w ⊆ U) (bU : ∀ w, B w ⊆ U)
    (pp : ∀ w v, w ≠ v → Disjoint (P w) (P v))
    (pb : ∀ w v, Disjoint (P w) (B v))
    (pmin : ∀ w, 2 ≤ (P w).card)
    (bthree : ∀ w, (P w).card = 2 → (B w).card = 3)
    (cap : ∀ w, (P w).card = 2 →
      (∀ g ∈ B w, ∃ v : Fin 13, v ≠ w ∧ g ∈ B v) →
      ∀ g ∈ B w, ((Finset.univ : Finset (Fin 13)).filter (fun v => g ∈ B v)).card ≤ 2) :
    39 ≤ U.card := by
  classical
  let owners (g : ℕ) := (Finset.univ : Finset (Fin 13)).filter (fun v => g ∈ B v)
  let rate (g : ℕ) : ℕ := if (owners g).card = 1 then 2 else if (owners g).card = 2 then 1 else 0
  let credit (w : Fin 13) (g : ℕ) : ℕ :=
    (if g ∈ P w then 2 else 0) + (if g ∈ B w then rate g else 0)
  have row (w : Fin 13) : 6 ≤ ∑ g ∈ U, credit w g := by
    have hp : U.filter (fun g => g ∈ P w) = P w := by
      ext g
      simp only [Finset.mem_filter]
      exact ⟨And.right, fun h => ⟨pU w h, h⟩⟩
    have hb : U.filter (fun g => g ∈ B w) = B w := by
      ext g
      simp only [Finset.mem_filter]
      exact ⟨And.right, fun h => ⟨bU w h, h⟩⟩
    simp only [credit, Finset.sum_add_distrib, ← Finset.sum_filter, hp, hb,
      Finset.sum_const, smul_eq_mul]
    by_cases weak : (P w).card = 2
    · suffices h : 2 ≤ ∑ g ∈ B w, rate g by omega
      by_cases shared : ∀ g ∈ B w, ∃ v : Fin 13, v ≠ w ∧ g ∈ B v
      · have each (g) (hg : g ∈ B w) : 1 ≤ rate g := by
          have pos : 0 < (owners g).card :=
            Finset.card_pos.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩⟩
          have lim : (owners g).card ≤ 2 := cap w weak shared g hg
          dsimp only [rate]
          split_ifs <;> omega
        have h := Finset.sum_le_sum each
        simp only [Finset.sum_const, smul_eq_mul, mul_one, bthree w weak] at h
        omega
      · push Not at shared
        obtain ⟨g, hg, onlyw⟩ := shared
        have ho : owners g = {w} := by
          ext v
          simpa [owners] using (show g ∈ B v ↔ v = w from
            ⟨fun hv => by by_contra h; exact onlyw v h hv, fun h => h ▸ hg⟩)
        have hrate : rate g = 2 := by simp [rate, ho]
        have h := Finset.single_le_sum (f := rate) (fun _ _ => Nat.zero_le _) hg
        omega
    · have := pmin w
      omega
  have column (g : ℕ) : (∑ w : Fin 13, credit w g) ≤ 2 := by
    simp only [credit, Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const,
      smul_eq_mul]
    by_cases privateGate : ∃ w, g ∈ P w
    · obtain ⟨w, hw⟩ := privateGate
      have hp : (Finset.univ : Finset (Fin 13)).filter (fun v => g ∈ P v) = {w} := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨fun hv => by
          by_contra h
          exact Finset.disjoint_left.mp (pp v w h) hv hw, fun h => h ▸ hw⟩
      have hb : owners g = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro v hv
        exact Finset.disjoint_left.mp (pb w v) hw (Finset.mem_filter.mp hv).2
      change _ + (owners g).card * rate g ≤ _
      simp [hp, hb]
    · have hp : (Finset.univ : Finset (Fin 13)).filter (fun v => g ∈ P v) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        exact fun v hv => privateGate ⟨v, (Finset.mem_filter.mp hv).2⟩
      change _ + (owners g).card * rate g ≤ _
      simp only [hp, Finset.card_empty, Nat.zero_mul, Nat.zero_add, rate]
      split_ifs <;> simp_all
  have rows := Finset.sum_le_sum (s := Finset.univ) (fun w _ => row w)
  have cols := Finset.sum_le_sum (s := U) (fun g _ => column g)
  rw [Finset.sum_comm] at rows
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at rows cols
  omega

-- Count private wires and the shared suppliers for the lines with only two private wires.
lemma abstract_plane_bound {N : ℕ} (S : ℕ → Finset (Fin 13))
    (F : ℕ → Fin 13 → Fin 13 → Prop) (out : Fin 13 → ℕ)
    (hs : WireSteps N S F)
    (hm : ∀ g p q, p ∈ S g ∨ q ∈ S g → F g p q)
    (hg : ∀ g, 2 ≤ (S g).card → g < N → 13 ≤ g)
    (hN : ∀ w, out w < N)
    (hline : ∀ w, S (out w) = planeLine w)
    (hlow : ∀ w, pairLow F (planeLine w) (out w)) : 39 ≤ N - 13 := by
  classical
  let U := Finset.Ico 13 N
  let P (w : Fin 13) := privateWires N S (planeLine w)
  have localBound (w : Fin 13) := classifyLine S F (planeLine w) (line_card w)
    hs hm hg (out w) (hN w) (hline w) (hlow w)
  have family (w : Fin 13) : ∃ T : Finset ℕ, supply (planeLine w) S U T ∧
      ((P w).card = 2 → T.card = 3) := by
    by_cases small : (P w).card = 2
    · obtain ⟨a,b,c,ha,ha',hb,hb',hc,hc',hra,hrb,hrc,hab,hac,hbc⟩ :=
        (localBound w).2 small.le
      obtain ⟨T, ht, hsup⟩ := three_supply (U := U) (S := S)
        (Finset.mem_Ico.mpr ⟨ha, ha'⟩) (Finset.mem_Ico.mpr ⟨hb, hb'⟩)
        (Finset.mem_Ico.mpr ⟨hc, hc'⟩) hra hrb hrc hab hac hbc
      exact ⟨T, hsup, fun _ => ht⟩
    · exact ⟨∅, by simp [supply], fun h => (small h).elim⟩
  choose B good bthree using family
  have counted := count_gates U P B (by
      intro w g h
      obtain ⟨hN', hsize, _⟩ := memPrivate.mp h
      exact Finset.mem_Ico.mpr ⟨hg g hsize hN',hN'⟩)
    (fun w => (good w).1) (by
      intro w v hwv
      apply Finset.disjoint_left.mpr
      intro g hw hv
      obtain ⟨_,hsz,hsw⟩ := memPrivate.mp hw
      obtain ⟨_,_,hsv⟩ := memPrivate.mp hv
      have sub : S g ⊆ planeLine w ∩ planeLine v := fun p hp =>
        Finset.mem_inter.mpr ⟨hsw hp, hsv hp⟩
      have lim := Finset.card_le_card sub
      rw [intersection_card w v hwv] at lim
      omega) (by
      intro w v
      apply Finset.disjoint_left.mpr
      intro g hw hv
      obtain ⟨_,_,hsw⟩ := memPrivate.mp hw
      have h₁ := Finset.card_le_card hsw
      have h₂ := Finset.card_lt_card ((good v).2.1 g hv)
      rw [line_card] at h₁ h₂
      omega)
    (fun w => (localBound w).1) bthree
    (fun w h => supply_capacity S U B good w (bthree w h))
  simpa [U, Nat.card_Ico] using counted

end PEqualNP.Outside.L_meta_667_aux

open PEqualNP.Outside.L_meta_667_aux

theorem PEqualNP.Outside.L_meta_667 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin 13 → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin 13) (x : Fin 13 → Bool), (∀ i j k : Fin 13, x i = true → x j = true → x k = true → i = j ∨ j = k ∨ i = k) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ (({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + w)), x v = true)) → 39 ≤ gates.length := by
  intro gates out hg ht
  have root (w : Fin 13) := semRoot gates (out w) (planeLine w)
    (Finset.card_pos.mp (by rw [line_card]; decide)) (ht w)
  have bound := abstract_plane_bound (N := 13 + gates.length) (Sg gates) (Pg gates) out
    (semGate gates hg) (semMono gates hg) (fun g h _ => semInput gates g h)
    (fun w => (root w).1) (fun w => (root w).2.1) (fun w => (root w).2.2)
  omega
