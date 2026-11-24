import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3592

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run {α : Type} (d : α) (F : GateOp → List α → α) (gs : List Gate) (init : List α) : List α :=
  gs.foldl (fun w g => w ++ [F g.op (g.inputs.map fun i => w.getD i d)]) init

lemma run_cons {α : Type} (d : α) (F : GateOp → List α → α) (g : Gate) (gs : List Gate)
    (init : List α) :
    run d F (g :: gs) init = run d F gs (init ++ [F g.op (g.inputs.map fun i => init.getD i d)]) :=
  rfl

lemma run_append {α : Type} (d : α) (F : GateOp → List α → α) (gs hs : List Gate)
    (init : List α) : run d F (gs ++ hs) init = run d F hs (run d F gs init) := by
  simp [run, List.foldl_append]

lemma run_snoc {α : Type} (d : α) (F : GateOp → List α → α) (gs : List Gate) (g : Gate)
    (init : List α) :
    run d F (gs ++ [g]) init = run d F gs init ++
      [F g.op (g.inputs.map fun i => (run d F gs init).getD i d)] := by
  rw [run_append]; rfl

lemma run_length {α : Type} (d : α) (F : GateOp → List α → α) (gs : List Gate) :
    ∀ init : List α, (run d F gs init).length = init.length + gs.length := by
  induction gs with
  | nil => intro init; rfl
  | cons g gs ih => intro init; rw [run_cons, ih]; simp; omega

lemma getD_ge' {α : Type} (d : α) (l : List α) (u : ℕ) (h : l.length ≤ u) : l.getD u d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

lemma getD_snoc' {α : Type} (d : α) (l : List α) (a : α) (u : ℕ) :
    (l ++ [a]).getD u d =
      if u < l.length then l.getD u d else if u = l.length then a else d := by
  by_cases h1 : u < l.length
  · rw [List.getD_append _ _ _ _ h1]; simp [h1]
  · by_cases h2 : u = l.length
    · subst h2; simp
    · have h3 : l.length ≤ u := by omega
      rw [List.getD_append_right _ _ _ _ h3]
      have h4 : ([a] : List α).length ≤ u - l.length := by simp; omega
      rw [getD_ge' _ _ _ h4]
      simp [h1, h2]

lemma wires_run (C : Circuit) (x : List Bool) :
    C.wires x = run false GateOp.eval C.gates x := rfl

abbrev Ent := Bool ⊕ ℕ

def val (wD : List Bool) : Ent → Bool
  | Sum.inl b => b
  | Sum.inr u => wD.getD u false

def andE (n : ℕ) (s : List Gate × List Ent) : Ent → Ent → List Gate × List Ent
  | Sum.inl false, _ => (s.1, s.2 ++ [Sum.inl false])
  | _, Sum.inl false => (s.1, s.2 ++ [Sum.inl false])
  | Sum.inl true, e => (s.1, s.2 ++ [e])
  | e, Sum.inl true => (s.1, s.2 ++ [e])
  | Sum.inr u, Sum.inr v =>
      if u = v then (s.1, s.2 ++ [Sum.inr u])
      else (s.1 ++ [({ op := GateOp.and, inputs := [u, v] } : Gate)],
        s.2 ++ [Sum.inr (n + s.1.length)])

def orE (n : ℕ) (s : List Gate × List Ent) : Ent → Ent → List Gate × List Ent
  | Sum.inl true, _ => (s.1, s.2 ++ [Sum.inl true])
  | _, Sum.inl true => (s.1, s.2 ++ [Sum.inl true])
  | Sum.inl false, e => (s.1, s.2 ++ [e])
  | e, Sum.inl false => (s.1, s.2 ++ [e])
  | Sum.inr u, Sum.inr v =>
      if u = v then (s.1, s.2 ++ [Sum.inr u])
      else (s.1 ++ [({ op := GateOp.or, inputs := [u, v] } : Gate)],
        s.2 ++ [Sum.inr (n + s.1.length)])

def stepE (n : ℕ) (s : List Gate × List Ent) (op : GateOp) (es : List Ent) :
    List Gate × List Ent :=
  match op, es with
  | GateOp.and, [] => (s.1, s.2 ++ [Sum.inl true])
  | GateOp.and, [e] => (s.1, s.2 ++ [e])
  | GateOp.and, [e1, e2] => andE n s e1 e2
  | GateOp.or, [] => (s.1, s.2 ++ [Sum.inl false])
  | GateOp.or, [e] => (s.1, s.2 ++ [e])
  | GateOp.or, [e1, e2] => orE n s e1 e2
  | GateOp.not, [] => (s.1, s.2 ++ [Sum.inl true])
  | GateOp.not, Sum.inl b :: _ => (s.1, s.2 ++ [Sum.inl (!b)])
  | GateOp.not, Sum.inr u :: _ =>
      (s.1 ++ [({ op := GateOp.not, inputs := [u] } : Gate)], s.2 ++ [Sum.inr (n + s.1.length)])
  | _, _ => (s.1, s.2 ++ [Sum.inl false])

def stepS (n : ℕ) (s : List Gate × List Ent) (g : Gate) : List Gate × List Ent :=
  stepE n s g.op (g.inputs.map fun i => s.2.getD i (Sum.inl false))

lemma stepE_spec (n : ℕ) (s : List Gate × List Ent) (op : GateOp) (es : List Ent)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : es.length ≤ 2) :
    (∃ e, stepE n s op es = (s.1, s.2 ++ [e]) ∧ (e = Sum.inl true ∨ e = Sum.inl false ∨ e ∈ es) ∧
      ∀ wD : List Bool, val wD e = op.eval (es.map (val wD))) ∨
    (∃ g : Gate, stepE n s op es = (s.1 ++ [g], s.2 ++ [Sum.inr (n + s.1.length)]) ∧
      g.op = op ∧ g.inputs.length ≤ 2 ∧ (∀ i ∈ g.inputs, Sum.inr i ∈ es) ∧
      ∀ wD : List Bool, op.eval (g.inputs.map fun i => wD.getD i false) =
        op.eval (es.map (val wD))) := by
  rcases es with _ | ⟨e1, _ | ⟨e2, _ | ⟨e3, t⟩⟩⟩
  · rcases hop with rfl | rfl | rfl
    · left; exact ⟨Sum.inl true, by simp [stepE], by simp, by intro wD; simp [val, GateOp.eval]⟩
    · left; exact ⟨Sum.inl false, by simp [stepE], by simp, by intro wD; simp [val, GateOp.eval]⟩
    · left; exact ⟨Sum.inl true, by simp [stepE], by simp, by intro wD; simp [val, GateOp.eval]⟩
  · rcases hop with rfl | rfl | rfl
    · left; exact ⟨e1, by simp [stepE], by simp, by intro wD; simp [val, GateOp.eval]⟩
    · left; exact ⟨e1, by simp [stepE], by simp, by intro wD; simp [val, GateOp.eval]⟩
    · rcases e1 with b | u
      · left; exact ⟨Sum.inl (!b), by simp [stepE], by cases b <;> simp,
          by intro wD; simp [val, GateOp.eval]⟩
      · right
        exact ⟨{ op := GateOp.not, inputs := [u] }, by simp [stepE], rfl, by simp, by simp,
          by intro wD; simp [val, GateOp.eval]⟩
  · rcases hop with rfl | rfl | rfl
    · rcases e1 with b | u <;> rcases e2 with c | v
      · cases b <;> cases c <;> left
        · exact ⟨Sum.inl false, by simp [stepE, andE], by simp, by intro wD; simp [val, GateOp.eval]⟩
        · exact ⟨Sum.inl false, by simp [stepE, andE], by simp, by intro wD; simp [val, GateOp.eval]⟩
        · exact ⟨Sum.inl false, by simp [stepE, andE], by simp, by intro wD; simp [val, GateOp.eval]⟩
        · exact ⟨Sum.inl true, by simp [stepE, andE], by simp, by intro wD; simp [val, GateOp.eval]⟩
      · cases b <;> left
        · exact ⟨Sum.inl false, by simp [stepE, andE], by simp, by intro wD; simp [val, GateOp.eval]⟩
        · exact ⟨Sum.inr v, by simp [stepE, andE], by simp, by intro wD; simp [val, GateOp.eval]⟩
      · cases c <;> left
        · exact ⟨Sum.inl false, by simp [stepE, andE], by simp, by intro wD; simp [val, GateOp.eval]⟩
        · exact ⟨Sum.inr u, by simp [stepE, andE], by simp, by intro wD; simp [val, GateOp.eval]⟩
      · by_cases huv : u = v
        · subst huv
          left
          exact ⟨Sum.inr u, by simp [stepE, andE], by simp, by intro wD; simp [val, GateOp.eval]⟩
        · right
          exact ⟨{ op := GateOp.and, inputs := [u, v] }, by simp [stepE, andE, huv], rfl, by simp,
            by simp, by intro wD; simp [val]⟩
    · rcases e1 with b | u <;> rcases e2 with c | v
      · cases b <;> cases c <;> left
        · exact ⟨Sum.inl false, by simp [stepE, orE], by simp, by intro wD; simp [val, GateOp.eval]⟩
        · exact ⟨Sum.inl true, by simp [stepE, orE], by simp, by intro wD; simp [val, GateOp.eval]⟩
        · exact ⟨Sum.inl true, by simp [stepE, orE], by simp, by intro wD; simp [val, GateOp.eval]⟩
        · exact ⟨Sum.inl true, by simp [stepE, orE], by simp, by intro wD; simp [val, GateOp.eval]⟩
      · cases b <;> left
        · exact ⟨Sum.inr v, by simp [stepE, orE], by simp, by intro wD; simp [val, GateOp.eval]⟩
        · exact ⟨Sum.inl true, by simp [stepE, orE], by simp, by intro wD; simp [val, GateOp.eval]⟩
      · cases c <;> left
        · exact ⟨Sum.inr u, by simp [stepE, orE], by simp, by intro wD; simp [val, GateOp.eval]⟩
        · exact ⟨Sum.inl true, by simp [stepE, orE], by simp, by intro wD; simp [val, GateOp.eval]⟩
      · by_cases huv : u = v
        · subst huv
          left
          exact ⟨Sum.inr u, by simp [stepE, orE], by simp, by intro wD; simp [val, GateOp.eval]⟩
        · right
          exact ⟨{ op := GateOp.or, inputs := [u, v] }, by simp [stepE, orE, huv], rfl, by simp,
            by simp, by intro wD; simp [val]⟩
    · rcases e1 with b | u
      · left; exact ⟨Sum.inl (!b), by simp [stepE], by cases b <;> simp,
          by intro wD; simp [val, GateOp.eval]⟩
      · right
        exact ⟨{ op := GateOp.not, inputs := [u] }, by simp [stepE], rfl, by simp, by simp,
          by intro wD; simp [val, GateOp.eval]⟩
  · simp at hlen


def Inv (n : ℕ) (D : List Gate) (m : List Ent) : Prop :=
  n ≤ m.length ∧
  (∀ w u, m.getD w (Sum.inl false) = Sum.inr u → u < n + D.length) ∧
  ∀ g ∈ D, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

def Sim (wC wD : List Bool) (m : List Ent) : Prop :=
  m.length = wC.length ∧ ∀ w, wC.getD w false = val wD (m.getD w (Sum.inl false))

lemma inv_step (n : ℕ) (s : List Gate × List Ent) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (h : Inv n s.1 s.2) : Inv n (stepS n s g).1 (stepS n s g).2 := by
  obtain ⟨D, m⟩ := s
  obtain ⟨hn, hb, hgs⟩ := h
  simp only at hn hb hgs
  have hes : (g.inputs.map fun i => m.getD i (Sum.inl false)).length ≤ 2 := by simpa using hg.2
  rcases stepE_spec n (D, m) g.op _ hg.1 hes with ⟨e, he, hee, _⟩ | ⟨g', he, hop', hlen', hin, _⟩
  · simp only [stepS, he]
    refine ⟨by simp; omega, ?_, hgs⟩
    intro w u hw
    rw [getD_snoc'] at hw
    split_ifs at hw with h1 h2
    · exact hb w u hw
    · rcases hee with rfl | rfl | hmem
      · simp at hw
      · simp at hw
      · obtain ⟨i, _, hi⟩ := List.mem_map.mp hmem
        exact hb i u (hi.trans hw)
  · simp only [stepS, he]
    refine ⟨by simp; omega, ?_, ?_⟩
    · intro w u hw
      simp only [List.length_append, List.length_singleton]
      rw [getD_snoc'] at hw
      split_ifs at hw with h1 h2
      · have := hb w u hw; omega
      · have := Sum.inr.inj hw; omega
    · intro g'' hg''
      rw [List.mem_append] at hg''
      rcases hg'' with hg'' | hg''
      · exact hgs g'' hg''
      · rw [List.mem_singleton] at hg''
        subst hg''
        exact ⟨hop' ▸ hg.1, hlen'⟩

lemma sim_snoc {wC wD : List Bool} {m : List Ent} (h : Sim wC wD m) (e : Ent) (v : Bool)
    (hv : v = val wD e) : Sim (wC ++ [v]) wD (m ++ [e]) := by
  obtain ⟨hl, hw⟩ := h
  refine ⟨by simp [hl], fun w => ?_⟩
  rw [getD_snoc' false wC v w, getD_snoc' (Sum.inl false) m e w, hl]
  by_cases h1 : w < wC.length
  · simp only [h1, ↓reduceIte]; exact hw w
  · by_cases h2 : w = wC.length
    · simp [h1, h2, hv]
    · simp [h1, h2, val]

lemma sim_add {wC wD : List Bool} {m : List Ent} (h : Sim wC wD m)
    (hb : ∀ w u, m.getD w (Sum.inl false) = Sum.inr u → u < wD.length) (v : Bool) :
    Sim (wC ++ [v]) (wD ++ [v]) (m ++ [Sum.inr wD.length]) := by
  obtain ⟨hl, hw⟩ := h
  refine ⟨by simp [hl], fun w => ?_⟩
  rw [getD_snoc' false wC v w, getD_snoc' (Sum.inl false) m (Sum.inr wD.length) w, hl]
  by_cases h1 : w < wC.length
  · simp only [h1, ↓reduceIte]
    rw [hw w]
    rcases hm : m.getD w (Sum.inl false) with b | u
    · simp [val]
    · have hu := hb w u hm
      simp only [val]
      rw [getD_snoc' false wD v u]
      simp [hu]
  · by_cases h2 : w = wC.length
    · simp [h1, h2, val, getD_snoc']
    · simp [h1, h2, val]

lemma sim_step (n : ℕ) (I : List Bool) (hI : I.length = n) (s : List Gate × List Ent)
    (wC : List Bool) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hinv : Inv n s.1 s.2) (hS : Sim wC (run false GateOp.eval s.1 I) s.2) :
    Sim (wC ++ [g.op.eval (g.inputs.map fun i => wC.getD i false)])
      (run false GateOp.eval (stepS n s g).1 I) (stepS n s g).2 := by
  obtain ⟨D, m⟩ := s
  simp only at hinv hS
  have hwl : (run false GateOp.eval D I).length = n + D.length := by rw [run_length, hI]
  have hbd : ∀ w u, m.getD w (Sum.inl false) = Sum.inr u →
      u < (run false GateOp.eval D I).length := by
    intro w u hw; rw [hwl]; exact hinv.2.1 w u hw
  have hes : (g.inputs.map fun i => m.getD i (Sum.inl false)).length ≤ 2 := by simpa using hg.2
  have hmap : g.inputs.map (fun i => wC.getD i false) =
      (g.inputs.map fun i => m.getD i (Sum.inl false)).map (val (run false GateOp.eval D I)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    exact hS.2 i
  rw [hmap]
  rcases stepE_spec n (D, m) g.op _ hg.1 hes with ⟨e, he, _, hv⟩ | ⟨g', he, hop', _, _, hv⟩
  · simp only [stepS, he]
    exact sim_snoc hS e _ (hv _).symm
  · simp only [stepS, he]
    rw [run_snoc]
    have hv' := hv (run false GateOp.eval D I)
    rw [hop', hv', ← hwl]
    exact sim_add hS hbd _

lemma sim_run (n : ℕ) (I : List Bool) (hI : I.length = n) :
    ∀ (gs : List Gate),
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) →
      ∀ (s : List Gate × List Ent) (wC : List Bool), Inv n s.1 s.2 →
        Sim wC (run false GateOp.eval s.1 I) s.2 →
        Inv n (gs.foldl (stepS n) s).1 (gs.foldl (stepS n) s).2 ∧
        Sim (run false GateOp.eval gs wC) (run false GateOp.eval (gs.foldl (stepS n) s).1 I)
          (gs.foldl (stepS n) s).2 := by
  intro gs
  induction gs with
  | nil => intro _ s wC hi hs; exact ⟨hi, hs⟩
  | cons g gs ih =>
    intro hgs s wC hi hs
    have hg := hgs g (by simp)
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) (stepS n s g)
      (wC ++ [g.op.eval (g.inputs.map fun i => wC.getD i false)]) (inv_step n s g hg hi)
      (sim_step n I hI s wC g hg hi hs)

lemma stepS_len (n : ℕ) (s : List Gate × List Ent) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) :
    (stepS n s g).2.length = s.2.length + 1 ∧ (stepS n s g).1.length ≤ s.1.length + 1 := by
  obtain ⟨D, m⟩ := s
  have hes : (g.inputs.map fun i => m.getD i (Sum.inl false)).length ≤ 2 := by simpa using hg.2
  rcases stepE_spec n (D, m) g.op _ hg.1 hes with ⟨e, he, _⟩ | ⟨g', he, _⟩
  · simp only [stepS, he]; simp
  · simp only [stepS, he]; simp

lemma len_run (n : ℕ) :
    ∀ (gs : List Gate),
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) →
      ∀ (s : List Gate × List Ent),
        (gs.foldl (stepS n) s).2.length = s.2.length + gs.length ∧
        (gs.foldl (stepS n) s).1.length ≤ s.1.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro _ s; simp
  | cons g gs ih =>
    intro hgs s
    have h1 := ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) (stepS n s g)
    have h2 := stepS_len n s g (hgs g (by simp))
    simp only [List.foldl_cons, List.length_cons]
    omega

def Viol (L : ℕ) (g : Gate) : Prop :=
  (∃ i ∈ g.inputs, L ≤ i) ∨ ¬ g.inputs.Nodup ∨ (g.op = GateOp.not ∧ g.inputs.length ≠ 1) ∨
    (g.op ≠ GateOp.not ∧ g.inputs.length ≠ 2)

lemma noadd (n : ℕ) (s : List Gate × List Ent) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : g.op = GateOp.not → g.inputs.length ≤ 1) (hV : Viol s.2.length g) :
    (stepS n s g).1 = s.1 := by
  obtain ⟨D, m⟩ := s
  simp only at hV
  rcases g with ⟨op, ins⟩
  obtain ⟨hop, hlen⟩ := hg
  unfold Viol at hV
  simp only at hop hlen hnot hV
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · rcases hop with rfl | rfl | rfl <;> simp [stepS, stepE]
  · rcases hop with rfl | rfl | rfl
    · simp [stepS, stepE]
    · simp [stepS, stepE]
    · have hma : m.length ≤ a := by
        rcases hV with ⟨i, hi, hle⟩ | hV | ⟨_, hV⟩ | ⟨hV, _⟩
        · simp at hi; subst hi; exact hle
        · simp at hV
        · simp at hV
        · exact absurd rfl hV
      have hga : m.getD a (Sum.inl false) = Sum.inl false := getD_ge' _ _ _ hma
      show (stepE n (D, m) GateOp.not [m.getD a (Sum.inl false)]).1 = D
      rw [hga]
      rfl
  · rcases hop with rfl | rfl | rfl
    · have key : ∀ (x y : Ent), (x = Sum.inl false ∨ y = Sum.inl false ∨ x = y) → (andE n (D, m) x y).1 = D := by
        intro x y hxy
        rcases x with bx | u <;> rcases y with by' | v
        · cases bx <;> cases by' <;> simp [andE]
        · cases bx <;> simp [andE]
        · cases by' <;> simp [andE]
        · by_cases huv : u = v
          · simp [andE, huv]
          · simp at hxy
            exact absurd hxy huv
      have hcond : m.getD a (Sum.inl false) = Sum.inl false ∨ m.getD b (Sum.inl false) = Sum.inl false ∨
          m.getD a (Sum.inl false) = m.getD b (Sum.inl false) := by
        rcases hV with ⟨i, hi, hle⟩ | hV | ⟨h3, _⟩ | ⟨_, h4⟩
        · simp at hi
          rcases hi with rfl | rfl
          · exact Or.inl (getD_ge' _ _ _ hle)
          · exact Or.inr (Or.inl (getD_ge' _ _ _ hle))
        · have : a = b := by simpa using hV
          subst this
          exact Or.inr (Or.inr rfl)
        · cases h3
        · exact absurd rfl h4
      exact key _ _ hcond
    · have key : ∀ (x y : Ent), (x = Sum.inl false ∨ y = Sum.inl false ∨ x = y) → (orE n (D, m) x y).1 = D := by
        intro x y hxy
        rcases x with bx | u <;> rcases y with by' | v
        · cases bx <;> cases by' <;> simp [orE]
        · cases bx <;> simp [orE]
        · cases by' <;> simp [orE]
        · by_cases huv : u = v
          · simp [orE, huv]
          · simp at hxy
            exact absurd hxy huv
      have hcond : m.getD a (Sum.inl false) = Sum.inl false ∨ m.getD b (Sum.inl false) = Sum.inl false ∨
          m.getD a (Sum.inl false) = m.getD b (Sum.inl false) := by
        rcases hV with ⟨i, hi, hle⟩ | hV | ⟨h3, _⟩ | ⟨_, h4⟩
        · simp at hi
          rcases hi with rfl | rfl
          · exact Or.inl (getD_ge' _ _ _ hle)
          · exact Or.inr (Or.inl (getD_ge' _ _ _ hle))
        · have : a = b := by simpa using hV
          subst this
          exact Or.inr (Or.inr rfl)
        · cases h3
        · exact absurd rfl h4
      exact key _ _ hcond
    · have := hnot rfl
      simp at this
  · simp at hlen

lemma strict_run (n : ℕ) :
    ∀ (gs : List Gate),
      (∀ g ∈ gs, ((g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)) →
      ∀ (j : ℕ) (g : Gate), gs[j]? = some g →
      ∀ (s : List Gate × List Ent), Viol (s.2.length + j) g →
        (gs.foldl (stepS n) s).1.length < s.1.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro _ j g hj; simp at hj
  | cons g0 gs ih =>
    intro hgs j g hj s hV
    have hg0 := hgs g0 (by simp)
    cases j with
    | zero =>
      simp at hj
      subst hj
      have e := noadd n s g0 hg0.1 hg0.2 (by simpa using hV)
      have h1 := (len_run n gs (fun g' hg' => (hgs g' (List.mem_cons_of_mem _ hg')).1)
        (stepS n s g0)).2
      simp only [List.foldl_cons, List.length_cons]
      rw [e] at h1
      omega
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      have hl := (stepS_len n s g0 hg0.1).1
      have h3 := ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) j g hj (stepS n s g0)
        (by rw [hl]; have : s.2.length + 1 + j = s.2.length + (j + 1) := by omega
            rw [this]; exact hV)
      have h4 := (stepS_len n s g0 hg0.1).2
      simp only [List.foldl_cons, List.length_cons]
      omega

def m0 (n : ℕ) : List Ent := (List.range n).map Sum.inr

lemma m0_getD (n w : ℕ) : (m0 n).getD w (Sum.inl false) = if w < n then Sum.inr w else Sum.inl false := by
  by_cases h : w < n
  · simp [m0, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h, h]
  · have hn : (List.range n)[w]? = none := List.getElem?_eq_none (by simp; omega)
    simp [m0, List.getD_eq_getElem?_getD, List.getElem?_map, hn, h]

lemma inv0 (n : ℕ) : Inv n [] (m0 n) := by
  refine ⟨by simp [m0], ?_, ?_⟩
  · intro w u hw
    rw [m0_getD] at hw
    split_ifs at hw with h
    have := Sum.inr.inj hw
    simp
    omega
  · intro g hg; simp at hg

lemma ofFn_getD' {n : ℕ} (x : Fin n → Bool) (j : ℕ) (hj : j < n) :
    (List.ofFn x).getD j false = x ⟨j, hj⟩ := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj]

lemma sim0 (n : ℕ) (x : Fin n → Bool) : Sim (List.ofFn x) (List.ofFn x) (m0 n) := by
  refine ⟨by simp [m0], fun w => ?_⟩
  rw [m0_getD]
  by_cases h : w < n
  · simp [h, val]
  · simp only [h, ↓reduceIte, val]
    exact getD_ge' false _ _ (by simp; omega)

lemma no_viol (n : ℕ) (C : Circuit) (hmin : IsMinimalCircuit n C)
    (hne : ∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y)
    (hnot : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1)
    (j : ℕ) (g : Gate) (hj : C.gates[j]? = some g) : ¬ Viol (n + j) g := by
  intro hV
  obtain ⟨hFI, hmin2⟩ := hmin
  have hgs : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    have := hFI g hg
    refine ⟨?_, this.2⟩
    have h1 := this.1
    simpa [or_assoc] using h1
  have hgs2 : ∀ g ∈ C.gates, ((g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) ∧ (g.op = GateOp.not → g.inputs.length ≤ 1) :=
    fun g hg => ⟨hgs g hg, hnot g hg⟩
  have hstrict := strict_run n C.gates hgs2 j g hj ([], m0 n) (by simpa [m0] using hV)
  obtain ⟨st, hst⟩ : ∃ st : List Gate × List Ent, st = C.gates.foldl (stepS n) ([], m0 n) :=
    ⟨_, rfl⟩
  rw [← hst] at hstrict
  simp only [List.length_nil, zero_add] at hstrict
  have hsim : ∀ x : Fin n → Bool, Inv n st.1 st.2 ∧
      Sim (run false GateOp.eval C.gates (List.ofFn x))
        (run false GateOp.eval st.1 (List.ofFn x)) st.2 := by
    intro x
    rw [hst]
    exact sim_run n (List.ofFn x) (by simp) C.gates hgs ([], m0 n) (List.ofFn x) (inv0 n)
      (sim0 n x)
  have hfun : ∀ x : Fin n → Bool, circuitFun n C x =
      val (run false GateOp.eval st.1 (List.ofFn x)) (st.2.getD C.output (Sum.inl false)) := by
    intro x
    exact (hsim x).2.2 C.output
  obtain ⟨u, hu⟩ : ∃ u, st.2.getD C.output (Sum.inl false) = Sum.inr u := by
    rcases hent : st.2.getD C.output (Sum.inl false) with b | u
    · exfalso
      obtain ⟨x, y, hxy⟩ := hne
      apply hxy
      rw [hfun x, hfun y, hent]
      rfl
    · exact ⟨u, rfl⟩
  have hFI' : FanInTwo (⟨st.1, u⟩ : Circuit) := by
    intro g' hg'
    have := ((hsim (fun _ => false)).1.2.2 g' hg')
    refine ⟨?_, this.2⟩
    simpa [or_assoc] using this.1
  have hD := hmin2 ⟨st.1, u⟩ hFI' (by
    funext x
    rw [hfun x, hu]
    simp only [circuitFun, Circuit.eval, wires_run, val])
  have hsz : (⟨st.1, u⟩ : Circuit).size = st.1.length := rfl
  have hcs : C.size = C.gates.length := rfl
  omega

end PEqualNP.Outside.L_meta_3592

open PEqualNP.Outside.L_meta_3592 in
theorem PEqualNP.Outside.L_meta_3592 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit x1 x2 → (∃ (x4 : Fin x1 → Bool) (x5 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x2 x4 ≠ PEqualNP.MetaComplexity.circuitFun x1 x2 x5) → (∀ x5 ∈ x2.gates, x5.op = PEqualNP.CircuitLowerBounds.GateOp.not → x5.inputs.length ≤ (1 : ℕ)) → ∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x6]? = Option.some x7 → (∀ x9 ∈ x7.inputs, x9 < x1 + x6) ∧ x7.inputs.Nodup ∧ (x7.op = PEqualNP.CircuitLowerBounds.GateOp.not → x7.inputs.length = (1 : ℕ)) ∧ (x7.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → x7.inputs.length = (2 : ℕ)) := by
  intro x1 x2 hmin hne hnot x6 x7 hx
  have h := PEqualNP.Outside.L_meta_3592.no_viol x1 x2 hmin hne hnot x6 x7 hx
  unfold PEqualNP.Outside.L_meta_3592.Viol at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x9 hx9
    by_contra hlt
    exact h (Or.inl ⟨x9, hx9, by omega⟩)
  · by_contra hnd
    exact h (Or.inr (Or.inl hnd))
  · intro hop
    by_contra hl
    exact h (Or.inr (Or.inr (Or.inl ⟨hop, hl⟩)))
  · intro hop
    by_contra hl
    exact h (Or.inr (Or.inr (Or.inr ⟨hop, hl⟩)))
