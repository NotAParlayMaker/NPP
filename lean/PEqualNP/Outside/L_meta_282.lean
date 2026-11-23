import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_282_aux

open PEqualNP.CircuitLowerBounds
-- The reduction to OR closures of AND outputs is adapted from L-meta-265.

private def red_e (i : Fin 6) : Fin 6 → Bool := fun k => decide (k = i)

private def red_pair (i j : Fin 6) : Fin 6 → Bool := fun k => red_e i k || red_e j k

private def red_hom (a : (Fin 6 → Bool) → Bool) : Prop :=
  ∀ x y : Fin 6 → Bool, a (fun i => x i || y i) = (a x || a y)

private theorem red_hom_pair {a : (Fin 6 → Bool) → Bool} (ha : red_hom a) (i j : Fin 6) :
    a (red_pair i j) = (a (red_e i) || a (red_e j)) := ha _ _

private def red_cl (G : List ((Fin 6 → Bool) → Bool)) (w : (Fin 6 → Bool) → Bool) : Prop :=
  ∃ h, red_hom h ∧ ∃ G' : List ((Fin 6 → Bool) → Bool),
    (∀ g ∈ G', g ∈ G) ∧ ∀ x, w x = (h x || G'.any (fun g => g x))

private def red_good : List ((Fin 6 → Bool) → Bool) → Prop
  | [] => True
  | g :: G => (∃ u v, red_cl G u ∧ red_cl G v ∧ ∀ x, g x = (u x && v x)) ∧ red_good G

private theorem red_hom_false : red_hom (fun _ => false) := fun _ _ => rfl

private theorem red_hom_true : red_hom (fun _ => true) := fun _ _ => rfl

private theorem red_cl_of_hom {G : List ((Fin 6 → Bool) → Bool)} {h : (Fin 6 → Bool) → Bool}
    (hh : red_hom h) : red_cl G h :=
  ⟨h, hh, [], by simp, by simp⟩

private theorem red_cl_congr {G : List ((Fin 6 → Bool) → Bool)} {u w : (Fin 6 → Bool) → Bool}
    (hu : red_cl G u) (e : ∀ x, w x = u x) : red_cl G w := by
  obtain ⟨h, hh, G', hs, he⟩ := hu
  exact ⟨h, hh, G', hs, fun x => by rw [e x, he x]⟩

private theorem red_cl_mono {G : List ((Fin 6 → Bool) → Bool)} {w : (Fin 6 → Bool) → Bool}
    (g : (Fin 6 → Bool) → Bool) (hw : red_cl G w) : red_cl (g :: G) w := by
  obtain ⟨h, hh, G', hs, he⟩ := hw
  exact ⟨h, hh, G', fun g' hg' => List.mem_cons_of_mem _ (hs g' hg'), he⟩

private theorem red_cl_or {G : List ((Fin 6 → Bool) → Bool)} {u v : (Fin 6 → Bool) → Bool}
    (hu : red_cl G u) (hv : red_cl G v) : red_cl G (fun x => u x || v x) := by
  obtain ⟨h, hh, G1, hs, he⟩ := hu
  obtain ⟨k, hk, G2, hs2, he2⟩ := hv
  refine ⟨fun x => h x || k x, ?_, G1 ++ G2, ?_, ?_⟩
  · intro x y
    show (h _ || k _) = ((h x || k x) || (h y || k y))
    rw [hh x y, hk x y]
    cases h x <;> cases h y <;> cases k x <;> cases k y <;> rfl
  · intro g hg
    rcases List.mem_append.mp hg with h1 | h1
    · exact hs g h1
    · exact hs2 g h1
  · intro x
    show (u x || v x) = ((h x || k x) || (G1 ++ G2).any fun g => g x)
    rw [he x, he2 x, List.any_append]
    cases h x <;> cases k x <;> cases (G1.any fun g => g x) <;> cases (G2.any fun g => g x) <;> rfl

private theorem red_cl_new (G : List ((Fin 6 → Bool) → Bool)) (g : (Fin 6 → Bool) → Bool) :
    red_cl (g :: G) g :=
  ⟨fun _ => false, red_hom_false, [g], by simp, by simp⟩

private theorem red_gate_or (G : List ((Fin 6 → Bool) → Bool)) (f : ℕ → (Fin 6 → Bool) → Bool)
    (hw : ∀ k, red_cl G (f k)) (ins : List ℕ) (hl : ins.length ≤ 2) :
    red_cl G (fun x => GateOp.eval GateOp.or (ins.map fun i => f i x)) := by
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, t⟩⟩⟩
  · exact red_cl_congr (red_cl_of_hom red_hom_false) (fun x => by simp [GateOp.eval])
  · exact red_cl_congr (hw i) (fun x => by simp [GateOp.eval])
  · exact red_cl_congr (red_cl_or (hw i) (hw j)) (fun x => by simp [GateOp.eval])
  · exact absurd hl (by simp only [List.length_cons]; omega)

private theorem red_gate_and (G : List ((Fin 6 → Bool) → Bool)) (f : ℕ → (Fin 6 → Bool) → Bool)
    (hw : ∀ k, red_cl G (f k)) (ins : List ℕ) (hl : ins.length ≤ 2) :
    ∃ u v, red_cl G u ∧ red_cl G v ∧
      ∀ x, GateOp.eval GateOp.and (ins.map fun i => f i x) = (u x && v x) := by
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, t⟩⟩⟩
  · exact ⟨fun _ => true, fun _ => true, red_cl_of_hom red_hom_true, red_cl_of_hom red_hom_true,
      fun x => by simp [GateOp.eval]⟩
  · exact ⟨f i, f i, hw i, hw i, fun x => by simp [GateOp.eval]⟩
  · exact ⟨f i, f j, hw i, hw j, fun x => by simp [GateOp.eval]⟩
  · exact absurd hl (by simp only [List.length_cons]; omega)

private def red_W (gs : List Gate) (x : Fin 6 → Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)

private def red_wf (gs : List Gate) (k : ℕ) : (Fin 6 → Bool) → Bool :=
  fun x => (red_W gs x).getD k false

private theorem red_fold_len (gs : List Gate) : ∀ w0 : List Bool,
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w0).length
      = w0.length + gs.length := by
  induction gs with
  | nil => intro w0; simp
  | cons g gs ih => intro w0; rw [List.foldl_cons, ih]; simp; omega

private theorem red_W_len (gs : List Gate) (x : Fin 6 → Bool) :
    (red_W gs x).length = 6 + gs.length := by
  unfold red_W
  rw [red_fold_len]
  simp

private theorem red_W_snoc (gs : List Gate) (g : Gate) (x : Fin 6 → Bool) :
    red_W (gs ++ [g]) x
      = red_W gs x ++ [g.op.eval (g.inputs.map fun i => (red_W gs x).getD i false)] := by
  simp [red_W, List.foldl_append]

private theorem red_wf_snoc (gs : List Gate) (g : Gate) (k : ℕ) :
    red_wf (gs ++ [g]) k = if k = 6 + gs.length then
      (fun x => g.op.eval (g.inputs.map fun i => red_wf gs i x)) else red_wf gs k := by
  funext x
  have hl := red_W_len gs x
  by_cases hk : k = 6 + gs.length
  · rw [ite_eq_left hk]
    show (red_W (gs ++ [g]) x).getD k false = g.op.eval (g.inputs.map fun i => (red_W gs x).getD i false)
    rw [red_W_snoc]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append, hl, hk]
  · rw [ite_eq_right hk]
    show (red_W (gs ++ [g]) x).getD k false = (red_W gs x).getD k false
    rw [red_W_snoc]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append, hl]
    split
    · rfl
    · rename_i h2
      have h3 : ¬ (k - (6 + gs.length) = 0) := by omega
      have h4 : ¬ k < (red_W gs x).length := by rw [hl]; exact h2
      simp [h3, hl, h2]

private theorem red_base (k : ℕ) : red_hom (red_wf [] k) := by
  intro x y
  unfold red_wf red_W
  simp only [List.foldl_nil, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases hk : k < 6
  · simp [hk]
  · simp [hk]

private theorem red_inv (A : Finset ℕ) (gs : List Gate)
    (hm : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hA : ∀ (j : ℕ) (g : Gate), gs[j]? = some g → g.op = GateOp.and → j ∈ A) :
    ∃ G, red_good G ∧ G.length ≤ (A.filter (fun j => j < gs.length)).card ∧
      ∀ k, red_cl G (red_wf gs k) := by
  induction gs using List.reverseRecOn with
  | nil => exact ⟨[], trivial, by simp, fun k => red_cl_of_hom (red_base k)⟩
  | append_singleton gs g ih =>
    obtain ⟨G, hG, hlen, hw⟩ := ih (fun g' hg' => hm g' (by simp [hg']))
      (fun j g' hj ho => hA j g' (by
        have hjl : j < gs.length := (List.getElem?_eq_some_iff.mp hj).1
        rw [List.getElem?_append_left hjl]; exact hj) ho)
    obtain ⟨hop, hl⟩ := hm g (by simp)
    rcases hop with hop | hop
    · obtain ⟨u, v, hu, hv, he⟩ := red_gate_and G (red_wf gs) hw g.inputs hl
      have hmem : gs.length ∈ A := hA gs.length g (by simp) hop
      refine ⟨(fun x => GateOp.eval GateOp.and (g.inputs.map fun i => red_wf gs i x)) :: G,
        ⟨⟨u, v, hu, hv, he⟩, hG⟩, ?_, ?_⟩
      · have hsub : insert gs.length (A.filter (fun j => j < gs.length))
            ⊆ A.filter (fun j => j < (gs ++ [g]).length) := by
          intro j hj
          simp only [Finset.mem_insert, Finset.mem_filter, List.length_append, List.length_cons,
            List.length_nil] at hj ⊢
          rcases hj with rfl | ⟨h1, h2⟩
          · exact ⟨hmem, by omega⟩
          · exact ⟨h1, by omega⟩
        have hc := Finset.card_le_card hsub
        rw [Finset.card_insert_of_notMem (by simp)] at hc
        simp only [List.length_cons]
        omega
      · intro k
        rw [red_wf_snoc, hop]
        by_cases hk : k = 6 + gs.length
        · rw [ite_eq_left hk]; exact red_cl_new _ _
        · rw [ite_eq_right hk]; exact red_cl_mono _ (hw k)
    · refine ⟨G, hG, ?_, ?_⟩
      · refine le_trans hlen (Finset.card_le_card ?_)
        intro j hj
        simp only [Finset.mem_filter, List.length_append, List.length_cons, List.length_nil] at hj ⊢
        exact ⟨hj.1, by omega⟩
      · intro k
        rw [red_wf_snoc, hop]
        by_cases hk : k = 6 + gs.length
        · rw [ite_eq_left hk]; exact red_gate_or G (red_wf gs) hw g.inputs hl
        · rw [ite_eq_right hk]; exact hw k

private theorem red_any2 (g1 g2 : (Fin 6 → Bool) → Bool) (G' : List ((Fin 6 → Bool) → Bool)) :
    (∀ g ∈ G', g = g2 ∨ g = g1) →
    ∃ c1 c2 : Bool, ∀ x, G'.any (fun g => g x) = (c1 && g1 x || c2 && g2 x) := by
  induction G' with
  | nil => intro _; exact ⟨false, false, fun x => rfl⟩
  | cons g G' ih =>
    intro hs
    obtain ⟨c1, c2, hc⟩ := ih (fun g' hg' => hs g' (List.mem_cons_of_mem _ hg'))
    rcases hs g (List.mem_cons_self) with hg | hg
    · refine ⟨c1, true, fun x => ?_⟩
      rw [List.any_cons, hc x, hg]
      cases c1 <;> cases c2 <;> cases (g2 x) <;> cases (g1 x) <;> rfl
    · refine ⟨true, c2, fun x => ?_⟩
      rw [List.any_cons, hc x, hg]
      cases c1 <;> cases c2 <;> cases (g2 x) <;> cases (g1 x) <;> rfl

private theorem red_cl_nil {a : (Fin 6 → Bool) → Bool} (ha : red_cl [] a) : red_hom a := by
  obtain ⟨h, hh, G', hs, he⟩ := ha
  have hG : G' = [] := List.eq_nil_iff_forall_not_mem.mpr (fun g hg => by simpa using hs g hg)
  subst hG
  have he' : ∀ x, a x = h x := fun x => by simpa using he x
  intro x y
  rw [he', he', he']
  exact hh x y

private theorem red_cl_one {g1 u : (Fin 6 → Bool) → Bool} (hu : red_cl [g1] u) :
    ∃ h, red_hom h ∧ ∃ c : Bool, ∀ x, u x = (h x || (c && g1 x)) := by
  obtain ⟨h, hh, G', hs, he⟩ := hu
  obtain ⟨c1, c2, hc⟩ := red_any2 g1 g1 G' (fun g hg => by simpa using hs g hg)
  refine ⟨h, hh, c1 || c2, fun x => ?_⟩
  rw [he x, hc x]
  cases c1 <;> cases c2 <;> cases (g1 x) <;> cases (h x) <;> rfl

private theorem red_cl_two {g1 g2 w : (Fin 6 → Bool) → Bool} (hw : red_cl [g2, g1] w) :
    ∃ h, red_hom h ∧ ∃ c1 c2 : Bool, ∀ x, w x = (h x || (c1 && g1 x || c2 && g2 x)) := by
  obtain ⟨h, hh, G', hs, he⟩ := hw
  obtain ⟨c1, c2, hc⟩ := red_any2 g1 g2 G' (fun g hg => by simpa using hs g hg)
  exact ⟨h, hh, c1, c2, fun x => by rw [he x, hc x]⟩

private theorem red_pad {G : List ((Fin 6 → Bool) → Bool)} (hG : red_good G) :
    red_good ((fun _ => false) :: G) :=
  ⟨⟨fun _ => false, fun _ => false, red_cl_of_hom red_hom_false, red_cl_of_hom red_hom_false,
    fun _ => rfl⟩, hG⟩


abbrev Input := Fin 6 → Bool
abbrev F := Input → Bool

def lhs : Fin 8 → Fin 6 := ![0,0,0,1,1,1,2,2]
def rhs : Fin 8 → Fin 6 := ![3,4,5,3,4,5,4,5]
def z (r : Fin 8) : Input := red_pair (lhs r) (rhs r)
def su (x y : Input) : Input := fun i => x i || y i

abbrev edge (x : Input) := ∃ u v : Fin 6, (u.val,v.val) ∈
  ([(0,1),(0,2),(1,2),(3,4),(3,5),(4,5),(2,3)] : List (ℕ × ℕ)) ∧ x u=true ∧ x v=true

theorem negative : ∀ i, ¬ edge (z i) := by decide +kernel
theorem positive : ∀ i j, i ≠ j → edge (su (z i) (z j)) := by decide +kernel

def Bounded (x y : Input) (u : F) : Prop := u (su x y) = true → u x=true ∨ u y=true

theorem free_bound {G : List F} {u : F} (hu : red_cl G u) {x y : Input}
    (hs : ∀ g ∈ G, Bounded x y g) : Bounded x y u := by
  obtain ⟨h,hom,H,sub,ev⟩ := hu
  unfold Bounded
  rw [ev,ev,ev,show h (su x y)= (h x || h y) by exact hom x y]
  simp only [Bool.or_eq_true,List.any_eq_true]
  rintro ((hx|hy)|⟨g,hg,t⟩)
  · exact Or.inl (Or.inl hx)
  · exact Or.inr (Or.inl hy)
  · rcases hs g (sub g hg) t with u | u
    · exact Or.inl (Or.inr ⟨g,hg,u⟩)
    · exact Or.inr (Or.inr ⟨g,hg,u⟩)

theorem meet_bound {g a b t : F} (hg : ∀ x, g x = (a x && b x)) {x y : Input}
    (ha : Bounded x y a) (hb : Bounded x y b) (side : t=a ∨ t=b) (eq : t x=t y) :
    Bounded x y g := by
  unfold Bounded at *
  simp only [hg,Bool.and_eq_true]
  rintro ⟨ax,bx⟩
  obtain ax | ay := ha ax <;> obtain bx | by' := hb bx <;>
    rcases side with rfl | rfl <;> grind

def circuitForm (g1 g2 g3 a b c d e f w : F) : Prop :=
  (red_cl [] a ∧ red_cl [] b ∧ ∀ x, g1 x=(a x && b x)) ∧
  (red_cl [g1] c ∧ red_cl [g1] d ∧ ∀ x, g2 x=(c x && d x)) ∧
  (red_cl [g2,g1] e ∧ red_cl [g2,g1] f ∧ ∀ x, g3 x=(e x && f x)) ∧
  red_cl [g3,g2,g1] w

abbrev Correct (w : F) := ∀ x, w x=true ↔ edge x

theorem codes {g1 g2 g3 a b c d e f w : F} (form : circuitForm g1 g2 g3 a b c d e f w)
    (correct : Correct w) {u v t : F} (s1 : u=a ∨ u=b) (s2 : v=c ∨ v=d) (s3 : t=e ∨ t=f) :
    Function.Injective (fun i : Fin 8 => (u (z i), v (z i), t (z i))) := by
  rintro i j eq
  by_contra ne
  obtain ⟨⟨ha,hb,h1⟩,⟨hc,hd,h2⟩,⟨he,hf,h3⟩,hw⟩ := form
  have eu := congrArg Prod.fst eq
  have ev := congrArg (fun p : Bool × Bool × Bool => p.2.1) eq
  have et := congrArg (fun p : Bool × Bool × Bool => p.2.2) eq
  have b1 : Bounded (z i) (z j) g1 := meet_bound h1
    (free_bound ha (by simp)) (free_bound hb (by simp)) s1 eu
  have old1 : ∀ g ∈ [g1], Bounded (z i) (z j) g := by simpa using b1
  have b2 : Bounded (z i) (z j) g2 := meet_bound h2 (free_bound hc old1) (free_bound hd old1) s2 ev
  have old2 : ∀ g ∈ [g2,g1], Bounded (z i) (z j) g := by simpa using And.intro b2 b1
  have b3 : Bounded (z i) (z j) g3 := meet_bound h3 (free_bound he old2) (free_bound hf old2) s3 et
  have last := free_bound hw (x:=z i) (y:=z j) (by simpa using And.intro b3 (And.intro b2 b1))
  rcases last ((correct _).mpr (positive i j ne)) with hi | hj
  · exact negative i ((correct _).mp hi)
  · exact negative j ((correct _).mp hj)


abbrev M := BitVec 8
def pack {n : ℕ} (fn : Fin n → Bool) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn fn)).cast (by simp)
theorem pack_read {n : ℕ} (fn : Fin n → Bool) (i : Fin n) :
    (pack fn).getLsbD i.val = fn i := by
  unfold pack
  rw [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt)]
  simp only [List.getElem_ofFn]

def mark (g : F) : M := pack (fun i => g (z i))
def rd (m : M) (i : Fin 8) : Bool := m.getLsbD i.val
theorem mark_read (g : F) (i : Fin 8) : rd (mark g) i = g (z i) := pack_read _ _
theorem extM {m n : M} (h : ∀ i : Fin 8, rd m i = rd n i) : m=n := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simpa only [rd,BitVec.getLsbD_eq_getElem hi] using h ⟨i,hi⟩

theorem mark_and {g a b : F} (h : ∀ x, g x=(a x && b x)) : mark g = (mark a &&& mark b) := by
  apply extM; intro i
  change rd (mark g) i = (mark a &&& mark b).getLsbD i.val
  rw [BitVec.getLsbD_and]
  simpa only [rd,mark,pack_read] using h (z i)

def projection (m : BitVec 6) : M := pack (fun i : Fin 8 =>
  m.getLsbD (lhs i).val || m.getLsbD (rhs i).val)

def raw : List M := [0x0, 0x7, 0x9, 0xf, 0x38, 0x39, 0x3f, 0x52, 0x57, 0x5b, 0x5f, 0x7a, 0x7b, 0x7f, 0xa4, 0xa7, 0xad, 0xaf, 0xbc, 0xbd, 0xbf, 0xc0, 0xc7, 0xc9, 0xcf, 0xd2, 0xd7, 0xdb, 0xdf, 0xe4, 0xe7, 0xed, 0xef, 0xf6, 0xf7, 0xf8, 0xf9, 0xfa, 0xfb, 0xfc, 0xfd, 0xfe, 0xff]
theorem raw_covers : ∀ b : BitVec 6, projection b ∈ raw := by decide +kernel
theorem hom_mem {u : F} (h : red_hom u) : mark u ∈ raw := by
  let bits := pack (fun i : Fin 6 => u (red_e i))
  have eq : mark u=projection bits := by
    apply extM; intro i
    rw [mark_read]
    change u (red_pair (lhs i) (rhs i)) = (pack _).getLsbD i.val
    rw [pack_read]
    simpa only [bits,pack_read] using red_hom_pair h (lhs i) (rhs i)
  rw [eq]; exact raw_covers bits

def opts : List M → List M
  | [] => raw
  | g :: gs => opts gs ++ (opts gs).map (fun v => v ||| g)

def addOpt (m n : M) (b : Bool) : M := if b then m ||| n else m
theorem opt_mem {m : M} {gs : List M} (hm : m ∈ opts gs) (n : M) (b : Bool) :
    addOpt m n b ∈ opts (n::gs) := by
  cases b
  · exact List.mem_append_left _ hm
  · exact List.mem_append_right _ (List.mem_map.mpr ⟨m,hm,rfl⟩)

theorem opt_read (m n : M) (b : Bool) (i : Fin 8) :
    rd (addOpt m n b) i = (rd m i || (b && rd n i)) := by
  cases b <;> simp [addOpt,rd]

theorem cls0 {u : F} (h : red_cl [] u) : mark u ∈ opts [] :=
  hom_mem (red_cl_nil h)
theorem cls1 {u a : F} (h : red_cl [a] u) : mark u ∈ opts [mark a] := by
  obtain ⟨v,hv,c,eq⟩ := red_cl_one h
  have hh : mark u = addOpt (mark v) (mark a) c := by
    apply extM; intro i
    rw [opt_read,mark_read,mark_read,mark_read,eq]
  rw [hh]; exact opt_mem (gs:=[]) (hom_mem hv) _ c
theorem cls2 {u a b : F} (h : red_cl [b,a] u) : mark u ∈ opts [mark b,mark a] := by
  obtain ⟨v,hv,c,d,eq⟩ := red_cl_two h
  have hh : mark u = addOpt (addOpt (mark v) (mark a) c) (mark b) d := by
    apply extM; intro i
    rw [opt_read,opt_read,mark_read,mark_read,mark_read,mark_read,eq,Bool.or_assoc]
  rw [hh]; exact opt_mem (opt_mem (gs:=[]) (hom_mem hv) _ c) _ d

theorem needs_zero {u g1 g2 g3 : F} (hw : red_cl [g3,g2,g1] u) (hc : Correct u) :
    mark g1=0 ∨ mark g2=0 ∨ mark g3=0 := by
  by_contra absent
  obtain ⟨h,hom,H,sub,eq⟩ := hw
  have zfalse (i : Fin 8) : u (z i)=false := by
    cases e : u (z i) with
    | false => rfl
    | true => exact False.elim (negative i ((hc _).mp e))
  have hempty : H=[] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro v hv
    have clear : mark v=0 := by
      apply extM; intro i
      rw [mark_read]
      have hh := (eq (z i)).symm.trans (zfalse i)
      have anyF := (Bool.or_eq_false_iff.mp hh).2
      have vv := List.any_eq_false.mp anyF v hv
      simpa [rd] using vv
    have member := sub v hv
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact absent (Or.inr (Or.inr clear))
    · exact absent (Or.inr (Or.inl clear))
    · exact absent (Or.inl clear)
  have hu (x : Input) : u x=h x := by simpa [hempty] using eq x
  have yes := (hc _).mpr (positive 0 1 (by decide))
  rw [hu,show h (su (z 0) (z 1))=(h (z 0) || h (z 1)) by exact hom _ _,
    ← hu, ← hu,zfalse,zfalse] at yes
  contradiction


def signMask (a : M) (b : Bool) := if b then a else ~~~a
def strip (m : M) := m &&& (m-1)
def one (m : M) := strip m == 0
def two (m : M) := one (strip m)
def four (m : M) := two (strip (strip m))
def hits (m : M) : Finset (Fin 8) := Finset.univ.filter (fun i => rd m i=true)

theorem counts : ∀ m : M, (one m=true ↔ (hits m).card ≤ 1) ∧
    (two m=true ↔ (hits m).card ≤ 2) ∧ (four m=true ↔ (hits m).card ≤ 4) := by decide +kernel

theorem sign_spec (a : M) (b : Bool) (i : Fin 8) :
    rd (signMask a b) i=true ↔ rd a i=b := by
  cases b <;> simp [rd,signMask,i.isLt]

theorem hit1 {a : M} {x : Bool} {i : Fin 8} (h : i ∈ hits (signMask a x)) : rd a i=x :=
  (sign_spec _ _ _).mp (Finset.mem_filter.mp h).2

theorem hit2 {a b : M} {x y : Bool} {i : Fin 8}
    (h : i ∈ hits (signMask a x &&& signMask b y)) : rd a i=x ∧ rd b i=y := by
  have h' := (Finset.mem_filter.mp h).2
  change (signMask a x &&& signMask b y).getLsbD i.val=true at h'
  rw [BitVec.getLsbD_and,Bool.and_eq_true] at h'
  exact ⟨(sign_spec _ _ _).mp h'.1,(sign_spec _ _ _).mp h'.2⟩

theorem hit3 {a b c : M} {x y v : Bool} {i : Fin 8}
    (h : i ∈ hits (signMask a x &&& signMask b y &&& signMask c v)) :
    rd a i=x ∧ rd b i=y ∧ rd c i=v := by
  have h' := (Finset.mem_filter.mp h).2
  change (signMask a x &&& signMask b y &&& signMask c v).getLsbD i.val=true at h'
  simp only [BitVec.getLsbD_and,Bool.and_eq_true] at h'
  exact ⟨(sign_spec _ _ _).mp h'.1.1,(sign_spec _ _ _).mp h'.1.2,(sign_spec _ _ _).mp h'.2⟩

def test1 (a : M) := decide (∀ x : Bool, four (signMask a x)=true)
def test2 (a b : M) := decide (∀ x y : Bool, two (signMask a x &&& signMask b y)=true)
def test3 (a b c : M) := decide (∀ x y z : Bool, one (signMask a x &&& signMask b y &&& signMask c z)=true)
def InjBits (a b c : M) := Function.Injective (fun i : Fin 8 => (rd a i,rd b i,rd c i))

theorem good1 {a b c : M} (h : InjBits a b c) : test1 a=true := by
  apply decide_eq_true
  intro x
  apply (counts _).2.2.mpr
  let T := hits (signMask a x)
  have inj : Function.Injective (fun i : (↥T) => (rd b i.val, rd c i.val)) := by
    intro i j eq
    apply Subtype.ext
    exact h (Prod.ext ((hit1 i.property).trans (hit1 j.property).symm) eq)
  have card := Fintype.card_le_of_injective _ inj
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_bool] using card

theorem good2 {a b c : M} (h : InjBits a b c) : test2 a b=true := by
  apply decide_eq_true
  intro x y
  apply (counts _).2.1.mpr
  let T := hits (signMask a x &&& signMask b y)
  have inj : Function.Injective (fun i : (↥T) => rd c i.val) := by
    intro i j eq
    obtain ⟨xi,yi⟩ := hit2 i.property
    obtain ⟨xj,yj⟩ := hit2 j.property
    apply Subtype.ext
    exact h (Prod.ext (xi.trans xj.symm) (Prod.ext (yi.trans yj.symm) eq))
  have card := Fintype.card_le_of_injective _ inj
  simpa only [Fintype.card_coe,Fintype.card_bool] using card

theorem good3 {a b c : M} (h : InjBits a b c) : test3 a b c=true := by
  apply decide_eq_true
  intro x y v
  apply (counts _).1.mpr
  apply Finset.card_le_one.mpr
  intro i hi j hj
  obtain ⟨xi,yi,vi⟩ := hit3 hi
  obtain ⟨xj,yj,vj⟩ := hit3 hj
  exact h (Prod.ext (xi.trans xj.symm) (Prod.ext (yi.trans yj.symm) (vi.trans vj.symm)))

def first : List M := [0x0f,0x39,0xc9,0xd2,0xe4]
theorem first_covers : ∀ a ∈ raw, test1 a=true → a ∈ first := by decide +kernel

def seconds (a b : M) := (opts [a &&& b]).filter (fun c => test2 a c && test2 b c)
def thirds (a b c d : M) := (opts [c &&& d,a &&& b]).filter (fun e =>
  test3 a c e && test3 a d e && test3 b c e && test3 b d e)

def lastCheck (a b c d : M) : Bool :=
  let es := thirds a b c d
  es.all (fun e => es.all (fun f => (a &&& b != 0) && (c &&& d != 0) && (e &&& f != 0)))

def midCheck (a b : M) : Bool :=
  let cs := seconds a b
  cs.all (fun c => cs.all (fun d => lastCheck a b c d))

def rootCheck (a : M) := first.all (midCheck a)


set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem root15 : rootCheck 15 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem root57 : rootCheck 57 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem root201 : rootCheck 201 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem root210 : rootCheck 210 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem root228 : rootCheck 228 = true := by decide +kernel

theorem roots {a : M} (ha : a ∈ first) : rootCheck a=true := by
  simp only [first,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · exact root15
  · exact root57
  · exact root201
  · exact root210
  · exact root228

theorem checked_masks {a b c d e f : M} (ha : a∈first) (hb : b∈first)
    (hc : c∈seconds a b) (hd : d∈seconds a b)
    (he : e∈thirds a b c d) (hf : f∈thirds a b c d) :
    (a &&& b) ≠ 0 ∧ (c &&& d) ≠ 0 ∧ (e &&& f) ≠ 0 := by
  have ch2 : midCheck a b=true := List.all_eq_true.mp (roots ha) b hb
  have ch3 : lastCheck a b c d=true := List.all_eq_true.mp (List.all_eq_true.mp ch2 c hc) d hd
  have last := List.all_eq_true.mp (List.all_eq_true.mp ch3 e he) f hf
  simpa only [Bool.and_eq_true,bne_iff_ne,and_assoc] using last

theorem three {g1 g2 g3 w : F} (hg : red_good [g3,g2,g1]) (hw : red_cl [g3,g2,g1] w)
    (correct : Correct w) : False := by
  obtain ⟨⟨e,f,he,hf,h3⟩,⟨⟨c,d,hc,hd,h2⟩,⟨⟨a,b,ha,hb,h1⟩,_⟩⟩⟩ := hg
  have form : circuitForm g1 g2 g3 a b c d e f w :=
    ⟨⟨ha,hb,h1⟩,⟨hc,hd,h2⟩,⟨he,hf,h3⟩,hw⟩
  have sep {u v t : F} (s1 : u=a ∨ u=b) (s2 : v=c ∨ v=d) (s3 : t=e ∨ t=f) :
      InjBits (mark u) (mark v) (mark t) := by
    unfold InjBits
    simpa only [mark_read] using codes form correct s1 s2 s3
  have hfa := first_covers (mark a) (cls0 ha) (good1 (sep (.inl rfl) (.inl rfl) (.inl rfl)))
  have hfb := first_covers (mark b) (cls0 hb) (good1 (sep (.inr rfl) (.inl rfl) (.inl rfl)))
  have sec {v : F} (hv : red_cl [g1] v) (s2 : v=c ∨ v=d) :
      mark v ∈ seconds (mark a) (mark b) := by
    apply List.mem_filter.mpr
    constructor
    · simpa only [← mark_and h1] using cls1 hv
    · simp only [Bool.and_eq_true]
      exact ⟨good2 (sep (.inl rfl) s2 (.inl rfl)),good2 (sep (.inr rfl) s2 (.inl rfl))⟩
  have third {t : F} (ht : red_cl [g2,g1] t) (s3 : t=e ∨ t=f) :
      mark t ∈ thirds (mark a) (mark b) (mark c) (mark d) := by
    apply List.mem_filter.mpr
    constructor
    · simpa only [← mark_and h1, ← mark_and h2] using cls2 ht
    · simp only [Bool.and_eq_true]
      exact ⟨⟨⟨good3 (sep (.inl rfl) (.inl rfl) s3),good3 (sep (.inl rfl) (.inr rfl) s3)⟩,
        good3 (sep (.inr rfl) (.inl rfl) s3)⟩,good3 (sep (.inr rfl) (.inr rfl) s3)⟩
  have n := checked_masks hfa hfb (sec hc (.inl rfl)) (sec hd (.inr rfl))
    (third he (.inl rfl)) (third hf (.inr rfl))
  rw [← mark_and h1,← mark_and h2,← mark_and h3] at n
  rcases needs_zero hw correct with hz | hz | hz
  · exact n.1 hz
  · exact n.2.1 hz
  · exact n.2.2 hz

theorem finish {G : List F} (good : red_good G) (small : G.length≤3) {w : F}
    (out : red_cl G w) (actual : Correct w) : False := by
  rcases G with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d,tail⟩⟩⟩⟩
  · exact three (red_pad (red_pad (red_pad good))) (red_cl_mono _ (red_cl_mono _ (red_cl_mono _ out))) actual
  · exact three (red_pad (red_pad good)) (red_cl_mono _ (red_cl_mono _ out)) actual
  · exact three (red_pad good) (red_cl_mono _ out) actual
  · exact three good out actual
  · simp only [List.length_cons] at small
    omega

theorem result (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C) (A : Finset ℕ) (hsize : A.card≤3)
    (hgate : ∀ j (g : Gate), C.gates[j]?=some g → g.op=GateOp.and → j∈A)
    (corr : ∀ x : Input, C.eval (List.ofFn x)=true ↔ edge x) : False := by
  obtain ⟨G,hG,sz,available⟩ := red_inv A C.gates
    (fun g hg => ⟨by simpa using (hm g hg).1,(hm g hg).2⟩) hgate
  have small : G.length≤3 := sz.trans ((Finset.card_le_card (Finset.filter_subset _ _)).trans hsize)
  exact finish hG small (available C.output) corr


end PEqualNP.Outside.L_meta_282_aux

open PEqualNP.Outside.L_meta_282_aux in
theorem PEqualNP.Outside.L_meta_282 : ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, (PEqualNP.MetaComplexity.Monotone2 C ∧ (∃ A : Finset ℕ, A.card ≤ 3 ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A)) ∧ (∀ x : Fin 6 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5), (2, 3)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  rintro ⟨C,⟨hm,A,hsize,hgate⟩,correct⟩
  exact result C hm A hsize hgate correct
