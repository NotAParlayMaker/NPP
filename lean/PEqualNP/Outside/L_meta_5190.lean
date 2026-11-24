import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.List.Forall2
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5190_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership

-- The wire monotonicity argument follows L_meta_3008.
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_le {w v : List Bool} (h : List.Forall₂ (fun a b => a ≤ b) w v) (i : ℕ) :
    w.getD i false ≤ v.getD i false := by
  induction h generalizing i with
  | nil => simp
  | cons hab _ ih =>
    cases i with
    | zero => simpa using hab
    | succ i => simpa using ih i

theorem bool_le {a b : Bool} : a ≤ b ↔ (a = true → b = true) := by
  cases a <;> cases b <;> decide

theorem gate_le (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) {w v : List Bool}
    (h : List.Forall₂ (fun a b => a ≤ b) w v) :
    g.op.eval (g.inputs.map fun i => w.getD i false) ≤
      g.op.eval (g.inputs.map fun i => v.getD i false) := by
  rw [bool_le]
  rcases hg with hg | hg
  · rw [hg]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro hx x hx2
    obtain ⟨i, hi, rfl⟩ := hx2
    exact bool_le.mp (getD_le h i) (hx _ ⟨i, hi, rfl⟩)
  · rw [hg]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨_, ⟨i, hi, rfl⟩, bool_le.mp (getD_le h i) hx⟩

theorem fold_le (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ w v : List Bool, List.Forall₂ (fun a b => a ≤ b) w v →
      List.Forall₂ (fun a b => a ≤ b) (gs.foldl step w) (gs.foldl step v) := by
  induction gs with
  | nil => intro w v h; simpa using h
  | cons g gs ih =>
    intro w v h
    simp only [List.foldl_cons]
    apply ih (fun g2 hg2 => hgs g2 (List.mem_cons_of_mem _ hg2))
    exact List.rel_append h (List.Forall₂.cons (gate_le g (hgs g List.mem_cons_self) h) List.Forall₂.nil)

theorem mono (n : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) (o : ℕ) :
    (gs.foldl step (List.ofFn x)).getD o false ≤ (gs.foldl step (List.ofFn y)).getD o false := by
  have h0 : List.Forall₂ (fun a b => a ≤ b) (List.ofFn x) (List.ofFn y) := by
    rw [List.forall₂_iff_get]
    refine ⟨by simp only [List.length_ofFn], fun i h1 h2 => ?_⟩
    simp only [List.get_eq_getElem, List.getElem_ofFn]
    exact bool_le.mpr (hxy _)
  exact getD_le (fold_le gs hgs _ _ h0) o



private theorem manyNonneighbors {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (degree : ∀ v, G.degree v = 0 ∨ 3 ≤ G.degree v)
    (girth : ∀ v (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) (v : Fin n) :
    n ≤ 2 * ((G.neighborFinset v)ᶜ).card := by
  classical
  have triangle (a b c : Fin n) (ab : G.Adj a b) (bc : G.Adj b c) : ¬G.Adj c a := by
    intro ca
    let W : G.Walk a a := .cons ab (.cons bc (.cons ca .nil))
    have cycle : W.IsCycle := by
      refine SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨?_, by simp [W]⟩
      simp only [W, SimpleGraph.Walk.tail_cons]
      simp [ab.ne.symm,bc.ne,ca.ne]
    have h := girth _ W cycle
    have len : W.length = 3 := rfl
    omega
  -- The four-cycle witness uses the path-tail argument from L_meta_1762.
  have square (a b c d : Fin n) (ac : a ≠ c) (bd : b ≠ d)
      (ab : G.Adj a b) (bc : G.Adj b c) (cd : G.Adj c d) : ¬G.Adj d a := by
    intro da
    let W : G.Walk a a := .cons ab (.cons bc (.cons cd (.cons da .nil)))
    have cycle : W.IsCycle := by
      refine SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨?_, by simp [W]⟩
      simp only [W, SimpleGraph.Walk.tail_cons]
      simp [ab.ne.symm,bc.ne,cd.ne,da.ne,ac.symm,bd]
    have h := girth _ W cycle
    have len : W.length = 4 := rfl
    omega
  have next (b : Fin n) (hb : b ∈ G.neighborFinset v) :
      ∃ c, G.Adj b c ∧ c ≠ v := by
    have adj := (G.mem_neighborFinset v b).mp hb
    have positive : 0 < (G.neighborFinset b).card := Finset.card_pos.mpr
      ⟨v,(G.mem_neighborFinset b v).mpr adj.symm⟩
    have two : 1 < (G.neighborFinset b).card := by
      rw [G.card_neighborFinset_eq_degree] at positive ⊢
      rcases degree b with h|h <;> omega
    obtain ⟨c,hc,ne⟩ := Finset.exists_mem_ne two v
    exact ⟨c,(G.mem_neighborFinset b c).mp hc,ne⟩
  let f := fun b => if h : b ∈ G.neighborFinset v then (next b h).choose else v
  have spec (b) (h : b ∈ G.neighborFinset v) : G.Adj b (f b) ∧ f b ≠ v := by
    simpa only [f,dif_pos h] using (next b h).choose_spec
  have injection : (G.neighborFinset v).card ≤ ((G.neighborFinset v)ᶜ).card := by
    apply Finset.card_le_card_of_injOn f
    · intro b hb
      apply Finset.mem_compl.mpr
      intro hm
      exact triangle v b (f b) ((G.mem_neighborFinset v b).mp hb) (spec b hb).1
        ((G.mem_neighborFinset v _).mp hm).symm
    · intro b hb d hd same
      by_contra different
      have last : G.Adj (f b) d := by rw [same]; exact (spec d hd).1.symm
      exact square v b (f b) d (spec b hb).2.symm different
        ((G.mem_neighborFinset v b).mp hb) (spec b hb).1 last ((G.mem_neighborFinset v d).mp hd).symm
  have total := Finset.card_add_card_compl (G.neighborFinset v)
  rw [Fintype.card_fin] at total
  omega

end PEqualNP.Outside.L_meta_5190_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_5190_aux in
theorem PEqualNP.Outside.L_meta_5190 : ∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj],   (2 : ℕ) * x1 + (1 : ℕ) ≤ x2 →     (∀ (x6 : Fin x2), x3.degree x6 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x6) →       (∀ (x7 : Fin x2) (x8 : x3.Walk x7 x7), x8.IsCycle → (5 : ℕ) ≤ x8.length) →         ∀ (x8 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.Monotone2 x8 →             ∀ (x10 x11 : Fin x2) (x12 : Fin x8.gates.length),               x3.Adj x10 x11 →                 have x14 : Fin x2 → Fin x2 → Prop := fun (x14 x15 : Fin x2) => PEqualNP.EdgeOwnership.gateVal x2 x8 (↑x12) (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true;                 have x15 : Fin x2 × Fin x2 → Finset (Fin x2) := fun (x15 : Fin x2 × Fin x2) => {x15.1, x15.2} \ {x10, x11};                 x14 x10 x10 ∨ x14 x11 x11 → ∃ (x17 : Finset (Fin x2 × Fin x2)), x17.card = x1 ∧ (∀ x18 ∈ x17, x14 x18.1 x18.2 ∧ ¬x3.Adj x18.1 x18.2) ∧ ∀ x18 ∈ x17, ∀ x20 ∈ x17, x18 ≠ x20 → Disjoint (x15 x18) (x15 x20) := by
  classical
  intro k n G inst size degree girth C hC u v j _
  dsimp only
  intro singleton
  let active := fun (a b : Fin n) => gateVal n C j.val (pairInput a b) = true
  change active u u ∨ active v v at singleton
  obtain ⟨c,hc,hit⟩ : ∃ c ∈ ({u,v} : Finset (Fin n)), active c c := by
    rcases singleton with hu|hv
    · exact ⟨u,by simp,hu⟩
    · exact ⟨v,by simp,hv⟩
  have extend (b : Fin n) : active c b := by
    have le := mono n C.gates (fun g hg => (hC g hg).1) (pairInput c c) (pairInput c b)
      (fun i h => by simpa [pairInput] using (Or.inl (by simpa [pairInput] using h) : i = c ∨ i = b))
      (n+j.val)
    exact bool_le.mp le hit
  have bound := manyNonneighbors G degree girth c
  obtain ⟨T,sub,card⟩ := Finset.exists_subset_card_eq
    (s := (G.neighborFinset c)ᶜ) (show k ≤ ((G.neighborFinset c)ᶜ).card by omega)
  let emb : Fin n ↪ Fin n × Fin n := ⟨fun b => (c,b), fun _ _ h => congrArg Prod.snd h⟩
  refine ⟨T.map emb,by simpa using card,?_,?_⟩
  · intro e he
    obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp he
    exact ⟨extend b,fun adj => (Finset.mem_compl.mp (sub hb)) ((G.mem_neighborFinset c b).mpr adj)⟩
  · intro e he e' he' ne
    obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp he
    obtain ⟨d,hd,rfl⟩ := Finset.mem_map.mp he'
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    have h1 : x = c ∨ x = b := Finset.mem_insert.mp (Finset.mem_sdiff.mp hx).1 |>.imp_right Finset.mem_singleton.mp
    have h2 : x = c ∨ x = d := Finset.mem_insert.mp (Finset.mem_sdiff.mp hx').1 |>.imp_right Finset.mem_singleton.mp
    have outside := (Finset.mem_sdiff.mp hx).2
    rcases h1 with rfl|rfl
    · exact outside hc
    · rcases h2 with eq|eq
      · exact outside (eq ▸ hc)
      · exact ne (congrArg emb eq)
