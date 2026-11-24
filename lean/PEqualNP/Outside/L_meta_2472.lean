import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2472

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

def rcell (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List ℕ) :=
  match g.op with
  | GateOp.or => (g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => (g.inputs.map fun i => R.getD i []).foldl (andStep k) [S.map fun _ => 0]
  | _ => []

def rf (S : List ℕ) (k : ℕ) (gs : List Gate) (R : List (List (List ℕ))) :
    List (List (List ℕ)) :=
  gs.foldl (fun R g => R ++ [rcell S k R g]) R

lemma rv_eq (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    readVectors C n S k = rf S k C.gates ((List.range n).map (leafVectors S k)) := rfl

lemma mem_insertNew (A : List (List ℕ)) (v x : List ℕ) :
    x ∈ insertNew A v ↔ x ∈ A ∨ x = v := by
  unfold insertNew
  split_ifs with h
  · constructor
    · exact Or.inl
    · rintro (h1 | rfl)
      · exact h1
      · exact h
  · simp

lemma mem_foldl_insertNew (L : List (List ℕ)) :
    ∀ (acc : List (List ℕ)) (x : List ℕ), x ∈ L.foldl insertNew acc ↔ x ∈ acc ∨ x ∈ L := by
  induction L with
  | nil => intro acc x; simp
  | cons v L ih =>
    intro acc x
    rw [List.foldl_cons, ih, mem_insertNew]
    simp [or_assoc]

lemma mem_andStep (k : ℕ) (A B : List (List ℕ)) (x : List ℕ) :
    x ∈ andStep k A B ↔ ∃ p ∈ A, ∃ q ∈ B, capAdd k p q = x := by
  unfold andStep
  rw [mem_foldl_insertNew]
  simp [List.mem_flatMap, List.mem_map]

lemma mem_orFold (ins : List (List (List ℕ))) :
    ∀ (acc : List (List ℕ)) (x : List ℕ),
      x ∈ ins.foldl (fun acc A => A.foldl insertNew acc) acc ↔ x ∈ acc ∨ ∃ A ∈ ins, x ∈ A := by
  induction ins with
  | nil => intro acc x; simp
  | cons A ins ih =>
    intro acc x
    rw [List.foldl_cons, ih, mem_foldl_insertNew]
    simp [or_assoc]

def mm (a : ℕ) : ℕ := min a 2

def Rel (A B : List (List ℕ)) : Prop := ∀ v ∈ A, ∃ v2 ∈ B, v = v2.map mm

lemma rel_nil (B : List (List ℕ)) : Rel [] B := by
  intro v hv
  simp at hv

lemma capAdd_min : ∀ p q : List ℕ,
    capAdd 1 (p.map mm) (q.map mm) = (capAdd 2 p q).map mm := by
  intro p
  induction p with
  | nil => intro q; simp [capAdd]
  | cons a p ih =>
    intro q
    cases q with
    | nil => simp [capAdd]
    | cons b q =>
      have h := ih q
      simp only [capAdd, List.map_cons, List.zipWith_cons_cons] at h ⊢
      rw [h]
      congr 1
      unfold mm
      omega

lemma andStep_rel (A1 A2 B1 B2 : List (List ℕ)) (hA : Rel A1 A2) (hB : Rel B1 B2) :
    Rel (andStep 1 A1 B1) (andStep 2 A2 B2) := by
  intro v hv
  obtain ⟨p, hp, q, hq, rfl⟩ := (mem_andStep 1 A1 B1 v).mp hv
  obtain ⟨p2, hp2, rfl⟩ := hA p hp
  obtain ⟨q2, hq2, rfl⟩ := hB q hq
  exact ⟨capAdd 2 p2 q2, (mem_andStep 2 A2 B2 _).mpr ⟨p2, hp2, q2, hq2, rfl⟩, capAdd_min p2 q2⟩

lemma rel_getD (R1 R2 : List (List (List ℕ))) (h : List.Forall₂ Rel R1 R2) :
    ∀ i, Rel (R1.getD i []) (R2.getD i []) := by
  induction h with
  | nil => intro i; simpa using rel_nil []
  | cons hab _ ih =>
    intro i
    cases i with
    | zero => simpa using hab
    | succ i => simpa using ih i

lemma f2_snoc (R1 R2 : List (List (List ℕ))) (c1 c2 : List (List ℕ))
    (h : List.Forall₂ Rel R1 R2) (hc : Rel c1 c2) :
    List.Forall₂ Rel (R1 ++ [c1]) (R2 ++ [c2]) := by
  induction h with
  | nil => exact List.Forall₂.cons hc List.Forall₂.nil
  | cons hab _ ih => exact List.Forall₂.cons hab ih

lemma or_rel (R1 R2 : List (List (List ℕ))) (hg : ∀ i, Rel (R1.getD i []) (R2.getD i []))
    (L : List ℕ) :
    Rel ((L.map fun i => R1.getD i []).foldl (fun acc A => A.foldl insertNew acc) [])
      ((L.map fun i => R2.getD i []).foldl (fun acc A => A.foldl insertNew acc) []) := by
  intro v hv
  rcases (mem_orFold _ _ _).mp hv with h0 | ⟨A, hA, hvA⟩
  · simp at h0
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hA
    obtain ⟨v2, hv2, e⟩ := hg i v hvA
    exact ⟨v2, (mem_orFold _ _ _).mpr (Or.inr ⟨_, List.mem_map.mpr ⟨i, hi, rfl⟩, hv2⟩), e⟩

lemma and_rel (R1 R2 : List (List (List ℕ))) (hg : ∀ i, Rel (R1.getD i []) (R2.getD i []))
    (L : List ℕ) : ∀ acc1 acc2 : List (List ℕ), Rel acc1 acc2 →
    Rel ((L.map fun i => R1.getD i []).foldl (andStep 1) acc1)
      ((L.map fun i => R2.getD i []).foldl (andStep 2) acc2) := by
  induction L with
  | nil => intro acc1 acc2 h; simpa using h
  | cons i L ih =>
    intro acc1 acc2 h
    simp only [List.map_cons, List.foldl_cons]
    exact ih _ _ (andStep_rel _ _ _ _ h (hg i))

lemma zero_rel (S : List ℕ) : Rel [S.map fun _ => 0] [S.map fun _ => 0] := by
  intro v hv
  rw [List.mem_singleton] at hv
  refine ⟨S.map fun _ => 0, List.mem_singleton.mpr rfl, ?_⟩
  rw [hv, List.map_map]
  apply List.map_congr_left
  intro j _
  simp [mm]

lemma cell_rel (S : List ℕ) (R1 R2 : List (List (List ℕ))) (g : Gate)
    (h : List.Forall₂ Rel R1 R2) : Rel (rcell S 1 R1 g) (rcell S 2 R2 g) := by
  have hg := rel_getD R1 R2 h
  unfold rcell
  cases g.op <;>
    first
    | exact or_rel R1 R2 hg g.inputs
    | exact and_rel R1 R2 hg g.inputs _ _ (zero_rel S)
    | exact rel_nil _

lemma fold_rel (S : List ℕ) (gs : List Gate) : ∀ R1 R2 : List (List (List ℕ)),
    List.Forall₂ Rel R1 R2 → List.Forall₂ Rel (rf S 1 gs R1) (rf S 2 gs R2) := by
  induction gs with
  | nil => intro R1 R2 h; exact h
  | cons g gs ih =>
    intro R1 R2 h
    show List.Forall₂ Rel (rf S 1 gs (R1 ++ [rcell S 1 R1 g])) (rf S 2 gs (R2 ++ [rcell S 2 R2 g]))
    exact ih _ _ (f2_snoc R1 R2 _ _ h (cell_rel S R1 R2 g h))

lemma leaf_rel (S : List ℕ) (i : ℕ) : Rel (leafVectors S 1 i) (leafVectors S 2 i) := by
  intro v hv
  unfold leafVectors at hv ⊢
  by_cases h : i ∈ S
  · rw [if_pos h] at hv ⊢
    rw [List.mem_singleton] at hv
    refine ⟨_, List.mem_singleton.mpr rfl, ?_⟩
    rw [hv, List.map_map]
    apply List.map_congr_left
    intro j _
    by_cases e : j = i <;> simp [e, mm]
  · rw [if_neg h] at hv
    simp at hv

lemma ini_rel (S : List ℕ) (L : List ℕ) :
    List.Forall₂ Rel (L.map (leafVectors S 1)) (L.map (leafVectors S 2)) := by
  induction L with
  | nil => exact List.Forall₂.nil
  | cons i L ih => exact List.Forall₂.cons (leaf_rel S i) ih

lemma main (C : Circuit) (n : ℕ) (S : List ℕ) :
    List.Forall₂ Rel (readVectors C n S 1) (readVectors C n S 2) := by
  rw [rv_eq, rv_eq]
  exact fold_rel S C.gates _ _ (ini_rel S (List.range n))

end PEqualNP.Outside.L_meta_2472

theorem PEqualNP.Outside.L_meta_2472 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (u w : ℕ), PEqualNP.ReadK.readsAtMost C n [u, w] 1 = true → ((PEqualNP.ReadK.readVectors C n [u, w] 2).getD C.output []).any (fun v_1 => decide (v_1.getD 0 0 ≤ 1 ∧ v_1.getD 1 0 ≤ 1)) = true := by
  intro n C u w hr
  unfold PEqualNP.ReadK.readsAtMost at hr
  rw [List.any_eq_true] at hr ⊢
  obtain ⟨v, hv, hall⟩ := hr
  obtain ⟨v2, hv2, rfl⟩ := PEqualNP.Outside.L_meta_2472.rel_getD _ _
    (PEqualNP.Outside.L_meta_2472.main C n [u, w]) C.output v hv
  rw [List.all_eq_true] at hall
  have key : ∀ i, v2.getD i 0 ≤ 1 := by
    intro i
    by_cases hi : i < v2.length
    · have h2 := hall (PEqualNP.Outside.L_meta_2472.mm v2[i])
        (List.mem_map.mpr ⟨v2[i], List.getElem_mem hi, rfl⟩)
      have h3 : PEqualNP.Outside.L_meta_2472.mm v2[i] ≤ 1 := by simpa using h2
      have h4 : v2.getD i 0 = v2[i] := by simp [List.getD_eq_getElem?_getD, hi]
      rw [h4]
      unfold PEqualNP.Outside.L_meta_2472.mm at h3
      omega
    · rw [List.getD_eq_default _ _ (by omega)]
      omega
  exact ⟨v2, hv2, decide_eq_true ⟨key 0, key 1⟩⟩
