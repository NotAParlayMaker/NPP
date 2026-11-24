import Cert

-- GLUE-BEGIN
-- New for this step: the two given wires are put back as the first two gates of a
-- circuit on the nine inputs. The second wire repeats an input, repeats the negated
-- input 0, or is constant, so a derivation reads only inputs and the negation of
-- input 0. If it reads that negation and input 0, pinning input 0 to false loses two
-- gates, against the checked bound for the graph without vertex 0. If it reads the
-- negation and not input 0, one more gate rebuilds the negation from input 0. Either
-- way the checked frontier certificate for fourteen gates excludes it.
namespace PEqualNP.Outside.L_meta_3116
namespace Glue
open PEqualNP.CircuitLowerBounds Main1672

def gN : Gate := ⟨.not, [0]⟩
def gC (a : Nat) : Gate := if a = 11 then ⟨.and, []⟩ else ⟨.and, [a]⟩
def sN : Sig := neg raw0
def sC (a : Nat) : Sig := gv (raw ++ [sN]) (gC a)
def cases9 : List Nat := [0, 1, 2, 3, 4, 6, 9, 10, 11]

lemma gvN : gv raw gN = sN := by decide +kernel
lemma raw0_ne_sN : raw0 ≠ sN := by decide +kernel
lemma raw0_proper : proper raw0 :=
  ⟨raw_valid raw0 (by simp [raw]), by decide +kernel, by decide +kernel⟩
lemma sC_kind : ∀ a ∈ cases9, sC a = zero ∨ sC a = one ∨ sC a ∈ raw ∨ sC a = sN := by
  decide +kernel

lemma valid_raw0 : Valid raw0 := raw_valid raw0 (by simp [raw])
lemma valid_sN : Valid sN := valid_neg valid_raw0

lemma gC_legal (a : Nat) :
    (gC a).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ (gC a).inputs.length ≤ 2 := by
  unfold gC
  split <;> simp

def extend (a : Nat) (C : Circuit) : Circuit := ⟨gN :: gC a :: C.gates, C.output⟩

lemma extend_fan (a : Nat) (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C) :
    PEqualNP.MetaComplexity.FanInTwo (extend a C) := by
  intro g hg
  simp only [extend, List.mem_cons] at hg
  rcases hg with rfl | rfl | hg
  · exact ⟨by simp [gN], by simp [gN]⟩
  · exact gC_legal a
  · exact h g hg

lemma extend_eval (a : Nat) (C : Circuit) (x : Fin 9 → Bool) :
    (extend a C).eval (List.ofFn x) =
      C.eval (List.ofFn x ++ [!x 0] ++
        [(gC a).op.eval ((gC a).inputs.map fun i => (List.ofFn x ++ [!x 0]).getD i false)]) := by
  have h1 : gN.op.eval (gN.inputs.map fun i => (List.ofFn x).getD i false) = !x 0 := by
    simp [gN, GateOp.eval, List.getD_eq_getElem?_getD]
  change ((C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    ((List.ofFn x ++ [gN.op.eval (gN.inputs.map fun i => (List.ofFn x).getD i false)]) ++
      [(gC a).op.eval ((gC a).inputs.map fun i =>
        (List.ofFn x ++ [gN.op.eval (gN.inputs.map fun i => (List.ofFn x).getD i false)]).getD
          i false)])).getD C.output false) = _
  rw [h1]
  rfl

def wiresW (a : Nat) : List Sig := raw ++ [sN] ++ [sC a]

lemma target_mem (a : Nat) (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0] ++
        [(gC a).op.eval ((gC a).inputs.map fun i => (List.ofFn x ++ [!x 0]).getD i false)])
      = edgeF x) :
    target ∈ execute C.gates (wiresW a) := by
  have h := circuit_target (extend a C) (extend_fan a C hf)
    (fun x => (extend_eval a C x).trans (he x))
  change target ∈ execute C.gates ((raw ++ [gv raw gN]) ++ [gv (raw ++ [gv raw gN]) (gC a)]) at h
  rw [gvN] at h
  exact h

lemma proj_raw0 : (homProject 0).fn raw0 = zero := project_raw_zero 0
lemma proj_sN : (homProject 0).fn sN = one := by
  change (homProject 0).fn (neg raw0) = one
  rw [(homProject 0).hneg valid_raw0, proj_raw0]
  exact neg_laws.1

lemma core (a : Nat) (ha : a ∈ cases9) (C : Circuit)
    (hf : PEqualNP.MetaComplexity.FanInTwo C) (hle : C.gates.length ≤ 13)
    (htgt : target ∈ execute C.gates (wiresW a)) : False := by
  have hvW : ∀ s ∈ wiresW a, Valid s := by
    intro s hs
    simp only [wiresW, List.mem_append, List.mem_singleton] at hs
    rcases hs with (hs | rfl) | rfl
    · exact raw_valid s hs
    · exact valid_sN
    · exact gv_valid (fun s hs => by
        rcases List.mem_append.mp hs with hs | hs
        · exact raw_valid s hs
        · simp only [List.mem_singleton] at hs; subst s; exact valid_sN) (gC a)
  obtain ⟨k, t, S, hk, hlive, hsub⟩ :=
    extract C.gates (wiresW a) hvW (fun g hg => hf g hg) htgt
  have hk13 : k ≤ 13 := hk.trans hle
  have hmem : ∀ s ∈ S, s ∈ raw ∨ s = sN := by
    intro s hs
    have hp := live_proper hlive s hs
    have h := hsub s hs
    simp only [wiresW, List.mem_append, List.mem_singleton] at h
    rcases h with (h | h) | h
    · exact Or.inl h
    · exact Or.inr h
    · rcases sC_kind a ha with h0 | h1 | hr | hn
      · exact (hp.2.1 (h.trans h0)).elim
      · exact (hp.2.2 (h.trans h1)).elim
      · exact Or.inl (h ▸ hr)
      · exact Or.inr (h.trans hn)
  have finish : ∀ {k' t' : Nat} {S' : Finset Sig}, Live k' t' S' → k' ≤ 14 →
      (∀ s ∈ S', s ∈ raw) → False := by
    intro k' t' S' hl hk' hs
    have heq := necessary hl hs
    subst S'
    have sz := live_size hl
    rw [List.toFinset_card_of_nodup raw_nd] at sz
    have hlenRaw : raw.length = 9 := rfl
    exact rootImpossible t' (by omega) k' hk' raw.toFinset rootTag rootWires_rep
      (restrict_live hl (rootTag_ok hk'))
  by_cases hn : sN ∈ S
  · by_cases h0 : raw0 ∈ S
    · obtain ⟨q, hq, m, hm, t2, T, hl, hs⟩ := feasible_two_consts hlive (homProject 0) raw0 sN h0 hn
        raw0_ne_sN (fun hp => hp.2.1 proj_raw0) (fun hp => hp.2.2 proj_sN)
      refine root_project_deg3 0 (by decide) ⟨m, by omega, t2, T, hl, ?_⟩
      intro x hx
      obtain ⟨s, hsS, rfl⟩ := Finset.mem_image.mp (hs hx)
      have hp := live_proper hl _ hx
      rcases hmem s hsS with h | rfl
      · exact Finset.mem_image_of_mem _ (List.mem_toFinset.mpr h)
      · exact (hp.2.2 proj_sN).elim
    · have hS : insert (neg raw0) (S.erase sN) = S := Finset.insert_erase hn
      have hfresh : neg raw0 ∉ insert raw0 (S.erase sN) := by
        intro hx
        rcases Finset.mem_insert.mp hx with hx | hx
        · exact raw0_ne_sN hx.symm
        · exact (Finset.mem_erase.mp hx).1 rfl
      have hl2 : Live (k + 1) (t + 1) (insert raw0 (S.erase sN)) :=
        Live.unary raw0_proper hfresh (hS.symm ▸ hlive)
      refine finish hl2 (by omega) ?_
      intro s hs
      rcases Finset.mem_insert.mp hs with rfl | hs
      · simp [raw]
      · obtain ⟨hne, hsS⟩ := Finset.mem_erase.mp hs
        exact (hmem s hsS).resolve_right hne
  · refine finish hlive (by omega) ?_
    intro s hs
    rcases hmem s hs with h | rfl
    · exact h
    · exact (hn hs).elim

lemma main : ∀ x1 ∈ [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (9, 9), (10, 10),
      ((11 : Fin 12), (11 : Fin 12))],
    ∀ C : Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
    ∃ x : Fin 9 → Bool,
      C.eval ((List.ofFn x ++ [!x 0]) ++
        [((fun j : Fin 12 => if j = 11 then true else (List.ofFn x ++ [!x 0]).getD (↑j) false) x1.1 &&
          (fun j : Fin 12 => if j = 11 then true else (List.ofFn x ++ [!x 0]).getD (↑j) false) x1.2)])
        ≠ edgeF x := by
  intro x1 hx1 C hf hsize
  by_contra hne
  push_neg at hne
  have key : ∀ a ∈ cases9, (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0] ++
        [(gC a).op.eval ((gC a).inputs.map fun i => (List.ofFn x ++ [!x 0]).getD i false)])
      = edgeF x) → False :=
    fun a ha he => core a ha C hf hsize (target_mem a C hf he)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx1
  rcases hx1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine key 0 (by decide) (fun x => ?_)
    simpa [gC, GateOp.eval, List.getD_eq_getElem?_getD] using hne x
  · refine key 1 (by decide) (fun x => ?_)
    simpa [gC, GateOp.eval, List.getD_eq_getElem?_getD] using hne x
  · refine key 2 (by decide) (fun x => ?_)
    simpa [gC, GateOp.eval, List.getD_eq_getElem?_getD] using hne x
  · refine key 3 (by decide) (fun x => ?_)
    simpa [gC, GateOp.eval, List.getD_eq_getElem?_getD] using hne x
  · refine key 4 (by decide) (fun x => ?_)
    simpa [gC, GateOp.eval, List.getD_eq_getElem?_getD] using hne x
  · refine key 6 (by decide) (fun x => ?_)
    simpa [gC, GateOp.eval, List.getD_eq_getElem?_getD] using hne x
  · refine key 9 (by decide) (fun x => ?_)
    simpa [gC, GateOp.eval, List.getD_eq_getElem?_getD] using hne x
  · refine key 10 (by decide) (fun x => ?_)
    simpa [gC, GateOp.eval, List.getD_eq_getElem?_getD] using hne x
  · refine key 11 (by decide) (fun x => ?_)
    simpa [gC, GateOp.eval, List.getD_eq_getElem?_getD] using hne x

end Glue
end PEqualNP.Outside.L_meta_3116

theorem PEqualNP.Outside.L_meta_3116 : ∀ x1 ∈ [((0 : Fin (12 : ℕ)), (0 : Fin (12 : ℕ))), ((1 : Fin (12 : ℕ)), (1 : Fin (12 : ℕ))), ((2 : Fin (12 : ℕ)), (2 : Fin (12 : ℕ))), ((3 : Fin (12 : ℕ)), (3 : Fin (12 : ℕ))), ((4 : Fin (12 : ℕ)), (4 : Fin (12 : ℕ))), ((6 : Fin (12 : ℕ)), (6 : Fin (12 : ℕ))), ((9 : Fin (12 : ℕ)), (9 : Fin (12 : ℕ))), ((10 : Fin (12 : ℕ)), (10 : Fin (12 : ℕ))), ((11 : Fin (12 : ℕ)), (11 : Fin (12 : ℕ)))],   ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size ≤ (13 : ℕ) →         ∃ (x6 : Fin (9 : ℕ) → Bool),           have x7 : List Bool := List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))];           have x8 : Fin (12 : ℕ) → Bool := fun (x8 : Fin (12 : ℕ)) => if x8 = (11 : Fin (12 : ℕ)) then Bool.true else x7.getD (↑x8) Bool.false;           x3.eval (x7 ++ [x8 x1.1 && x8 x1.2]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) :=
  PEqualNP.Outside.L_meta_3116.Glue.main
