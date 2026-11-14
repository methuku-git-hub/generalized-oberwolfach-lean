module

public import Oberwolfach.FactorLongShortClassification

@[expose] public section
/-! The initial class assignment: long factors first, otherwise the least
abundant short length. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def factorShortCandidates {n:ℕ} (F:SimpleGraph (Fin n)) (K:ℕ):Finset (Fin K):=
  Finset.univ.filter (fun i=>(1/(2*(K:ℝ)):ℝ)≤
    ((Finset.univ.filter (fun v=>Fintype.card (F.connectedComponentMk v)=i.val+1)).card:ℝ)/n)

def factorPreparationClass {n:ℕ} (F:SimpleGraph (Fin n)) (K:ℕ):Option (Fin K):=
  if (1/2:ℝ)≤((Finset.univ.filter (fun v=>K<Fintype.card (F.connectedComponentMk v))).card:ℝ)/n then none
  else if h:(factorShortCandidates F K).Nonempty then some ((factorShortCandidates F K).min' h) else none

theorem factor_preparation_class {n:ℕ} (hn:0<n)
    (F:SimpleGraph (Fin n)) (hF:F.IsRegularOfDegree 2) (S:Set ℕ)
    (hS:AllowedCycleLengths F S) (K:ℕ) (hK:0<K):
    (factorPreparationClass F K=none ↔
      (1/2:ℝ)≤((Finset.univ.filter (fun v=>K<Fintype.card (F.connectedComponentMk v))).card:ℝ)/n) ∧
    ∀ i, factorPreparationClass F K=some i→
      (3 : ℕ) ≤ (i.val + 1) ∧ i.val+1∈S ∧ i∈factorShortCandidates F K ∧
      ∀ j∈factorShortCandidates F K,i ≤ j:=by
  have H:=factor_long_or_abundant_short hn F hF S hS K hK
  unfold factorPreparationClass
  split_ifs with hl hc
  · constructor
    · exact ⟨fun _=>hl,fun _=>rfl⟩
    · intro i hi
      cases hi
  · let i:Fin K:=(factorShortCandidates F K).min' hc
    have hi:i∈factorShortCandidates F K:=Finset.min'_mem _ hc
    have hmin:∀ j∈factorShortCandidates F K,i ≤ j:=fun j hj=>Finset.min'_le _ _ hj
    have hf:(1/(2*(K:ℝ)):ℝ)≤
      ((Finset.univ.filter (fun v=>Fintype.card (F.connectedComponentMk v)=i.val+1)).card:ℝ)/n:=
        (Finset.mem_filter.mp hi).2
    have hshort:(Finset.univ.filter (fun v=>longPreparationCycleClass F hF K v=some i))=
      (Finset.univ.filter (fun v=>Fintype.card (F.connectedComponentMk v)=i.val+1)):=by
      apply Finset.filter_congr
      intro v _
      exact (long_preparation_cycle_class F hF K v).2 i
    have heq:(50:ℝ)/(100*(K:ℝ))=1/(2*(K:ℝ)):=by field_simp;norm_num
    have ht:(50:ℝ)/(100*(K:ℝ))≤
      ((Finset.univ.filter (fun v=>longPreparationCycleClass F hF K v=some i)).card:ℝ)/n:=by
      rw [heq,hshort]
      exact hf
    have hh:=long_preparation_retained_length_allowed hn F hF S hS K hK 50 (by norm_num) i ht
    constructor
    · constructor
      · intro h
        cases h
      · intro h
        exact False.elim (hl h)
    · intro j hj
      have hji:j=i:=Option.some.inj hj |>.symm
      subst j
      exact ⟨hh.1,hh.2.1,hi,hmin⟩
  · exfalso
    rcases H with h | ⟨i,_,_,hi⟩
    · exact hl h
    · apply hc
      exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
end Oberwolfach
