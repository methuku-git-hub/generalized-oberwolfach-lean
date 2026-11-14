module

public import Oberwolfach.LongMatchingSourceCountWitness

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longMatchingSourceCountErrorFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem long_matching_source_count_witness_error
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ) (θ eps:ℝ)
    (T:Finset (LongRawHubResource n U))
    (Nraw:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ))
      (Function.Embedding.subtype (·∈T))))
    (h:LongMatchingSourceCountWitness F hF π d m ℓ θ eps T Nraw) (w:U):
    ∃sourceCard:ℕ,
      sourceCard=∑i:Fin K,(Nraw.filter (fun c=>c.val.1=some i ∧ longRawSeedHub π d m ℓ c.val.1 c.val.2=w)).card*ℓ i ∧
      |((sourceCard:ℝ)-(n:ℝ)*((1-θ)*(∑i:Fin K,longAssignedKeptFraction F hF K θ i w)))|≤
        ((max (3*eps) 0)*(n:ℝ))*(∑i:Fin K,((ℓ i:ℕ):ℝ)) :=by
  obtain ⟨assign,C,hC,hcount,herr⟩:=h
  refine ⟨Fintype.card (longRawSourceDomain F π d m ℓ (Function.Embedding.subtype (·∈T)) Nraw C w),hcount w,?_⟩
  convert herr w using 1 <;> ring
end Oberwolfach
