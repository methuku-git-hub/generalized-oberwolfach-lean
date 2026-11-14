module

public import Oberwolfach.LongUncoveredMarkedSpokes

@[expose] public section
/-! Missing residual positions are controlled by the same matching incidence
test that is present in the common event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longResidualMissingFinDecidable (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_residual_missing_positions_le_uncovered_incidence
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (hd:1≤d)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (ℓ:Fin K→ℕ) (raw:RawMarkedOutcome (Fin n) U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (Del:Finset (Sym2 (Fin n))):
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let S:=longRawSurvivingResources P π d raw true true Del
    let hST:=long_raw_surviving_resources_subset P π d raw true true Del
    let q:=survivingCandidateEmbedding R S T hST
    let Q:=restrictedResourceSet R (Function.Embedding.subtype (·∈S))
    ∀(M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S)))) (w:U),
    let Marked:=longRawMarkedWheelsAtHub P π d m ℓ raw true true (M.map q) w
    ∀s:Finset {x:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) x true},
    let positions:=fun i:{x:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) x true}=>
      packedPhysicalSpokePositions _ _ _ _ m (3*d) d π
        (rawMarkedPairSpokes π d raw true true false) (rawMarkedPairSpokes π d raw true true true) Marked w i.val
    (∑i∈s,(d-(positions i).card))≤
      (longRawIncidenceSet S (.inr (true,.inr w))\M.biUnion Q).card:=by
  intro R T S hST q Q M w Marked s positions
  have h₁:=raw_packed_missing_positions_le_uncovered π d hd hnoshort (fun e=>raw (Sum.inr e)) t J w s
    _ _ _ _ m (3*d) (rawMarkedPairSpokes π d raw true true false)
    (rawMarkedPairSpokes π d raw true true true) Marked
  have h₂:=long_uncovered_marked_spokes_le_matching_incidence P π d m ℓ raw Del M w
  exact h₁.trans h₂
end Oberwolfach
