module

public import Oberwolfach.LongMatchedOrdinarySpokeWheel

@[expose] public section
/-! Matched ordinary spokes are occupied once both wheel types are embedded. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longMatchedOrdinaryOldFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_matched_ordinary_spoke_in_old_image
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool):
    let state:=longRawHubState P π d raw true true
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    let Q:=restrictedResourceSet (mixedCandidateResources R) e
    ∀(M:Finset (RestrictedResource (mixedCandidateResources R) e)) (old:U→Finset (Fin n)),
      (∀(w:U) (a:LongRawSelectedOrdinary π d m ℓ e M),
        (longRawSelectedOrdinaryWheel π d m ℓ e M a).val.2=w→
        ∀v∈Finset.univ.image ((longRawSelectedOrdinaryWheel π d m ℓ e M a).val.1.val),v∈old w)→
      (∀w W,W∈longRawMarkedWheelsAtHub P π d m ℓ raw true true M w→
        ∀i:Fin (m+1),W.1.val i∈old w)→
      ∀v w (x:{z // z∈bernoulliVertexSet state}),
        x.val=Sum.inr (false,v,w)→x∈M.biUnion Q→v∈old w:=by
  intro state e R Q M old hOrd hMarked v w x hx hmatch
  rcases long_matched_ordinary_spoke_wheel P π d m ℓ raw M v w x hx hmatch with h|h
  · obtain ⟨a,hhub,hv⟩:=h
    exact hOrd w a hhub v hv
  · obtain ⟨W,hW,i,hi⟩:=h
    rw [←hi]
    exact hMarked w W hW i
end Oberwolfach
