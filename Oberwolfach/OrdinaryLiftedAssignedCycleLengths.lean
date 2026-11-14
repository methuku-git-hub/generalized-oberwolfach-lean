module

public import Oberwolfach.OrdinaryPhysicalAssignedPayloadLength
public import Oberwolfach.OrdinaryPhysicalMatchedPartialEmbedding

@[expose] public section
/-! The source component chosen by the matching has exactly the length of
its extracted ordered wheel, including the harmless padded indices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_lifted_assigned_cycle_lengths
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (RM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→Finset (((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)))
    (state:(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))→Bool)
    (L:Finset (PhysicalSampledCandidate (mixedCandidateResources
      (ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W))) state))
    (u:U) (i₀:Fin K) (Cres:Finset (F u).ConnectedComponent)
    (assign:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u↪↥(Finset.univ\Cres))
    (hsize:∀a,Fintype.card (assign a).val=(a.val.val.1.getD i₀).val+1):
    ∀(orig lifted:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u→ℕ),
      (∀a,orig a=Fintype.card (assign a).val)→(∀a,lifted a=orig a)→
      ∀a,lifted a=longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L u a).1+2 :=by
  intro orig lifted hOrig hLift a
  have hh:=ordinary_physical_assigned_payload_length F hF π d m RM state L u i₀ Cres assign hsize a
  exact (hLift a).trans ((hOrig a).trans hh)
end Oberwolfach
