module

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

theorem ordinary_physical_assigned_payload_length
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
    ∀a,Fintype.card (assign a).val=longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L u a).1+2 :=by
  intro a
  have hs:=hsize a
  rw [ordinary_physical_unmarked_payload_index π d m RM state L u a i₀] at hs
  have hthree:3≤Fintype.card (assign a).val:=(component_regular_two_cycle_iso (F u) (hF u) (assign a).val).1
  have hreal:longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L u a).1+2=
      (ordinaryPhysicalUnmarkedPayload π d m RM state L u a).1.val+1:=by
    rw [long_padded_seed_length_eq_exponent]
    exact long_assigned_padded_length_true (ordinaryPhysicalUnmarkedPayload π d m RM state L u a).1 (by omega)
  exact hs.trans hreal.symm
end Oberwolfach
