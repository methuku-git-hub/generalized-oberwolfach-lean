module

public import Oberwolfach.OrdinaryMatchingRetainedMassUpper
public import Oberwolfach.ResidualActualCycleMass

@[expose] public section
/-! Transfer the selected matching's cycle mass to the actual unreserved
residual data, preserving the matching error term. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_matching_residual_cycle_mass_upper
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (i₀:Fin K) (rsv θ:ℝ) (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (RM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→Finset (((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)))
    (state:(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))→Bool)
    (L:Finset (PhysicalSampledCandidate (mixedCandidateResources
      (ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W))) state))
    (u:U) (err:ℝ)
    (hmass:((∑a:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u,
        (longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L u a).1+2)):ℝ)≤
      (1-θ+err)*(n:ℝ)*(∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i))
    {V Z:Type} [Fintype V] [DecidableEq V] [DecidableEq Z] {G:SimpleGraph V}
    (a:ActualResidualData (K:=Z) (J:=OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u) G)
    (ht:a.t=Finset.univ)
    (hC:a.Cembed=a.t.biUnion (fun j=>(a.C j).support.toFinset))
    (hlen:∀j,(a.C j).length=longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L u j).1+2):
    ((a.t.biUnion (fun j=>(a.C j).support.toFinset)).card:ℝ)≤
      (n:ℝ)*((1-θ)*(∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i))+
      err*n*(∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i):=by
  have hcard:(a.t.biUnion (fun j=>(a.C j).support.toFinset)).card=
      ∑j:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u,
        (longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L u j).1+2):=by
    rw [←hC,actual_residual_cycle_mass a ht hC]
    exact Finset.sum_congr rfl (fun j _=>hlen j)
  rw [hcard]
  push_cast at hmass ⊢
  convert hmass using 1 <;> ring
end Oberwolfach
