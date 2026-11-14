module

public import Oberwolfach.OrdinaryReservedForcedLoadFromBoundary
public import Oberwolfach.OrdinaryMatchedPhysicalHubFamilyShape
public import Oberwolfach.OrdinaryPrescribedBoundarySpokeMatchingNamed

@[expose] public section
/-! A coherent matching package supplies the actual paths and marked positions
needed by the boundary-and-uncovered-spoke prescribed-load estimate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryPackagedLoadTargetColumnsShape
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    {X:U→Type} [∀w,Fintype (X w)] [∀w,DecidableEq (X w)]
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (hd:1≤d)
    (Rim:(Fin n×Fin n)⊕(Fin n×Fin n)→Prop)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t):Prop :=
    let σ:=fun e=>raw (Sum.inr e)
    let H:=rawMarkedPairSpokes π d raw true true
    let RM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W
    let state:=typedMarkedResourceState Rim H
    let RR:=ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let φ:=ordinaryMixedPhysicalResource (U:=U) π;
    ∀(L:Finset (PhysicalSampledCandidate (mixedCandidateResources RR) state)),
    let AM:=fun u:U=>OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L u
    let AU:=fun u:U=>OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u
    let len:=fun (u:U) (a:AU u)=>longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L u a).1+2
    let Qwheel:=fun (u:U) (a:AU u)=>(ordinaryPhysicalUnmarkedPayload π d m RM state L u a).2
    let E:={e:Fin n×Fin n // Rim (Sum.inl e)}
    let S:={e:Fin n×Fin n // Rim (Sum.inr e)}
    let MW:=MarkedWheel (fun e:E=>e.val.1) (fun e:E=>e.val.2) (fun e:S=>e.val.1) (fun e:S=>e.val.2) m π (3*d) (H false) (H true)
    let W:=fun u=>AM u→MW
    let Good:=fun u (w:W u)=>∀a,(w a).1.val=(ordinaryPhysicalMarkedPayload π d m RM state L u a).1.val ∧ (w a).2.val=u
    let Pack:=fun u (w:W u)=>mixedWheelRimPack (len u) (Finset.univ.image w) (Qwheel u)
    let A:=fun u=>retainedMarkedIndex π d σ false t Jret u
    let B:=fun u=>{a:Fin n // rawIntervalColouredStart π d (fun e=>σ (u,e)) a true}
    let root:=fun u=>retainedAndRawIntervalRoot π d σ false true t Jret u
    let Pos:=fun u (w:W u) (i:B u)=>packedPhysicalSpokePositions
      (fun e:E=>e.val.1) (fun e:E=>e.val.2) (fun e:S=>e.val.1) (fun e:S=>e.val.2)
      m (3*d) d π (H false) (H true) (Finset.univ.image w) u (root u (.inr i));
    ∀(F:∀u,SimpleGraph (X u)) (Arc:Fin n→Fin n→Prop) (Avail Reserve:U→Finset (Fin n))
    (p:∀u,OrdinaryMatchedResidualHubPackage (F u) m d π (root u) Arc (Avail u) (Reserve u)
      (Good u) (Pack u) (Pos u) (len u)) (δ a γ:ℝ),
    let Q:=physicalSampledCandidateSet φ (mixedCandidateResources RR) state
    let Row:=fun v=>physicalSampledRow φ state (ordinaryPhysicalRow (.inr (.inl v)))
    let Prescribed:=fun u=>(residualSubtypeSet (p u).data.remaining (p u).data.prescribed).image (fun x=>(p u).ψ x.1);
    0≤δ→Fintype.card U≤n→4/(d:ℝ)≤δ/16→4*(n:ℝ)^(3/4:ℝ)≤δ*n/16→
    2*((max a γ)*n)≤δ*n/8→
    (∀v,((Row v\L.biUnion Q).card:ℝ)≤(max a γ)*n)→
    (∀v,((rawIntervalBoundaryHubSet π d σ Finset.univ v).card:ℝ)≤
      4*(Fintype.card U:ℝ)/d+4*(n:ℝ)^(3/4:ℝ))→
    ∀(T Old:U→Finset (Fin n)) (Gbad:SimpleGraph (Fin n)),
    (∀v,(Gbad.degree v:ℝ)≤δ*n/8)→
    (∀v,((Finset.univ.filter (fun u=>v∈T u\Old u)).card:ℝ)≤δ*n/2)→
    ∀v,((Finset.univ.filter (fun u=>v∈Prescribed u)).card:ℝ)+Gbad.degree v+
      ((Finset.univ.filter (fun u=>v∈T u\Old u)).card:ℝ)≤δ*n
end Oberwolfach
