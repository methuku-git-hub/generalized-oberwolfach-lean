module

public import Oberwolfach.OrdinaryMatchedResidualHubFamily
public import Oberwolfach.OrdinaryPhysicalPairHubRimPacksNamed

@[expose] public section
/-! Apply the cross-hub disjointness of one physical matching to coherent
per-hub residual packages and obtain an old-edge family in the target host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryMatchedPhysicalHubFamilyShape
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (R:(Fin n×Fin n)⊕(Fin n×Fin n)→Prop) (H:Bool→Fin n→U→Prop):Prop :=
    let RM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W
    let state:=typedMarkedResourceState R H
    let RR:=ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let φ:=ordinaryMixedPhysicalResource (U:=U) π;
    ∀(L:Finset (PhysicalSampledCandidate (mixedCandidateResources RR) state))
    (hL:∀x∈L,∀y∈L,x≠y→Disjoint (physicalSampledCandidateSet φ (mixedCandidateResources RR) state x)
      (physicalSampledCandidateSet φ (mixedCandidateResources RR) state y)),
    let AM:=fun u:U=>OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L u
    let AU:=fun u:U=>OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u
    let len:=fun (u:U) (a:AU u)=>longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L u a).1+2
    let Q:=fun (u:U) (a:AU u)=>(ordinaryPhysicalUnmarkedPayload π d m RM state L u a).2
    let E:={e:Fin n×Fin n // R (Sum.inl e)}
    let S:={e:Fin n×Fin n // R (Sum.inr e)}
    let MW:=MarkedWheel (fun e:E=>e.val.1) (fun e:E=>e.val.2) (fun e:S=>e.val.1) (fun e:S=>e.val.2) m π (3*d) (H false) (H true)
    let W:=fun u=>AM u→MW
    let Good:=fun u (w:W u)=>∀a,(w a).1.val=(ordinaryPhysicalMarkedPayload π d m RM state L u a).1.val ∧ (w a).2.val=u
    let Pack:=fun u (w:W u)=>mixedWheelRimPack (len u) (Finset.univ.image w) (Q u);
    ∀{X A B:U→Type} [∀u,Fintype (X u)] [∀u,DecidableEq (X u)]
      [∀u,Fintype (A u)] [∀u,DecidableEq (A u)] [∀u,Fintype (B u)] [∀u,DecidableEq (B u)]
    (G:∀u,SimpleGraph (X u)) (root:∀u,A u⊕B u→Fin n) (Arc:Fin n→Fin n→Prop)
    (Avail Reserve:U→Finset (Fin n)),
    let Pos:=fun u (w:W u) (i:B u)=>packedPhysicalSpokePositions
      (fun e:E=>e.val.1) (fun e:E=>e.val.2) (fun e:S=>e.val.1) (fun e:S=>e.val.2)
      m (3*d) d π (H false) (H true) (Finset.univ.image w) u (root u (.inr i));
    (∀u,Nonempty (OrdinaryMatchedResidualHubPackage (G u) m d π (root u) Arc (Avail u) (Reserve u)
      (Good u) (Pack u) (Pos u) (len u)))→
    ∀(Host:SimpleGraph (Fin n)),(∀x y,Arc x y→Host.Adj x y)→
    ∃p:∀u,OrdinaryMatchedResidualHubPackage (G u) m d π (root u) Arc (Avail u) (Reserve u) (Good u) (Pack u) (Pos u) (len u),
    (∀u v,u≠v→Disjoint (Pack u (p u).marker) (Pack v (p v).marker)) ∧
    let Old:=fun u=>((p u).data.deletedEdges\(Finset.univ.biUnion
      (fun i:{i // i∈(p u).data.s₁}=>((p u).data.path (.inl i)).edges.toFinset))).image (Sym2.map (p u).ψ);
    (∀u v,u≠v→Disjoint (Old u) (Old v)) ∧
    ∃All:Finset (Sym2 (Fin n)),(∀u,Old u⊆All) ∧ All⊆Host.edgeFinset
end Oberwolfach
