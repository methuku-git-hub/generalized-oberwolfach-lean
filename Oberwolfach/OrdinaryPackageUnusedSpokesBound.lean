module

public import Oberwolfach.OrdinaryUnusedSpokesFromMatchedWheelPack
public import Oberwolfach.OrdinaryPackageOldRimOccupancy

@[expose] public section

/-! The coherent package's actual old image covers all matched spokes, so
its unused ordinary labels are bounded by the matching's uncovered row. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
set_option synthInstance.maxSize 65536
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_package_unused_spokes_bound
    (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (Rim:(Fin n×Fin n)⊕(Fin n×Fin n)→Prop) (H:Bool→Fin n→U→Prop):
    let RM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W
    let state:=typedMarkedResourceState Rim H
    let RR:=ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let φ:=ordinaryMixedPhysicalResource (U:=U) π;
    ∀(L:Finset (PhysicalSampledCandidate (mixedCandidateResources RR) state)) (u:U),
    let AM:=OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L u
    let AU:=OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u
    let MW:=MarkedWheel (fun e:{e:Fin n×Fin n // Rim (Sum.inl e)}=>e.val.1) (fun e=>e.val.2)
      (fun e:{e:Fin n×Fin n // Rim (Sum.inr e)}=>e.val.1) (fun e=>e.val.2) m π (3*d) (H false) (H true)
    let W:=AM→MW
    let Good:=fun (w:W)=>∀a,(w a).1.val=(ordinaryPhysicalMarkedPayload π d m RM state L u a).1.val ∧ (w a).2.val=u
    let len:=fun a:AU=>longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L u a).1+2
    let Q:=fun a:AU=>(ordinaryPhysicalUnmarkedPayload π d m RM state L u a).2
    let Pack:=fun w:W=>mixedWheelRimPack len (Finset.univ.image w) Q;
    ∀{X A B:Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [IsEmpty A]
      [Fintype B] [DecidableEq B]
    (G:SimpleGraph X) (root:A⊕B→Fin n) (Arc:Fin n→Fin n→Prop) (Avail Reserve:Finset (Fin n))
    (Pos:W→B→Finset ℕ)
    (pk:OrdinaryMatchedResidualHubPackage G m d π root Arc Avail Reserve Good Pack Pos len),
    let Old:=(pk.data.oldDomain\bufferedPathStrictInterior (fun _:A=>(m+1)*d) pk.inner).image pk.ψ;
    ((Finset.univ.filter (fun v=>H false v u))\Old).card≤
      ((physicalSampledRow φ state (ordinaryPhysicalRow (.inr (.inr u))))\
        L.biUnion (physicalSampledCandidateSet φ (mixedCandidateResources RR) state)).card :=by
  intro RM state RR φ L u AM AU MW W Good len Q Pack X A B _ _ _ _ _ _ _ G root Arc Avail Reserve Pos pk Old
  apply ordinary_unused_spokes_from_matched_wheel_pack (K:=K) π d m Rim H L u pk.marker pk.hGood Old
  exact ordinary_package_old_rim_occupancy m d π root Arc Avail Reserve Good Pack Pos len pk
end Oberwolfach
