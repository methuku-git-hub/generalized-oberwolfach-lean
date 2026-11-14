module

public import Oberwolfach.OrdinaryPhysicalRestrictedMarkedFamily
public import Oberwolfach.OrdinaryPhysicalUnmarkedWheelPacking
public import Oberwolfach.OrdinaryPhysicalUnmarkedSampled
public import Oberwolfach.OrdinaryShiftedSampledPhysicalArcs

@[expose] public section
/-! From one selected physical matching, build the marked and ordinary wheel
families required by the buffered source embedding on the same sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_physical_matching_wheel_family (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool):
    let Host:=ordinaryEligibleHost P π d
    let Rim:=ordinaryShiftedPairRims Host π d raw
    let H:=rawMarkedPairSpokes π d raw true true
    let RM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W
    let state:=typedMarkedResourceState Rim H
    let RR:=ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let φ:=ordinaryMixedPhysicalResource (U:=U) π;
    ∀(L:Finset (PhysicalSampledCandidate (mixedCandidateResources RR) state))
    (hL:∀x∈L,∀y∈L,x≠y→Disjoint (physicalSampledCandidateSet φ (mixedCandidateResources RR) state x)
      (physicalSampledCandidateSet φ (mixedCandidateResources RR) state y))
    (u:U),
    let A:=OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u
    let lens:=fun a:A=>longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L u a).1+2
    let Q:=fun a:A=>(ordinaryPhysicalUnmarkedPayload π d m RM state L u a).2
    let Arc:=rawMixedPhysicalArc Host π d raw
    let E:={e:Fin n×Fin n // Rim (Sum.inl e)}
    let S:={e:Fin n×Fin n // Rim (Sum.inr e)};
    ∃M:Finset (MarkedWheel (fun e:E=>e.val.1) (fun e:E=>e.val.2)
      (fun e:S=>e.val.1) (fun e:S=>e.val.2) m π (3*d) (H false) (H true)),
    (∀W∈M,W.2.val=u) ∧
    (∀W∈M,∀Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z)) ∧
    (∀a:A,(Q a).2=u) ∧ (∀a:A,∀i:Fin (lens a),H false ((Q a).1.val i) u) ∧
    (∀a b:A,a≠b→Disjoint (ordinaryWheelPhysicalResources (Q a)) (ordinaryWheelPhysicalResources (Q b))) ∧
    (∀a:A,∀W∈M,Disjoint (ordinaryWheelPhysicalResources (Q a)) (markedWheelPhysicalResources W)) ∧
    (∀e:E,Host.Adj e.val.1 e.val.2 ∧ Arc e.val.1 e.val.2) ∧
    (∀e:S,Host.Adj e.val.1 (π e.val.2) ∧ Arc e.val.1 (π e.val.2)) ∧
    (∀a:A,∀i:Fin (lens a),Arc ((Q a).1.val i) ((Q a).1.val (cycleNext i))) :=by
  intro Host Rim H RM state RR φ L hL u A lens Q Arc E S
  obtain ⟨W,hW,hpair,hcross⟩:=ordinary_physical_restricted_marked_family π d m Rim H L hL u
  let M:=Finset.univ.image W
  have hmhub:∀Z∈M,Z.2.val=u:=by
    intro Z hZ
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hZ
    exact (hW a).2
  have hmpair:∀Y∈M,∀Z∈M,Y≠Z→Disjoint (markedWheelPhysicalResources Y) (markedWheelPhysicalResources Z):=by
    intro Y hY Z hZ hYZ
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hY
    obtain ⟨b,_,rfl⟩:=Finset.mem_image.mp hZ
    exact hpair a b (fun he=>hYZ (congrArg W he))
  have hqq:=ordinary_physical_unmarked_wheel_packing π d m Rim H L hL u
  have hsample:=ordinary_physical_unmarked_payload_sampled π d m Rim H L u
  have harcs:=ordinary_shifted_sampled_physical_arcs P π d raw
  refine ⟨M,hmhub,hmpair,?_,?_,hqq,?_,harcs.1,harcs.2,?_⟩
  · intro a
    exact ordinary_physical_unmarked_payload_hub π d m RM state L u a
  · intro a i
    exact (hsample a).1 i
  · intro a Z hZ
    obtain ⟨b,_,rfl⟩:=Finset.mem_image.mp hZ
    exact (hcross b a).symm
  · intro a i
    have hh:=(hsample a).2 i
    exact (harcs.1 ⟨_,hh⟩).2
end Oberwolfach
