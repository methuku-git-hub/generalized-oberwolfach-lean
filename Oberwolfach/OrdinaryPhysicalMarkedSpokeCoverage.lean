module

public import Oberwolfach.OrdinaryPhysicalTrueSpoke
public import Oberwolfach.OrdinaryTrueSpokeCandidate
public import Oberwolfach.OrdinaryPhysicalMarkedRestricted

@[expose] public section
/-! A sampled true spoke covered by a mixed physical matching is a spoke of
one of that matching's marked payloads at the same hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_physical_marked_spoke_coverage
    (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (Rim:(Fin n×Fin n)⊕(Fin n×Fin n)→Prop) (H:Bool→Fin n→U→Prop)
    (hexclusive:∀v u,H true v u→¬H false v u):
    let RM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W
    let state:=typedMarkedResourceState Rim H
    let RR:=ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let φ:=ordinaryMixedPhysicalResource (U:=U) π;
    ∀(L:Finset (PhysicalSampledCandidate (mixedCandidateResources RR) state)) (u:U)
    (W:OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L u→
      MarkedWheel (fun e:{e:Fin n×Fin n // Rim (Sum.inl e)}=>e.val.1) (fun e=>e.val.2)
      (fun e:{e:Fin n×Fin n // Rim (Sum.inr e)}=>e.val.1) (fun e=>e.val.2) m π (3*d) (H false) (H true))
    (hW:∀a,(W a).1.val=(ordinaryPhysicalMarkedPayload π d m RM state L u a).1.val ∧ (W a).2.val=u)
    (c:PhysicalSampledCandidate (mixedCandidateResources RR) state) (hc:c∈L)
    (x:PhysicalSampledActive φ state) (v:Fin n)
    (hx:x.val=Sum.inr (v,u)) (hcx:x∈physicalSampledCandidateSet φ (mixedCandidateResources RR) state c)
    (ht:H true v u),
    ∃a:OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L u,
      Sum.inr (v,u)∈markedWheelPhysicalResources (W a) :=by
  intro RM state RR φ L u W hW c hc x v hx hcx ht
  have htyped:=ordinary_physical_candidate_true_spoke π (mixedCandidateResources RR) Rim H hexclusive c x v u hx
    (by simpa only [physicalSampledCandidateSet,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image] using hcx) ht
  have htag:=ordinary_true_spoke_candidate_is_marked RM
    (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    c.val v u htyped
  have hnone:c.val.1.isNone:=by simp [htag]
  let z := (⟨c.val,hnone⟩ : {v // v.1.isNone})
  let Q:=ordinaryMixedNonePayload z
  have horig:=ordinary_mixed_none_payload_original z
  have hres:mixedCandidateResources RR c.val=typedMarkedOccurrenceResources Q:=by
    rw [horig]
    rfl
  rw [hres] at htyped
  obtain ⟨i,hi⟩:=(typedMarkedOccurrenceResources_spoke Q (true,v,u)).mp htyped
  have hi':decide (i=0)=true ∧ Q.1.val i=v ∧ Q.2.val=u:=by
    simpa only [Prod.mk.injEq] using hi
  have hv:Q.1.val i=v:=hi'.2.1
  have hu:Q.2.val=u:=hi'.2.2
  have hhub:ordinaryMixedGenericWheelHub (U:=U) π (3*d) m longPaddedSeedExponent c.val.1 c.val.2=u:=by
    rw [horig]
    exact hu
  let a:OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L u:=⟨c,Finset.mem_filter.mpr ⟨hc,hnone,hhub⟩⟩
  have htuple:(ordinaryPhysicalMarkedPayload π d m RM state L u a).1.val=Q.1.val:=by rfl
  refine ⟨a,(markedWheelPhysicalResources_spoke (W a) v u).mpr ⟨(hW a).2,?_⟩⟩
  apply Finset.mem_image.mpr
  refine ⟨i,Finset.mem_univ _,?_⟩
  rw [(hW a).1,htuple]
  exact hv
end Oberwolfach
