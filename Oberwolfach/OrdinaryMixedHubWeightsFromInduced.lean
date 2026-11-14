module

public import Oberwolfach.OrdinaryLocalInducedWeights
public import Oberwolfach.OrdinaryMixedHubWeights
public import Oberwolfach.EndpointWeightScaleTransfer

@[expose] public section
/-! Transfer fixed inner-domain cycle weights and their local loads to the
actual ambient hub-factor classes, at the original ambient scale. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
set_option synthInstance.maxSize 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinary_mixed_hub_weights_from_induced
    (Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (Z:Finset U)
    (b₀ B₀ b B η K:ℝ) (hA:0<A.card) (hb₀:0≤b₀) (hB₀:0≤B₀) (hK:0≤K)
    (hsize:(Fintype.card V:ℝ)≤K*A.card) (hb:b≤b₀) (hB:B₀*K^2≤B)
    (weight:∀j:{u:U // u∉Z},LocalOrdinaryCycle (Q.induce (A:Set V)) (F.induce (A:Set V))
      (ordinaryInducedLocalDomain A (ordinaryBoundaryHubSet H Z A j)) 3→ℝ)
    (hweight:∀j C,b₀/(A.card:ℝ)^2≤weight j C∧weight j C≤B₀/(A.card:ℝ)^2)
    (hload:∀j,∀v∈ordinaryInducedLocalDomain A (ordinaryBoundaryHubSet H Z A j),
      |1-hypergraphWeightedDegree localOrdinaryVertices (weight j) v|≤η):
    OrdinaryMixedHubWeights b B η Q F H A Z:=by
  have hTA (j:{u:U // u∉Z}):ordinaryBoundaryHubSet H Z A j⊆A:=by
    intro v hv
    exact (Finset.mem_filter.mp hv).1
  let w:=fun (j:{u:U // u∉Z}) (C:LocalOrdinaryCycle (spanningRestriction Q A) F (ordinaryBoundaryHubSet H Z A j) 3)=>
    weight j ((ordinaryLocalInducedEquiv Q F A (ordinaryBoundaryHubSet H Z A j) (hTA j)).symm C)
  refine ⟨w,?_,?_⟩
  · intro j C
    have ha:(0:ℝ)<A.card:=Nat.cast_pos.mpr hA
    have han:(A.card:ℝ)≤Fintype.card V:=by exact_mod_cast Finset.card_le_univ A
    have hh:=endpoint_weight_scale_transfer A.card (Fintype.card V) b₀ B₀ K (w j C)
      ha han hK hsize hb₀ hB₀ (hweight j _).1 (hweight j _).2
    exact ⟨(div_le_div_of_nonneg_right hb (by positivity)).trans hh.1,
      hh.2.trans (div_le_div_of_nonneg_right hB (by positivity))⟩
  · intro j v hv
    have hv':(⟨v,hTA j hv⟩:{v:V // v∈A})∈ordinaryInducedLocalDomain A (ordinaryBoundaryHubSet H Z A j):=by
      simp [ordinaryInducedLocalDomain,hv]
    have heq:=ordinary_local_induced_weighted_degree Q F A (ordinaryBoundaryHubSet H Z A j) (hTA j) (weight j) v hv
    rw [heq]
    exact hload j _ hv'
end Oberwolfach
