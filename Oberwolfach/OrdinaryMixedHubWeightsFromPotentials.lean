module

public import Oberwolfach.OrdinaryLocalWeightsFromPotential
public import Oberwolfach.OrdinaryLocalWeightsRestrictHost
public import Oberwolfach.OrdinaryMixedHubWeights

@[expose] public section
/-! Fixed parent cycle weights and the actual local potential estimates
construct the hub weights; restricting to the inner host loses no cycles. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
set_option synthInstance.maxSize 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinary_mixed_hub_weights_from_potentials
    (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (Z:Finset U)
    (p q s D δ ξ L cLo cHi b B η:ℝ) (hn:0<Fintype.card V) (hQP:Q≤P)
    (hp:0<p) (hp1:p≤1) (hq:p≤q) (hq1:q≤1) (hs:p≤s) (hs1:s≤1)
    (hδ:0≤δ) (hL:0≤L) (hcLo:0<cLo) (hcHi:0≤cHi)
    (hDlo:(Fintype.card V:ℝ)/2≤D) (hDhi:D≤2*Fintype.card V)
    (hreg:∀v,|(P.degree v:ℝ)-D|≤δ*Fintype.card V)
    (hF:∀v,(F.degree v:ℝ)≤L) (weight:OrdinaryCycle P 3→ℝ)
    (hweight:∀C,cLo/(Fintype.card V:ℝ)≤weight C ∧ weight C≤cHi/(Fintype.card V:ℝ))
    (hedge:∀x y,(∑C,if C.val.val.Adj x y then weight C else 0)=if P.Adj x y then 1 else 0)
    (hpotential:∀j:{u:U // u∉Z},∀v∈ordinaryBoundaryHubSet H Z A j,
      |ordinaryLocalPotential P Q F (ordinaryBoundaryHubSet H Z A j)
        (fun C=>2*weight C/(D*q^3*s^2)) v-ordinaryLocalTarget P F weight D v|≤ξ)
    (hb:b≤cLo) (hB:4*cHi/p^7≤B)
    (herr:ξ+2*δ+12*(3:ℝ)^4*cHi*L/Fintype.card V≤η):
    OrdinaryMixedHubWeights b B η Q F H A Z:=by
  have hex (j:{u:U // u∉Z}):∃w:LocalOrdinaryCycle (spanningRestriction Q A) F
      (ordinaryBoundaryHubSet H Z A j) 3→ℝ,
      (∀C,b/(Fintype.card V:ℝ)^2≤w C∧w C≤B/(Fintype.card V:ℝ)^2) ∧
      (∀v∈ordinaryBoundaryHubSet H Z A j,|1-hypergraphWeightedDegree localOrdinaryVertices w v|≤η):=by
    let T:=ordinaryBoundaryHubSet H Z A j
    have hTA:T⊆A:=by intro v hv;exact (Finset.mem_filter.mp hv).1
    obtain ⟨w,hw,hl⟩:=ordinary_local_weights_from_potential 2 (by omega) P Q F T 1 p q s D δ ξ L cLo cHi
      hn hQP (by omega) hp hp1 hq hq1 hs hs1 hδ hL hcLo hcHi hDlo hDhi
      (fun v _=>hreg v) hF weight (by simpa using hweight) hedge (by simpa using hpotential j)
    obtain ⟨w',hw',heq⟩:=ordinary_local_weights_restrict_host Q F T A hTA w
    refine ⟨w',?_,?_⟩
    · intro C
      rw [hw' C]
      have hh:=hw (localOrdinaryRestrictionParent
        (show spanningRestriction Q A≤Q from fun a b h=>(spanningRestriction_adj Q A a b).mp h |>.1)
        (Finset.Subset.rfl) C)
      constructor
      · exact (div_le_div_of_nonneg_right hb (by positivity)).trans hh.1
      · apply hh.2.trans
        apply div_le_div_of_nonneg_right _ (by positivity)
        simpa using hB
    · intro v hv
      rw [heq v]
      apply (hl v hv).trans
      norm_num at herr ⊢
      exact herr
  choose w hw hl using hex
  exact ⟨w,hw,hl⟩
end Oberwolfach
