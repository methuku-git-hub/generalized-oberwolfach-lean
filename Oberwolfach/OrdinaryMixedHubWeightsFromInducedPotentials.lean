module

public import Oberwolfach.OrdinaryMixedHubWeightsFromInduced
public import Oberwolfach.OrdinaryLocalWeightsFromPotential

@[expose] public section
/-! Fixed fractional parent cycles on the actual inner domain and their
local sampled potentials construct the ambient hub-factor weights. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
set_option synthInstance.maxSize 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinary_mixed_hub_weights_from_induced_potentials
    (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (Z:Finset U)
    (p q s D δ ξ L cLo cHi b B η K:ℝ) (hA:0<A.card) (hQP:Q≤P)
    (hp:0<p) (hp1:p≤1) (hq:p≤q) (hq1:q≤1) (hs:p≤s) (hs1:s≤1)
    (hδ:0≤δ) (hL:0≤L) (hcLo:0<cLo) (hcHi:0≤cHi) (hK:0≤K)
    (hDlo:(A.card:ℝ)/2≤D) (hDhi:D≤2*A.card)
    (hreg:∀v:{v:V // v∈A},|((P.induce (A:Set V)).degree v:ℝ)-D|≤δ*A.card)
    (hF:∀v:{v:V // v∈A},((F.induce (A:Set V)).degree v:ℝ)≤L)
    (weight:OrdinaryCycle (P.induce (A:Set V)) 3→ℝ)
    (hweight:∀C,cLo/(A.card:ℝ)≤weight C∧weight C≤cHi/(A.card:ℝ))
    (hedge:∀x y,(∑C,if C.val.val.Adj x y then weight C else 0)=if (P.induce (A:Set V)).Adj x y then 1 else 0)
    (hpotential:∀j:{u:U // u∉Z},∀v∈ordinaryInducedLocalDomain A (ordinaryBoundaryHubSet H Z A j),
      |ordinaryLocalPotential (P.induce (A:Set V)) (Q.induce (A:Set V)) (F.induce (A:Set V))
        (ordinaryInducedLocalDomain A (ordinaryBoundaryHubSet H Z A j))
        (fun C=>2*weight C/(D*q^3*s^2)) v-
        ordinaryLocalTarget (P.induce (A:Set V)) (F.induce (A:Set V)) weight D v|≤ξ)
    (hsize:(Fintype.card V:ℝ)≤K*A.card) (hb:b≤cLo) (hB:(4*cHi/p^7)*K^2≤B)
    (herr:ξ+2*δ+12*(3:ℝ)^4*cHi*L/A.card≤η):
    OrdinaryMixedHubWeights b B η Q F H A Z:=by
  let I:={v:V // v∈A}
  have hcard:Fintype.card I=A.card:=by simp [I]
  have hn:0<Fintype.card I:=by omega
  have hqi:Q.induce (A:Set V)≤P.induce (A:Set V):=by
    intro v w hvw
    exact hQP hvw
  have hex (j:{u:U // u∉Z}):∃w:LocalOrdinaryCycle (Q.induce (A:Set V)) (F.induce (A:Set V))
      (ordinaryInducedLocalDomain A (ordinaryBoundaryHubSet H Z A j)) 3→ℝ,
      (∀C,cLo/(A.card:ℝ)^2≤w C∧w C≤(4*cHi/p^7)/(A.card:ℝ)^2) ∧
      (∀v∈ordinaryInducedLocalDomain A (ordinaryBoundaryHubSet H Z A j),
        |1-hypergraphWeightedDegree localOrdinaryVertices w v|≤η):=by
    obtain ⟨w,hw,hl⟩:=ordinary_local_weights_from_potential 2 (by omega)
      (P.induce (A:Set V)) (Q.induce (A:Set V)) (F.induce (A:Set V))
      (ordinaryInducedLocalDomain A (ordinaryBoundaryHubSet H Z A j)) 1 p q s D δ ξ L cLo cHi
      hn hqi (by omega) hp hp1 hq hq1 hs hs1 hδ hL hcLo hcHi
      (by simpa using hDlo) (by simpa using hDhi)
      (by intro v hv;simpa using hreg v) hF weight
      (by simpa using hweight) hedge (by simpa using hpotential j)
    refine ⟨w,?_,?_⟩
    · intro C
      simpa using hw C
    · intro v hv
      apply (hl v hv).trans
      norm_num at herr ⊢
      simpa using herr
  choose w hw hl using hex
  have hupper:0≤4*cHi/p^7:=by positivity
  exact ordinary_mixed_hub_weights_from_induced Q F H A Z cLo (4*cHi/p^7) b B η K hA hcLo.le hupper hK
    hsize hb hB w hw hl
end Oberwolfach
