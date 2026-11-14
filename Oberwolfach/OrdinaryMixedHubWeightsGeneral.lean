module

public import Oberwolfach.OrdinaryLocalInducedWeights
public import Oberwolfach.OrdinaryMixedOtherParentInputsInside

@[expose] public section
/-! Transfer arbitrary fixed-length local cycle weights from the actual
    inner domain to ambient hub classes with the correct power scaling. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
set_option synthInstance.maxSize 8192
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_weight_scale_transfer_power (m:ℕ) (a n b B K w:ℝ)
    (ha:0<a) (han:a≤n) (hK:0≤K) (hnK:n≤K*a) (hb:0≤b) (hB:0≤B)
    (hwlo:b/a^m≤w) (hwhi:w≤B/a^m):
    b/n^m≤w ∧ w≤(B*K^m)/n^m:=by
  have hn:0<n:=ha.trans_le han
  have hpow:a^m≤n^m:=pow_le_pow_left₀ ha.le han m
  have hKpow:n^m≤(K*a)^m:=pow_le_pow_left₀ hn.le hnK m
  constructor
  · exact (div_le_div_of_nonneg_left hb (by positivity) hpow).trans hwlo
  · apply hwhi.trans
    apply (div_le_div_iff₀ (by positivity : 0<a^m) (by positivity : 0<n^m)).mpr
    rw [mul_pow] at hKpow
    have hh:=mul_le_mul_of_nonneg_left hKpow hB
    nlinarith only [hh]

structure OrdinaryMixedHubWeightsOfLength (m:ℕ) (b B η:ℝ) (Q F:SimpleGraph V) (H:V→U→Prop)
    (A:Finset V) (Z:Finset U) where
  weight:∀j:{u:U // u∉Z},LocalOrdinaryCycle (spanningRestriction Q A) F (ordinaryBoundaryHubSet H Z A j) (m+1)→ℝ
  bounds:∀j C,b/(Fintype.card V:ℝ)^m≤weight j C ∧ weight j C≤B/(Fintype.card V:ℝ)^m
  loads:∀j,∀v∈ordinaryBoundaryHubSet H Z A j,|1-hypergraphWeightedDegree localOrdinaryVertices (weight j) v|≤η

def ordinary_mixed_hub_weights_of_length_from_induced
    (m:ℕ) (Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (Z:Finset U)
    (b₀ B₀ b B η K:ℝ) (hA:0<A.card) (hb₀:0≤b₀) (hB₀:0≤B₀) (hK:0≤K)
    (hsize:(Fintype.card V:ℝ)≤K*A.card) (hb:b≤b₀) (hB:B₀*K^m≤B)
    (weight:∀j:{u:U // u∉Z},LocalOrdinaryCycle (Q.induce (A:Set V)) (F.induce (A:Set V))
      (ordinaryInducedLocalDomain A (ordinaryBoundaryHubSet H Z A j)) (m+1)→ℝ)
    (hweight:∀j C,b₀/(A.card:ℝ)^m≤weight j C∧weight j C≤B₀/(A.card:ℝ)^m)
    (hload:∀j,∀v∈ordinaryInducedLocalDomain A (ordinaryBoundaryHubSet H Z A j),
      |1-hypergraphWeightedDegree localOrdinaryVertices (weight j) v|≤η):
    OrdinaryMixedHubWeightsOfLength m b B η Q F H A Z:=by
  have hTA (j:{u:U // u∉Z}):ordinaryBoundaryHubSet H Z A j⊆A:=by
    intro v hv
    exact (Finset.mem_filter.mp hv).1
  let w:=fun (j:{u:U // u∉Z}) (C:LocalOrdinaryCycle (spanningRestriction Q A) F (ordinaryBoundaryHubSet H Z A j) (m+1))=>
    weight j ((ordinaryLocalInducedEquiv Q F A (ordinaryBoundaryHubSet H Z A j) (hTA j)).symm C)
  refine ⟨w,?_,?_⟩
  · intro j C
    have ha:(0:ℝ)<A.card:=Nat.cast_pos.mpr hA
    have han:(A.card:ℝ)≤Fintype.card V:=by exact_mod_cast Finset.card_le_univ A
    have hh:=ordinary_weight_scale_transfer_power m A.card (Fintype.card V) b₀ B₀ K (w j C)
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
