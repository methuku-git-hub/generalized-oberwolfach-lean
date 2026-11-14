module

public import Oberwolfach.OrdinaryMixedHubWeightsGeneral

@[expose] public section
/-! Keep the natural inner-domain normalization of adaptive hub weights,
so their constants need not deteriorate with the vortex scale. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

structure OrdinaryMixedHubWeightsInnerScale (m:ℕ) (b B η:ℝ) (Q F:SimpleGraph V) (H:V→U→Prop)
    (A:Finset V) (Z:Finset U) where
  weight:∀j:{u:U // u∉Z},LocalOrdinaryCycle (spanningRestriction Q A) F (ordinaryBoundaryHubSet H Z A j) (m+1)→ℝ
  bounds:∀j C,b/(A.card:ℝ)^m≤weight j C ∧ weight j C≤B/(A.card:ℝ)^m
  loads:∀j,∀v∈ordinaryBoundaryHubSet H Z A j,|1-hypergraphWeightedDegree localOrdinaryVertices (weight j) v|≤η

def ordinary_mixed_hub_weights_inner_scale_from_induced
    (m:ℕ) (Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (Z:Finset U) (b B η:ℝ)
    (weight:∀j:{u:U // u∉Z},LocalOrdinaryCycle (Q.induce (A:Set V)) (F.induce (A:Set V))
      (ordinaryInducedLocalDomain A (ordinaryBoundaryHubSet H Z A j)) (m+1)→ℝ)
    (hweight:∀j C,b/(A.card:ℝ)^m≤weight j C∧weight j C≤B/(A.card:ℝ)^m)
    (hload:∀j,∀v∈ordinaryInducedLocalDomain A (ordinaryBoundaryHubSet H Z A j),
      |1-hypergraphWeightedDegree localOrdinaryVertices (weight j) v|≤η):
    OrdinaryMixedHubWeightsInnerScale m b B η Q F H A Z:=by
  have hTA (j:{u:U // u∉Z}):ordinaryBoundaryHubSet H Z A j⊆A:=by
    intro v hv
    exact (Finset.mem_filter.mp hv).1
  let w:=fun (j:{u:U // u∉Z}) (C:LocalOrdinaryCycle (spanningRestriction Q A) F (ordinaryBoundaryHubSet H Z A j) (m+1))=>
    weight j ((ordinaryLocalInducedEquiv Q F A (ordinaryBoundaryHubSet H Z A j) (hTA j)).symm C)
  refine ⟨w,?_,?_⟩
  · intro j C
    exact hweight j _
  · intro j v hv
    have hv':(⟨v,hTA j hv⟩:{v:V // v∈A})∈ordinaryInducedLocalDomain A (ordinaryBoundaryHubSet H Z A j):=by
      simp [ordinaryInducedLocalDomain,hv]
    have heq:=ordinary_local_induced_weighted_degree Q F A (ordinaryBoundaryHubSet H Z A j) (hTA j) (weight j) v hv
    rw [heq]
    exact hload j _ hv'

theorem ordinary_inner_scale_weights_normalize_to_hub_class
    (m:ℕ) (b B η α:ℝ) (Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (Z:Finset U)
    (hA:0<A.card) (hb:0≤b) (hB:0≤B) (hα:0<α)
    (hsize:∀j:{u:U // u∉Z},α*A.card≤((ordinaryBoundaryHubSet H Z A j).card:ℝ))
    (data:OrdinaryMixedHubWeightsInnerScale m b B η Q F H A Z):
    ∀j C,(b*α^m)/((ordinaryBoundaryHubSet H Z A j).card:ℝ)^m≤data.weight j C ∧
      data.weight j C≤B/((ordinaryBoundaryHubSet H Z A j).card:ℝ)^m:=by
  intro j C
  let t:ℝ:=(ordinaryBoundaryHubSet H Z A j).card
  let a:ℝ:=A.card
  have ha:0<a:=by dsimp [a];exact_mod_cast hA
  have ht:0<t:=(mul_pos hα ha).trans_le (hsize j)
  have hta:t≤a:=by
    dsimp [t,a]
    exact_mod_cast Finset.card_le_card (show ordinaryBoundaryHubSet H Z A j⊆A from by
      intro v hv;exact (Finset.mem_filter.mp hv).1)
  have hpow:(α*a)^m≤t^m:=pow_le_pow_left₀ (mul_nonneg hα.le ha.le) (hsize j) m
  rw [mul_pow] at hpow
  have hlo:(b*α^m)/t^m≤b/a^m:=by
    apply (div_le_div_iff₀ (pow_pos ht _) (pow_pos ha _)).2
    have hh:=mul_le_mul_of_nonneg_left hpow hb
    nlinarith only [hh]
  have hhi:B/a^m≤B/t^m:=div_le_div_of_nonneg_left hB (pow_pos ht _)
    (pow_le_pow_left₀ ht.le hta m)
  exact ⟨hlo.trans (data.bounds j C).1,(data.bounds j C).2.trans hhi⟩
end Oberwolfach
