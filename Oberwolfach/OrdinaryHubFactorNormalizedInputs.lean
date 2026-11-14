module

public import Oberwolfach.OrdinaryMixedHubWeightsInnerScale
public import Oberwolfach.OrdinaryLocalWeightsInduceDomain
public import Oberwolfach.OrdinaryInducedCommonCard

@[expose] public section
/-! The actual hub class, not the ambient vertex set, is the domain for
the fresh factor theorem. The cycle weights and common neighborhoods retain
uniform constants on that domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_hub_factor_normalized_inputs
    (m k:ℕ) (b B η γ:ℝ) (Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (Z:Finset U)
    (hA:0<A.card) (hb:0≤b) (hB:0≤B) (hγ:0<γ)
    (hsize:∀j:{u:U // u∉Z},γ*A.card≤((ordinaryBoundaryHubSet H Z A j).card:ℝ))
    (hcommon:∀j:{u:U // u∉Z},∀S:Finset V,S⊆ordinaryBoundaryHubSet H Z A j→S.card≤k→
      γ*A.card≤((common (ordinaryBoundaryHubSet H Z A j) S
        (fun x=>(spanningRestriction Q A).neighborFinset x)).card:ℝ))
    (data:OrdinaryMixedHubWeightsInnerScale m b B η Q F H A Z):
    ∀j:{u:U // u∉Z},
      let T:=ordinaryBoundaryHubSet H Z A j
      (∀S:Finset {v:V // v∈T},S.card≤k→γ*Fintype.card {v:V // v∈T}≤
        ((common Finset.univ S (fun x=>((spanningRestriction Q A).induce (T:Set V)).neighborFinset x)).card:ℝ)) ∧
      ∃wt:LocalOrdinaryCycle ((spanningRestriction Q A).induce (T:Set V))
          (F.induce (T:Set V)) Finset.univ (m+1)→ℝ,
        (∀C,(b*γ^m)/(Fintype.card {v:V // v∈T}:ℝ)^m≤wt C ∧
          wt C≤B/(Fintype.card {v:V // v∈T}:ℝ)^m) ∧
        (∀v,|1-hypergraphWeightedDegree localOrdinaryVertices wt v|≤η):=by
  intro j
  let T:=ordinaryBoundaryHubSet H Z A j
  have hTA:T⊆A:=by
    intro v hv
    exact (Finset.mem_filter.mp hv).1
  have hc:Fintype.card {v:V // v∈T}=T.card:=by simp
  have hbound:=ordinary_inner_scale_weights_normalize_to_hub_class m b B η γ Q F H A Z hA hb hB hγ hsize data j
  constructor
  · intro S hS
    have himage:(S.image Subtype.val).card=S.card:=
      Finset.card_image_of_injective S (Subtype.val_injective : Function.Injective (Subtype.val : {v:V // v∈T}→V))
    have hsub:S.image Subtype.val⊆T:=by
      intro v hv
      obtain ⟨x,_,rfl⟩:=Finset.mem_image.mp hv
      exact x.property
    have hle:(T.card:ℝ)≤A.card:=by exact_mod_cast Finset.card_le_card hTA
    have hscale:γ*T.card≤γ*A.card:=mul_le_mul_of_nonneg_left hle hγ.le
    have hh:=hcommon j (S.image Subtype.val) hsub (by rw [himage];exact hS)
    have heq:=ordinary_induced_common_card (spanningRestriction Q A) T S
    rw [hc,heq]
    exact hscale.trans hh
  · have hw:=ordinary_local_weights_induce_domain (spanningRestriction Q A) F T
      ((b*γ^m)/(T.card:ℝ)^m) (B/(T.card:ℝ)^m) η (data.weight j) hbound (data.loads j)
    change ∃wt:LocalOrdinaryCycle ((spanningRestriction Q A).induce (T:Set V))
        (F.induce (T:Set V)) Finset.univ (m+1)→ℝ,
      (∀C,(b*γ^m)/(Fintype.card {v:V // v∈T}:ℝ)^m≤wt C ∧
        wt C≤B/(Fintype.card {v:V // v∈T}:ℝ)^m) ∧
      (∀v,|1-hypergraphWeightedDegree localOrdinaryVertices wt v|≤η)
    rw [hc]
    exact hw
end Oberwolfach
