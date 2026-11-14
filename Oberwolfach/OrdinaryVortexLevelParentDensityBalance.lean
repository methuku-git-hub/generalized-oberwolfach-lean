module

public import Oberwolfach.MarkedFixedVortexNeighbourTransport

@[expose] public section
/-! Every nonterminal vortex level inherits density and assigned parent
    balance on the actual next inner pair, for every current-level root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_level_parent_density_balance
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (D m:ℕ) (β ε θ α ρ pH:ℝ)
    (Q:Vortex U P D β ε m) (hn:0<Fintype.card V) (hreg:P.IsRegularOfDegree D)
    (hρ:ρ=initialIndexDensity U D) (hρpos:0<ρ) (hβ:0≤β) (hpH:0≤pH)
    (hdegree:(θ+α)*Fintype.card V≤D) (i:ℕ) (hi:i+1≤Q.length):
    let I:=markedVortexInnerVertices Q i;
    let Z:=markedVortexInnerHubs Q i;
    let Plevel:=P.comap (markedVortexVertexEmbedding Q i);
    (∀v,(θ+α-β/2)*I.card≤((I∩Plevel.neighborFinset v).card:ℝ)) ∧
    (∀v,|(ρ*pH)*(I∩Plevel.neighborFinset v).card-2*pH*Z.card|≤(ρ*pH)*β*I.card) := by
  intro I Z Plevel
  have hnR:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
  have hD:(θ+α)≤(D:ℝ)/Fintype.card V:=(le_div_iff₀ hnR).2 (by simpa [mul_comm] using hdegree)
  have hIcard:I.card=(Q.vertices (i+1)).card:=by
    have hh:=congrArg Finset.card (marked_vortex_inner_images Q i).1
    rw [Finset.card_image_of_injective _ (markedVortexVertexEmbedding Q i).injective,
      Q.extendedVertices_eq hi] at hh
    exact hh
  have hZcard:Z.card=(Q.indices (i+1)).card:=by
    have hh:=congrArg Finset.card (marked_vortex_inner_images Q i).2.2.1
    rw [Finset.card_image_of_injective _ (markedVortexHubEmbedding Q i).injective,
      Q.extendedIndices_eq hi] at hh
    exact hh
  have hI:(0:ℝ)≤I.card:=by positivity
  have hρp:0≤ρ*pH:=mul_nonneg hρpos.le hpH
  constructor
  · intro v
    have hv:v.val∈Q.vertices ((i+1)-2):=by
      have hv':v.val∈Q.extendedVertices ((i+1)-2):=Q.extendedVertices_subset (by omega) v.property
      rwa [Q.extendedVertices_eq (by omega : (i+1)-2≤Q.length)] at hv'
    have hcounts:((I∩Plevel.neighborFinset v).card:ℝ)=
        ((P.neighborFinset v.val∩Q.vertices (i+1)).card:ℝ):=by
      rw [Finset.inter_comm,marked_vortex_inner_neighbour_card Q i v,Q.extendedVertices_eq hi]
    have hdeg:=Q.degrees (i+1) hi (by omega) v.val hv
    have hcoeff:=mul_le_mul_of_nonneg_right hD hI
    rw [← hIcard,← hcounts] at hdeg
    have hh:=(abs_le.mp hdeg).1
    nlinarith only [hcoeff,hh]
  · intro v
    have hv:v.val∈Q.vertices ((i+1)-2):=by
      have hv':v.val∈Q.extendedVertices ((i+1)-2):=Q.extendedVertices_subset (by omega) v.property
      rwa [Q.extendedVertices_eq (by omega : (i+1)-2≤Q.length)] at hv'
    have hcounts:((I∩Plevel.neighborFinset v).card:ℝ)=
        ((P.neighborFinset v.val∩Q.vertices (i+1)).card:ℝ):=by
      rw [Finset.inter_comm,marked_vortex_inner_neighbour_card Q i v,Q.extendedVertices_eq hi]
    have hcent: |((P.neighborFinset v.val∩Q.vertices (i+1)).card:ℝ)-
        2*((Q.indices (i+1)).card:ℝ)/ρ|≤β*(Q.vertices (i+1)).card:=by
      rw [hρ]
      exact (Q.centre_estimates (i+1) hi (by omega)).2 v.val hv
    rw [← hIcard,← hZcard,← hcounts] at hcent
    have heq:(ρ*pH)*((I∩Plevel.neighborFinset v).card:ℝ)-2*pH*Z.card =
      (ρ*pH)*(((I∩Plevel.neighborFinset v).card:ℝ)-2*(Z.card:ℝ)/ρ):=by
      field_simp [hρpos.ne']
      <;> ring
    rw [heq,abs_mul,abs_of_nonneg hρp]
    nlinarith only [mul_le_mul_of_nonneg_left hcent hρp]
end Oberwolfach
