module

public import Oberwolfach.OrdinaryVortexBufferedNeighbourTransport
public import Oberwolfach.VortexExtendedLookback

@[expose] public section
/-! The original vortex estimates give the parent mean balance on the
pair two levels down, for every vertex of the current parent. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_lookback_parent_balance
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (D m t:ℕ) (β ε pH:ℝ)
    (Q:VortexLookback U P D β ε m t) (hn:0<Fintype.card V) (hreg:P.IsRegularOfDegree D)
    (hρ:0< initialIndexDensity U D) (hβ:0≤β) (hpH:0≤pH) (i:ℕ):
    let T:=ordinaryVortexBufferedVertices Q.toVortex i (t+1);
    let W:=ordinaryVortexBufferedHubs Q.toVortex i (t+1);
    let f:=markedVortexVertexEmbedding Q.toVortex i;
    ∀v,|(initialIndexDensity U D*pH)*(T∩(P.comap f).neighborFinset v).card-
      2*pH*W.card|≤(initialIndexDensity U D*pH)*β*T.card:=by
  intro T W f v
  have hT:T.card=(Q.toVortex.extendedVertices (i+(t+1))).card:=by
    have hh:=congrArg Finset.card (ordinary_vortex_buffered_images Q.toVortex i (t+1)).1
    rw [Finset.card_image_of_injective _ (markedVortexVertexEmbedding Q.toVortex i).injective] at hh
    exact hh
  have hW:W.card=(Q.toVortex.extendedIndices (i+(t+1))).card:=by
    have hh:=congrArg Finset.card (ordinary_vortex_buffered_images Q.toVortex i (t+1)).2
    rw [Finset.card_image_of_injective _ (markedVortexHubEmbedding Q.toVortex i).injective] at hh
    exact hh
  have hc:((T∩(P.comap f).neighborFinset v).card:ℝ)=
      ((P.neighborFinset v.val∩Q.toVortex.extendedVertices (i+(t+1))).card:ℝ):=by
    rw [Finset.inter_comm,ordinary_vortex_buffered_neighbour_card Q.toVortex i (t+1) v]
  have hv:v.val∈Q.toVortex.extendedVertices ((i+(t+1))-(t+1)):=by simpa using v.property
  have he:|((P.neighborFinset v.val∩Q.toVortex.extendedVertices (i+(t+1))).card:ℝ)-
      2*((Q.toVortex.extendedIndices (i+(t+1))).card:ℝ)/initialIndexDensity U D|≤β*(Q.toVortex.extendedVertices (i+(t+1))).card:=
    (Q.extended_centre_estimates_lookback (i+(t+1)) (by omega)).2 v.val hv
  rw [←hT,←hW,←hc] at he
  have hmul:0≤ initialIndexDensity U D*pH:=mul_nonneg hρ.le hpH
  have heq:(initialIndexDensity U D*pH)*((T∩(P.comap f).neighborFinset v).card:ℝ)-2*pH*W.card=
      (initialIndexDensity U D*pH)*(((T∩(P.comap f).neighborFinset v).card:ℝ)-2*(W.card:ℝ)/initialIndexDensity U D):=by
    field_simp [hρ.ne']
    <;> ring
  rw [heq,abs_mul,abs_of_nonneg hmul]
  nlinarith only [mul_le_mul_of_nonneg_left he hmul]
end Oberwolfach
