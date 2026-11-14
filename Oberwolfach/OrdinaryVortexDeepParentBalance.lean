module

public import Oberwolfach.OrdinaryVortexBufferedNeighbourTransport

@[expose] public section
/-! The original vortex estimates give the parent mean balance on the
pair two levels down, for every vertex of the current parent. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_deep_parent_balance
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (D m:ℕ) (β ε pH:ℝ)
    (Q:Vortex U P D β ε m) (hn:0<Fintype.card V) (hreg:P.IsRegularOfDegree D)
    (hρ:0< initialIndexDensity U D) (hβ:0≤β) (hpH:0≤pH) (i:ℕ):
    let T:=ordinaryVortexBufferedVertices Q i 2;
    let W:=ordinaryVortexBufferedHubs Q i 2;
    let f:=markedVortexVertexEmbedding Q i;
    ∀v,|(initialIndexDensity U D*pH)*(T∩(P.comap f).neighborFinset v).card-
      2*pH*W.card|≤(initialIndexDensity U D*pH)*β*T.card:=by
  intro T W f v
  have hT:T.card=(Q.extendedVertices (i+2)).card:=by
    have hh:=congrArg Finset.card (ordinary_vortex_buffered_images Q i 2).1
    rw [Finset.card_image_of_injective _ (markedVortexVertexEmbedding Q i).injective] at hh
    exact hh
  have hW:W.card=(Q.extendedIndices (i+2)).card:=by
    have hh:=congrArg Finset.card (ordinary_vortex_buffered_images Q i 2).2
    rw [Finset.card_image_of_injective _ (markedVortexHubEmbedding Q i).injective] at hh
    exact hh
  have hc:((T∩(P.comap f).neighborFinset v).card:ℝ)=
      ((P.neighborFinset v.val∩Q.extendedVertices (i+2)).card:ℝ):=by
    rw [Finset.inter_comm,ordinary_vortex_buffered_neighbour_card Q i 2 v]
  have hv:v.val∈Q.extendedVertices ((i+2)-2):=by simpa using v.property
  have he:|((P.neighborFinset v.val∩Q.extendedVertices (i+2)).card:ℝ)-
      2*((Q.extendedIndices (i+2)).card:ℝ)/initialIndexDensity U D|≤β*(Q.extendedVertices (i+2)).card:=
    (Q.extended_estimates hreg hn hρ hβ (i+2)).2 v.val hv
  rw [←hT,←hW,←hc] at he
  have hmul:0≤ initialIndexDensity U D*pH:=mul_nonneg hρ.le hpH
  have heq:(initialIndexDensity U D*pH)*((T∩(P.comap f).neighborFinset v).card:ℝ)-2*pH*W.card=
      (initialIndexDensity U D*pH)*(((T∩(P.comap f).neighborFinset v).card:ℝ)-2*(W.card:ℝ)/initialIndexDensity U D):=by
    field_simp [hρ.ne']
    <;> ring
  rw [heq,abs_mul,abs_of_nonneg hmul]
  nlinarith only [mul_le_mul_of_nonneg_left he hmul]
end Oberwolfach
