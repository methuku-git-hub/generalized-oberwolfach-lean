module

public import Oberwolfach.MarkedFixedVortexParentDegrees
public import Oberwolfach.MarkedVortexBalanceIdentities

@[expose] public section
/-! The sampled reference event's full-parent and inner degree centres,
including their exact density identities, for fixed vortex domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε α:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_reference_degree_inputs
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V)
    (hD:(1/2+α)*Fintype.card V≤(D:ℝ)) (hα:0<α)
    (hρ:0 < initialIndexDensity U D) (hb:0≤β) (hbα:β≤α/8) (hb1:β≤1/4) (he:0<ε) (hm:0<m)
    (i:ℕ) (hi:i<Q.length) (s:ℝ) (r:ℕ) (hr:0<r):
    let W:=markedVortexVertexType Q i
    let Z:=markedVortexHubType Q i
    let I:=markedVortexInnerVertices Q i
    let J:=markedVortexInnerHubs Q i
    let ρ:=initialIndexDensity U D
    let Dbal:=2*(J.card:ℝ)/ρ
    let Dload:=2*(Fintype.card Z:ℝ)/ρ
    let p:=ρ*s/2
    let k:=p/(r:ℝ)
    (∀ x:W,(1/2+α/2)*(I.card:ℝ)≤
      (((G.comap (markedVortexVertexEmbedding Q i)).neighborFinset x∩I).card:ℝ)) ∧
    (∀ x:W,|(((G.comap (markedVortexVertexEmbedding Q i)).neighborFinset x∩I).card:ℝ)-Dbal|≤β*Fintype.card W) ∧
    (∀ x:W,(1/2+α/2)*(Fintype.card W:ℝ)≤((G.comap (markedVortexVertexEmbedding Q i)).degree x:ℝ)) ∧
    (∀ x:W,|((G.comap (markedVortexVertexEmbedding Q i)).degree x:ℝ)-Dload|≤β*Fintype.card W) ∧
    ((Fintype.card W:ℝ)/2≤Dload) ∧ (Dload≤2*Fintype.card W) ∧
    p*Dbal=s*J.card ∧ k*Dbal=(s/r)*J.card ∧
    (Fintype.card Z:ℝ)*(s/r)=Dload*k ∧ (Fintype.card Z:ℝ)*(s/r)*r=Dload*p:=by
  intro W Z I J ρ Dbal Dload p k
  have hinner:=marked_vortex_fixed_inner_degree_fields Q hreg hn hD hα hρ hb hbα hb1 he hm i hi
  have hparent:=marked_vortex_fixed_parent_degree_fields Q hreg hn hD hα hρ hb hbα hb1 he hm i hi
  have hcard:((I.card:ℝ)≤Fintype.card W):=by exact_mod_cast Finset.card_le_univ I
  have hscale:β*(I.card:ℝ)≤β*Fintype.card W:=mul_le_mul_of_nonneg_left hcard hb
  have hbal:=marked_vortex_density_centre_identities ρ s J.card (Fintype.card Z) r hρ hr
  refine ⟨hinner.1,?_,hparent.1,hparent.2.1,hparent.2.2.1,hparent.2.2.2,?_⟩
  · intro x
    exact (hinner.2.1 x).trans hscale
  · exact hbal
end Oberwolfach
