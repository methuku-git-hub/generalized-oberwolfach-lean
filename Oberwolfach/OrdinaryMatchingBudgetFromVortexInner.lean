module

public import Oberwolfach.OrdinaryVortexCertificateMatchingThreshold

@[expose] public section
/-! The uniform local size bound itself supplies the global size needed to
absorb the fixed matching conflict loss. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_matching_budget_from_vortex_inner
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    {P:SimpleGraph V} {D mv:ℕ} {β ε:ℝ} (Q:Vortex U P D β ε mv)
    (i M d:ℕ) (η cost:ℝ)
    (hthreshold:∀n:ℕ,M≤n→∀x:ℝ,x≤14*η*n→x+2*((3*d:ℕ):ℝ)≤15*η*n)
    (hinner:M≤(markedVortexInnerVertices Q i).card)
    (hcost:cost≤14*η*Fintype.card V):
    cost+2*((3*d:ℕ):ℝ)≤15*η*Fintype.card V :=by
  have hlocal:(markedVortexInnerVertices Q i).card≤Fintype.card (markedVortexVertexType Q i):=
    Finset.card_le_univ _
  have hglobal:Fintype.card (markedVortexVertexType Q i)≤Fintype.card V:=
    Fintype.card_le_of_injective (markedVortexVertexEmbedding Q i) (markedVortexVertexEmbedding Q i).injective
  exact hthreshold (Fintype.card V) (hinner.trans (hlocal.trans hglobal)) cost hcost
end Oberwolfach
