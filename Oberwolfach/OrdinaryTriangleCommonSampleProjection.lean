module

public import Oberwolfach.OrdinaryTriangleCommonSampleBundle

@[expose] public section
/-! Extract the retained prior from the named triangle common sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_common_sample_retains_prior
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (D vsize d:ℕ) (β ε:ℝ)
    (Q:Vortex U P D β ε vsize) (π:Equiv.Perm (Fin n))
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (εR εH pR pH θsample κ αcut pmin δcap βe βh b Bweight ηHub tpot:ℝ)
    (s:U→Bool→ℝ) (j:Bool)
    (weight:∀i,markedVortexVertexType Q i→Sym2 (markedVortexVertexType Q i⊕markedVortexHubType Q i)→ℝ)
    (m aK bK:ℕ) (ξCorr:ℝ)
    {R:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)→Type}
    (E:(Σσ,R σ)→Prop) (z:(Σσ,R σ)×(Sym2 (Fin n)→Bool)) :
    OrdinaryTriangleCommonSampleBundle P D vsize d β ε Q π hπ εR εH pR pH θsample κ αcut pmin δcap
      βe βh b Bweight ηHub tpot s j weight m aK bK ξCorr E z → E z.1 :=by
  intro h
  exact h.1.1.1.1.1.1.1
end Oberwolfach
