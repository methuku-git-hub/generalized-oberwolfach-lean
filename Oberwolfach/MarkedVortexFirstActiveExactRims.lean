module

public import Oberwolfach.MarkedRestrictedRimsExactOnProtected
public import Oberwolfach.MarkedVortexFirstActiveConfigurationRestrictHubs

@[expose] public section
/-! The corrected rim labels agree exactly on the first active vertex set,
including when the active tests use hubs outside the first inner hub set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_vortex_first_active_exact_rims
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [Nonempty V] [DecidableEq U]
    (G:SimpleGraph V) (D mm:ℕ) (β ε:ℝ) (Q:Vortex U G D β ε mm)
    (π:Equiv.Perm V) (hπ:∀i v,π v∈Q.extendedVertices i↔v∈Q.extendedVertices i)
    (d:ℕ) (σ τ:RawMarkedOutcome V U Γ Color)
    (hprotected:∀e:Sym2 V,e.toFinset⊆Q.extendedVertices 1→τ (Sum.inl e)=σ (Sum.inl e)):
    let f:=markedVortexActiveVertexEmbedding Q 1
    let g:=markedVortexNonDeeperHubToPhysical Q 0
    let ρ:=markedVortexActivePermutation Q π hπ 1;
    rawMarkedPairRims (G.comap f) ρ d (rawMarkedRestrictPair f g τ)=
      rawMarkedPairRims (G.comap f) ρ d (rawMarkedRestrictPair f g σ) :=by
  intro f g ρ
  apply marked_restricted_rims_exact_on_protected f g (Q.extendedVertices 1) ?_ σ τ hprotected (G.comap f) ρ d
  intro x
  exact x.val.property
end Oberwolfach
