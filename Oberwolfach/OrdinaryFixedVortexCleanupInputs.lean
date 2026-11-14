module

public import Oberwolfach.OrdinaryFixedVortexRowIndexEvent
public import Oberwolfach.OrdinaryVortexLevelParentDensityBalance

@[expose] public section
/-! A single fixed-vortex event supplies the actual local row and hub tests;
the original vortex supplies their parent density and balance means. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_fixed_vortex_cleanup_inputs
    (P F:SimpleGraph V) (D m:ℕ) (β ε θ α pR pH εR εH:ℝ)
    (Q:Vortex U P D β ε m) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d:ℕ) (s:U→Color→ℝ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
    (hn:0<Fintype.card V) (hreg:P.IsRegularOfDegree D)
    (hρ:0< initialIndexDensity U D) (hβ:0≤β) (hpH:0≤pH)
    (hdegree:(θ+α)*Fintype.card V≤D)
    (hgood:OrdinaryFixedVortexRowIndexEvent 3 d εR εH P F D m β ε Q π hπ pR pH s j σ):
    ∀i,i<Q.length→
      let I:=markedVortexInnerVertices Q i;let Z:=markedVortexInnerHubs Q i;
      let f:=markedVortexVertexEmbedding Q i;let g:=markedVortexHubEmbedding Q i;
      let ρ:=markedVortexPermutation Q π hπ i;
      (∀v,(θ+α-β/2)*I.card≤((I∩(P.comap f).neighborFinset v).card:ℝ)) ∧
      (∀v,|(initialIndexDensity U D*pH)*(I∩(P.comap f).neighborFinset v).card-
        2*pH*Z.card|≤(initialIndexDensity U D*pH)*β*I.card) ∧
      RawOrdinaryRows (P.comap f) ρ d 3 I pR (fun u=>s (g u)) j (εR*I.card)
        (ordinaryRawRestrictPair f g σ) ∧
      RawOrdinaryDomainIndices (F.comap f) ρ d 3 Z pH j (εH*Z.card)
        (ordinaryRawRestrictPair f g σ):=by
  intro i hi I Z f g ρ
  have hprofile:=ordinary_vortex_level_parent_density_balance P D m β ε θ α (initialIndexDensity U D) pH
    Q hn hreg rfl hρ hβ hpH hdegree i (by omega)
  have htests:=hgood i hi
  exact ⟨hprofile.1,hprofile.2,htests.1,htests.2⟩
end Oberwolfach
