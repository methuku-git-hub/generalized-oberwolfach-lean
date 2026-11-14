module

public import Oberwolfach.OrdinaryRootFirstGeneralProtectedInnerExtensions
public import Oberwolfach.OrdinaryProtectedCoverDownCostMono

@[expose] public section
/-! The numeric inputs for completing a general wheel on the actual
    root-first cleaned host, including its protected-trace budget. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def OrdinaryGeneralRootFirstAsymmetricMargins
    (m:ℕ) (Q Qfactor F:SimpleGraph V) (H Hfactor:V→U→Prop) (X T:Finset V) (Z W:Finset U)
    (η ell t ν:ℝ) (D:OrdinaryRootCoverData Q F H X T Z W (m+1) η ell)
    (σ:Sym2 (V⊕U)→Bool) (O:OrdinaryRootFirstCleanupOutcome Q F H X T Z W (m+1) η ell t ν D σ)
    (p ρ ζh ζe n εsup βe budget sampledCover:ℝ):Prop :=
  ordinaryPhysicalGraph Qfactor Hfactor≤spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z) ∧
  (p+εsup)*Fintype.card (V⊕U)+(t+ν)≤ρ*Fintype.card (V⊕U) ∧
  (p^2+εsup)*Fintype.card (V⊕U)+2*(t+ν)≤ρ^2*Fintype.card (V⊕U) ∧
  (∀j:{u:U // u∉Z},t+ν+sampledCover≤ζh*(p*(ordinaryBoundaryHubSet H Z X j).card)) ∧
  t+ν+sampledCover≤ζe*(p*n) ∧
  (∀j:{u:U // u∉Z},2*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))+
    2*(Nat.ceil (4*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))):ℝ)+(ν+η)≤ζh*(p*(ordinaryBoundaryHubSet H Z X j).card)) ∧
  2*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))+
    2*(Nat.ceil (4*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))):ℝ)+(ν+η)≤ζe*(p*n) ∧
  ∃Dmax Kcap:ℕ,0<Kcap ∧ ρ*Fintype.card (V⊕U)≤(Dmax:ℝ) ∧
    ∃Lconf:ℝ,0≤Lconf ∧ (∀v,(F.degree v:ℝ)≤Lconf) ∧
    let H₂:=ordinaryRootFirstCleanRemainderSpokes Q F H X T Z W (m+1) η ell t ν D σ O;
    ((Fintype.card (Σi:{v:V // v∉X},ordinaryBoundaryRowSet H₂ X Z i)*(m+1):ℕ):ℝ)/(Kcap:ℝ)+
      (((m+1:ℕ):ℝ)+3)*(Lconf+1)+2*(2*(ρ*Fintype.card (V⊕U))+2*((Kcap+Dmax:ℕ):ℝ))+
      (Dmax:ℝ)+((Dmax*(m+1):ℕ):ℝ)+3*Dmax<βe*Fintype.card (V⊕U)-3*ν-T.card ∧
    ν+η+(2*(ρ*Fintype.card (V⊕U))+((3*(Kcap+Dmax)+Dmax*(m+1):ℕ):ℝ))≤budget

end Oberwolfach
