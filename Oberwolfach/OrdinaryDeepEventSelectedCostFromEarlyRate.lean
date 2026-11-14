module

public import Oberwolfach.OrdinaryDeepEventUniformEditWeights
public import Oberwolfach.OrdinarySelectedCostRate
public import Oberwolfach.OrdinarySameSampleSelectedCostWeights

@[expose] public section
/-! Every outcome in the deep common event satisfies the actual selected
cost-weight event when the deterministic cost bound is available. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_deep_event_selected_cost_from_early_rate
    (n qCount D mv m K d:ℕ) (β ε:ℝ) (P:SimpleGraph (Fin n))
    (Q:Vortex (Fin qCount) P D β ε mv) (π:Equiv.Perm (Fin n))
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (p pH pmin αcut c C b Bweight ξ ηHub Kdom a aLoad ρdeep θdeep cap eParent hParent εR εH:ℝ)
    (density tR tH:ℕ→ℝ) (s:Fin qCount→Bool→ℝ) (j:Bool)
    (R:(∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e)→Type)
    [∀σ,Fintype (R σ)]
    (μ:FiniteLaw (∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e))
    (ν:∀σ,FiniteLaw (R σ))
    (E:(Σσ:∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e,R σ)×(Sym2 (Fin n)→Bool)→Prop)
    (loss χinner χdeep χone χtwo χcut:ℝ)
    (rateActual:ℝ)
    (ρ₀ costRate:ℝ) (hcost:OrdinarySelectedCostRate ε ρ₀ cap d costRate)
    (hβ:0≤β) (hβ1:β≤1/4) (hreg:P.IsRegularOfDegree D) (hn:0<n)
    (hhalf:(n:ℝ)/2≤D) (hρlo:ρ₀ ≤ initialIndexDensity (Fin qCount) D)
    (hρhi:initialIndexDensity (Fin qCount) D≤1)
    (hr0:0≤rateActual) (hr:rateActual≤costRate):
    ∃mCost:ℕ,1≤mCost ∧ (mCost≤mv → ∀z,OrdinaryDeepRowsCutsEvent n qCount D mv m K d β ε P Q π hπ p pH pmin αcut c C b Bweight ξ ηHub Kdom a aLoad ρdeep θdeep cap eParent hParent εR εH density tR tH s j R μ ν E loss χinner χdeep χone χtwo χcut z →
      OrdinarySelectedCostWeightEvents Q π hπ m d (2*p) pH cap (eParent*ε) (hParent*ε)
        c (4*C/pmin^(3*m+1)) ηHub rateActual density tR tH s j
        (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) :=by
  obtain ⟨mCost,hmCost,hselect⟩:=hcost β hβ hβ1
  refine ⟨mCost,hmCost,?_⟩
  intro hmv z hz
  have hInner:OrdinaryUniformInnerHubEvent m P D mv d β ε Q π hπ (2*p) pH
      (eParent*ε) (hParent*ε) c (4*C/pmin^(3*m+1)) ηHub cap density tR tH s j
      (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)):=hz.1.1.1.1.2
  exact hselect (Fin n) (Fin qCount) Bool Bool P D mv hreg (by simpa using hn)
    (by simpa using hhalf) hρlo hρhi hmv Q π hπ m (2*p) pH (eParent*ε) (hParent*ε)
    c (4*C/pmin^(3*m+1)) ηHub density tR tH s j _ rateActual hr0 hr hInner
end Oberwolfach
