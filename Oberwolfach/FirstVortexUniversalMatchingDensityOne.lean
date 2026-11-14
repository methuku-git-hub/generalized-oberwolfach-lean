module

public import Oberwolfach.FirstVortexUniversalMatchingFullHost
public import Oberwolfach.ExpandedDensityOneClassFromSample

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance universalDensityOneFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n
local instance (priority := 2000) universalDensityOneSix:DecidableEq (Fin 6):=instDecidableEqFin 6

theorem first_vortex_universal_matching_density_one
    {n:ℕ} [Nonempty (Fin n)] {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d K r Dv mm:ℕ) (β ε:ℝ)
    (Vort:Vortex U P Dv β ε mm) (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (θ lamAssign eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ βList ξPart γLoss σLoss:ℝ)
    (weight:(Fin ((r+4)+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (z:MarkedExpandedActualOutcome (U:=U) π d) (L e₀:ℕ)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1) (hone:2*p+2*k+2*p₂+2*k₂+u=1) (hd:2≤d)
    (q:U→Bool→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Bool→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
    (ν:∀ω:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e),
      FiniteLaw (StartRetentionOutcome (rawStartHubSet π d (fun e=>ω (Sum.inr e)) false)
        (startRetentionMinimum (rawStartHubSet π d (fun e=>ω (Sum.inr e)) false))))
    (hpos:0<((FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)).sigma ν).mass z)
    (hreg:P.IsRegularOfDegree (2*Fintype.card U)) (hξ:0≤ξPart)
    (h:FirstVortexConcreteUniversalMatchedOutcome P π d K r Dv mm β ε Vort F hF θ lamAssign eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ βList ξPart γLoss σLoss weight w z L e₀):
    ∃D₀:MarkedReferenceDeletion P π d (fun x=>rawExpandedMarkedCollapse x (z.1 x)),
    ∃C:Finset (Finset (Fin n)⊕(Fin n×U)),
      longTerminalProtectedReserve P π d r z z.2 (Vort.extendedVertices 1) (Vort.extendedIndices 1)
        γLoss σLoss e₀ (Vort.extendedVertices (L+1)) (Vort.extendedIndices (L+1)) D₀ C ∧
    ∃Mhost:Fin n→Fin n→ℕ,∃Del:SimpleGraph (Fin n),
      LongClassMatchingDeletionWitness Δ P π d r z (Vort.extendedVertices 1) K θ Dv a γ eps βList F hF weight w D₀ C P Mhost Del ∧
      FirstVortexClassPreparedRetainedFullPackingOutcomeWithAllHubLoad P P π Dv mm d (r+4) β ε Vort F hF θ lamAssign eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ weight w z.1
        (startRetentionMinimum (rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false)) z.2 :=by
  have hState:=expanded_density_one_class_eq_host p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum hone d hd q hq hQ s hs hS ν P z hpos
  exact first_vortex_universal_matching_full_host P π d K r Dv mm β ε Vort F hF θ lamAssign eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ βList ξPart γLoss σLoss weight w z L e₀ hState hreg hξ h
end Oberwolfach
