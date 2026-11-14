module

public import Oberwolfach.LongTerminalFullHostContinuation
public import Oberwolfach.FirstVortexLongSelectorMatchingDensityOne

@[expose] public section
/-! Positive mass in the exact density-one selector gives the full host for
any continuation attached to its fixed reserve. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance terminalDensityFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n
local instance (priority := 2000) terminalDensitySix:DecidableEq (Fin 6):=instDecidableEqFin 6

theorem long_terminal_density_one_continuation
    {n:ℕ} [Nonempty (Fin n)] {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r Dv mm:ℕ) (β ε:ℝ)
    (Vort:Vortex U P Dv β ε mm) (ξPart γLoss σLoss:ℝ)
    (z:MarkedExpandedActualOutcome (U:=U) π d) (L e₀:ℕ)
    (D₀:MarkedReferenceDeletion P π d (fun x=>rawExpandedMarkedCollapse x (z.1 x)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U)))
    (hTerminal:longTerminalProtectedReserve P π d r z z.2 (Vort.extendedVertices 1) (Vort.extendedIndices 1)
      γLoss σLoss e₀ (Vort.extendedVertices (L+1)) (Vort.extendedIndices (L+1)) D₀ C)
    (sfrac:ℝ) (aWeight bWeight:U→ℝ) (hDv:0<Dv) (hDensity:initialIndexDensity U Dv=1)
    (p k p₂ k₂ u:ℝ)
    (hpEq:p=initialIndexDensity U Dv*(1/100)/2) (hkEq:k=initialIndexDensity U Dv*sfrac/2)
    (hp₂Eq:p₂=(∑w,bWeight w)/(Dv:ℝ)) (hk₂Eq:k₂=(∑w,aWeight w)/(Dv:ℝ))
    (huEq:u=2*(∑w,(1-1/100-sfrac-aWeight w-bWeight w))/(Dv:ℝ))
    (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1) (hd:2≤d)
    (q:U→Bool→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Bool→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
    (ν:∀ω:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e),
      FiniteLaw (StartRetentionOutcome (rawStartHubSet π d (fun e=>ω (Sum.inr e)) false)
        (startRetentionMinimum (rawStartHubSet π d (fun e=>ω (Sum.inr e)) false))))
    (hpos:0<((FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)).sigma ν).mass z)
    (hreg:P.IsRegularOfDegree Dv) (hξ:0≤ξPart)
    (Continuation:SimpleGraph (Fin n)→Prop)
    (hFor:∀S:SimpleGraph (Fin n),S≤P→S.IsRegularOfDegree (2*Fintype.card U)→
      (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξPart*n)→
      (∀x∈Vort.extendedVertices 1,∀y∈Vort.extendedVertices 1,S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)→
      markedResourceRimGraph C≤S→Continuation S):
    Continuation P :=by
  have hD:(Dv:ℝ)≠0:=by exact_mod_cast (Nat.ne_of_gt hDv)
  have hsize:initialIndexDensity U Dv*(Dv:ℝ)=2*Fintype.card U:=by
    simp [initialIndexDensity,hD]
  have hone:2*p+2*k+2*p₂+2*k₂+u=1:=by
    rw [hpEq,hkEq,hp₂Eq,hk₂Eq,huEq]
    exact long_selector_density_one_mass (initialIndexDensity U Dv) (Dv:ℝ) sfrac aWeight bWeight hD hsize hDensity
  have hState:=expanded_density_one_class_eq_host p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum hone d hd q hq hQ s hs hS ν P z hpos
  have hreg':P.IsRegularOfDegree (2*Fintype.card U):=initial_density_one_regular_host P Dv hDv hreg hDensity
  exact long_terminal_full_host_continuation P π d r Dv mm β ε Vort ξPart γLoss σLoss z L e₀ D₀ C hTerminal hState hreg' hξ Continuation hFor
end Oberwolfach
