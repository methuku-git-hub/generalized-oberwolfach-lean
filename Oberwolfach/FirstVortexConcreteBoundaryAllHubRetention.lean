module

public import Oberwolfach.FirstVortexConcreteBoundaryEvent
public import Oberwolfach.FirstVortexGlobalRetentionToLocal

@[expose] public section
/-! The global test in the concrete event supplies all-hub first-inner
retention on the very same sample, at the appropriately scaled tolerance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance concreteAllHubFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_concrete_boundary_all_hub_retention
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r Dv mm:ℕ) (β ε:ℝ)
    (Vort:Vortex U P Dv β ε mm) (θ ρ₀ BM:ℝ) (BO:Fin K→ℝ)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin ((r+4)+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (a γ eps Δ ξSeed ΔSeed ζret ζselect βList terr τerr ζlocal:ℝ)
    (z:MarkedExpandedActualOutcome (U:=U) π d) (Inner:Finset (Fin n))
    (hε:0<ε) (hε1:ε≤1) (hmm:0<mm) (hlocal:0≤ζlocal)
    (hscale:ζret≤ζlocal*ε/2)
    (hEvent:FirstVortexConcreteBoundaryEvent P π d r Dv mm β ε Vort θ ρ₀ BM BO F hF weight w
      a γ eps Δ ξSeed ΔSeed ζret ζselect βList terr τerr z Inner):
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (z.1 e)
    let t:=startRetentionMinimum (rawStartHubSet π d (fun e=>rawExpandedMarkedCollapse (Sum.inr e) (z.1 (Sum.inr e))) false)
    RetainedRestrictionLocalGood π d (fun e=>raw (Sum.inr e)) false t
      (Vort.extendedVertices 1) Finset.univ ζlocal z.2 ∧
    (∀u g,|rawIntervalHubStartCount π d g (fun e=>raw (Sum.inr e)) u-
      (n:ℝ)*longAssignedIntervalProbability F hF K (r+4) θ u g/d|<(n:ℝ)^(3/4:ℝ)/d) :=by
  dsimp only [FirstVortexConcreteBoundaryEvent] at hEvent
  dsimp only
  have hglobal:RetainedRestrictionGood π d (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (z.1 (Sum.inr e))) false
    (startRetentionMinimum (rawStartHubSet π d (fun e=>rawExpandedMarkedCollapse (Sum.inr e) (z.1 (Sum.inr e))) false))
    (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζret z.2 := hEvent.2.2.2.2.1.1
  constructor
  · exact first_vortex_global_retention_to_local P Dv mm β ε Vort hε hε1 hmm π d _ false _ z.2 ζret ζlocal hlocal hscale hglobal
  · exact hEvent.2.2.1.2
end Oberwolfach
