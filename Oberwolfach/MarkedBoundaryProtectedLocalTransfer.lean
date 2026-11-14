module

public import Oberwolfach.MarkedBoundaryRimLocalChanges
public import Oberwolfach.MarkedBoundarySpokeLocalChanges

@[expose] public section
/-! Transfer the actual boundary tests from the protected correction using
only outside-inner rim changes and first-inner spoke losses. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_boundary_protected_local_transfer
    (P:SimpleGraph V) (π:Equiv.Perm V) (d h:ℕ) (I A:Finset V) (J B:Finset U)
    (hAI:A⊆I) (hBJ:B⊆J) (hπ:∀v,π v∈I↔v∈I)
    (p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color)
    (errR errI δR δS:ℝ) (hR:0≤δR) (hS:0≤δS)
    (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (hr:MarkedRowsWithSpokes P π d h A p k q s g j errR σ H)
    (hi:MarkedIndicesWithSpokes π d h B q s g j errI σ H)
    (FR:SimpleGraph V)
    (hrim:∀mark v w,v∈I→w∈I→
      (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark v w=1 ↔
       markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark v w=1))
    (hchange:∀a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a)→markedPairPhysical π a∈FR.edgeFinset)
    (hFR:∀v,v∉I→(FR.degree v:ℝ)≤δR)
    (hspoke:∀b v u,v∈I→u∈J→(H b v u↔H' b v u))
    (hrowOutside:∀v,v∉I→(∑u∈J,if ¬(H false v u↔H' false v u) then (1:ℝ) else 0)≤δS)
    (hmark:∀v u,H true v u↔H' true v u)
    (hnoNew:∀u v,v∈I→H' false v u→H false v u)
    (hloss:∀u,((I.filter (fun v=>H false v u ∧ ¬H' false v u)).card:ℝ)≤δS):
    MarkedRowsWithSpokes P π d h A p k q s g j (errR+h*(δR+δS)) τ H' ∧
    MarkedIndicesWithSpokes π d h B q s g j (errI+h*δS) τ H' :=by
  have hrimLocal:=marked_boundary_rim_local_changes P π d I A hAI hπ σ τ FR δR hR hrim hchange hFR
  obtain ⟨hrow,hcol⟩:=marked_boundary_spoke_local_changes I A J B hAI hBJ H H' δS hS hspoke hrowOutside hmark hnoNew hloss
  exact marked_neighbourhoods_after_local_change P π d h A B p k q s g j errR errI δR δS δS hR hS hS σ τ H H' hr hi hrimLocal hrow hcol
end Oberwolfach
