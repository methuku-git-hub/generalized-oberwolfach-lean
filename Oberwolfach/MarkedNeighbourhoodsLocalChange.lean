module

public import Oberwolfach.MarkedModifiedPhysicalIncidence

@[expose] public section
/-! Boundary row and index tests can be transferred using changes counted
only on their actual test domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_neighbourhoods_after_local_change
    (P:SimpleGraph V) (π:Equiv.Perm V) (d h:ℕ) (A:Finset V) (B:Finset U)
    (p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color)
    (errR errI deltaR deltaV deltaU:ℝ) (hR:0≤deltaR) (hV:0≤deltaV) (hU:0≤deltaU)
    (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (hr:MarkedRowsWithSpokes P π d h A p k q s g j errR σ H)
    (hi:MarkedIndicesWithSpokes π d h B q s g j errI σ H)
    (hrim:∀a,(∑ x∈A,if ¬(rawMarkedPairRims P π d σ (markedRowRim a x)↔
      rawMarkedPairRims P π d τ (markedRowRim a x)) then (1:ℝ) else 0)≤deltaR)
    (hrow:∀a x,(∑u∈B,if ¬(H a x u↔H' a x u) then (1:ℝ) else 0)≤deltaV)
    (hcol:∀a u,(∑x∈A,if ¬(H a x u↔H' a x u) then (1:ℝ) else 0)≤deltaU):
    MarkedRowsWithSpokes P π d h A p k q s g j (errR+h*(deltaR+deltaU)) τ H' ∧
    MarkedIndicesWithSpokes π d h B q s g j (errI+h*deltaV) τ H' :=by
  have hr':=markedRows_rim_changes P π d h A p k q s g j errR deltaR hR σ τ H hr hrim
  have hr'':=markedRows_spoke_relation_changes P π d h A p k q s g j
    (errR+h*deltaR) deltaU hU τ H H' hr' hcol
  have hi':=markedIndices_rim_changes π d h B q s g j errI σ τ H hi
  have hi'':=markedIndices_spoke_relation_changes π d h B q s g j errI deltaV hV τ H H' hi' hrow
  refine ⟨?_,hi''⟩
  convert hr'' using 1 <;> ring
end Oberwolfach
