module

public import Oberwolfach.OrdinaryUnreservedDeletionBounds

@[expose] public section
/-! Two bounded physical deletions have degree at most the sum of their
individual bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A:Type} [Fintype A] [DecidableEq A]

theorem ordinary_physical_union_degree (C R:SimpleGraph A) (L M:ℝ)
    (hC:∀a,(C.degree a:ℝ)≤L) (hR:∀a,(R.degree a:ℝ)≤M):
    ∀a,((C⊔R).degree a:ℝ)≤L+M:=by
  intro a
  have hnat:=graph_degree_sup_le C R a
  have hcast:=(Nat.cast_le (α:=ℝ)).mpr hnat
  push_cast at hcast
  have hh:((C⊔R).degree a:ℝ)≤(C.degree a:ℝ)+(R.degree a:ℝ):=by
    convert hcast using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  linarith [hC a,hR a]
end Oberwolfach
