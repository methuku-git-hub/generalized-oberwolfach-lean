module

public import Oberwolfach.OrdinaryProtectedTraceInvariant

@[expose] public section
/-! Every host represented by a protected deletion trace remains a subgraph
of the host from which the trace started. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_protected_trace_host_le
    (Q G:SimpleGraph V) (H Hs:V→U→Prop) (X T:ℕ→Finset V) (Z W:ℕ→Finset U)
    (cost deepCost:ℕ→ℝ) (n:ℕ) (A:Finset (Sym2 V⊕(V×U)))
    (htrace:OrdinaryProtectedTrace Q H X T Z W cost deepCost n A)
    (hstate:ordinaryHostResources G Hs=A):G≤Q := by
  obtain ⟨R,S,hist,_,_⟩:=htrace
  obtain ⟨hG,_⟩:=ordinaryHostResources_injective G (ordinaryHistoryRim Q R S n) Hs
    (ordinaryHistorySpokes H R S n) (hstate.trans hist.symm)
  rw [hG]
  exact sdiff_le
end Oberwolfach
