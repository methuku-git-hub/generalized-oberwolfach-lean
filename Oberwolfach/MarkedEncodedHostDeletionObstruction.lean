module

public import Oberwolfach.MarkedHostRawEncoding
public import Oberwolfach.RawMarkedRimDeletion

@[expose] public section

/-! An encoded typed host can add a physical rim coordinate outside the
protected set. A raw deletion can never create a previously absent rim. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem encoded_host_not_rim_deletion_of_absent_edge
    (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)
    (σ:RawMarkedOutcome V U Γ Color) (I:Finset V) (e:Sym2 V)
    (hout:¬e.toFinset⊆I) (habsent:σ (Sum.inl e)=none)
    (hhost:∃ a:E⊕K,markedHostPhysicalCoordinate tail head ktail khead π a=e):
    ∀ D:Finset (Sym2 V),rawMarkedEncodeHost tail head ktail khead π σ I≠rawMarkedDeleteRims σ D := by
  intro D heq
  have hh:=congrFun heq (Sum.inl e)
  rw [rawMarkedEncodeHost,ite_eq_right hout,markedHostRimEncoding,dite_eq_left hhost] at hh
  simp only [rawMarkedDeleteRims,habsent,ite_self] at hh
  cases hh
end Oberwolfach
