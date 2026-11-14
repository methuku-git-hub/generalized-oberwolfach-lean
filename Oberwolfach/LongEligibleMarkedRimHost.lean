module

public import Oberwolfach.LongEligibleMarkedIncomingChange
public import Oberwolfach.MarkedPhysicalHostContainment

@[expose] public section
/-! Both sides of the corrected residual partition remain inside the original
oriented class host. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_eligible_marked_rim_le_host
    {V E K:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype E] [Fintype K]
    (S Small:SimpleGraph V) (M:V→V→ℕ)
    (hphysical:∀x y,M x y+M y x=if S.Adj x y then 1 else 0)
    (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)
    (hE:∀e,longEligibleResidualArc M Small ⊥ (tail e,head e))
    (hK:∀e,longEligibleResidualArc M Small ⊥ (ktail e,π (khead e))):
    physicalEdgeGraph (markedPhysicalRimSet tail head ktail khead π)≤S:=by
  apply marked_physical_host_graph_le S tail head ktail khead π
  · intro e
    have h: M (tail e) (head e)=1:=(hE e).1
    have hs:=hphysical (tail e) (head e)
    split_ifs at hs with hh
    · exact hh
    · omega
  · intro e
    have h: M (ktail e) (π (khead e))=1:=(hK e).1
    have hs:=hphysical (ktail e) (π (khead e))
    split_ifs at hs with hh
    · exact hh
    · omega
end Oberwolfach
