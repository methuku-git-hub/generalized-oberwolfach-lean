module

public import Oberwolfach.LongReservedComponentPathFamily

@[expose] public section
/-! The manuscript's summed floor capacity gives an injective assignment
of requests to blocks across the specified components. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_reserved_requests_fit_blocks
    {J I:Type*} [Fintype J] [Fintype I] (capacity:I→ℕ)
    (hcapacity:Fintype.card J≤∑i,capacity i):
    Nonempty (J↪Σi:I,Fin (capacity i)) := by
  apply Function.Embedding.nonempty_of_card_le
  simpa only [Fintype.card_sigma,Fintype.card_fin] using hcapacity
end Oberwolfach
