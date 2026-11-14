module

public import Oberwolfach.ProtectedRegularSample

@[expose] public section
/-! The protected binary partition property as an event of the colour map. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def GroupedProtectedPartitionEvent {n:ℕ} (P Z:SimpleGraph (Fin n))
    (m:Fin 2→ℕ) (B:ℕ) (ξ:ℝ) (col:Sym2 (Fin n)→Fin 2):Prop:=
  ∀A:SimpleGraph (Fin n),(∀v,A.degree v≤B)→∃H:Fin 2→SimpleGraph (Fin n),
    EdgePartition P H ∧ (∀a,(H a).IsRegularOfDegree (2*m a)) ∧
    (∀a x y,(Z⊔A).Adj x y→((H a).Adj x y↔(edgeColourGraph P col a).Adj x y)) ∧
    (∀a x,((Finset.univ.filter (fun y=>Xor ((H a).Adj x y) ((edgeColourGraph P col a).Adj x y))).card:ℝ)≤ξ*n)
end Oberwolfach
