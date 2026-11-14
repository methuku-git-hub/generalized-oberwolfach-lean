module

public import Oberwolfach.FiniteHighEventsCommon

@[expose] public section
/-! Already assigned and still unembedded component vertices occupy disjoint
subsets of the same source factor. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {X:Type} [DecidableEq X]

theorem prescribed_source_component_size (Q A:Finset X) (as:List X) (ha:as.Nodup)
    (hsub:A∪as.toFinset⊆Q) (hdis:Disjoint A as.toFinset) (δ n:ℝ)
    (hQ:(Q.card:ℝ)≤δ*n):
    (A.card:ℝ)+as.length≤δ*n := by
  have hc:A.card+as.length≤Q.card:=by
    have hh:=Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdis,List.toFinset_card_of_nodup ha] at hh
    exact hh
  have hcR:((A.card:ℝ)+as.length)≤Q.card:=by exact_mod_cast hc
  exact hcR.trans hQ
end Oberwolfach
