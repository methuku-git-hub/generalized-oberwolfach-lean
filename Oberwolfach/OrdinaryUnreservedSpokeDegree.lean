module

public import Oberwolfach.OrdinaryUnreservedCutsFromReserve
public import Oberwolfach.MarkedPhysicalDeletionExtensions

@[expose] public section
/-! Removing the protected inner rectangle and the physical reserve costs at
most the inner hub count and the reserve degree in each spoke row. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_unreserved_spoke_degree
    (H:V→U→Prop) (X:Finset V) (Z:Finset U) (R:SimpleGraph (V⊕U)) (β₀ β ξ ζ:ℝ)
    (hparent:∀v,β₀*Fintype.card V≤((Finset.univ.filter (H v)).card:ℝ))
    (hZ:(Z.card:ℝ)≤ξ*Fintype.card V)
    (hR:∀v,(R.degree (Sum.inl v):ℝ)≤ζ*Fintype.card V)
    (hmargin:β+ξ+ζ≤β₀):
    ∀v,β*Fintype.card V≤((Finset.univ.filter (ordinaryUnreservedSpokes H X Z R v)).card:ℝ):=by
  intro v
  have hz:((Finset.univ.filter (fun u:U=>u∈Z)).card:ℝ)≤ξ*Fintype.card V:=by simpa using hZ
  have hr:((Finset.univ.filter (fun u=>R.Adj (Sum.inl v) (Sum.inr u))).card:ℝ)≤ζ*Fintype.card V:=by
    exact (Nat.cast_le.mpr (ordinary_physical_spoke_row_le_degree R v)).trans (hR v)
  have hh:=finite_predicate_delete_two (H v) (fun u:U=>u∈Z) (fun u=>R.Adj (Sum.inl v) (Sum.inr u))
    (ξ*Fintype.card V) (ζ*Fintype.card V)
    (by convert hz using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by convert hr using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  have hsub:(Finset.univ.filter (fun u=>H v u∧¬u∈Z∧¬R.Adj (Sum.inl v) (Sum.inr u)))⊆
      Finset.univ.filter (ordinaryUnreservedSpokes H X Z R v):=by
    intro u hu
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,ordinaryUnreservedSpokes] at hu ⊢
    exact ⟨hu.1,fun h=>hu.2.1 h.2,hu.2.2⟩
  have hs:((Finset.univ.filter (fun u=>H v u∧¬u∈Z∧¬R.Adj (Sum.inl v) (Sum.inr u))).card:ℝ)≤
      (Finset.univ.filter (ordinaryUnreservedSpokes H X Z R v)).card:=by
    exact_mod_cast Finset.card_le_card hsub
  have hm:=mul_le_mul_of_nonneg_right hmargin (Nat.cast_nonneg (Fintype.card V): (0:ℝ)≤_)
  let A:=Finset.univ.filter (H v)
  let T:=Finset.univ.filter (fun u=>H v u∧¬u∈Z∧¬R.Adj (Sum.inl v) (Sum.inr u))
  have hp:β₀*Fintype.card V≤(A.card:ℝ):=by
    convert hparent v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hh':(A.card:ℝ)-ξ*Fintype.card V-ζ*Fintype.card V≤(T.card:ℝ):=by
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hs':(T.card:ℝ)≤(Finset.univ.filter (ordinaryUnreservedSpokes H X Z R v)).card:=by
    convert hs using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  nlinarith only [hp,hh',hs',hm]
end Oberwolfach
