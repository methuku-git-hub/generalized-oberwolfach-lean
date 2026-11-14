module

public import Oberwolfach.OrdinaryUnreservedDeletionBounds
public import Oberwolfach.OrdinaryRestrictedConfigurationCounts

@[expose] public section
/-! Original isolator and transfer counts survive removal of the inner pair
and a bounded-degree physical reserve. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_unreserved_configuration_counts
    (P Q F:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U) (R:SimpleGraph (V⊕U))
    (r k:ℕ) (hr:3≤r) (hk:4≤k) (θ α β₀ β ξ ζ:ℝ)
    (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V) (hξ:0≤ξ) (hζ:0≤ζ)
    (hX:(X.card:ℝ)≤ξ*Fintype.card V) (hZ:(Z.card:ℝ)≤ξ*Fintype.card V)
    (hR:∀w,(R.degree w:ℝ)≤ζ*Fintype.card V)
    (hparentI:∀x y,Q.Adj x y→β₀*(Fintype.card V:ℝ)^(k-1)≤
      (Fintype.card (OrdinaryIsolatorConfiguration P Q F H k θ α x y):ℝ))
    (hparentT:∀v (i j:{u // H v u}),i.val≠j.val→β₀*(Fintype.card V:ℝ)^(r^2)≤
      (Fintype.card (OrdinaryTransferConfiguration hr Q F H v i.val j.val):ℝ))
    (hsmallI:8*((ξ+ζ)*Fintype.card V)≤(β₀-β)*Fintype.card V)
    (hsmallT:5*(r:ℝ)^4*((ξ+ζ)*Fintype.card V)≤(β₀-β)*Fintype.card V):
    (∀x y,(ordinaryUnreservedRim Q X R).Adj x y→β*(Fintype.card V:ℝ)^(k-1)≤
      (Fintype.card (OrdinaryIsolatorConfiguration P (ordinaryUnreservedRim Q X R) F
        (ordinaryUnreservedSpokes H X Z R) k θ α x y):ℝ)) ∧
    (∀v (i j:{u // ordinaryUnreservedSpokes H X Z R v u}),i.val≠j.val→β*(Fintype.card V:ℝ)^(r^2)≤
      (Fintype.card (OrdinaryTransferConfiguration hr (ordinaryUnreservedRim Q X R) F
        (ordinaryUnreservedSpokes H X Z R) v i.val j.val):ℝ)):=by
  let D:=ordinaryUnreservedRimDeletion Q X R
  let E:=ordinaryUnreservedSpokeDeletion X Z R
  let d:ℝ:=(ξ+ζ)*Fintype.card V
  have hd:0≤d:=by dsimp [d];positivity
  have hb:=ordinary_unreserved_deletion_degree_bounds Q X Z R ξ ζ hX hZ hR
  have hEout:∀v,(∑u,bipAdj E v u)≤d:=by
    intro v
    simpa [bipAdj,Finset.sum_boole,d,E] using hb.2.1 v
  have hEin:∀u,(∑v,bipAdj E v u)≤d:=by
    intro u
    simpa [bipAdj,Finset.sum_boole,d,E] using hb.2.2 u
  have hc:=ordinary_restricted_configuration_counts P Q F D H E r k hr hk θ α β₀ β d hn hu hd
    hb.1 hEout hEin hparentI hparentT hsmallI hsmallT
  have he:=ordinary_unreserved_as_deletion Q H X Z R
  rw [he.1,he.2]
  exact hc
end Oberwolfach
