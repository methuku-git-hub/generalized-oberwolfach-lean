module

public import Oberwolfach.OrdinaryInducedPairEmbedding
public import Oberwolfach.OrdinaryRootResources

@[expose] public section
/-! A globally balanced divisible host supported on a row/hub pair remains
exactly balanced and divisible when reindexed to that pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_supported_host_induced_exact_balance
    (G:SimpleGraph V) (H:V→U→Prop) (I:Finset V) (B:Finset U) (r:ℕ)
    (hsupport:ordinaryHostResources G H⊆ordinaryRootResources I B)
    (hbal:∀v,G.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>H v u)).card):
    (∀v:I,(G.induce (I:Set V)).degree v=2*(Finset.univ.filter (fun u:B=>H v.val u.val)).card) ∧
    (∀u:B,r∣(Finset.univ.filter (fun v:I=>H v.val u.val)).card) := by
  have hrim:∀v w,G.Adj v w→v∈I ∧ w∈I:=by
    intro v w hvw
    have he:Sum.inl s(v,w)∈ordinaryHostResources G H:=by
      exact (ordinaryHostResources_rim G H _).mpr hvw
    exact (ordinaryRootResources_rim_iff I B v w).mp (hsupport he)
  have hspoke:∀v u,H v u→v∈I ∧ u∈B:=by
    intro v u hvu
    exact (ordinaryRootResources_spoke_iff I B v u).mp (hsupport ((ordinaryHostResources_spoke G H v u).mpr hvu))
  let φ:I↪V:=⟨Subtype.val,Subtype.val_injective⟩
  let ψ:B↪U:=⟨Subtype.val,Subtype.val_injective⟩
  let Hloc:=fun v:I=>fun u:B=>H v.val u.val
  have hmap:ordinaryMappedSpokes Hloc φ ψ=H:=by
    rw [ordinary_induced_spokes_map]
    funext v u
    apply propext
    constructor
    · exact fun h=>h.1
    · intro h
      exact ⟨h,(hspoke v u h).1,(hspoke v u h).2⟩
  have hrow:∀v:I,(Finset.univ.filter (H v.val)).card=(Finset.univ.filter (fun u:B=>H v.val u.val)).card:=by
    intro v
    have hh:=congrArg Finset.card (ordinaryMappedSpokes_row Hloc φ ψ v)
    rw [Finset.card_image_of_injective _ ψ.injective] at hh
    rw [hmap] at hh
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hcol:∀u:B,(Finset.univ.filter (fun v=>H v u.val)).card=(Finset.univ.filter (fun v:I=>H v.val u.val)).card:=by
    intro u
    have hh:=congrArg Finset.card (ordinaryMappedSpokes_column Hloc φ ψ u)
    rw [Finset.card_image_of_injective _ φ.injective] at hh
    rw [hmap] at hh
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  constructor
  · intro v
    have hnb:G.neighborSet v.val⊆(I:Set V):=by
      intro w hw
      exact (hrim v.val w hw).2
    have hd:((G.induce (I:Set V)).degree v)=G.degree v.val:=by
      convert G.degree_induce_of_neighborSet_subset hnb using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    rw [hd,hbal v.val,hrow v]
  · intro u
    rw [←hcol u]
    exact hdiv u.val
end Oberwolfach
