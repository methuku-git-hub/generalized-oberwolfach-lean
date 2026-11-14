module

public import Oberwolfach.OrdinaryHubRowNonrootSupportBounds

@[expose] public section
/-! The root-cover wheels use no nonroot vertex or hub inside the protected
inner pair, so their contribution has no cross imbalance there. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {Q F:SimpleGraph V} {H:V→U→Prop}

theorem ordinary_triangle_hub_row_support_avoids_nonroot
    (nh nr:ℕ) (I T:Finset V) (J W:Finset U) (u:Fin nh→U) (x:Fin nr→V)
    (hx:∀i,x i∈T) (hu:∀i,u i∈W)
    (M:Finset (OrdinaryWheel Q F H 3))
    (hsupport:∀C∈M,(∃i,ordinaryWheelHub C=u i ∧ ∀v∈(ordinaryWheelRim C).support,v∈Finset.univ\I) ∨
      (∃i,x i∈(ordinaryWheelRim C).support ∧ ordinaryWheelHub C∈Finset.univ\J ∧
        ∀v∈(ordinaryWheelRim C).support,v=x i∨v∈Finset.univ\I)):
    (∀v∈I\T,∀w,¬(ordinaryWheelRimGraph M).Adj v w) ∧
    (∀u∈J\W,∀v,¬ordinaryPackingSpokes M v u) :=by
  constructor
  · intro v hv w hvw
    obtain ⟨C,hC,hCedge⟩:=(ordinaryWheelRimGraph_edges M s(v,w)).mp hvw
    have hvrim:v∈(ordinaryWheelRim C).support:=⟨w,hCedge⟩
    have hvI: v∈I:=(Finset.mem_sdiff.mp hv).1
    have hvT: v∉T:=(Finset.mem_sdiff.mp hv).2
    rcases hsupport C hC with ⟨i,_,hverts⟩|⟨i,_,_,hverts⟩
    · exact (Finset.mem_sdiff.mp (hverts v hvrim)).2 hvI
    · rcases hverts v hvrim with heq|houtside
      · exact hvT (heq ▸ hx i)
      · exact (Finset.mem_sdiff.mp houtside).2 hvI
  · intro a ha v hvu
    have haJ:a∈J:=(Finset.mem_sdiff.mp ha).1
    have haW:a∉W:=(Finset.mem_sdiff.mp ha).2
    obtain ⟨C,hC,hHub,_⟩:=hvu
    rcases hsupport C hC with ⟨i,hi,_⟩|⟨i,_,hi,_⟩
    · exact haW ((hHub.symm.trans hi) ▸ hu i)
    · exact (Finset.mem_sdiff.mp (hHub ▸ hi)).2 haJ
end Oberwolfach
