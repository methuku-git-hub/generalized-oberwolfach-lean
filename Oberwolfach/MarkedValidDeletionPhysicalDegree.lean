module

public import Oberwolfach.MarkedReferenceDeletionState
public import Oberwolfach.MarkedUnchangedInnerSample

@[expose] public section

/-! A valid reference deletion already controls the actual physical rim graph.
This lets later matching and class choices use the very same deletion chosen by
the level-chain construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]

theorem marked_valid_deletion_physical_degree
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop) (X:Finset V) (Y:Finset U) (γ σloss:ℝ)
    (D:MarkedReferenceDeletion P π d σ) (hvalid:D.Valid H m X Y γ σloss) :
    (∀v, ((markedSampleArcSetGraph P π d σ D.arcs).degree v:ℝ)≤γ) ∧
    (∀x∈X,∀y∈X,¬(markedSampleArcSetGraph P π d σ D.arcs).Adj x y) := by
  let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
  let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
  let tail:=fun e:E=>e.val.1
  let head:=fun e:E=>e.val.2
  let ktail:=fun e:K=>e.val.1
  let khead:=fun e:K=>e.val.2
  let Active:=MarkedActiveEdge E K (H false) (H true)
  let G:=markedSampleArcSetGraph P π d σ D.arcs
  constructor
  · intro v
    let I:Finset Active:=(markedIncidentEdges tail head ktail khead π (H false) (H true) true (Sum.inl v)).filter
      (fun a=>markedActivePhysical tail head ktail khead π (H false) (H true) a∈D.removed)
    have hsource (u:{u:V // G.Adj v u}) : ∃a:E⊕K, a∈D.arcs ∧ markedPhysicalEdge tail head ktail khead π a=({v,u.val}:Finset V) := by
      exact Finset.mem_image.mp u.property.2
    let f : {u:V // G.Adj v u} → {a // a∈I} := fun u => by
      let a:=Classical.choose (hsource u)
      have ha:=Classical.choose_spec (hsource u)
      refine ⟨Sum.inl a,?_⟩
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,?_⟩
        rw [markedResourceIncident_physical]
        change markedPhysicalIncident (Sum.inl v) (Sum.inl (markedPhysicalEdge tail head ktail khead π a))
        rw [ha.2]
        simp [markedPhysicalIncident]
      · change Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈D.removed
        unfold MarkedReferenceDeletion.removed markedFiniteResources
        exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,ha.1,rfl⟩)
    have hf:Function.Injective f:=by
      intro u w he
      apply Subtype.ext
      have ha : Classical.choose (hsource u)=Classical.choose (hsource w) := by
        exact Sum.inl.inj (congrArg Subtype.val he)
      have hp : ({v,u.val}:Finset V)=({v,w.val}:Finset V) := by
        rw [←(Classical.choose_spec (hsource u)).2,ha,(Classical.choose_spec (hsource w)).2]
      have hu:u.val∈({v,w.val}:Finset V):=by rw [←hp];simp
      rcases Finset.mem_insert.mp hu with hv|hu
      · exact (u.property.1 hv.symm).elim
      · exact Finset.mem_singleton.mp hu
    have hh:=Fintype.card_le_of_injective f hf
    have he:Fintype.card {u:V // G.Adj v u}=G.degree v:=by
      convert G.card_neighborSet_eq_degree v using 1 <;> congr!
    rw [he,Fintype.card_coe] at hh
    have hbound:((I.card:ℕ):ℝ)≤γ:=hvalid.2.2.1 true (Sum.inl v)
    exact (Nat.cast_le.mpr hh).trans hbound
  · exact (marked_removed_resources_empty_inner P π d σ D.arcs D.spokes X Y hvalid.2.1).1
end Oberwolfach
