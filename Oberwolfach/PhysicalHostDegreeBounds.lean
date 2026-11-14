module

public import Oberwolfach.OrdinaryBoundaryGraph
public import Oberwolfach.MarkedPackingRimGraphs
public import Oberwolfach.MarkedWheelFamilyLoads

@[expose] public section

/-! Convert the actual rim and spoke degrees into one physical degree
bound, without confusing auxiliary incidences and physical neighbours. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_physical_degree_row (Q:SimpleGraph V) (H:V→U→Prop) (x:V):
    (ordinaryPhysicalGraph Q H).degree (Sum.inl x)=Q.degree x+(Finset.univ.filter (H x)).card:=by
  have he:(ordinaryPhysicalGraph Q H).neighborFinset (Sum.inl x)=
      (Q.neighborFinset x).image Sum.inl∪(Finset.univ.filter (H x)).image Sum.inr:=by
    ext z
    rw [SimpleGraph.mem_neighborFinset]
    cases z <;> simp [ordinaryPhysicalGraph]
  have hd:Disjoint ((Q.neighborFinset x).image (Sum.inl:V→V⊕U))
      ((Finset.univ.filter (H x)).image Sum.inr):=by
    apply Finset.disjoint_left.mpr
    intro z hz hw
    obtain ⟨v,_,hv⟩:=Finset.mem_image.mp hz
    obtain ⟨u,_,hu⟩:=Finset.mem_image.mp hw
    exact Sum.inl_ne_inr (hv.trans hu.symm)
  rw [←SimpleGraph.card_neighborFinset_eq_degree,he,Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injective _ Sum.inl_injective,Finset.card_image_of_injective _ Sum.inr_injective,
    SimpleGraph.card_neighborFinset_eq_degree]

theorem ordinary_physical_degree_column (Q:SimpleGraph V) (H:V→U→Prop) (u:U):
    (ordinaryPhysicalGraph Q H).degree (Sum.inr u)=(Finset.univ.filter (fun x=>H x u)).card:=by
  have he:(ordinaryPhysicalGraph Q H).neighborFinset (Sum.inr u)=
      (Finset.univ.filter (fun x=>H x u)).image Sum.inl:=by
    ext z
    rw [SimpleGraph.mem_neighborFinset]
    cases z <;> simp [ordinaryPhysicalGraph]
  rw [←SimpleGraph.card_neighborFinset_eq_degree,he,Finset.card_image_of_injective _ Sum.inl_injective]

theorem ordinary_physical_degree_bound (Q:SimpleGraph V) (H:V→U→Prop) (r s c D:ℝ)
    (hr:∀ x,(Q.degree x:ℝ)≤r) (hs:∀ x,((Finset.univ.filter (H x)).card:ℝ)≤s)
    (hc:∀ u,((Finset.univ.filter (fun x=>H x u)).card:ℝ)≤c)
    (hrs:r+s≤D) (hcD:c≤D):
    ∀ z,((ordinaryPhysicalGraph Q H).degree z:ℝ)≤D:=by
  intro z
  cases z with
  | inl x=>rw [ordinary_physical_degree_row,Nat.cast_add];exact (add_le_add (hr x) (hs x)).trans hrs
  | inr u=>rw [ordinary_physical_degree_column];exact (hc u).trans hcD
end Oberwolfach
