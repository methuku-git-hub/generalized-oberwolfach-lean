module

public import Oberwolfach.HubNeighbourClasses
public import Oberwolfach.SupportedBernoulliFactor
public import Oberwolfach.EmbeddedClassChanges

@[expose] public section

/-! Actual selected row sets in the two hub-neighbour classes. These
identities allow outcome-dependent final sets without changing the parent
class domains or the coefficients. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [DecidableEq V]

def selectedHubClasses (H₀ HK:V→U→Prop) (u:U) (Y:Finset V) :
    Finset (Σ i,hubNeighbourClass H₀ HK u i) := Finset.univ.filter (fun v=>v.2.val∈Y)

theorem selected_hub_classes_image (H₀ HK:V→U→Prop) (u:U)
    (hd:∀ v,¬(H₀ v u∧HK v u)) (Y:Finset V)
    (hY:∀ v∈Y,H₀ v u∨HK v u) :
    (selectedHubClasses H₀ HK u Y).image (hubNeighbourEmbedding H₀ HK u hd)=Y := by
  ext v
  simp only [Finset.mem_image,selectedHubClasses,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨z,hz,he⟩;exact he ▸ hz
  · intro hv
    rcases hY v hv with h|h
    · exact ⟨⟨false,⟨v,h⟩⟩,hv,rfl⟩
    · exact ⟨⟨true,⟨v,h⟩⟩,hv,rfl⟩

theorem selected_hub_class_card (H₀ HK:V→U→Prop) (u:U) (Y:Finset V) (i:Bool) :
    (Finset.univ.filter (fun v:hubNeighbourClass H₀ HK u i=>(⟨i,v⟩:Σ j,hubNeighbourClass H₀ HK u j)∈selectedHubClasses H₀ HK u Y)).card=
      (Y.filter (fun v=>if i then HK v u else H₀ v u)).card := by
  apply Finset.card_bij (fun v _=>v.val)
  · intro v hv
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hv).2).2,v.property⟩
  · intro v hv w hw he;exact Subtype.ext he
  · intro v hv
    refine ⟨⟨v,(Finset.mem_filter.mp hv).2⟩,?_,rfl⟩
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,selectedHubClasses]
    exact (Finset.mem_filter.mp hv).1

theorem hub_neighbour_total_card (H₀ HK:V→U→Prop) (u:U)
    (hd:∀ v,¬(H₀ v u∧HK v u)) :
    Fintype.card (Σ i,hubNeighbourClass H₀ HK u i)=
      (Finset.univ.filter (fun v=>H₀ v u∨HK v u)).card := by
  have hh:=congrArg Finset.card (hubNeighbourEmbedding_image H₀ HK u hd)
  simpa only [Finset.card_image_of_injective _ (hubNeighbourEmbedding H₀ HK u hd).injective,Finset.card_univ] using hh

theorem selected_hub_class_change_card (H₀ HK:V→U→Prop) (u:U)
    (hd:∀ v,¬(H₀ v u∧HK v u)) (Y:Finset V) (hY:∀ v∈Y,H₀ v u∨HK v u) (σ:V→Bool) :
    (changed (selectedHubClasses H₀ HK u Y)
      (bernoulliVertexSet (fun z=>σ (hubNeighbourEmbedding H₀ HK u hd z)))).card=
    (changed Y ((Finset.univ.filter (fun v=>H₀ v u∨HK v u)).filter (fun v=>σ v=true))).card := by
  let e:=hubNeighbourEmbedding H₀ HK u hd
  have he : (bernoulliVertexSet (fun z=>σ (e z))).image e=
      (Finset.univ.filter (fun v=>H₀ v u∨HK v u)).filter (fun v=>σ v=true) := by
    rw [←hubNeighbourEmbedding_image H₀ HK u hd]
    convert (filter_image_class e Finset.univ (fun v=>σ v=true)).symm using 1 <;> try congr!
    ext z;simp [bernoulliVertexSet]
  rw [←changed_image_card e e.injective,selected_hub_classes_image H₀ HK u hd Y hY,he]

 theorem changed_card_eq_differences {X:Type} [DecidableEq X] (A B:Finset X) :
    (changed A B).card=(B\A).card+(A\B).card := by
  have hd:Disjoint (A\B) (B\A):=by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1
  unfold changed
  convert (Finset.card_union_of_disjoint hd).trans (Nat.add_comm _ _) using 1 <;> congr!

end Oberwolfach
