module

public import Oberwolfach.PrescribedCompletionImageLoad
public import Oberwolfach.PrescribedBadEdgeAssignments

@[expose] public section
/-! Physical assigned-edge provenance converts the global anchor bound and
free completion bound into a bound for all actual completion images. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem prescribed_assigned_completion_image_load
    {I V:Type} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]
    {X:I→Type} [∀i,Fintype (X i)] [∀i,DecidableEq (X i)]
    (K:SimpleGraph V) (assign:Sym2 V→I) (orient:Sym2 V→V×V)
    (horient:∀e∈K.edgeFinset,prescribedArcPhysical (orient e)=e)
    (Φ:∀i,X i→V) (B:∀i,Finset (X i)) (g:∀i,X i→V) (P Z:I→Finset V)
    (hAnchor:∀i,(B i).image (g i)=P i∪prescribedMatchingEndpoints (prescribedAssignedArcs K assign orient i)∪Z i)
    (hAgree:∀i x,x∈B i→Φ i x=g i x)
    (Λ free:ℝ)
    (hGlobal:∀v,((Finset.univ.filter (fun i=>v∈P i)).card:ℝ)+K.degree v+
      ((Finset.univ.filter (fun i=>v∈Z i)).card:ℝ)≤Λ)
    (hFree:∀v,(((Finset.univ.filter (fun z:(Σi,X i)=>z.2∉B z.1)).filter (fun z=>Φ z.1 z.2=v)).card:ℝ)≤free):
    ∀v,((Finset.univ.filter (fun i=>v∈Finset.univ.image (Φ i))).card:ℝ)≤Λ+free:=by
  intro v
  let M:=prescribedAssignedArcs K assign orient
  let Q:=fun i=>P i∪prescribedMatchingEndpoints (M i)∪Z i
  have hAnchor':∀i x,x∈B i→Φ i x∈Q i:=by
    intro i x hx
    change Φ i x∈P i∪prescribedMatchingEndpoints (prescribedAssignedArcs K assign orient i)∪Z i
    rw [hAgree i x hx,←hAnchor i]
    exact Finset.mem_image.mpr ⟨x,hx,rfl⟩
  have hassigned:=prescribed_assigned_arcs_physical K assign orient horient
  have hsub:∀i,(M i).image prescribedArcPhysical⊆K.edgeFinset:=by
    intro i e he
    exact (hassigned.1 i e he).1
  have hOcc:=prescribed_augmented_occurrence_bound P Z M K hsub hassigned.2.2 v
  have hOccR:((Finset.univ.filter (fun i=>v∈Q i)).card:ℝ)≤
      ((Finset.univ.filter (fun i=>v∈P i)).card:ℝ)+K.degree v+
      ((Finset.univ.filter (fun i=>v∈Z i)).card:ℝ):=by exact_mod_cast hOcc
  have hImage:=prescribed_completion_image_load Φ B Q hAnchor' v
  have hImageR:((Finset.univ.filter (fun i=>v∈Finset.univ.image (Φ i))).card:ℝ)≤
      ((Finset.univ.filter (fun i=>v∈Q i)).card:ℝ)+
      (((Finset.univ.filter (fun z:(Σi,X i)=>z.2∉B z.1)).filter (fun z=>Φ z.1 z.2=v)).card:ℝ):=by
    exact_mod_cast hImage
  linarith [hGlobal v,hFree v]
end Oberwolfach
