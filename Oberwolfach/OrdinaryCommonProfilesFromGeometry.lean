module

public import Oberwolfach.OrdinaryCommonCycleProfiles
public import Oberwolfach.OrdinaryLocalAbsorbers

@[expose] public section

/-! Construct the pair profiles with the explicit paired absorber template.
The absorber counts follow uniformly from the actual common-neighbourhood
bounds; the supplied weights and their original domains are unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 14000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinary_common_profiles_from_geometry
    (m:ℕ) (hm:2≤m) (Q F:SimpleGraph V) (H:V→U→Prop)
    (β b B η γ L:ℝ) (hγ:0<γ) (hL:0≤L)
    (hF:∀ v,(F.degree v:ℝ)≤L)
    (hsize:∀ u u':U,u≠u'→β*Fintype.card V≤
      ((Finset.univ.filter (fun v=>H v u∧H v u')).card:ℝ))
    (hcommon:∀ u u':U,u≠u'→∀ S:Finset V,S.card≤(if m=2 then 3 else 2)→
      γ*Fintype.card V≤((common (Finset.univ.filter (fun v=>H v u∧H v u')) S
        (fun x=>Q.neighborFinset x)).card:ℝ))
    (hbudget:(m+3:ℝ)*(L+1)≤γ/2*Fintype.card V)
    (hnb:2*(m+1:ℝ)^2≤ordinaryLocalCountCoeff m γ*Fintype.card V)
    (hnp:2*(m:ℝ)*(2*(m+1)+(m+1)*m)≤ordinaryLocalCountCoeff m γ*Fintype.card V)
    (w:∀ u u':U,u≠u'→LocalOrdinaryCycle Q F (Finset.univ.filter (fun v=>H v u∧H v u')) (m+1)→ℝ)
    (hw:∀ u u' (hne:u≠u') C,b/(Fintype.card V:ℝ)^m≤w u u' hne C ∧
      w u u' hne C≤B/(Fintype.card V:ℝ)^m)
    (hdeg:∀ u u' (hne:u≠u'),∀ v∈Finset.univ.filter (fun v=>H v u∧H v u'),
      |1-hypergraphWeightedDegree localOrdinaryVertices (w u u' hne) v|≤η) :
    OrdinaryCommonCycleProfiles Q F H (m+1) (fun (_:Unit)=>pairedAbsorberTemplate (m+1)) β
      ((ordinaryLocalCountCoeff m γ/2)^(m+2)) b B η := by
  refine ⟨w,hsize,?_,hdeg,?_⟩
  · intro u u' hne C
    simpa only [Nat.add_sub_cancel] using hw u u' hne C
  · intro u u' hne X hXT hXr
    let T:Finset V:=Finset.univ.filter (fun v=>H v u∧H v u')
    let e:Fin (m+1)≃X:=Fintype.equivOfCardEq (by simp only [Fintype.card_fin,Fintype.card_coe,hXr])
    let x:Fin (m+1)→V:=fun i=>(e i).val
    have hx:Function.Injective x:=by intro i j hij;exact e.injective (Subtype.ext hij)
    have hxT (i:Fin (m+1)):x i∈T:=hXT (e i).property
    have hxX:Finset.univ.image x=X:=by
      ext v
      simp only [Finset.mem_image,Finset.mem_univ,true_and]
      constructor
      · rintro ⟨i,rfl⟩;exact (e i).property
      · intro hv;obtain ⟨i,hi⟩:=e.surjective ⟨v,hv⟩;exact ⟨i,congrArg Subtype.val hi⟩
    have habs:=ordinary_local_paired_absorber_count Q F T hm γ L hγ hL hF (hcommon u u' hne)
      hbudget hnb hnp x hx hxT
    rw [hxX] at habs
    let inject:LabelledCycleRecord localOrdinaryVertices (pairedAbsorberTemplate (m+1)).val X→
      LabelledAbsorberFamily (localOrdinaryVertices (Q:=Q) (F:=F) (T:=T) (r:=m+1))
        (fun (_:Unit)=>pairedAbsorberTemplate (m+1)) X:=fun D=>⟨(),D⟩
    have hinj:Function.Injective inject:=by intro C D h;exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
    exact habs.trans (by exact_mod_cast Fintype.card_le_of_injective inject hinj)

end Oberwolfach
