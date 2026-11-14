module

public import Oberwolfach.OrdinaryRelativeFourTransformerAbsorber

@[expose] public section

/-! The fixed cycle coefficients supplied for each distinct pair of hubs.
This records the existing fractional-degree and absorber-count hypotheses;
it does not assert their existence or change their domains after choices. -/
set_option autoImplicit false
set_option synthInstance.maxSize 2048
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Tpl:Type} [Fintype V] [Fintype U] [Fintype Tpl]
    [DecidableEq V] [DecidableEq U] [DecidableEq Tpl]

structure OrdinaryCommonCycleProfiles (Q F:SimpleGraph V) (H:V→U→Prop)
    (r:ℕ) (Tpls:Tpl→VertexAbsorberTemplate r) (β a b B η:ℝ) where
  weight : ∀ u u':U,u≠u'→LocalOrdinaryCycle Q F (Finset.univ.filter (fun v=>H v u∧H v u')) r→ℝ
  size : ∀ u u':U,u≠u'→β*Fintype.card V≤((Finset.univ.filter (fun v=>H v u∧H v u')).card:ℝ)
  bounds : ∀ u u' (hne:u≠u') C,b/(Fintype.card V:ℝ)^(r-1)≤weight u u' hne C∧weight u u' hne C≤B/(Fintype.card V:ℝ)^(r-1)
  degree : ∀ u u' (hne:u≠u'),∀ v∈Finset.univ.filter (fun v=>H v u∧H v u'),
    |1-hypergraphWeightedDegree localOrdinaryVertices (weight u u' hne) v|≤η
  absorbers : ∀ u u' (hne:u≠u'),∀ X:Finset V,X⊆Finset.univ.filter (fun v=>H v u∧H v u')→X.card=r→
    a*(Fintype.card V:ℝ)^(r*r)≤Fintype.card
      (LabelledAbsorberFamily (localOrdinaryVertices (Q:=Q) (F:=F) (T:=Finset.univ.filter (fun v=>H v u∧H v u')) (r:=r)) Tpls X)

end Oberwolfach
