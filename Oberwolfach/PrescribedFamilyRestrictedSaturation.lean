module

public import Oberwolfach.PrescribedRestrictedFamilySaturation
public import Oberwolfach.PrescribedFamilyState

@[expose] public section
/-! The extra saturation set is constructed from the current family state;
its size is small under the selected-hub residual-source bound. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem prescribed_family_restricted_saturation
    {I X V:Type} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq X] [DecidableEq V]
    (st:PrescribedFamilyState I X V) (QV:I→Finset X) (H:Finset I)
    (a κ θ β:ℝ) (ha:0<a) (hκ:0<κ) (hθ:0≤θ)
    (hH:(H.card:ℝ)≤a) (hθbudget:θ≤κ*(β/4))
    (hQ:∀i∈H,((QV i).card:ℝ)≤θ*Fintype.card V)
    (hT:∀p∈st.freeOccurrences,p.2∈QV p.1):
    let T:=st.freeOccurrences.filter (fun p=>p.1∈H)
    let Slocal:=Finset.univ.filter (fun v=>κ*a≤((T.filter (fun p=>familyVertexImage st.vertexMap p=v)).card:ℝ));
    (Slocal.card:ℝ)≤β*Fintype.card V/4 ∧
    ∀v,κ*a≤((T.filter (fun p=>familyVertexImage st.vertexMap p=v)).card:ℝ)→v∈Slocal :=by
  intro T Slocal
  have hh:=prescribed_restricted_family_saturation H QV T (familyVertexImage st.vertexMap)
    a (Fintype.card V) κ θ (β/4) ha hκ (by positivity) hθ hH hθbudget hQ (by
      intro p hp
      exact ⟨(Finset.mem_filter.mp hp).2,hT p (Finset.mem_filter.mp hp).1⟩)
  constructor
  · dsimp only [Slocal]
    convert hh using 1 <;> ring
  · intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩
end Oberwolfach
