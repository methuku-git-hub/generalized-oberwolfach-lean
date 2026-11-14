module

public import Oberwolfach.ClassProjectedRetention

@[expose] public section
/-! A common raw experiment whose class views have the prescribed collapsed
laws can be followed by class-specific retention on the same outcome. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem class_common_retained_inputs {I Ω:Type} [Fintype I] [DecidableEq I] [Fintype Ω]
    {A B:I→Type} [∀ i,Fintype (A i)] [∀ i,Fintype (B i)]
    {F:∀ i,B i→Type} [∀ i x,Fintype (F i x)]
    (μ:FiniteLaw Ω) (view:∀ i,Ω→A i) (f:∀ i,A i→B i)
    (raw:∀ i,FiniteLaw (A i)) (selected:∀ i,FiniteLaw (B i))
    (hview:∀ i,μ.map (view i)=raw i) (hcollapse:∀ i,(raw i).map (f i)=selected i)
    (ν:∀ i x,FiniteLaw (F i x)):
    let joint:=μ.sigma (fun ω=>FiniteLaw.pi (fun i=>ν i (f i (view i ω))));
    ∀ i,joint.map (fun z=>(⟨f i (view i z.1),z.2 i⟩:(Σ x:B i,F i x)))=
      (selected i).sigma (ν i):=by
  intro joint i
  have hh:=class_projected_retention_map μ view f ν i
  rw [hview i,hcollapse i] at hh
  exact hh
end Oberwolfach
