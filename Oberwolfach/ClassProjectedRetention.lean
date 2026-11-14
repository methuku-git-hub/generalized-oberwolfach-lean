module

public import Oberwolfach.ClassSharedRetentionProjection

@[expose] public section
/-! Each class retains starts after projecting its full raw experiment to the
selected reference coordinates; all retention kernels share the same global
raw outcome. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem class_projected_retention_map {I Ω:Type} [Fintype I] [DecidableEq I] [Fintype Ω]
    {A B:I→Type} [∀ i,Fintype (A i)] [∀ i,Fintype (B i)]
    {F:∀ i,B i→Type} [∀ i x,Fintype (F i x)]
    (μ:FiniteLaw Ω) (view:∀ i,Ω→A i) (f:∀ i,A i→B i) (ν:∀ i x,FiniteLaw (F i x)) (i:I):
    (μ.sigma (fun ω=>FiniteLaw.pi (fun j=>ν j (f j (view j ω))))).map
      (fun z=>(⟨f i (view i z.1),z.2 i⟩:(Σ x:B i,F i x)))=
      ((μ.map (view i)).map (f i)).sigma (ν i):=by
  let G:=fun j (x:A j)=>F j (f j x)
  let ν':∀ j x,FiniteLaw (G j x):=fun j x=>ν j (f j x)
  let E:=fun z:(Σ x:A i,G i x)=>(⟨f i z.1,z.2⟩:(Σ x:B i,F i x))
  have hproj:=finiteLaw_sigma_projection_probability (μ.map (view i)) (f i) (ν i)
  apply finiteLaw_ext
  intro z
  have hmap:=finiteLaw_map_probability
    (μ.sigma (fun ω=>FiniteLaw.pi (fun j=>ν j (f j (view j ω)))))
    (fun z=>(⟨f i (view i z.1),z.2 i⟩:(Σ x:B i,F i x))) (fun y=>y=z)
  have h₁:=class_shared_retention_probability μ view ν' i (fun x=>E x=z)
  have h₂:=hproj (fun y=>y=z)
  rw [finiteLaw_sigma_probability] at h₂
  have h₃:=finiteLaw_sigma_probability (μ.map (view i)) (fun x=>ν i (f i x)) (fun x=>E x=z)
  have hp:=hmap.trans (h₁.trans (h₃.trans h₂))
  simpa [FiniteLaw.probability,eq_comm,E] using hp
end Oberwolfach
