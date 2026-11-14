module

public import Oberwolfach.ClassSharedRawProduct
public import Oberwolfach.FiniteLawSigmaProjection

@[expose] public section
/-! Retention is sampled after the full shared raw outcome. For each class its
retained marginal is exactly the original conditional retention law. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem class_shared_retention_probability {I Ω:Type} [Fintype I] [DecidableEq I] [Fintype Ω]
    {A:I→Type} [∀ i,Fintype (A i)] {F:∀ i,A i→Type} [∀ i x,Fintype (F i x)]
    (μ:FiniteLaw Ω) (view:∀ i,Ω→A i) (ν:∀ i x,FiniteLaw (F i x))
    (i:I) (E:(Σ x:A i,F i x)→Prop):
    let joint:=μ.sigma (fun ω=>FiniteLaw.pi (fun j=>ν j (view j ω)));
    joint.probability (fun z=>E ⟨view i z.1,z.2 i⟩)=((μ.map (view i)).sigma (ν i)).probability E:=by
  intro joint
  have hleft:=finiteLaw_sigma_probability μ (fun ω=>FiniteLaw.pi (fun j=>ν j (view j ω)))
    (fun z=>E ⟨view i z.1,z.2 i⟩)
  have hpoint (ω:Ω):
      (FiniteLaw.pi (fun j=>ν j (view j ω))).probability (fun z=>E ⟨view i ω,z i⟩)=
        (ν i (view i ω)).probability (fun x=>E ⟨view i ω,x⟩):=by
    have hp:=finiteLaw_map_probability (FiniteLaw.pi (fun j=>ν j (view j ω)))
      (fun z=>z i) (fun x=>E ⟨view i ω,x⟩)
    rw [finiteLaw_pi_map_coordinate] at hp
    exact hp.symm
  simp_rw [hpoint] at hleft
  have hright:=finiteLaw_sigma_projection_probability μ (view i) (ν i) E
  rw [finiteLaw_sigma_probability] at hright
  exact hleft.trans hright

theorem class_shared_retention_map {I Ω:Type} [Fintype I] [DecidableEq I] [Fintype Ω]
    {A:I→Type} [∀ i,Fintype (A i)] {F:∀ i,A i→Type} [∀ i x,Fintype (F i x)]
    (μ:FiniteLaw Ω) (view:∀ i,Ω→A i) (ν:∀ i x,FiniteLaw (F i x)) (i:I):
    (μ.sigma (fun ω=>FiniteLaw.pi (fun j=>ν j (view j ω)))).map
      (fun z=>(⟨view i z.1,z.2 i⟩:(Σ x:A i,F i x)))=(μ.map (view i)).sigma (ν i):=by
  apply finiteLaw_ext
  intro z
  have hh:=class_shared_retention_probability μ view ν i (fun y=>y=z)
  have hm:=finiteLaw_map_probability (μ.sigma (fun ω=>FiniteLaw.pi (fun j=>ν j (view j ω))))
    (fun z=>(⟨view i z.1,z.2 i⟩:(Σ x:A i,F i x))) (fun y=>y=z)
  have hp:=hm.trans hh
  simpa [FiniteLaw.probability,eq_comm] using hp
end Oberwolfach
