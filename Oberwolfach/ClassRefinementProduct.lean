module

public import Oberwolfach.ClassRefinementLaw

@[expose] public section
/-! Product refinements preserve the shared class colouring and, for each
fixed class, the exact law of its refined view. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_sigma_map_first {C A:Type} [Fintype C] [Fintype A]
    (μ:FiniteLaw C) (ν:C→FiniteLaw A):
    (μ.sigma ν).map (fun z:Σ _:C,A=>z.1)=μ:=by
  apply finiteLaw_ext
  intro c
  have hh:=finiteLaw_sigma_first_probability μ ν (fun x=>x=c)
  have hm:=finiteLaw_map_probability (μ.sigma ν) (fun z:Σ _:C,A=>z.1) (fun x=>x=c)
  have hp:=hm.trans hh
  simpa [FiniteLaw.probability] using hp

theorem categorical_refinement_product_views {E A:Type} [Fintype E] [DecidableEq E] [Fintype A]
    {k:ℕ} (ρ:Fin k→ℝ) (hρ:∀ a,0≤ρ a) (htotal:∑ a,ρ a=1)
    (ν:E→Fin k→FiniteLaw A):
    let base:=FiniteLaw.categorical ρ hρ htotal
    let joint:=FiniteLaw.pi (fun e:E=>base.sigma (ν e));
    joint.map (fun z e=>(z e).1)=FiniteLaw.pi (fun _:E=>base) ∧
    ∀ a,
      joint.map (fun z e=>classRefinedView a (z e))=
      FiniteLaw.pi (fun e:E=>FiniteLaw.optional (ρ a) (hρ a)
        (by have h:=Finset.single_le_sum (fun b _=>hρ b) (Finset.mem_univ a);linarith) (ν e a)):=by
  intro base joint
  constructor
  · rw [finiteLaw_pi_map]
    congr 1
    funext e
    exact finiteLaw_sigma_map_first base (ν e)
  · intro a
    rw [finiteLaw_pi_map]
    congr 1
    funext e
    exact categorical_refinement_class_marginal ρ hρ htotal (ν e) a
end Oberwolfach
