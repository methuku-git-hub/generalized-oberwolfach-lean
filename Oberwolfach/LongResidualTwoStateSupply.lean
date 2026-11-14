module

public import Oberwolfach.LongResidualSelectedStateSupply
public import Oberwolfach.LongApproximateStateLoss
public import Oberwolfach.LongResidualSelectedTypes

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
local instance residualTwoStateDecEq : DecidableEq V := Classical.decEq V

theorem long_residual_two_selected_state_supply
    (G Del Small Bad Loss:SimpleGraph V)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (M:V→V→ℕ)
    (hcorrect:orientationDisagreementGraph (longPhysicalStateGraph G ω {0,1,2,3,4}) (fun e=>(ω (Sum.inl e)).2) M≤Del)
    (hcover:Small≤longPhysicalStateGraph G ω {2,3}⊔Loss)
    (L:ℝ) (hLoss:∀v,((Del⊔Loss⊔Bad).degree v:ℝ)≤L)
    (b₀ b₁:V→ℝ)
    (hraw₀:∀v,b₀ v≤((∑x,sampledColourOrientation G (fun e=>ω (Sum.inl e)) 0 x v:ℕ):ℝ))
    (hraw₁:∀v,b₁ v≤((∑x,sampledColourOrientation G (fun e=>ω (Sum.inl e)) 1 x v:ℕ):ℝ)):
    let P:=longResidualHostArc M Small Bad
    let S₀:Finset {e:V×V // P e}:=Finset.univ.filter (fun e=>sampledColourOrientation G (fun e=>ω (Sum.inl e)) 0 e.val.1 e.val.2=1)
    let S₁:Finset {e:V×V // P e}:=Finset.univ.filter (fun e=>sampledColourOrientation G (fun e=>ω (Sum.inl e)) 1 e.val.1 e.val.2=1)
    let T₁:=longResidualInitialMarked G (fun e=>ω (Sum.inl e)) M Small Bad
    let T₀:Finset {e:V×V // P e}:=Finset.univ\T₁
    S₀⊆T₀ ∧ S₁=T₁ ∧
    (∀v,b₀ v-L≤(S₀.filter (fun e=>e.val.2=v)).card) ∧
    (∀v,b₁ v-L≤(S₁.filter (fun e=>e.val.2=v)).card):=by
  intro P S₀ S₁ T₁ T₀
  have hi:=long_residual_selected_state_type_inclusions G Small Bad ω M
  refine ⟨hi.1,hi.2,?_,?_⟩
  · intro v
    have hs:=long_approximate_embedding_state_loss G Small Loss ω 0 {2,3} (by decide) hcover
    have hc:=long_residual_selected_state_incoming_supply G Del Small Bad Loss ω M 0 (by decide) hcorrect hs v
    have hr:((∑x,sampledColourOrientation G (fun e=>ω (Sum.inl e)) 0 x v:ℕ):ℝ)≤
      (S₀.filter (fun e=>e.val.2=v)).card+(Del⊔Loss⊔Bad).degree v:=by exact_mod_cast hc
    linarith only [hr,hraw₀ v,hLoss v]
  · intro v
    have hs:=long_approximate_embedding_state_loss G Small Loss ω 1 {2,3} (by decide) hcover
    have hc:=long_residual_selected_state_incoming_supply G Del Small Bad Loss ω M 1 (by decide) hcorrect hs v
    have hr:((∑x,sampledColourOrientation G (fun e=>ω (Sum.inl e)) 1 x v:ℕ):ℝ)≤
      (S₁.filter (fun e=>e.val.2=v)).card+(Del⊔Loss⊔Bad).degree v:=by exact_mod_cast hc
    linarith only [hr,hraw₁ v,hLoss v]
end Oberwolfach
