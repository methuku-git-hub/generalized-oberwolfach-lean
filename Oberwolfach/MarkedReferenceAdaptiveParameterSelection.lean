module

public import Oberwolfach.MarkedReferenceTwoStageParameterOrder

@[expose] public section
/-! Choose positive tolerances so one baseline level tolerates every later
physical change within the selected degree budget. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
theorem marked_reference_choose_uniform_change_margins
    (r:ℕ) (betaA t betaCap:ℝ) (hbetaA:0<betaA) (ht:0<t) (hbetaCap:0<betaCap):
    ∃ beta:ℝ,0<beta∧beta≤t/2∧beta≤betaCap∧
    ∀ eps₁ eps₂ theta C cap:ℝ,0<eps₁→0<eps₂→0<theta→0≤C→0<cap→
    ∃ kappa thetaDeep ζ:ℝ,0<kappa∧0<thetaDeep∧0<ζ∧
      kappa≤cap∧thetaDeep≤cap∧ζ≤cap∧kappa≤eps₂∧
      kappa/4+(r+12:ℝ)*(ζ+ζ)≤min eps₁ eps₂∧
      kappa/4+(r+12:ℝ)*ζ≤min eps₁ eps₂∧
      2*beta≤3*min betaA (t/4)-(r+5:ℝ)*(ζ+ζ)∧
      2*beta≤3*min betaA (t/4)-(r+7:ℝ)*ζ-(r+4:ℝ)*ζ∧
      thetaDeep/4+C*ζ≤theta/2:=by
  let m:=min betaA (t/4)
  let beta:=min (m/4) (betaCap/2)
  have hm:0<m:=by dsimp [m];positivity
  have htbound:m≤t/4:=min_le_right _ _
  have hb1:beta≤m/4:=min_le_left _ _
  have hb2:beta≤betaCap/2:=min_le_right _ _
  refine ⟨beta,by dsimp [beta];positivity,by linarith,by linarith,?_⟩
  intro eps₁ eps₂ theta C cap he₁ he₂ hθ hC hcap
  let e:=min eps₁ eps₂
  let kappa:=min e (cap/2)
  let thetaDeep:=min theta (cap/2)
  let cR:ℝ:=2*((r:ℝ)+12)
  let cI:ℝ:=(r:ℝ)+12
  let cC:ℝ:=2*((r:ℝ)+5)
  let cP:ℝ:=((r:ℝ)+7)+((r:ℝ)+4)
  let den:=1+cR+cI+cC+cP+C
  let gap:=min (e/4) (min m (theta/4))
  let ζ:=min (gap/(2*den)) (cap/2)
  have hr:0≤(r:ℝ):=Nat.cast_nonneg _
  have he:0<e:=by dsimp [e];positivity
  have hcR:0≤cR:=by dsimp [cR];positivity
  have hcI:0≤cI:=by dsimp [cI];positivity
  have hcC:0≤cC:=by dsimp [cC];positivity
  have hcP:0≤cP:=by dsimp [cP];positivity
  have hden:0<den:=by dsimp [den];linarith
  have hgap:0<gap:=by dsimp [gap];positivity
  have hz:0<ζ:=by dsimp [ζ];positivity
  have hk:0<kappa:=by dsimp [kappa];positivity
  have htd:0<thetaDeep:=by dsimp [thetaDeep];positivity
  have hkcap:kappa≤cap:=by have hh:kappa≤cap/2:=min_le_right _ _;linarith
  have htdcap:thetaDeep≤cap:=by have hh:thetaDeep≤cap/2:=min_le_right _ _;linarith
  have hzcap:ζ≤cap:=by have hh:ζ≤cap/2:=min_le_right _ _;linarith
  have hke:kappa≤e:=min_le_left _ _
  have htdθ:thetaDeep≤theta:=min_le_left _ _
  have hzden:ζ≤gap/(2*den):=min_le_left _ _
  have hge:gap≤e/4:=min_le_left _ _
  have hgm:gap≤m:=(min_le_right _ _).trans (min_le_left _ _)
  have hgθ:gap≤theta/4:=(min_le_right _ _).trans (min_le_right _ _)
  have hebound:e≤eps₂:=min_le_right _ _
  have hdenR:cR≤den:=by dsimp [den];linarith
  have hdenI:cI≤den:=by dsimp [den];linarith
  have hdenC:cC≤den:=by dsimp [den];linarith
  have hdenP:cP≤den:=by dsimp [den];linarith
  have hdenL:C≤den:=by dsimp [den];linarith
  have heq:den*(gap/(2*den))=gap/2:=by field_simp
  have hdz:den*ζ≤gap/2:=(mul_le_mul_of_nonneg_left hzden hden.le).trans (le_of_eq heq)
  have hR:cR*ζ≤gap/2:=(mul_le_mul_of_nonneg_right hdenR hz.le).trans hdz
  have hI:cI*ζ≤gap/2:=(mul_le_mul_of_nonneg_right hdenI hz.le).trans hdz
  have hcc:cC*ζ≤gap/2:=(mul_le_mul_of_nonneg_right hdenC hz.le).trans hdz
  have hP:cP*ζ≤gap/2:=(mul_le_mul_of_nonneg_right hdenP hz.le).trans hdz
  have hL:C*ζ≤gap/2:=(mul_le_mul_of_nonneg_right hdenL hz.le).trans hdz
  refine ⟨kappa,thetaDeep,ζ,hk,htd,hz,hkcap,htdcap,hzcap,hke.trans hebound,?_,?_,?_,?_,?_⟩
  all_goals dsimp only [cR,cI,cC,cP] at * <;> push_cast at * <;> nlinarith
end Oberwolfach
