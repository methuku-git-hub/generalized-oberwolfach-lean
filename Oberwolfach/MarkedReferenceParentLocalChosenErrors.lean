module

public import Oberwolfach.MarkedReferenceJointLoadMargin
public import Oberwolfach.MarkedReferenceParentAndLocalLoad
public import Oberwolfach.MarkedReferenceParentLoadAdaptiveError
public import Oberwolfach.MarkedLocalEstimateMonotonicity
public import Oberwolfach.MarkedReferenceParentLoadFromZeroDeletionSplit
public import Oberwolfach.MarkedReferenceParentPackingLoad
public import Oberwolfach.MarkedPackingZeroDeletionAnyInstance

@[expose] public section
/-! The no-deletion case of the adaptive packing event gives the parent load. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
theorem marked_reference_parent_and_local_load_with_chosen_errors
    (P:SimpleGraph V) (π:Equiv.Perm V) (d r:ℕ) (rho t kappa theta ρstar sstar Bload Kload:ℝ)
    (hκ:0<kappa) (hθ:0<theta) (hρ:0<ρstar) (hs:0<sstar) (hB:0<Bload) (hK:0<Kload)
    (weight:(Fin (r+4+1)→V)→ℝ) (a:Γ) (j:Color)
    (q:U→Γ→ℝ) (s:U→Color→ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop):
    ∃ τ εLoad ζLoad ζLocal:ℝ,0<τ ∧ 0<εLoad ∧ 0<ζLoad ∧ 0<ζLocal ∧
    let base:=(((r+4):ℝ)+1)^4*(2*Bload/(ρstar*sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1));
    let η:=τ+εLoad+11*base*Kload*ζLoad;
    let localErr:=τ+εLoad+5*base*Kload*ζLocal;
    let C:=33*base;
    let pRef:=rho*(r+4:ℝ)*t/2
    let kRef:=pRef/(r+4:ℝ)
    let DRef:=2*Fintype.card U/rho;
    (∀ δ:ℝ,0≤δ→∀ (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)),
      (∀ x,(DR.degree x:ℝ)≤δ)→(∀ x,(DS.degree x:ℝ)≤δ)→
      MarkedPackingLoadsWithSpokes P π d (r+4) DRef pRef kRef ((r+4:ℝ)*t) weight a j
        (Equiv.refl U) q s (η+C*δ/Fintype.card V)
        (rawMarkedDeleteRims σ DR.edgeFinset) (markedDeletePhysicalSpokes H DS)) →
    MarkedLocalSpokeLoadsWithSpokes P π d (r+4) DRef pRef kRef ((r+4:ℝ)*t) weight localErr σ H →
    let seed:=fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd (r+4) π (3*d)
      (fun (_:V) (_:U)=>True) (fun _ _=>True)=>weight W.1.val/(DRef*pRef^(r+4)*kRef*((r+4:ℝ)*t)^(r+4));
    (∀ root,rawMarkedWheelMarginal P π d pRef kRef q s a j root≠0 →
      |typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) H root-1|≤kappa/4) ∧
    MarkedLocalSpokeLoadsWithSpokes P π d (r+4) DRef pRef kRef ((r+4:ℝ)*t) weight (theta/4) σ H := by
  obtain ⟨τ,εLoad,ζLoad,ζLocal,hτ,hε,hζ,hζlocal,hη,hlocal⟩:=
    marked_reference_joint_load_margin_choice r kappa theta ρstar sstar Bload Kload hκ hθ hρ hs hB hK
  refine ⟨τ,εLoad,ζLoad,ζLocal,hτ,hε,hζ,hζlocal,?_⟩
  intro base η localErr C pRef kRef DRef h hspoke seed
  exact marked_reference_parent_and_local_load_from_adaptive P π d r rho t kappa theta τ εLoad ζLoad ζLocal ρstar sstar Bload Kload weight a j q s σ H hη hlocal h hspoke
end Oberwolfach
