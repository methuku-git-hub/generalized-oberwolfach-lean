module

public import Oberwolfach.MarkedPackingFullHubLoads

@[expose] public section
/-! The identity-hub packing event supplies the parent load field at the
reference parameters, retaining the fixed sequence weights. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
theorem marked_reference_parent_packing_load
    (P:SimpleGraph V) (π:Equiv.Perm V) (d r:ℕ) (rho t kappa η:ℝ)
    (weight:(Fin (r+4+1)→V)→ℝ) (a:Γ) (j:Color)
    (q:U→Γ→ℝ) (s:U→Color→ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hη:η≤kappa/4):
    let pRef:=rho*(r+4:ℝ)*t/2
    let kRef:=pRef/(r+4:ℝ)
    let DRef:=2*Fintype.card U/rho;
    MarkedPackingLoadsWithSpokes P π d (r+4) DRef pRef kRef ((r+4:ℝ)*t) weight a j
      (Equiv.refl U) q s η σ H →
    let seed:=fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd (r+4) π (3*d)
      (fun (_:V) (_:U)=>True) (fun _ _=>True)=>weight W.1.val/(DRef*pRef^(r+4)*kRef*((r+4:ℝ)*t)^(r+4));
    ∀ root,rawMarkedWheelMarginal P π d pRef kRef q s a j root≠0 →
      |typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) H root-1|≤kappa/4 := by
  intro pRef kRef DRef h seed root hroot
  have hh:=marked_packing_loads_on_all_hubs P π d (r+4) DRef pRef kRef ((r+4:ℝ)*t) weight a j q s η σ H h
  exact (hh root hroot).trans hη
end Oberwolfach
