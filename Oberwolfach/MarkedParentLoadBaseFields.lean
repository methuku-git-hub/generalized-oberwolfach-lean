module

public import Oberwolfach.MarkedPackingFullHubLoads
public import Oberwolfach.MarkedFixedTerminalAbsorberOriginal

@[expose] public section
/-! The unchanged parent sample inherits the full-root and local load bounds
from the adaptive-deletion estimate by taking empty deletion graphs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_parent_load_base_fields
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (D p k s₀:ℝ)
    (weight:(Fin (m+1)→V)→ℝ) (a:Γ) (j:Color)
    (q:U→Γ→ℝ) (s:U→Color→ℝ) (η C:ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hadapt:∀ δ:ℝ,0≤δ→∀ (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)),
      (∀ x,(DR.degree x:ℝ)≤δ)→(∀ x,(DS.degree x:ℝ)≤δ)→
      MarkedPackingLoadsWithSpokes P π d m D p k s₀ weight a j
        (Function.Embedding.refl U) q s (η+C*δ/Fintype.card V)
        (rawMarkedDeleteRims σ DR.edgeFinset) (markedDeletePhysicalSpokes H DS)):
    MarkedLocalSpokeLoadsWithSpokes P π d m D p k s₀ weight η σ H ∧
    (let seed:=fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
        (fun (_:V) (_:U)=>True) (fun _ _=>True)=>weight W.1.val/(D*p^m*k*s₀^m);
      ∀ root:((V×V)⊕(V×V))⊕(Bool×V×U),
        rawMarkedWheelMarginal P π d p k q s a j root≠0→
        |typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) H root-1|≤η):=by
  have hz:=hadapt 0 le_rfl (⊥:SimpleGraph V) (⊥:SimpleGraph (V⊕U)) (by intro x;simp) (by intro x;simp)
  rw [graph_bottom_edgeFinset_any_instance _,rawMarkedDeleteRims_empty,markedDeletePhysicalSpokes_bottom] at hz
  simp only [mul_zero,zero_div,add_zero] at hz
  refine ⟨hz.1,?_⟩
  exact marked_packing_loads_on_all_hubs P π d m D p k s₀ weight a j q s η σ H hz
end Oberwolfach
