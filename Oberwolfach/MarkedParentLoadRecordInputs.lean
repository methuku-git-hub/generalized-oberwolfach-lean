module

public import Oberwolfach.MarkedParentLoadBaseFields
public import Oberwolfach.MarkedLocalEstimateMonotonicity

@[expose] public section
/-! Original-sample parent load inputs with the record error tolerances. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
theorem marked_parent_load_record_inputs
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (D p k s₀:ℝ)
    (weight:(Fin (m+1)→V)→ℝ) (a:Γ) (j:Color)
    (q:U→Γ→ℝ) (s:U→Color→ℝ) (η C κ thetaDeep:ℝ)
    (hpot:η≤κ/4) (hlocal:η≤thetaDeep/4)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hadapt:∀ δ:ℝ,0≤δ→∀ (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)),
      (∀ x,(DR.degree x:ℝ)≤δ)→(∀ x,(DS.degree x:ℝ)≤δ)→
      MarkedPackingLoadsWithSpokes P π d m D p k s₀ weight a j
        (Function.Embedding.refl U) q s (η+C*δ/Fintype.card V)
        (rawMarkedDeleteRims σ DR.edgeFinset) (markedDeletePhysicalSpokes H DS)):
    MarkedLocalSpokeLoadsWithSpokes P π d m D p k s₀ weight (thetaDeep/4) σ H ∧
    (let seed:=fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
        (fun (_:V) (_:U)=>True) (fun _ _=>True)=>weight W.1.val/(D*p^m*k*s₀^m);
      ∀ root:((V×V)⊕(V×V))⊕(Bool×V×U),
        rawMarkedWheelMarginal P π d p k q s a j root≠0→
        |typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) H root-1|≤κ/4) :=by
  obtain ⟨hl,hp⟩:=marked_parent_load_base_fields P π d m D p k s₀ weight a j q s η C σ H hadapt
  constructor
  · exact markedLocalSpokeLoads_mono P π d m D p k s₀ weight η (thetaDeep/4) hlocal σ H hl
  · intro seed root hroot
    exact (hp root hroot).trans hpot
end Oberwolfach
