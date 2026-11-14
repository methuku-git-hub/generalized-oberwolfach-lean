module

public import Oberwolfach.OrdinaryAdaptiveFreshFromCleanupParent
public import Oberwolfach.FiniteLawPositiveEventWitness

@[expose] public section
/-! After the original outcome is fixed, every admissible cleanup parent
    can choose its own fresh auxiliary sample. No union over parents is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_fresh_triangle_for_each_cleanup_parent
    (γ κ b B:ℝ) (hγ:0<γ) (hκ:0<κ) (hb:0<b) (hB:0≤B):
    ∃ε η ζ:ℝ,0<ε ∧ 0<η ∧ 0<ζ ∧
    ∀(p:ℝ) (hp:0<p) (hp1:p≤1) (ρ:ℝ) (hρ:0<ρ)
      (εres εsup βe βh:ℝ) (hres:0<εres) (hsup:0<εsup) (hβe:0<βe) (hβh:0<βh),∃N:ℕ,
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq V] [DecidableEq U],
      N≤Fintype.card V→Fintype.card U≤Fintype.card V→
    ∀(P Q₀ F:SimpleGraph V) (H₀:V→U→Prop) (X:Finset V) (Z:Finset U)
      (π:Equiv.Perm V) (d:ℕ) (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color)
      (pR pH density tR tH Ledit:ℝ),
    let Q:=spanningRestriction Q₀ X;
    let H:=fun v u=>H₀ v u ∧ v∈X ∧ u∈Z;
    OrdinaryCleanupParentProfiles P Q₀ F H₀ π d X Z pR pH density tR tH Ledit βe βh s j raw→
    Nonempty (MixedFreshParentDataInsideRoots γ κ b B ε η Q F
      (ordinaryPhysicalGraph Q H) (ordinaryPhysicalGraph F (fun _ _=>False))
      (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet H₀ Z X)
      (fun i=>(ordinaryBoundaryRimSet Q₀ X i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet H₀ X Z i).image Sum.inr))→
    ∃σ:Sym2 (V⊕U)→Bool,
      OrdinaryBoundaryReserveGood Q₀ H₀ X Z p εres σ ∧
      BoundaryReserveSupportGood (ordinaryBoundaryGraph Q₀ H₀ X Z) p εsup σ ∧
      (∃data:MixedFreshParentDataInsideRoots γ κ b B ε η Q F
        (ordinaryPhysicalGraph Q H) (ordinaryPhysicalGraph F (fun _ _=>False))
        (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet H₀ Z X)
        (fun i=>(ordinaryBoundaryRimSet Q₀ X i).image Sum.inl)
        (fun i=>(ordinaryBoundaryRowSet H₀ X Z i).image Sum.inr),
        MixedFreshBoundaryAvoidingEvent p ρ ζ Q F
          (ordinaryPhysicalGraph Q H) (ordinaryPhysicalGraph F (fun _ _=>False))
          (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet H₀ Z X)
          (fun i=>(ordinaryBoundaryRimSet Q₀ X i).image Sum.inl)
          (fun i=>(ordinaryBoundaryRowSet H₀ X Z i).image Sum.inr)
          (fun j=>hubSpokeCoin j.val) (fun i=>physicalIncidentCoin (Sum.inl i.val)) data.endpoint_disjoint σ) ∧
      OrdinaryBoundaryExtensionGood Q₀ H₀ X βe p σ ∧
      OrdinaryBoundaryHubPairGood H₀ Z βh p σ :=by
  obtain ⟨ε,η,ζ,hε,hη,hζ,hmain⟩:=ordinary_adaptive_fresh_from_cleanup_parent_event γ κ b B hγ hκ hb hB
  refine ⟨ε,η,ζ,hε,hη,hζ,?_⟩
  intro p hp hp1 ρ hρ εres εsup βe βh hres hsup hβe hβh
  obtain ⟨N,hN⟩:=hmain p hp hp1 ρ hρ 1 εres εsup βe βh hres hsup hβe hβh
  refine ⟨max N 6,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hu P Q₀ F H₀ X Z π d s j raw pR pH density tR tH Ledit Q H hprofile hparent
  let μ:FiniteLaw Unit:={mass:=fun _=>1, nonneg:=by intro _;norm_num, total:=by simp}
  have hE:1-(0:ℝ)≤μ.probability (fun _:Unit=>True):=by
    simp [FiniteLaw.probability,μ]
  have hprob:=hN V U Unit Γ Color (by omega) hu μ (fun _=>True) 0 hE
    (fun _=>P) (fun _=>Q₀) (fun _=>F) (fun _=>H₀) (fun _=>X) (fun _=>Z) π d s j (fun _=>raw)
    pR pH density tR tH Ledit (fun _ _=>hprofile) (fun _ _=>hparent)
  have hcard:6≤(Fintype.card V:ℝ):=by exact_mod_cast (show 6≤Fintype.card V by omega)
  have hcardSum:(Fintype.card V:ℝ)≤Fintype.card (V⊕U):=by
    exact_mod_cast Fintype.card_le_of_injective (Sum.inl:V→V⊕U) Sum.inl_injective
  have h4:4/(Fintype.card (V⊕U):ℝ)≤4/6:=by gcongr <;> linarith
  have h1:1/(Fintype.card V:ℝ)≤1/6:=by gcongr <;> linarith
  have hpos:0<1-(4/(Fintype.card (V⊕U):ℝ)+1/(Fintype.card V:ℝ)):=by linarith
  have hp':0<((μ.sigma (fun _=>FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1))).probability
    (fun z=>True ∧ OrdinaryBoundaryReserveGood Q₀ H₀ X Z p εres z.2 ∧
      BoundaryReserveSupportGood (ordinaryBoundaryGraph Q₀ H₀ X Z) p εsup z.2 ∧
      (∃hE:True,MixedFreshBoundaryAvoidingEvent p ρ ζ Q F
        (ordinaryPhysicalGraph Q H) (ordinaryPhysicalGraph F (fun _ _=>False))
        (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet H₀ Z X)
        (fun i=>(ordinaryBoundaryRimSet Q₀ X i).image Sum.inl)
        (fun i=>(ordinaryBoundaryRowSet H₀ X Z i).image Sum.inr)
        (fun j=>hubSpokeCoin j.val) (fun i=>physicalIncidentCoin (Sum.inl i.val))
        (Classical.choice hparent).endpoint_disjoint z.2) ∧
      OrdinaryBoundaryExtensionGood Q₀ H₀ X βe p z.2 ∧ OrdinaryBoundaryHubPairGood H₀ Z βh p z.2)):=by
    apply lt_of_lt_of_le hpos
    simpa only [zero_add,pow_one] using hprob
  obtain ⟨z,_,hz⟩:=finiteLaw_positive_mass_witness_of_event _ _ hp'
  obtain ⟨_,hreserve,hsupport,⟨_,hfresh⟩,hext,hhub⟩:=hz
  exact ⟨z.2,hreserve,hsupport,⟨Classical.choice hparent,hfresh⟩,hext,hhub⟩
end Oberwolfach
