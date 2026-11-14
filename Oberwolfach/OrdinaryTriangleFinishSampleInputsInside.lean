module

public import Oberwolfach.OrdinaryTriangleFinishTwoPackingsInside

@[expose] public section
/-! Per-outcome assumptions for applying the final triangle boundary
factors after the approximate packing and sparse cleanup. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

structure OrdinaryTriangleFinishSampleInputsInside
    (Q₀ Q F:SimpleGraph V) (H₀ H:V→U→Prop) (X:Finset V) (Z:Finset U)
    (σ:Sym2 (V⊕U)→Bool) (γ κ b B ε η ζ p εs τ ν:ℝ):Prop where
  gamma_pos:0<γ
  kappa_pos:0<κ
  zeta_pos:0<ζ
  p_pos:0<p
  p_le_one:p≤1
  tau_nonneg:0≤τ
  nu_nonneg:0≤ν
  hub_upper:Fintype.card U≤Fintype.card V
  factors:∃data:MixedFreshParentDataInsideRoots γ κ b B ε η Q F (ordinaryPhysicalGraph Q H)
      (ordinaryPhysicalGraph F (fun _ _=>False)) (Function.Embedding.inl:V↪V⊕U)
      (ordinaryBoundaryHubSet H₀ Z X) (fun i=>(ordinaryBoundaryRimSet Q₀ X i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet H₀ X Z i).image Sum.inr),
    MixedFreshBoundaryAvoidingEvent p (2*p) ζ Q F (ordinaryPhysicalGraph Q H)
      (ordinaryPhysicalGraph F (fun _ _=>False)) (Function.Embedding.inl:V↪V⊕U)
      (ordinaryBoundaryHubSet H₀ Z X) (fun i=>(ordinaryBoundaryRimSet Q₀ X i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet H₀ X Z i).image Sum.inr)
      (fun j=>hubSpokeCoin j.val) (fun i=>physicalIncidentCoin (Sum.inl i.val)) data.endpoint_disjoint σ
  support:BoundaryReserveSupportGood (ordinaryBoundaryGraph Q₀ H₀ X Z) p εs σ
  factor_base:ordinaryPhysicalGraph Q H≤spanningRestriction (ordinaryPhysicalGraph Q₀ H₀) (ordinaryInnerVertices X Z)
  forbidden:Disjoint Q₀ F
  balanced:∀v,Q₀.degree v=2*(Finset.univ.filter (H₀ v)).card
  divisible:∀u,3∣(Finset.univ.filter (fun v=>H₀ v u)).card
  support_small:εs≤p^2/4
  deletion_small:τ+ν≤p^2/4
  density_small:p≤4*ζ*min (κ/2) γ
  sqrt_small:20*Real.sqrt (2*p)≤ζ*min (κ/2) γ/2
  cleanup_small:ν≤ζ*min (κ/2) γ*p/4
  order:2≤ζ*min (κ/2) γ*p*Fintype.card (V⊕U)/4

theorem ordinary_triangle_finish_from_inside_sample_inputs
    (Q₀ Q F:SimpleGraph V) (H₀ H:V→U→Prop) (X:Finset V) (Z:Finset U)
    (σ:Sym2 (V⊕U)→Bool) (γ κ b B ε η ζ p εs τ ν:ℝ)
    (i:OrdinaryTriangleFinishSampleInputsInside Q₀ Q F H₀ H X Z σ γ κ b B ε η ζ p εs τ ν):
    let R:=retainedGraph (ordinaryBoundaryGraph Q₀ H₀ X Z) σ;
    ∀(M:OrdinaryUnreservedPackingData Q₀ F H₀ X Z R 3 (τ*Fintype.card (V⊕U))),
    let C:=ordinaryPackingUsedGraph Q₀ F H₀ X Z R 3 (τ*Fintype.card (V⊕U)) M;
    let Q₁:=ordinaryPackingPostRim Q₀ F H₀ X Z R 3 (τ*Fintype.card (V⊕U)) M;
    let H₁:=ordinaryPackingPostSpokes Q₀ F H₀ X Z R 3 (τ*Fintype.card (V⊕U)) M;
    ∀(K:OrdinaryOutsideCleanupData Q₁ F H₁ X Z C 3 (ν*Fintype.card (V⊕U))),
    OrdinaryTriangleFinishResult
      (ordinaryCleanupPostRim Q₁ F H₁ X Z C 3 (ν*Fintype.card (V⊕U)) K)
      (ordinaryCleanupPostSpokes Q₁ F H₁ X Z C 3 (ν*Fintype.card (V⊕U)) K) X Z p:=by
  obtain ⟨data,hgood⟩:=i.factors
  exact ordinary_triangle_finish_after_two_packings_inside Q₀ Q F H₀ H X Z σ γ κ b B ε η ζ p εs τ ν
    i.gamma_pos i.kappa_pos i.zeta_pos i.p_pos i.p_le_one i.tau_nonneg i.nu_nonneg i.hub_upper
    data hgood i.support i.factor_base i.forbidden i.balanced i.divisible i.support_small i.deletion_small
    i.density_small i.sqrt_small i.cleanup_small i.order
end Oberwolfach
