module

public import Oberwolfach.OrdinaryTriangleFinishAfterCleanupInside
public import Oberwolfach.OrdinaryTriangleFinishResult
public import Oberwolfach.OrdinaryCleanupPostFacts

@[expose] public section
/-! Connect the actual approximate packing, its sparse cleanup and the
fresh triangle finish on the same sampled boundary graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
set_option synthInstance.maxSize 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_triangle_finish_after_two_packings_inside
    (Q₀ Q:SimpleGraph V) (F:SimpleGraph V) (H₀ H:V→U→Prop) (X:Finset V) (Z:Finset U)
    (σ:Sym2 (V⊕U)→Bool) (γ κ b B ε η ζ p εs τ ν:ℝ)
    (hγ:0<γ) (hκ:0<κ) (hζ:0<ζ) (hp:0<p) (hp1:p≤1) (hτ:0≤τ) (hν:0≤ν)
    (hu:Fintype.card U≤Fintype.card V)
    (data:MixedFreshParentDataInsideRoots γ κ b B ε η Q F (ordinaryPhysicalGraph Q H)
      (ordinaryPhysicalGraph F (fun _ _=>False)) (Function.Embedding.inl:V↪V⊕U)
      (ordinaryBoundaryHubSet H₀ Z X) (fun i=>(ordinaryBoundaryRimSet Q₀ X i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet H₀ X Z i).image Sum.inr))
    (hgood:MixedFreshBoundaryAvoidingEvent p (2*p) ζ Q F (ordinaryPhysicalGraph Q H)
      (ordinaryPhysicalGraph F (fun _ _=>False)) (Function.Embedding.inl:V↪V⊕U)
      (ordinaryBoundaryHubSet H₀ Z X) (fun i=>(ordinaryBoundaryRimSet Q₀ X i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet H₀ X Z i).image Sum.inr)
      (fun j=>hubSpokeCoin j.val) (fun i=>physicalIncidentCoin (Sum.inl i.val)) data.endpoint_disjoint σ)
    (hsample:BoundaryReserveSupportGood (ordinaryBoundaryGraph Q₀ H₀ X Z) p εs σ)
    (hbase:ordinaryPhysicalGraph Q H≤spanningRestriction (ordinaryPhysicalGraph Q₀ H₀) (ordinaryInnerVertices X Z))
    (hQF:Disjoint Q₀ F)
    (hbal:∀v,Q₀.degree v=2*(Finset.univ.filter (H₀ v)).card)
    (hdiv:∀u,3∣(Finset.univ.filter (fun v=>H₀ v u)).card)
    (hεs:εs≤p^2/4) (hsmall:τ+ν≤p^2/4)
    (hpκ:p≤4*ζ*min (κ/2) γ) (hsqrt:20*Real.sqrt (2*p)≤ζ*min (κ/2) γ/2)
    (hνsmall:ν≤ζ*min (κ/2) γ*p/4)
    (horder:2≤ζ*min (κ/2) γ*p*Fintype.card (V⊕U)/4):
    let R:=retainedGraph (ordinaryBoundaryGraph Q₀ H₀ X Z) σ;
    ∀(M:OrdinaryUnreservedPackingData Q₀ F H₀ X Z R 3 (τ*Fintype.card (V⊕U))),
    let C:=ordinaryPackingUsedGraph Q₀ F H₀ X Z R 3 (τ*Fintype.card (V⊕U)) M;
    let Q₁:=ordinaryPackingPostRim Q₀ F H₀ X Z R 3 (τ*Fintype.card (V⊕U)) M;
    let H₁:=ordinaryPackingPostSpokes Q₀ F H₀ X Z R 3 (τ*Fintype.card (V⊕U)) M;
    ∀(K:OrdinaryOutsideCleanupData Q₁ F H₁ X Z C 3 (ν*Fintype.card (V⊕U))),
    let Q₂:=ordinaryCleanupPostRim Q₁ F H₁ X Z C 3 (ν*Fintype.card (V⊕U)) K;
    let H₂:=ordinaryCleanupPostSpokes Q₁ F H₁ X Z C 3 (ν*Fintype.card (V⊕U)) K;
    OrdinaryTriangleFinishResult Q₂ H₂ X Z p:=by
  intro R M C Q₁ H₁ K Q₂ H₂
  have hm:=ordinary_packing_post_facts Q₀ F H₀ X Z R 3 (τ*Fintype.card (V⊕U)) M hbal hdiv
  have hk:=ordinary_cleanup_post_facts Q₁ F H₁ X Z C 3 (ν*Fintype.card (V⊕U)) K hm.balance hm.divisible
  let D:=ordinaryCleanupUsedGraph Q₁ F H₁ X Z C 3 (ν*Fintype.card (V⊕U)) K
  have hpost:ordinaryPhysicalGraph Q₂ H₂=(ordinaryPhysicalGraph Q₀ H₀\C)\D:=by
    rw [hk.exact_remainder,hm.exact_remainder]
  exact ordinary_triangle_finish_after_cleanup_inside Q₀ Q Q₂ F H₀ H H₂ X Z C D σ γ κ b B ε η ζ p εs τ ν
    hγ hκ hζ hp hp1 hτ hν hu data hgood hsample hbase hm.inner_avoided hm.reserve_avoided hpost hQF
    hm.unreserved_leftover hk.degree hk.no_outer_rim hk.no_outer_spoke hk.balance hk.divisible
    hεs hsmall hpκ hsqrt hνsmall horder
end Oberwolfach
