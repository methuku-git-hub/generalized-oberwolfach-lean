module

public import Oberwolfach.OrdinaryTriangleSampledBoundaryCoverDown
public import Oberwolfach.OrdinaryInnerFactorSurvival
public import Oberwolfach.OrdinaryBoundaryChangeFromPacking
public import Oberwolfach.MixedFreshParentClassSizes
public import Oberwolfach.OrdinaryBoundarySelectionMargins

@[expose] public section
/-! Finish the actual triangle boundary after approximate packing and sparse
cleanup, using the same fresh factor and support events. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
set_option synthInstance.maxSize 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_triangle_finish_after_cleanup
    (Q₀ Q Q':SimpleGraph V) (F:SimpleGraph V) (H₀ H H':V→U→Prop)
    (X:Finset V) (Z:Finset U) (C D:SimpleGraph (V⊕U)) (σ:Sym2 (V⊕U)→Bool)
    (γ κ b B ε η ζ p εs τ ν:ℝ)
    (hγ:0<γ) (hκ:0<κ) (hζ:0<ζ) (hp:0<p) (hp1:p≤1) (hτ:0≤τ) (hν:0≤ν)
    (hu:Fintype.card U≤Fintype.card V)
    (data:MixedFreshParentData γ κ b B ε η Q F (ordinaryPhysicalGraph Q H)
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
    (hCinner:Disjoint C (spanningRestriction (ordinaryPhysicalGraph Q₀ H₀) (ordinaryInnerVertices X Z)))
    (hCR:Disjoint C (retainedGraph (ordinaryBoundaryGraph Q₀ H₀ X Z) σ))
    (hpost:ordinaryPhysicalGraph Q' H'=(ordinaryPhysicalGraph Q₀ H₀\C)\D)
    (hQF:Disjoint Q₀ F)
    (hrem:∀w,((((ordinaryPhysicalGraph Q₀ H₀\spanningRestriction (ordinaryPhysicalGraph Q₀ H₀)
      (ordinaryInnerVertices X Z))\retainedGraph (ordinaryBoundaryGraph Q₀ H₀ X Z) σ)\C).degree w:ℝ)≤τ*Fintype.card (V⊕U))
    (hD:∀w,(D.degree w:ℝ)≤ν*Fintype.card (V⊕U))
    (hNoR:∀v∉X,∀w∉X,¬Q'.Adj v w) (hNoS:∀v∉X,∀u∉Z,¬H' v u)
    (hbal:∀v,Q'.degree v=2*(Finset.univ.filter (H' v)).card)
    (hdiv:∀u,3∣(Finset.univ.filter (fun v=>H' v u)).card)
    (hεs:εs≤p^2/4) (hsmall:τ+ν≤p^2/4)
    (hpκ:p≤4*ζ*min (κ/2) γ) (hsqrt:20*Real.sqrt (2*p)≤ζ*min (κ/2) γ/2)
    (hνsmall:ν≤ζ*min (κ/2) γ*p/4)
    (horder:2≤ζ*min (κ/2) γ*p*Fintype.card (V⊕U)/4):
    ∃R:SimpleGraph V,∃S:V→U→Prop,
      R≤Q' ∧ (∀v u,S v u→H' v u) ∧ HasOrdinaryWheelDecomposition R S 3 ∧
      let Qnext:=Q'\R;let Hnext:=fun v u=>H' v u∧¬S v u;
      Qnext≤spanningRestriction Q' X ∧ (∀v u,Hnext v u→H' v u∧v∈X∧u∈Z) ∧
      (∀v,Qnext.degree v=2*(Finset.univ.filter (Hnext v)).card) ∧
      (∀u,3∣(Finset.univ.filter (fun v=>Hnext v u)).card) ∧
      ordinaryHostResources Qnext Hnext⊆ordinaryRootResources X Z ∧
      (∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)).degree w:ℝ)
        ≤2*((2*p)*Fintype.card (V⊕U))):=by
  let n:ℝ:=Fintype.card (V⊕U)
  let κ₀:=min (κ/2) γ
  have hκ₀:0<κ₀:=lt_min (by positivity) hγ
  have hn:0≤n:=by positivity
  have hcard:(Fintype.card (V⊕U):ℝ)≤2*Fintype.card V:=by
    simp only [Fintype.card_sum,Nat.cast_add]
    have hh:(Fintype.card U:ℝ)≤Fintype.card V:=Nat.cast_le.mpr hu
    linarith
  have hsizes:=mixed_fresh_parent_class_sizes γ κ b B ε η hγ.le hκ.le Q F
    (ordinaryPhysicalGraph Q H) (ordinaryPhysicalGraph F (fun _ _=>False))
    (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet H₀ Z X)
    (fun i=>(ordinaryBoundaryRimSet Q₀ X i).image Sum.inl)
    (fun i=>(ordinaryBoundaryRowSet H₀ X Z i).image Sum.inr) data hcard
  have hLnum:(τ+ν)*n≤(p^2/4)*n:=mul_le_mul_of_nonneg_right hsmall hn
  have hδnum:ν*n≤ζ*κ₀*p*n/4:=by
    have hh:=mul_le_mul_of_nonneg_right hνsmall hn
    dsimp only [κ₀] at hh ⊢
    nlinarith only [hh]
  have hnumb:=ordinary_boundary_selection_margins p εs ((τ+ν)*n) (ν*n) κ₀ ζ n hp hp1 hκ₀ hζ hn
    hεs hLnum hpκ hsqrt hδnum horder
  have hclassesY (j:{u:U // u∉Z}):κ₀*n≤((ordinaryBoundaryHubSet H₀ Z X j).card:ℝ):=hsizes.1 j
  have hclassesZ (i:{v:V // v∉X}):κ₀*n≤((ordinaryBoundaryRowSet H₀ X Z i).card:ℝ):=by
    simpa only [Finset.card_image_of_injective _ Sum.inr_injective] using hsizes.2 i
  have hchanges:=ordinary_boundary_change_degree_after_packings Q₀ H₀ X Z C D σ (τ*n) (ν*n) hrem hD
  have hphys:=ordinary_boundary_after_physical_packings Q₀ Q' H₀ H' X Z C D hpost
  have hkeep:=ordinary_inner_factor_edges_survive_cleanup Q₀ Q Q' H₀ H H' X Z C D hbase hCinner hpost
  have hQsub:Q'≤Q₀:=by
    intro v w hvw
    have hh:(ordinaryPhysicalGraph Q' H').Adj (Sum.inl v) (Sum.inl w):=hvw
    rw [hpost] at hh
    exact hh.1.1
  have hQF':Disjoint Q' F:=hQF.mono_left hQsub
  apply ordinary_triangle_sampled_boundary_cover_down Q₀ Q Q' F H₀ H H' X Z C D D σ p (2*p) ζ εs ((τ+ν)*n) (ν*n)
    hgood hp.le hsample hCR hphys (by intro w;convert hchanges w using 1 <;> ring) hD hkeep hQF'
    hNoR hNoS hbal hdiv hnumb.1 hnumb.2.1
  · intro j;exact (hnumb.2.2 _ (hclassesY j)).1
  · intro i;exact (hnumb.2.2 _ (hclassesZ i)).1
  · intro j;exact (hnumb.2.2 _ (hclassesY j)).2
  · intro i;exact (hnumb.2.2 _ (hclassesZ i)).2
end Oberwolfach
