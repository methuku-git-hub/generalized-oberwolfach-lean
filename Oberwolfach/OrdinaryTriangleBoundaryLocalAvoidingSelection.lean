module

public import Oberwolfach.OrdinaryTriangleFreshEventActualHostWithAvoid
public import Oberwolfach.OrdinaryBoundaryFactorClassesOutsideDegree
public import Oberwolfach.OrdinaryBoundarySupportFromSample
public import Oberwolfach.OrdinaryBoundaryClassDivisibility
public import Oberwolfach.OrdinaryBoundaryFactorClassesAfterPacking
public import Oberwolfach.OrdinaryBoundaryClassesMonotone

@[expose] public section
/-! Actual triangle boundary factors after packing, with class overlap,
class changes, balance and divisibility discharged from the actual graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_triangle_sampled_boundary_selection_local_avoiding
    (Q₀ Q Q' F:SimpleGraph V) (H₀ H H':V→U→Prop) (X:Finset V) (Z:Finset U)
    (C Dsupport Dclass K:SimpleGraph (V⊕U)) (σ:Sym2 (V⊕U)→Bool) (p ρ ζ ε Lsupport Lclass δ:ℝ)
    (hgood:MixedFreshBoundaryAvoidingEvent p ρ ζ Q F (ordinaryPhysicalGraph Q H)
      (ordinaryPhysicalGraph F (fun _ _=>False)) (Function.Embedding.inl:V↪V⊕U)
      (ordinaryBoundaryHubSet H₀ Z X)
      (fun i=>(ordinaryBoundaryRimSet Q₀ X i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet H₀ X Z i).image Sum.inr)
      (fun j=>hubSpokeCoin j.val) (fun i=>physicalIncidentCoin (Sum.inl i.val))
      (ordinary_boundary_root_domains_disjoint Q₀ H₀ X Z) σ)
    (hτ:0≤p) (hsample:BoundaryReserveSupportGood (ordinaryBoundaryGraph Q₀ H₀ X Z) p ε σ)
    (hCR:Disjoint C (retainedGraph (ordinaryBoundaryGraph Q₀ H₀ X Z) σ))
    (hphys:ordinaryBoundaryGraph Q' H' X Z=((ordinaryBoundaryGraph Q₀ H₀ X Z\C)\Dclass))
    (hsupport:ordinaryBoundaryGraph Q' H' X Z≤((ordinaryBoundaryGraph Q₀ H₀ X Z\C)\Dsupport))
    (hLsupport:∀w,((((ordinaryBoundaryGraph Q₀ H₀ X Z)\retainedGraph (ordinaryBoundaryGraph Q₀ H₀ X Z) σ)\C).degree w:ℝ)+
      (Dsupport.degree w:ℝ)≤Lsupport)
    (hLhub:∀j:{u:U // u∉Z},((((ordinaryBoundaryGraph Q₀ H₀ X Z)\retainedGraph (ordinaryBoundaryGraph Q₀ H₀ X Z) σ)\C).degree (Sum.inr j.val):ℝ)+
      (Dclass.degree (Sum.inr j.val):ℝ)≤Lclass)
    (hLrim:∀i:{v:V // v∉X},((((ordinaryBoundaryGraph Q₀ H₀ X Z)\retainedGraph (ordinaryBoundaryGraph Q₀ H₀ X Z) σ)\C).degree (Sum.inl i.val):ℝ)+
      (Dclass.degree (Sum.inl i.val):ℝ)≤Lclass)
    (hK:∀w,(K.degree w:ℝ)≤δ)
    (hkeep:ordinaryPhysicalGraph Q H\K≤ordinaryPhysicalGraph Q' H')
    (hNoR:∀v∉X,∀w∉X,¬Q'.Adj v w)
    (hNoS:∀v∉X,∀u∉Z,¬H' v u)
    (hbal:∀v,Q'.degree v=2*(Finset.univ.filter (H' v)).card)
    (hdiv:∀u,3∣(Finset.univ.filter (fun v=>H' v u)).card)
    (hdeg:(p+ε)*Fintype.card (V⊕U)+Lsupport≤ρ*Fintype.card (V⊕U))
    (hpair:(p^2+ε)*Fintype.card (V⊕U)+2*Lsupport≤ρ^2*Fintype.card (V⊕U))
    (hscaleY:∀j:{u:U // u∉Z},Lclass≤ζ*(p*(ordinaryBoundaryHubSet H₀ Z X j).card))
    (hscaleZ:∀i:{v:V // v∉X},Lclass≤ζ*(p*(ordinaryBoundaryRowSet H₀ X Z i).card))
    (hbudgetY:∀j:{u:U // u∉Z},2*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))+
      2*(Nat.ceil (4*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))):ℝ)+δ≤ζ*(p*(ordinaryBoundaryHubSet H₀ Z X j).card))
    (hbudgetZ:∀i:{v:V // v∉X},2*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))+
      2*(Nat.ceil (4*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))):ℝ)+δ≤ζ*(p*(ordinaryBoundaryRowSet H₀ X Z i).card)):
    ∃Csel:OrdinaryTriangleSelectedFactors Q' F H' (ordinaryBoundaryRimSet Q' X) (ordinaryBoundaryRowSet H' X Z)
      (ordinaryBoundaryHubSet H₀ Z X) (ordinaryBoundaryHubSet H' Z X)
      (ordinary_boundary_root_domains_disjoint Q' H' X Z) (2*(ρ*Fintype.card (V⊕U))),
      (∀j,Disjoint ((localOrdinaryFactorGraph (Csel.hub j)).map (Function.Embedding.inl:V↪V⊕U)) K) ∧
      (∀i,Disjoint (endpointFactorGraph (ordinary_boundary_root_domains_disjoint Q' H' X Z i) (Csel.row i)) K):=by
  let G:=ordinaryBoundaryGraph Q₀ H₀ X Z
  have hsub:ordinaryBoundaryGraph Q' H' X Z≤G:=by rw [hphys];exact sdiff_le.trans sdiff_le
  have hm:=ordinary_boundary_classes_of_subgraph Q₀ Q' H₀ H' X Z hsub
  have hA (i:{v:V // v∉X}):(ordinaryBoundaryRimSet Q' X i).image (Sum.inl:V→V⊕U)⊆
      (ordinaryBoundaryRimSet Q₀ X i).image (Sum.inl:V→V⊕U):=Finset.image_subset_image (hm.2.1 i)
  have hB (i:{v:V // v∉X}):(ordinaryBoundaryRowSet H' X Z i).image (Sum.inr:U→V⊕U)⊆
      (ordinaryBoundaryRowSet H₀ X Z i).image (Sum.inr:U→V⊕U):=Finset.image_subset_image (hm.2.2 i)
  have hd:=ordinary_boundary_local_class_divisibility Q' H' X Z hNoR hNoS hbal hdiv
  have hr (i:{v:V // v∉X}):
      (((ordinaryBoundaryRimSet Q' X i).image Sum.inl∪(ordinaryBoundaryRowSet H' X Z i).image Sum.inr)∩
        (ordinaryBoundaryRimSet Q₀ X i).image Sum.inl).card=
      2*((((ordinaryBoundaryRimSet Q' X i).image Sum.inl∪(ordinaryBoundaryRowSet H' X Z i).image Sum.inr)∩
        (ordinaryBoundaryRowSet H₀ X Z i).image Sum.inr).card):=
    endpoint_image_union_ratio_of_classes _ _ _ _ (ordinary_boundary_root_domains_disjoint Q₀ H₀ X Z i) (hA i) (hB i) (hd.1 i)
  have hc:=ordinary_boundary_factor_classes_after_packing_outside_degree Q₀ Q' H₀ H' X Z C Dclass σ Lclass hCR hphys hLhub hLrim
  have hs:=ordinary_boundary_supports_from_sample Q' H' X Z G C Dsupport σ p ε Lsupport ρ hτ hsample hCR hLsupport
    hsupport hdeg hpair
  apply ordinary_triangle_fresh_event_actual_host_with_avoid p ρ ζ Q Q' F H H' _ _ _ _ _
    (ordinary_boundary_root_domains_disjoint Q₀ H₀ X Z) σ hgood
    (ordinaryBoundaryHubSet H' Z X) (ordinaryBoundaryRimSet Q' X) (ordinaryBoundaryRowSet H' X Z)
    (ordinary_boundary_root_domains_disjoint Q' H' X Z) hA hB K δ hK hm.1 hd.2 hr
  · intro j;exact (hc.1 j).trans (hscaleY j)
  · intro i;simpa only [Finset.card_image_of_injective _ Sum.inr_injective] using (hc.2 i).trans (hscaleZ i)
  · intro a b hab
    have hh:=hs.1 a b hab
    convert hh using 1 <;> simp only [ordinaryBoundaryPhysicalSupports] <;> congr! 12 <;> exact Subsingleton.elim _ _
  · intro w
    have hh:=hs.2 w
    convert hh using 1 <;> simp only [ordinaryBoundaryPhysicalSupports] <;> congr! 12 <;> exact Subsingleton.elim _ _
  · exact hbudgetY
  · intro i;simpa only [Finset.card_image_of_injective _ Sum.inr_injective] using hbudgetZ i
  · exact hkeep
end Oberwolfach
