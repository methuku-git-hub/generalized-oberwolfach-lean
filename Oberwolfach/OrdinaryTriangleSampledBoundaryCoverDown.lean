module

public import Oberwolfach.OrdinaryTriangleSampledBoundarySelection
public import Oberwolfach.OrdinaryTriangleCanonicalDomainBoundary

@[expose] public section
/-! Same-sample triangle boundary factors yield the actual wheel cover-down
and balanced divisible next-level host after the preceding packings. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_triangle_sampled_boundary_cover_down
    (Q₀ Q Q' F:SimpleGraph V) (H₀ H H':V→U→Prop) (X:Finset V) (Z:Finset U)
    (C D K:SimpleGraph (V⊕U)) (σ:Sym2 (V⊕U)→Bool) (p ρ ζ ε L δ:ℝ)
    (hgood:MixedFreshBoundaryAvoidingEvent p ρ ζ Q F (ordinaryPhysicalGraph Q H)
      (ordinaryPhysicalGraph F (fun _ _=>False)) (Function.Embedding.inl:V↪V⊕U)
      (ordinaryBoundaryHubSet H₀ Z X)
      (fun i=>(ordinaryBoundaryRimSet Q₀ X i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet H₀ X Z i).image Sum.inr)
      (fun j=>hubSpokeCoin j.val) (fun i=>physicalIncidentCoin (Sum.inl i.val))
      (ordinary_boundary_root_domains_disjoint Q₀ H₀ X Z) σ)
    (hτ:0≤p) (hsample:BoundaryReserveSupportGood (ordinaryBoundaryGraph Q₀ H₀ X Z) p ε σ)
    (hCR:Disjoint C (retainedGraph (ordinaryBoundaryGraph Q₀ H₀ X Z) σ))
    (hphys:ordinaryBoundaryGraph Q' H' X Z=((ordinaryBoundaryGraph Q₀ H₀ X Z\C)\D))
    (hL:∀w,((((ordinaryBoundaryGraph Q₀ H₀ X Z)\retainedGraph (ordinaryBoundaryGraph Q₀ H₀ X Z) σ)\C).degree w:ℝ)+
      (D.degree w:ℝ)≤L)
    (hK:∀w,(K.degree w:ℝ)≤δ)
    (hkeep:ordinaryPhysicalGraph Q H\K≤ordinaryPhysicalGraph Q' H')
    (hQF:Disjoint Q' F)
    (hNoR:∀v∉X,∀w∉X,¬Q'.Adj v w)
    (hNoS:∀v∉X,∀u∉Z,¬H' v u)
    (hbal:∀v,Q'.degree v=2*(Finset.univ.filter (H' v)).card)
    (hdiv:∀u,3∣(Finset.univ.filter (fun v=>H' v u)).card)
    (hdeg:(p+ε)*Fintype.card (V⊕U)+L≤ρ*Fintype.card (V⊕U))
    (hpair:(p^2+ε)*Fintype.card (V⊕U)+2*L≤ρ^2*Fintype.card (V⊕U))
    (hscaleY:∀j:{u:U // u∉Z},L≤ζ*(p*(ordinaryBoundaryHubSet H₀ Z X j).card))
    (hscaleZ:∀i:{v:V // v∉X},L≤ζ*(p*(ordinaryBoundaryRowSet H₀ X Z i).card))
    (hbudgetY:∀j:{u:U // u∉Z},2*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))+
      2*(Nat.ceil (4*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))):ℝ)+δ≤ζ*(p*(ordinaryBoundaryHubSet H₀ Z X j).card))
    (hbudgetZ:∀i:{v:V // v∉X},2*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))+
      2*(Nat.ceil (4*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))):ℝ)+δ≤ζ*(p*(ordinaryBoundaryRowSet H₀ X Z i).card)):
    ∃R:SimpleGraph V,∃S:V→U→Prop,
      R≤Q' ∧ (∀v u,S v u→H' v u) ∧ HasOrdinaryWheelDecomposition R S 3 ∧
      let Qnext:=Q'\R;let Hnext:=fun v u=>H' v u∧¬S v u;
      Qnext≤spanningRestriction Q' X ∧ (∀v u,Hnext v u→H' v u∧v∈X∧u∈Z) ∧
      (∀v,Qnext.degree v=2*(Finset.univ.filter (Hnext v)).card) ∧
      (∀u,3∣(Finset.univ.filter (fun v=>Hnext v u)).card) ∧
      ordinaryHostResources Qnext Hnext⊆ordinaryRootResources X Z ∧
      (∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)).degree w:ℝ)
        ≤2*(ρ*Fintype.card (V⊕U))):=by
  obtain ⟨Csel⟩:=ordinary_triangle_sampled_boundary_selection Q₀ Q Q' F H₀ H H' X Z C D K σ p ρ ζ ε L δ
    hgood hτ hsample hCR hphys hL hK hkeep hNoR hNoS hbal hdiv hdeg hpair hscaleY hscaleZ hbudgetY hbudgetZ
  exact ordinary_triangle_canonical_boundary_remainder_on_domains Q' F H' X Z hQF hNoR hNoS hbal hdiv
    (ordinaryBoundaryHubSet H₀ Z X) (2*(ρ*Fintype.card (V⊕U))) Csel
end Oberwolfach
