module

public import Oberwolfach.OrdinaryGeneralSampledBoundarySelection
public import Oberwolfach.OrdinaryGeneralCanonicalRemainderInHost
public import Oberwolfach.OrdinaryBoundaryClassDegreeBounds
public import Oberwolfach.OrdinaryBoundarySeparateClassChanges
public import Oberwolfach.OrdinaryBoundarySupportFromSample
public import Oberwolfach.OrdinaryBoundaryClassDivisibilityGeneral
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

theorem ordinary_general_sampled_boundary_remainder_in_host
    (m:ℕ) (hm:3≤m)
    (Q₀ Q Q' F:SimpleGraph V) (H₀ H H':V→U→Prop) (X:Finset V) (Z:Finset U)
    (C D K:SimpleGraph (V⊕U)) (σ:Sym2 (V⊕U)→Bool) (p ρ ζ ε L δ:ℝ)
    (hgood:MixedFreshPairingAvoidingEvent m p ρ ζ Q F (ordinaryPhysicalGraph Q H)
      (ordinaryPhysicalGraph F (fun _ _=>False)) (Function.Embedding.inl:V↪V⊕U)
      (ordinaryBoundaryHubSet H₀ Z X)
      (fun i=>(ordinaryBoundaryRimSet Q₀ X i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet H₀ X Z i).image Sum.inr)
      (fun j=>hubSpokeCoin j.val) (fun i=>physicalIncidentCoin (Sum.inl i.val))
      σ)
    (hτ:0≤p) (hsample:BoundaryReserveSupportGood (ordinaryBoundaryGraph Q₀ H₀ X Z) p ε σ)
    (hCR:Disjoint C (retainedGraph (ordinaryBoundaryGraph Q₀ H₀ X Z) σ))
    (hphys:ordinaryBoundaryGraph Q' H' X Z=((ordinaryBoundaryGraph Q₀ H₀ X Z\C)\D))
    (hL:∀w,((((ordinaryBoundaryGraph Q₀ H₀ X Z)\retainedGraph (ordinaryBoundaryGraph Q₀ H₀ X Z) σ)\C).degree w:ℝ)+
      (D.degree w:ℝ)≤L)
    (hK:∀w,(K.degree w:ℝ)≤δ)
    (hkeep:ordinaryPhysicalGraph Q H\K≤ordinaryPhysicalGraph Q' H')
    (hNoR:∀v∉X,∀w∉X,¬Q'.Adj v w)
    (hNoS:∀v∉X,∀u∉Z,¬H' v u)
    (hbal:∀v,Q'.degree v=2*(Finset.univ.filter (H' v)).card)
    (hdiv:∀u,(m+1)∣(Finset.univ.filter (fun v=>H' v u)).card)
    (hdeg:(p+ε)*Fintype.card (V⊕U)+L≤ρ*Fintype.card (V⊕U))
    (hpair:(p^2+ε)*Fintype.card (V⊕U)+2*L≤ρ^2*Fintype.card (V⊕U))
    (hscaleY:∀j:{u:U // u∉Z},L≤ζ*(p*(ordinaryBoundaryHubSet H₀ Z X j).card))
    (hscaleZ:L≤ζ*(p*Fintype.card (V⊕U)))
    (hbudgetY:∀j:{u:U // u∉Z},2*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))+
      2*(Nat.ceil (4*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))):ℝ)+δ≤ζ*(p*(ordinaryBoundaryHubSet H₀ Z X j).card))
    (hbudgetZ:2*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))+
      2*(Nat.ceil (4*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))):ℝ)+δ≤ζ*(p*Fintype.card (V⊕U))):
    ∀(hQF:Disjoint Q' F) (Dmax Kcap:ℕ) (hKcap:0<Kcap)
      (hQdeg:∀w:V⊕U,(ordinaryPhysicalGraph Q' H').degree w≤Dmax)
      (Lconf bcount:ℝ) (hLconf:0≤Lconf) (hF:∀v,(F.degree v:ℝ)≤Lconf)
      (hcount:∀i,∀z∈ordinaryBoundaryRowSet H' X Z i,∀v∈X,∀w∈X,
        bcount≤(((X.filter (fun a=>H' a z))∩Q'.neighborFinset v∩Q'.neighborFinset w).card:ℝ))
      (hcompletion:((Fintype.card (Σi:{v:V // v∉X},ordinaryBoundaryRowSet H' X Z i)*(m+1):ℕ):ℝ)/(Kcap:ℝ)+
        (((m+1:ℕ):ℝ)+3)*(Lconf+1)+2*(2*(ρ*Fintype.card (V⊕U))+2*((Kcap+Dmax:ℕ):ℝ))+
        (Dmax:ℝ)+((Dmax*(m+1):ℕ):ℝ)+3*Dmax<bcount),
    ∃R:SimpleGraph V,∃S:V→U→Prop,
      R≤Q' ∧ (∀v u,S v u→H' v u) ∧
      HasResourceDecomposition (ordinaryWheelResources (P:=Q') (F:=F) (Hbase:=H') (r:=m+1)) (ordinaryHostResources R S) ∧
      HasOrdinaryWheelDecomposition R S (m+1) ∧
      let Qnext:=Q'\R;let Hnext:=fun v u=>H' v u∧¬S v u;
      Qnext≤spanningRestriction Q' X ∧ (∀v u,Hnext v u→H' v u∧v∈X∧u∈Z) ∧
      (∀v,Qnext.degree v=2*(Finset.univ.filter (Hnext v)).card) ∧
      (∀u,(m+1)∣(Finset.univ.filter (fun v=>Hnext v u)).card) ∧
      ordinaryHostResources Qnext Hnext⊆ordinaryRootResources X Z ∧
      (∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)).degree w:ℝ)≤
        2*(ρ*Fintype.card (V⊕U))+((3*(Kcap+Dmax)+Dmax*(m+1):ℕ):ℝ)):=by
  intro hQF Dmax Kcap hKcap hQdeg Lconf bcount hLconf hF hcount hcompletion
  obtain ⟨selected⟩:=ordinary_general_sampled_boundary_selection m Q₀ Q Q' F H₀ H H' X Z C D K σ p ρ ζ ε L δ
    hgood hτ hsample hCR hphys hL hK hkeep hNoR hNoS hbal hdiv hdeg hpair hscaleY hscaleZ hbudgetY hbudgetZ
  have hclass:=ordinary_boundary_class_degree_bounds Q' H' X Z Dmax hQdeg
  exact ordinary_general_canonical_boundary_remainder_in_host m hm Q' F H' X Z hQF hNoR hNoS hbal hdiv
    (ordinaryBoundaryHubSet H₀ Z X) Kcap Dmax hKcap hclass.1 hclass.2.1 hclass.2.2.1 hclass.2.2.2
    Lconf (2*(ρ*Fintype.card (V⊕U))) bcount hLconf hF hcount hcompletion selected
end Oberwolfach
