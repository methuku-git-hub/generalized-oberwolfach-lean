module

public import Oberwolfach.OrdinaryBoundaryRowSumFromBoundary
public import Oberwolfach.OrdinaryGeneralSampledRemainderBoundaryDegree
public import Oberwolfach.BoundaryDegreeAfterPacking
public import Oberwolfach.OrdinaryGeneralFinishHostResult
public import Oberwolfach.OrdinaryInnerCountsAfterPackingCleanup
public import Oberwolfach.OrdinaryCleanupPostFacts
public import Oberwolfach.OrdinaryInnerFactorSurvival
public import Oberwolfach.OrdinaryBoundaryChangeFromPacking
public import Oberwolfach.OrdinaryBoundaryRowSumBound

@[expose] public section
/-! Complete the actual general-length boundary following the unreserved
packing and its sparse cleanup, with the extension counts inherited from the
same boundary sample. Numerical and parent-event inputs remain explicit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 24000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_general_finish_after_two_packings_boundary_degree
    (m:ℕ) (hm:3≤m)
    (P Q₀ Q F:SimpleGraph V) (H₀ H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ)
    (X:Finset V) (Z:Finset U) (σ:Sym2 (V⊕U)→Bool)
    (pR pH p density tR tH Ledit βe βh t ν ρ ζ ε:ℝ)
    (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color)
    (profile:OrdinaryCleanupParentProfiles P Q₀ F H₀ π d X Z pR pH density tR tH Ledit βe βh s j raw)
    (hgood:MixedFreshPairingAvoidingEvent m p ρ ζ Q F (ordinaryPhysicalGraph Q H)
      (ordinaryPhysicalGraph F (fun _ _=>False)) (Function.Embedding.inl:V↪V⊕U)
      (ordinaryBoundaryHubSet H₀ Z X)
      (fun i=>(ordinaryBoundaryRimSet Q₀ X i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet H₀ X Z i).image Sum.inr)
      (fun j=>hubSpokeCoin j.val) (fun i=>physicalIncidentCoin (Sum.inl i.val)) σ)
    (hp:0≤p) (hsample:BoundaryReserveSupportGood (ordinaryBoundaryGraph Q₀ H₀ X Z) p ε σ)
    (hbase:ordinaryPhysicalGraph Q H≤spanningRestriction (ordinaryPhysicalGraph Q₀ H₀) (ordinaryInnerVertices X Z))
    (hQF:Disjoint Q₀ F)
    (hbal:∀v,Q₀.degree v=2*(Finset.univ.filter (H₀ v)).card)
    (hdiv:∀u,(m+1)∣(Finset.univ.filter (fun v=>H₀ v u)).card)
    (hdeg:(p+ε)*Fintype.card (V⊕U)+(t+ν)≤ρ*Fintype.card (V⊕U))
    (hpair:(p^2+ε)*Fintype.card (V⊕U)+2*(t+ν)≤ρ^2*Fintype.card (V⊕U))
    (hscaleY:∀j:{u:U // u∉Z},t+ν≤ζ*(p*(ordinaryBoundaryHubSet H₀ Z X j).card))
    (hscaleZ:t+ν≤ζ*(p*Fintype.card (V⊕U)))
    (hbudgetY:∀j:{u:U // u∉Z},2*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))+
      2*(Nat.ceil (4*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))):ℝ)+ν≤ζ*(p*(ordinaryBoundaryHubSet H₀ Z X j).card))
    (hbudgetZ:2*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))+
      2*(Nat.ceil (4*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))):ℝ)+ν≤ζ*(p*Fintype.card (V⊕U)))
    (Dmax Kcap:ℕ) (hKcap:0<Kcap)
    (hDmax:ρ*Fintype.card (V⊕U)≤(Dmax:ℝ))
    (Lconf:ℝ) (hLconf:0≤Lconf) (hF:∀v,(F.degree v:ℝ)≤Lconf)
    (hcompletion:(((Fintype.card (V⊕U)*Dmax*(m+1):ℕ):ℝ)/(Kcap:ℝ)+
      (((m+1:ℕ):ℝ)+3)*(Lconf+1)+2*(2*(ρ*Fintype.card (V⊕U))+2*((Kcap+Dmax:ℕ):ℝ))+
      (Dmax:ℝ)+((Dmax*(m+1):ℕ):ℝ)+3*Dmax < βe*Fintype.card (V⊕U)-3*ν)):
    let R:=retainedGraph (ordinaryBoundaryGraph Q₀ H₀ X Z) σ;
    ∀(M:OrdinaryUnreservedPackingData Q₀ F H₀ X Z R (m+1) t),
    let C:=ordinaryPackingUsedGraph Q₀ F H₀ X Z R (m+1) t M;
    let Q₁:=ordinaryPackingPostRim Q₀ F H₀ X Z R (m+1) t M;
    let H₁:=ordinaryPackingPostSpokes Q₀ F H₀ X Z R (m+1) t M;
    ∀(K:OrdinaryOutsideCleanupData Q₁ F H₁ X Z C (m+1) ν),
    let Q₂:=ordinaryCleanupPostRim Q₁ F H₁ X Z C (m+1) ν K;
    let H₂:=ordinaryCleanupPostSpokes Q₁ F H₁ X Z C (m+1) ν K;
    OrdinaryGeneralFinishHostResult Q₂ F H₂ X Z m Kcap Dmax ρ:=by
  intro R M C Q₁ H₁ K Q₂ H₂
  have hm0:=ordinary_packing_post_facts Q₀ F H₀ X Z R (m+1) t M hbal hdiv
  have hk:=ordinary_cleanup_post_facts Q₁ F H₁ X Z C (m+1) ν K hm0.balance hm0.divisible
  let D:=ordinaryCleanupUsedGraph Q₁ F H₁ X Z C (m+1) ν K
  have hpost:ordinaryPhysicalGraph Q₂ H₂=(ordinaryPhysicalGraph Q₀ H₀\C)\D:=by
    rw [hk.exact_remainder,hm0.exact_remainder]
  have hphys:=ordinary_boundary_after_physical_packings Q₀ Q₂ H₀ H₂ X Z C D hpost
  have hkeep:=ordinary_inner_factor_edges_survive_cleanup Q₀ Q Q₂ H₀ H H₂ X Z C D hbase hm0.inner_avoided hpost
  have hchanges:=ordinary_boundary_change_degree_after_packings Q₀ H₀ X Z C D σ t ν hm0.unreserved_leftover hk.degree
  have hQsub:Q₂≤Q₀:=by
    intro v w hvw
    have hh:(ordinaryPhysicalGraph Q₂ H₂).Adj (Sum.inl v) (Sum.inl w):=hvw
    rw [hpost] at hh
    exact hh.1.1
  have hQF':Disjoint Q₂ F:=hQF.mono_left hQsub
  have hbd:=boundary_degree_after_packing (ordinaryBoundaryGraph Q₀ H₀ X Z) C D σ p ε (t+ν)
    hp hsample hm0.reserve_avoided hchanges
  have hQdeg':∀w:V⊕U,(ordinaryBoundaryGraph Q₂ H₂ X Z).degree w≤Dmax:=by
    intro w
    have hh:=hbd w
    have hdeq:(ordinaryBoundaryGraph Q₂ H₂ X Z).degree w=
        (((ordinaryBoundaryGraph Q₀ H₀ X Z\C)\D).degree w):=by
      convert congrArg (fun G:SimpleGraph (V⊕U)=>G.degree w) hphys using 1 <;>
        congr! 8 <;> exact Subsingleton.elim _ _
    rw [←hdeq] at hh
    have hbound:((ordinaryBoundaryGraph Q₂ H₂ X Z).degree w:ℝ)≤(Dmax:ℝ):=hh.trans (hdeg.trans hDmax)
    exact_mod_cast hbound
  have hsum:=ordinary_boundary_row_sum_bound_from_boundary Q₂ H₂ X Z Dmax hQdeg'
  have hsum':(((Fintype.card (Σi:{v:V // v∉X},ordinaryBoundaryRowSet H₂ X Z i)*(m+1):ℕ):ℝ))≤
      (((Fintype.card (V⊕U)*Dmax*(m+1):ℕ):ℝ)):=by exact_mod_cast Nat.mul_le_mul_right (m+1) hsum
  have hdivsum:=div_le_div_of_nonneg_right hsum' (show (0:ℝ)≤Kcap by positivity)
  have hcompletion':(((Fintype.card (Σi:{v:V // v∉X},ordinaryBoundaryRowSet H₂ X Z i)*(m+1):ℕ):ℝ)/(Kcap:ℝ)+
      (((m+1:ℕ):ℝ)+3)*(Lconf+1)+2*(2*(ρ*Fintype.card (V⊕U))+2*((Kcap+Dmax:ℕ):ℝ))+
      (Dmax:ℝ)+((Dmax*(m+1):ℕ):ℝ)+3*Dmax < βe*Fintype.card (V⊕U)-3*ν):=by
    linarith only [hdivsum,hcompletion]
  have hcounts:=ordinary_inner_counts_after_packing_cleanup P Q₀ F H₀ π d (m+1) X Z pR pH density
    tR tH Ledit βe βh t ν s j raw R profile hbal hdiv M K
  have hcount:∀i,∀z∈ordinaryBoundaryRowSet H₂ X Z i,∀v∈X,∀w∈X,
      βe*Fintype.card (V⊕U)-3*ν≤
        (((X.filter (fun a=>H₂ a z))∩Q₂.neighborFinset v∩Q₂.neighborFinset w).card:ℝ):=by
    intro i z hz v hv w hw
    have hzZ:z∈Z:=(Finset.mem_filter.mp hz).1
    convert hcounts z hzZ v hv w hw using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  unfold OrdinaryGeneralFinishHostResult
  exact ordinary_general_sampled_boundary_remainder_boundary_degree m hm Q₀ Q Q₂ F H₀ H H₂ X Z C D D σ p ρ ζ ε (t+ν) ν
    hgood hp hsample hm0.reserve_avoided hphys hchanges hk.degree hkeep hk.no_outer_rim hk.no_outer_spoke
    hk.balance hk.divisible hdeg hpair hscaleY hscaleZ hbudgetY hbudgetZ hQF' Dmax Kcap hKcap hQdeg'
    Lconf (βe*Fintype.card (V⊕U)-3*ν) hLconf hF hcount hcompletion'
end Oberwolfach
