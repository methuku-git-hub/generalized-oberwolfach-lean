module

public import Oberwolfach.OrdinarySelectedWheelComponentAssignment
public import Oberwolfach.OrdinaryAssignedMatchedRelativeFrequency
public import Oberwolfach.OrdinaryPositiveCandidateRetained

@[expose] public section
/-! A positive-support matching with retained hub-frequency tests admits
length-preserving assignments to distinct unreserved components. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

set_option backward.isDefEq.respectTransparency true in
theorem ordinary_matched_component_assignment
    (hn:0<n) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (hK:0<K) (i₀:Fin K) (s θ c D:ℝ) (hs0:0≤s) (hθ:0<θ)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (weights:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (wM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ)
    (R:∀i,OrdinaryMixedGenericFamily
      (MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
        (fun _ (_:U)=>True) (fun _ (_:U)=>True))
      (fun i=>OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2)) i→
        Finset (((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)))
    (state:(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))→Bool)
    (C:∀u,Finset (F u).ConnectedComponent)
    (hC:∀u c,c∈C u→Fintype.card c=i₀.val+1)
    (hreserve:∀u,((i₀.val+1:ℕ):ℝ)*((C u).card:ℝ)=s*n)
    (L:Finset (PhysicalSampledCandidate (mixedCandidateResources R) state))
    (ε γ:ℝ) (hγ:0≤γ) (hslack:ε+γ*(1-θ+ε)<θ):
    let w:=ordinaryMixedGenericWeight wM (ordinaryAssignedUnshiftedSeed F hF i₀ s θ c D P π d weights)
    let hub:=ordinaryMixedGenericWheelHub (U:=U) π (3*d) m longPaddedSeedExponent
    let mass:=fun z:OrdinaryAssignedRetainedHubTest F hF i₀ s θ=>
      ∑x:PhysicalSampledCandidate (mixedCandidateResources R) state,
        ordinaryAssignedRetainedHubIndicator F hF i₀ s θ π (3*d) m longPaddedSeedExponent z x.val*mixedCandidateWeight w x.val;
    (∀x∈L,0<mixedCandidateWeight w x.val)→
    (∀z,|((longPaddedSeedExponent z.val.1+2:ℕ):ℝ)*mass z-
      (1-θ)*ordinaryAssignedKeptFraction F hF K i₀ s θ z.val.2 z.val.1*n|≤
      ε*ordinaryAssignedKeptFraction F hF K i₀ s θ z.val.2 z.val.1*n)→
    (∀z,(1-γ)*mass z≤∑x∈L,ordinaryAssignedRetainedHubIndicator F hF i₀ s θ π (3*d) m longPaddedSeedExponent z x.val)→
    (∀z,(∑x∈L,ordinaryAssignedRetainedHubIndicator F hF i₀ s θ π (3*d) m longPaddedSeedExponent z x.val)≤(1+γ)*mass z)→
    ∀u,∃f:↥(L.filter (fun x=>x.val.1.isSome ∧ hub x.val.1 x.val.2=u))↪↥(Finset.univ\C u),
      ∀a,Fintype.card (f a).val=((a.val.val.1).getD i₀).val+1 :=by
  intro w hub mass hsupp hdev hlo hhi
  apply ordinary_selected_wheel_component_assignment hn F hF Allowed hAllowed hK i₀ s θ
    (ε+γ*(1-θ+ε)) hs0 hθ hslack C hC hreserve L (fun x=>x.val.1) (fun x=>hub x.val.1 x.val.2)
  · intro x hx i htag
    have hh:=ordinary_positive_candidate_retained F hF i₀ s θ c D P π d m weights wM x.val i htag (hsupp x hx)
    exact hh
  · intro z
    have hh:=ordinary_assigned_matched_relative_frequency F hF i₀ s θ π d m R w state z L ε γ hγ
      (by convert hdev z using 1 <;> (try simp only [mass]) <;> congr! 5)
      (by convert hlo z using 1 <;> (try simp only [mass]) <;> congr! 5)
      (by convert hhi z using 1 <;> (try simp only [mass]) <;> congr! 5)
    convert hh using 1 <;> (try simp only [hub,mass]) <;> congr! 5
end Oberwolfach
