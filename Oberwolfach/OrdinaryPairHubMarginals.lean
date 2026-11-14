module

public import Oberwolfach.OrdinaryPairHubLoadConcentration

@[expose] public section

/-! Exact single-resource marginals for the intersection of the spoke
neighbourhoods of two distinct hubs in the original raw experiment. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

def ordinaryPairHubMarginal (P:SimpleGraph V) (ρ:Sym2 V→ℝ) (s:U→Color→ℝ)
    (j:Color) (u u':U):Sym2 V⊕(V×Unit)→ℝ
  | Sum.inl e=>if e∈P.edgeSet then ρ e else 0
  | Sum.inr _=>s u j*s u' j

theorem ordinary_pair_hub_resource_probability
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (ρ:Sym2 V→ℝ) (hρ:∀ e,0≤ρ e) (hρ1:∀ e,ρ e≤1)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
    (hS:∀ u,∑ j,s u j ≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort:∀ x k,0<k→k<2*d+1→(π^k) x≠x)
    (j:Color) (u u':U) (hne:u≠u') (a:Sym2 V⊕(V×Unit)):
    (FiniteLaw.pi (rawWheelLaw ρ hρ hρ1 d hd q hq hQ s hs hS)).probability
      (fun σ=>ordinaryResourceState (rawWheelGraph P σ) (ordinaryPairHubSpokes π d σ j u u') a=true)=
      ordinaryPairHubMarginal P ρ s j u u' a := by
  let μ:=rawWheelLaw ρ hρ hρ1 d hd q hq hQ s hs hS
  cases a with
  | inl e=>
    have hh:=rawWheelResource_probability P π ρ hρ hρ1 d hd q hq hQ s hs hS hnoshort j (Sum.inl e)
    simpa [ordinaryResourceState,ordinaryPairHubMarginal,rawWheelMarginal] using hh
  | inr a=>
    rcases a with ⟨v,⟨⟩⟩
    let a:Sym2 V⊕(V×U):=Sum.inr (v,u)
    let b:Sym2 V⊕(V×U):=Sum.inr (v,u')
    have hab:a≠b:=by intro h;exact hne (congrArg Prod.snd (Sum.inr.inj h))
    have hdis:=rawWheelResourceCoordinates_disjoint π d a b hab (by
      intro x h y k hx hy
      have hx':(x,h)=(v,u):=Sum.inr.inj hx.symm
      have hy':(y,k)=(v,u'):=Sum.inr.inj hy.symm
      left
      have hh:h=u:=congrArg Prod.snd hx'
      have hk:k=u':=congrArg Prod.snd hy'
      simpa only [hh,hk] using hne)
    let Ev:=fun (z:RawWheelOutcome V U Γ Color)=>rawWheelSpokes π d z j v u
    let Ev':=fun (z:RawWheelOutcome V U Γ Color)=>rawWheelSpokes π d z j v u'
    have hEv:∀ z z',(∀ e∈rawWheelResourceCoordinates π d a,z e=z' e)→(Ev z↔Ev z'):=by
      intro z z' hz
      have hh:=rawWheelResourceState_supported P π d j a z z' hz
      simpa [a,Ev,ordinaryResourceState,decide_eq_decide] using hh
    have hEv':∀ z z',(∀ e∈rawWheelResourceCoordinates π d b,z e=z' e)→(Ev' z↔Ev' z'):=by
      intro z z' hz
      have hh:=rawWheelResourceState_supported P π d j b z z' hz
      simpa [b,Ev',ordinaryResourceState,decide_eq_decide] using hh
    have hind:=finiteLaw_disjoint_supported_events μ _ _ hdis Ev Ev' hEv hEv'
    have hp:=rawWheelResource_probability P π ρ hρ hρ1 d hd q hq hQ s hs hS hnoshort j a
    have hp':=rawWheelResource_probability P π ρ hρ hρ1 d hd q hq hQ s hs hS hnoshort j b
    have hp0:(FiniteLaw.pi μ).probability Ev=s u j:=by
      simpa [μ,Ev,a,ordinaryResourceState,rawWheelMarginal] using hp
    have hp0':(FiniteLaw.pi μ).probability Ev'=s u' j:=by
      simpa [μ,Ev',b,ordinaryResourceState,rawWheelMarginal] using hp'
    rw [hp0,hp0'] at hind
    simpa [ordinaryResourceState,ordinaryPairHubSpokes,ordinaryPairHubMarginal,Ev,Ev'] using hind
end Oberwolfach
