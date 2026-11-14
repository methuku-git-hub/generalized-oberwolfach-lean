module

public import Oberwolfach.OrdinaryRetainedComponentAssignment
public import Oberwolfach.OrdinarySelectedHubFilter

@[expose] public section
/-! Apply the retained component assignment simultaneously at every hub
using exactly the wheel-count sets tested by the matching. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_selected_wheel_component_assignment
    {n K:ℕ} (hn:0<n) {U A:Type} [Fintype U] [DecidableEq U] [DecidableEq A]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (hK:0<K) (i₀:Fin K) (s θ lam:ℝ) (hs0:0≤s) (hθ:0<θ) (hlam:lam<θ)
    (C:∀u,Finset (F u).ConnectedComponent)
    (hC:∀u c,c∈C u→Fintype.card c=i₀.val+1)
    (hreserve:∀u,((i₀.val+1:ℕ):ℝ)*((C u).card:ℝ)=s*n)
    (L:Finset A) (tag:A→Option (Fin K)) (hub:A→U)
    (hret:∀a∈L,∀i,tag a=some i→
      θ/(100*(K:ℝ))≤ordinaryAssignedKeptFraction F hF K i₀ s θ (hub a) i)
    (hcount:∀z:OrdinaryAssignedRetainedHubTest F hF i₀ s θ,
      |((longPaddedSeedExponent z.val.1+2:ℕ):ℝ)*
        ((L.filter (fun a=>tag a=some z.val.1 ∧ hub a=z.val.2)).card:ℝ)-
        (1-θ)*ordinaryAssignedKeptFraction F hF K i₀ s θ z.val.2 z.val.1*n|≤
        lam*ordinaryAssignedKeptFraction F hF K i₀ s θ z.val.2 z.val.1*n):
    ∀u,∃f:↥(L.filter (fun a=>(tag a).isSome ∧ hub a=u))↪↥(Finset.univ\C u),
      ∀a,Fintype.card (f a).val=((tag a.val).getD i₀).val+1 :=by
  intro u
  let L' := L.filter (fun a=>(tag a).isSome ∧ hub a=u)
  apply ordinary_retained_component_assignment hn F hF Allowed hAllowed hK i₀ s θ lam hs0 hθ hlam u (C u)
    (hC u) (hreserve u) L' (fun a=>(tag a).getD i₀)
  · intro a ha
    have ha':a∈L ∧ (tag a).isSome ∧ hub a=u:=by simpa only [L',Finset.mem_filter] using ha
    cases ht:tag a with
    | none => simp [ht] at ha'
    | some i =>
      have hh:=hret a ha'.1 i ht
      simpa only [ht,Option.getD_some,ha'.2.2] using hh
  · intro i hi
    let z:OrdinaryAssignedRetainedHubTest F hF i₀ s θ:=⟨(i,u),hi⟩
    have hh:=hcount z
    have heq: L'.filter (fun a=>(tag a).getD i₀=i)=L.filter (fun a=>tag a=some i ∧ hub a=u):=
      ordinary_selected_hub_filter L tag hub i₀ i u
    have hh':|((longPaddedSeedExponent i+2:ℕ):ℝ)*((L'.filter (fun a=>(tag a).getD i₀=i)).card:ℝ)-
        (1-θ)*ordinaryAssignedKeptFraction F hF K i₀ s θ u i*n|≤
        lam*ordinaryAssignedKeptFraction F hF K i₀ s θ u i*n:=by
      rw [heq]
      exact hh
    convert hh' using 1 <;> congr! 5
end Oberwolfach
