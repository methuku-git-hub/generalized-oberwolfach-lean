module

public import Oberwolfach.MarkedRimFullIncidence
public import Oberwolfach.MarkedPotentialModifiedHost

@[expose] public section
/-! Fixed root-omitted weighted loads on the original ambient domain after
arbitrary typed changes supported on bounded-degree physical graphs. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_reference_weighted_load_after_changes
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (hm:3≤m)
    (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (w:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ _=>True) (fun _ _=>True)→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U))
    (δR δS:ℝ) (hδR:0≤δR) (hδS:0≤δS)
    (hdegR:∀ x,(DR.degree x:ℝ)≤δR)
    (hdegSrow:∀ x,(DS.degree (Sum.inl x):ℝ)≤δS)
    (hdegScol:∀ u,(DS.degree (Sum.inr u):ℝ)≤δS)
    (hrim:∀ a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a)→
      markedPairPhysical π a∈DR.edgeFinset)
    (hspoke:∀ b x u,¬(H b x u↔H' b x u)→DS.Adj (Sum.inl x) (Sum.inr u))
    (valid:(((V×V)⊕(V×V))⊕(Bool×V×U))→Prop) (error:ℝ)
    (hbase:∀ root,valid root→
      |typedMarkedPotentialLoad w (rawMarkedPairRims P π d σ) H root-1|≤error):
    ∀ root,valid root→
      |typedMarkedPotentialLoad w (rawMarkedPairRims P π d τ) H' root-1|≤
       error+11*((m:ℝ)+1)^4*B*(2*δR+δS)/Fintype.card V := by
  obtain ⟨hout,hin⟩:=marked_rim_physical_change_incidence P π d σ τ DR hrim δR hdegR
  obtain ⟨hsrow,hscol⟩:=marked_spoke_physical_change_incidence H H' DS hspoke
  have hpos:0≤2*δR+δS:=by positivity
  have hr:2*δR≤2*δR+δS:=by linarith
  have hs:δS≤2*δR+δS:=by linarith
  exact marked_potential_load_after_host_modification hm hn hu w B hB hw
    (rawMarkedPairRims P π d σ) (rawMarkedPairRims P π d τ) H H'
    (2*δR+δS) hpos (fun x=>(hout x).trans hr) (fun x=>(hin x).trans hr)
    (fun b x=>(hsrow b x).trans ((hdegSrow x).trans hs))
    (fun b u=>(hscol b u).trans ((hdegScol u).trans hs)) valid error hbase
end Oberwolfach
