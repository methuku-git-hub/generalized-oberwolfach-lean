module

public import Oberwolfach.MarkedPotentialPhysicalDeletion
public import Oberwolfach.MarkedRimFullIncidence
public import Oberwolfach.TypedMarkedSpokeColumnStability

@[expose] public section
/-! Fixed-weight local spoke-root loads after arbitrary typed changes
supported on physical graphs of bounded degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_local_spoke_loads_after_column_changes
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (hm:3≤m) (hn:0<Fintype.card V)
    (D τ A B:ℝ) (hDlo:(Fintype.card V:ℝ)/2≤D) (hDhi:D≤2*Fintype.card V)
    (p k s₀ pstar:ℝ) (hpstar:0<pstar) (hp:pstar≤p) (hk:pstar≤k) (hs:pstar≤s₀)
    (hp1:p≤1) (hk1:k≤1) (hs1:s₀≤1) (hB:0≤B)
    (weight:(Fin (m+1)→V)→ℝ) (hw:SuccessorSequenceWeightConditions P π (3*d) D τ A B weight)
    (eps deltaR deltaS:ℝ) (hR:0≤deltaR) (hS:0≤deltaS)
    (σ σ':RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (hload:MarkedLocalSpokeLoadsWithSpokes P π d m D p k s₀ weight eps σ H)
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U))
    (hchangeR:∀ e,¬(rawMarkedPairRims P π d σ e↔rawMarkedPairRims P π d σ' e)→
      markedPairPhysical π e∈DR.edgeFinset)
    (hchangeS:∀ b v u,¬(H b v u↔H' b v u)→DS.Adj (Sum.inl v) (Sum.inr u))
    (hrim:∀ x,(DR.degree x:ℝ)≤deltaR)
    (hcol:∀ u,(DS.degree (Sum.inr u):ℝ)≤deltaS):
    MarkedLocalSpokeLoadsWithSpokes P π d m D p k s₀ weight
      (eps+5*((m:ℝ)+1)^4*(2*B/pstar^(2*m+1))*(2*deltaR+deltaS)/Fintype.card V) σ' H' :=by
  let seed:=fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun (_:V) (_:U)=>True) (fun _ _=>True)=>weight W.1.val/(D*p^m*k*s₀^m)
  have hseed:=fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun (_:V) (_:U)=>True) (fun _ _=>True)=>successor_seed_nonneg_upper hw (by omega) hn hDlo hDhi
        p k s₀ pstar hpstar hp hk hs hp1 hk1 hs1 hB W.1.val
  obtain ⟨hout,hin⟩:=marked_rim_physical_change_incidence P π d σ σ' DR hchangeR deltaR hrim
  obtain ⟨hsrow,hscol⟩:=marked_spoke_physical_change_incidence H H' DS hchangeS
  have hdelta:0≤2*deltaR+deltaS:=by positivity
  have h2:2*deltaR≤2*deltaR+deltaS:=by linarith only [hS]
  have hS':deltaS≤2*deltaR+deltaS:=by linarith only [hR]
  intro a
  have hc:=typedMarkedPotentialLoad_spoke_column_stability hm hn seed (2*B/pstar^(2*m+1))
    (by positivity) hseed (rawMarkedPairRims P π d σ) (rawMarkedPairRims P π d σ') H H'
    (2*deltaR+deltaS) hdelta
    (fun x=>(hout x).trans h2) (fun x=>(hin x).trans h2)
    (fun b u=>(hscol b u).trans ((hcol u).trans hS')) a.1 a.2.1 a.2.2
  have hh:=abs_sub_le
    (typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ') H' (Sum.inr a))
    (typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) H (Sum.inr a)) 1
  exact hh.trans ((add_le_add hc (hload a)).trans_eq (by ring))
end Oberwolfach
