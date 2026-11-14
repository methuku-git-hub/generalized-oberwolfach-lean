module

public import Oberwolfach.MarkedLocalSpokeLoadsAfterChanges

@[expose] public section
/-! Fixed parent weights retain their potential-load estimates at both rim
and spoke roots after the same bounded physical changes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_potential_all_roots_after_changes
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (hm:3≤m)
    (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (D τ A B:ℝ) (hDlo:(Fintype.card V:ℝ)/2≤D) (hDhi:D≤2*Fintype.card V)
    (p k s₀ pstar:ℝ) (hpstar:0<pstar) (hp:pstar≤p) (hk:pstar≤k) (hs:pstar≤s₀)
    (hp1:p≤1) (hk1:k≤1) (hs1:s₀≤1) (hB:0≤B)
    (weight:(Fin (m+1)→V)→ℝ) (hw:SuccessorSequenceWeightConditions P π (3*d) D τ A B weight)
    (eps deltaR deltaS:ℝ) (hR:0≤deltaR) (hS:0≤deltaS)
    (σ σ':RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U))
    (hchangeR:∀e,¬(rawMarkedPairRims P π d σ e↔rawMarkedPairRims P π d σ' e)→markedPairPhysical π e∈DR.edgeFinset)
    (hchangeS:∀b v u,¬(H b v u↔H' b v u)→DS.Adj (Sum.inl v) (Sum.inr u))
    (hrim:∀v,(DR.degree v:ℝ)≤deltaR)
    (hrow:∀v,(DS.degree (Sum.inl v):ℝ)≤deltaS)
    (hcol:∀u,(DS.degree (Sum.inr u):ℝ)≤deltaS):
    let seed:=fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun (_:V) (_:U)=>True) (fun _ _=>True)=>weight W.1.val/(D*p^m*k*s₀^m);
    ∀root:((V×V)⊕(V×V))⊕(Bool×V×U),
      |typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) H root-1|≤eps→
      |typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ') H' root-1|≤
        eps+11*((m:ℝ)+1)^4*(2*B/pstar^(2*m+1))*(2*deltaR+deltaS)/Fintype.card V := by
  intro seed root hload
  have hseed:=fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun (_:V) (_:U)=>True) (fun _ _=>True)=>successor_seed_nonneg_upper hw (by omega) hn hDlo hDhi
        p k s₀ pstar hpstar hp hk hs hp1 hk1 hs1 hB W.1.val
  obtain ⟨hout,hin⟩:=marked_rim_physical_change_incidence P π d σ σ' DR hchangeR deltaR hrim
  obtain ⟨hsrow,hscol⟩:=marked_spoke_physical_change_incidence H H' DS hchangeS
  let δ:=2*deltaR+deltaS
  have hδ:0≤δ:=by dsimp [δ];positivity
  have h2:2*deltaR≤δ:=by dsimp [δ];linarith
  have hS':deltaS≤δ:=by dsimp [δ];linarith
  have hout':∀v,(∑e,if ¬(rawMarkedPairRims P π d σ e↔rawMarkedPairRims P π d σ' e) ∧ Sum.elim Prod.fst Prod.fst e=v then (1:ℝ) else 0)≤δ:=fun v=>(hout v).trans h2
  have hin':∀v,(∑e,if ¬(rawMarkedPairRims P π d σ e↔rawMarkedPairRims P π d σ' e) ∧ Sum.elim Prod.snd Prod.snd e=v then (1:ℝ) else 0)≤δ:=fun v=>(hin v).trans h2
  have hrow':∀b v,(∑u,bipAdj (fun v u=>¬(H b v u↔H' b v u)) v u)≤δ:=fun b v=>(hsrow b v).trans ((hrow v).trans hS')
  have hcol':∀b u,(∑v,bipAdj (fun v u=>¬(H b v u↔H' b v u)) v u)≤δ:=fun b u=>(hscol b u).trans ((hcol u).trans hS')
  have hbound:0≤2*B/pstar^(2*m+1):=by positivity
  have hnR:0<(Fintype.card V:ℝ):=by exact_mod_cast hn
  have hcost:0≤((m:ℝ)+1)^4*(2*B/pstar^(2*m+1))*δ/Fintype.card V:=by positivity
  have hdiff:|typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ') H' root-
      typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) H root|≤
      11*((m:ℝ)+1)^4*(2*B/pstar^(2*m+1))*δ/Fintype.card V:=by
    cases root with
    | inl e =>
      exact typedMarkedPotentialLoad_rim_degree_stability hm hn hu seed _ hbound hseed _ _ H H' δ hδ hout' hin' hrow' hcol' e
    | inr a =>
      have hh:=typedMarkedPotentialLoad_spoke_degree_stability hm hn seed _ hbound hseed _ _ H H' δ hδ hout' hin' hrow' hcol' a.1 a.2.1 a.2.2
      have hle:5*((m:ℝ)+1)^4*(2*B/pstar^(2*m+1))*δ/Fintype.card V≤
          11*((m:ℝ)+1)^4*(2*B/pstar^(2*m+1))*δ/Fintype.card V:=by
        have hm:=mul_le_mul_of_nonneg_right (show (5:ℝ)≤11 by norm_num) hcost
        convert hm using 1 <;> ring
      exact hh.trans hle
  have hh:=(abs_sub_le _ _ _).trans (add_le_add hdiff hload)
  simpa only [δ,add_comm] using hh
end Oberwolfach
