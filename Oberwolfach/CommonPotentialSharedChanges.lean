module

public import Oberwolfach.RetainedCommonWeightWitness
public import Oberwolfach.MarkedLocalSpokeLoadsAfterChanges

@[expose] public section

/-! A fixed common-hub selector and fixed parent coefficients survive
later bounded physical rim and spoke deletions. The load at every potential
root is compared on the original vertex domain, including deleted roots. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem common_potential_loads_after_shared_changes
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (hm:3≤m) (hn:0<Fintype.card V)
    (D τ A B p k sbar pstar:ℝ) (hB:0≤B)
    (hDlo:(Fintype.card V:ℝ)/2≤D) (hDhi:D≤2*Fintype.card V)
    (hpstar:0<pstar) (hpmin:pstar≤p) (hkmin:pstar≤k) (hsmin:pstar≤sbar)
    (hp1:p≤1) (hk1:k≤1) (hs1:sbar≤1)
    (weight:(Fin (m+1)→V)→ℝ) (hw:SuccessorSequenceWeightConditions P π (3*d) D τ A B weight)
    (ε deltaR deltaS:ℝ) (hR:0≤deltaR) (hS:0≤deltaS)
    (σ σnew:RawMarkedOutcome V U Γ Color) (H Hnew:Bool→V→U→Prop) (κ:V→Bool) (u u':U)
    (hload:CommonPotentialSpokeLoads P π d m D p k sbar weight ε σ H κ u u')
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U))
    (hchangeR:∀ e,¬(rawMarkedPairRims P π d σ e↔rawMarkedPairRims P π d σnew e)→
      markedPairPhysical π e∈DR.edgeFinset)
    (hchangeS:∀ b v u,¬(H b v u↔Hnew b v u)→DS.Adj (Sum.inl v) (Sum.inr u))
    (hrim:∀ x,(DR.degree x:ℝ)≤deltaR)
    (hcol:∀ z,(DS.degree (Sum.inr z):ℝ)≤deltaS) :
    CommonPotentialSpokeLoads P π d m D p k sbar weight
      (ε+10*((m:ℝ)+1)^4*(2*B/pstar^(2*m+1))*(deltaR+deltaS)/Fintype.card V)
      σnew Hnew κ u u' := by
  let H':=Hnew
  have hc:∀ b z,(∑ x,if ¬(H b x z↔H' b x z) then (1:ℝ) else 0)≤deltaS:=by
    intro b z
    obtain ⟨_,hscol⟩:=marked_spoke_physical_change_incidence H Hnew DS hchangeS
    have hh:=(hscol b z).trans (hcol z)
    apply le_trans ?_ hh
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro x _
    simp only [H',bipAdj]
    split_ifs <;> rfl
  have hsp:=commonPotentialSpokeLoads_change P π d m hm hn D τ A B p k sbar pstar hB
    hDlo hDhi hpstar hpmin hkmin hsmin hp1 hk1 hs1 weight hw ε deltaS hS σ H H' κ u u' hload hc
  let Parent:=MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
    (fun (_:V) (_:Unit)=>True) (fun _ _=>True)
  let seed:=fun W:Parent=>weight W.1.val/(D*p^m*k*sbar^m)
  let bound:ℝ:=2*B/pstar^(2*m+1)
  have hb:0≤bound:=by dsimp [bound];positivity
  have hseed:∀ W:Parent,0≤seed W∧seed W≤bound/(Fintype.card V:ℝ)^m:=by
    intro W
    exact successor_seed_nonneg_upper hw (by omega) hn hDlo hDhi p k sbar pstar hpstar hpmin hkmin hsmin hp1 hk1 hs1 hB W.1.val
  have hinc:=marked_rim_physical_change_incidence P π d σ σnew DR hchangeR deltaR hrim
  intro b v
  have hdiff:=typedMarkedPotentialLoad_spoke_degree_stability (m:=m) (π:=π) (b:=3*d)
    hm hn seed bound hb hseed (rawMarkedPairRims P π d σ)
    (rawMarkedPairRims P π d σnew)
    (commonThinnedSpokes H' κ u u') (commonThinnedSpokes H' κ u u')
    (2*deltaR) (by positivity) hinc.1 hinc.2
    (by intro j x; simp [bipAdj] <;> positivity) (by intro j z; simp [bipAdj] <;> positivity) b v ()
  have hsum:= (abs_sub_le _ _ _).trans (add_le_add hdiff (hsp b v))
  have heq:5*((m:ℝ)+1)^4*bound*(2*deltaR)/Fintype.card V+
      (ε+10*((m:ℝ)+1)^4*bound*deltaS/Fintype.card V)=
      ε+10*((m:ℝ)+1)^4*bound*(deltaR+deltaS)/Fintype.card V:=by ring
  convert hsum.trans_eq heq using 1 <;> simp only [Parent,seed,bound,H'] <;> ring

end Oberwolfach
