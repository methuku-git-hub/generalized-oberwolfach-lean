module

public import Oberwolfach.MarkedPotentialPhysicalDeletion
public import Oberwolfach.TypedMarkedPotentialDeletion

@[expose] public section

/-! The same fixed potential coefficients control rim and spoke roots after
actual physical deletion, including roots absent from either outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_packing_potential_after_physical_deletion
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (hm:3≤m) (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (D τ A B:ℝ) (hDlo:(Fintype.card V:ℝ)/2≤D) (hDhi:D≤2*Fintype.card V)
    (p k s₀ pstar:ℝ) (hpstar:0<pstar) (hp:pstar≤p) (hk:pstar≤k) (hs:pstar≤s₀)
    (hp1:p≤1) (hk1:k≤1) (hs1:s₀≤1) (hB:0≤B)
    (weight:(Fin (m+1)→V)→ℝ) (hw:SuccessorSequenceWeightConditions P π (3*d) D τ A B weight)
    (deltaR deltaS:ℝ) (hR:0≤deltaR) (hS:0≤deltaS)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (root:((V×V)⊕(V×V))⊕(Bool×V×U))
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U))
    (hrim:∀ x,(DR.degree x:ℝ)≤deltaR)
    (hrow:∀ x,(DS.degree (Sum.inl x):ℝ)≤deltaS)
    (hcol:∀ u,(DS.degree (Sum.inr u):ℝ)≤deltaS):
    let seed:=fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun (_:V) (_:U)=>True) (fun _ _=>True)=>weight W.1.val/(D*p^m*k*s₀^m)
    |typedMarkedPotentialLoad seed (rawMarkedPairRims P π d (rawMarkedDeleteRims σ DR.edgeFinset))
      (markedDeletePhysicalSpokes H DS) root-typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) H root|
      ≤11*((m:ℝ)+1)^4*(2*B/pstar^(2*m+1))*(2*deltaR+deltaS)/Fintype.card V:=by
  intro seed
  have hseed:=fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun (_:V) (_:U)=>True) (fun _ _=>True)=>successor_seed_nonneg_upper hw (by omega) hn hDlo hDhi
        p k s₀ pstar hpstar hp hk hs hp1 hk1 hs1 hB W.1.val
  obtain ⟨hout,hin⟩:=marked_rim_physical_deletion_incidence P π d σ DR deltaR hrim
  have hdelta:0≤2*deltaR+deltaS:=by positivity
  have h2:2*deltaR≤2*deltaR+deltaS:=by linarith only [hS]
  have hS':deltaS≤2*deltaR+deltaS:=by linarith only [hR]
  have hc:=typedMarkedPotentialLoad_degree_stability hm hn hu seed (2*B/pstar^(2*m+1))
    (by positivity) hseed (rawMarkedPairRims P π d σ)
    (rawMarkedPairRims P π d (rawMarkedDeleteRims σ DR.edgeFinset))
    H (markedDeletePhysicalSpokes H DS) (2*deltaR+deltaS) hdelta
    (fun x=>(hout x).trans h2) (fun x=>(hin x).trans h2)
    (by
      intro b x
      convert ((marked_spoke_physical_deletion_row_change H DS Finset.univ b x).trans (hrow x)).trans hS' using 1
      apply Finset.sum_congr rfl
      intro u _
      unfold bipAdj
      split_ifs <;> rfl)
    (by
      intro b u
      convert ((marked_spoke_physical_deletion_column_change H DS Finset.univ b u).trans (hcol u)).trans hS' using 1
      apply Finset.sum_congr rfl
      intro x _
      unfold bipAdj
      split_ifs <;> rfl)
    root
  exact hc

end Oberwolfach
