module

public import Oberwolfach.MarkedNeighbourhoodPhysicalDeletion
public import Oberwolfach.MarkedLocalLoadSpokeChanges

@[expose] public section

/-! Fixed root-omitted spoke weights after a later physical rim and spoke
deletion. Both orientations of the auxiliary rim requests are bounded
using the actual physical roots; the seed weights and all roots stay fixed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
set_option maxRecDepth 4096
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem pair_indicator_sum_at_first (f:V×V→Prop) (x:V):
    (∑ e:V×V,if f e ∧ e.1=x then (1:ℝ) else 0)=∑ y:V,if f (x,y) then (1:ℝ) else 0:=by
  simp only [Fintype.sum_prod_type]
  have he (a z:V):(if f (a,z)∧a=x then (1:ℝ) else 0)=
      if a=x then (if f (a,z) then 1 else 0) else 0:=by split_ifs <;> tauto
  simp only [he,Finset.sum_ite_irrel,Finset.sum_const_zero]
  simp

theorem pair_indicator_sum_at_second (f:V×V→Prop) (x:V):
    (∑ e:V×V,if f e ∧ e.2=x then (1:ℝ) else 0)=∑ y:V,if f (y,x) then (1:ℝ) else 0:=by
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  have he (a z:V):(if f (z,a)∧a=x then (1:ℝ) else 0)=
      if a=x then (if f (z,a) then 1 else 0) else 0:=by split_ifs <;> tauto
  simp only [he,Finset.sum_ite_irrel,Finset.sum_const_zero]
  simp

theorem marked_rim_physical_deletion_incidence
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (DR:SimpleGraph V) (delta:ℝ) (hD:∀ x,(DR.degree x:ℝ)≤delta):
    let R:=rawMarkedPairRims P π d σ
    let R':=rawMarkedPairRims P π d (rawMarkedDeleteRims σ DR.edgeFinset)
    (∀ x,(∑ e:(V×V)⊕(V×V),if ¬(R e↔R' e) ∧ Sum.elim Prod.fst Prod.fst e=x then (1:ℝ) else 0)≤2*delta) ∧
    (∀ x,(∑ e:(V×V)⊕(V×V),if ¬(R e↔R' e) ∧ Sum.elim Prod.snd Prod.snd e=x then (1:ℝ) else 0)≤2*delta):=by
  dsimp only
  have hh (mark incoming:Bool) (x:V):=
    (marked_row_rim_physical_deletion_change P π d σ DR Finset.univ (mark,incoming,x)).trans (hD _)
  constructor
  · intro x
    have h0:=hh false false x
    have h1:=hh true false x
    calc
      _ ≤ delta+delta:=by
        rw [Fintype.sum_sum_type]
        apply add_le_add
        · convert h0 using 1
          convert pair_indicator_sum_at_first
            (fun e=>¬(rawMarkedPairRims P π d σ (Sum.inl e)↔
              rawMarkedPairRims P π d (rawMarkedDeleteRims σ DR.edgeFinset) (Sum.inl e))) x using 1 <;>
            (apply Finset.sum_congr rfl
             intro z _
             simp only [markedRowRim,Sum.elim_inl,Sum.elim_inr,Bool.false_eq_true,ite_false,ite_true]
             split_ifs <;> rfl)
        · convert h1 using 1
          convert pair_indicator_sum_at_first
            (fun e=>¬(rawMarkedPairRims P π d σ (Sum.inr e)↔
              rawMarkedPairRims P π d (rawMarkedDeleteRims σ DR.edgeFinset) (Sum.inr e))) x using 1 <;>
            (apply Finset.sum_congr rfl
             intro z _
             simp only [markedRowRim,Sum.elim_inl,Sum.elim_inr,Bool.false_eq_true,ite_false,ite_true]
             split_ifs <;> rfl)
      _ = _:=by ring
  · intro x
    have h0:=hh false true x
    have h1:=hh true true x
    calc
      _ ≤ delta+delta:=by
        rw [Fintype.sum_sum_type]
        apply add_le_add
        · convert h0 using 1
          convert pair_indicator_sum_at_second
            (fun e=>¬(rawMarkedPairRims P π d σ (Sum.inl e)↔
              rawMarkedPairRims P π d (rawMarkedDeleteRims σ DR.edgeFinset) (Sum.inl e))) x using 1 <;>
            (apply Finset.sum_congr rfl
             intro z _
             simp only [markedRowRim,Sum.elim_inl,Sum.elim_inr,Bool.false_eq_true,ite_false,ite_true]
             split_ifs <;> rfl)
        · convert h1 using 1
          convert pair_indicator_sum_at_second
            (fun e=>¬(rawMarkedPairRims P π d σ (Sum.inr e)↔
              rawMarkedPairRims P π d (rawMarkedDeleteRims σ DR.edgeFinset) (Sum.inr e))) x using 1 <;>
            (apply Finset.sum_congr rfl
             intro z _
             simp only [markedRowRim,Sum.elim_inl,Sum.elim_inr,Bool.false_eq_true,ite_false,ite_true]
             split_ifs <;> rfl)
      _ = _:=by ring

theorem marked_local_spoke_loads_after_physical_deletion
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (hm:3≤m) (hn:0<Fintype.card V)
    (D τ A B:ℝ) (hDlo:(Fintype.card V:ℝ)/2≤D) (hDhi:D≤2*Fintype.card V)
    (p k s₀ pstar:ℝ) (hpstar:0<pstar) (hp:pstar≤p) (hk:pstar≤k) (hs:pstar≤s₀)
    (hp1:p≤1) (hk1:k≤1) (hs1:s₀≤1) (hB:0≤B)
    (weight:(Fin (m+1)→V)→ℝ) (hw:SuccessorSequenceWeightConditions P π (3*d) D τ A B weight)
    (eps deltaR deltaS:ℝ) (hR:0≤deltaR) (hS:0≤deltaS)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hload:MarkedLocalSpokeLoadsWithSpokes P π d m D p k s₀ weight eps σ H)
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U))
    (hrim:∀ x,(DR.degree x:ℝ)≤deltaR)
    (hrow:∀ x,(DS.degree (Sum.inl x):ℝ)≤deltaS)
    (hcol:∀ u,(DS.degree (Sum.inr u):ℝ)≤deltaS):
    MarkedLocalSpokeLoadsWithSpokes P π d m D p k s₀ weight
      (eps+5*((m:ℝ)+1)^4*(2*B/pstar^(2*m+1))*(2*deltaR+deltaS)/Fintype.card V)
      (rawMarkedDeleteRims σ DR.edgeFinset) (markedDeletePhysicalSpokes H DS):=by
  let seed:=fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun (_:V) (_:U)=>True) (fun _ _=>True)=>weight W.1.val/(D*p^m*k*s₀^m)
  have hseed:=fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun (_:V) (_:U)=>True) (fun _ _=>True)=>successor_seed_nonneg_upper hw (by omega) hn hDlo hDhi
        p k s₀ pstar hpstar hp hk hs hp1 hk1 hs1 hB W.1.val
  obtain ⟨hout,hin⟩:=marked_rim_physical_deletion_incidence P π d σ DR deltaR hrim
  have hdelta:0≤2*deltaR+deltaS:=by positivity
  have h2:2*deltaR≤2*deltaR+deltaS:=by linarith only [hS]
  have hS':deltaS≤2*deltaR+deltaS:=by linarith only [hR]
  intro a
  have hc:=typedMarkedPotentialLoad_spoke_degree_stability hm hn seed (2*B/pstar^(2*m+1))
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
    a.1 a.2.1 a.2.2
  have hh:=abs_sub_le
    (typedMarkedPotentialLoad seed (rawMarkedPairRims P π d (rawMarkedDeleteRims σ DR.edgeFinset))
      (markedDeletePhysicalSpokes H DS) (Sum.inr a))
    (typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) H (Sum.inr a)) 1
  exact hh.trans ((add_le_add hc (hload a)).trans_eq (by ring))

end Oberwolfach
