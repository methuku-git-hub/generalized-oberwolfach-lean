module

public import Oberwolfach.OrdinaryLocalStateDegree

@[expose] public section
/-! The exceptional physical states contribute at the protected-set scale;
only conflict and edited edges use ambient degree bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_local_exceptional_rim_degree
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P Del:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (Inner:Finset (Fin n)) (p k p₂ k₂ u t δ:ℝ)
    (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1) (ht:0≤t)
    (hcolour:∀a:Fin 6,∀x∈Inner,
      |(((P.neighborFinset x∩Inner).filter (fun y=>(σ (Sum.inl s(x,y))).1=a)).card:ℝ)-
        markedExpandedPhysicalProbability p k p₂ k₂ u a*(P.neighborFinset x∩Inner).card|≤t)
    (hDel:∀x,(Del.degree x:ℝ)≤δ):
    let Except:=(((longPhysicalStateGraph P σ {1}⊔longPhysicalStateGraph P σ {3})⊔longPhysicalStateGraph P σ {4})⊔
      (permutationConflictGraph π (3*d+2)⊔Del));
    ∀x,((spanningRestriction Except Inner).degree x:ℝ)≤
      (2*k+2*k₂+u)*Inner.card+3*t+(6*d+4:ℕ)+δ :=by
  intro Except
  have hlocal:∀(a:Fin 6) x,
      ((spanningRestriction (longPhysicalStateGraph P σ {a}) Inner).degree x:ℝ)≤
        markedExpandedPhysicalProbability p k p₂ k₂ u a*Inner.card+t:=by
    intro a x
    have hρ:=markedExpandedPhysicalProbability_nonneg p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum a
    by_cases hx:x∈Inner
    · rw [ordinary_local_state_degree P σ Inner a x hx]
      have hc:( ((P.neighborFinset x∩Inner).card:ℕ):ℝ)≤Inner.card:=by exact_mod_cast Finset.card_le_card (Finset.inter_subset_right : P.neighborFinset x∩Inner⊆Inner)
      have hh:= (abs_le.mp (hcolour a x hx)).2
      have hr:=mul_le_mul_of_nonneg_left hc hρ
      have hbound:(((P.neighborFinset x∩Inner).filter (fun y=>(σ (Sum.inl s(x,y))).1=a)).card:ℝ)≤
          markedExpandedPhysicalProbability p k p₂ k₂ u a*Inner.card+t:=by linarith only [hh,hr]
      convert hbound using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
    · rw [spanningRestriction_degree,if_neg hx]
      have hh:0≤markedExpandedPhysicalProbability p k p₂ k₂ u a*(Inner.card:ℝ):=by positivity
      norm_num
      linarith
  let A:=longPhysicalStateGraph P σ {1}
  let B:=longPhysicalStateGraph P σ {3}
  let C:=longPhysicalStateGraph P σ {4}
  let D:=permutationConflictGraph π (3*d+2)
  intro x
  have h1:=ordinary_restricted_sup_degree_le ((A⊔B)⊔C) (D⊔Del) Inner x
  have h2:=ordinary_restricted_sup_degree_le (A⊔B) C Inner x
  have h3:=ordinary_restricted_sup_degree_le A B Inner x
  have h4:=ordinary_restricted_sup_degree_le D Del Inner x
  have hD:((spanningRestriction D Inner).degree x:ℝ)≤(6*d+4:ℕ):=by
    have ha:(spanningRestriction D Inner).degree x≤D.degree x:=SimpleGraph.degree_le_of_le (by intro a b h;exact ((spanningRestriction_adj D Inner a b).mp h).1)
    have hb:D.degree x≤6*d+4:=by
      have hh:=permutationConflictGraph_degree_le π (3*d+2) x
      have hh':D.degree x≤2*(3*d+2):=by convert hh using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
      omega
    exact_mod_cast ha.trans hb
  have hDel':((spanningRestriction Del Inner).degree x:ℝ)≤δ:=by
    have hh:(spanningRestriction Del Inner).degree x≤Del.degree x:=SimpleGraph.degree_le_of_le (by intro a b h;exact ((spanningRestriction_adj Del Inner a b).mp h).1)
    have hh':((spanningRestriction Del Inner).degree x:ℝ)≤Del.degree x:=by exact_mod_cast hh
    exact hh'.trans (hDel x)
  have hA:=hlocal 1 x
  have hB:=hlocal 3 x
  have hC:=hlocal 4 x
  norm_num [markedExpandedPhysicalProbability] at hA hB hC
  have h1':((spanningRestriction Except Inner).degree x:ℝ)≤
      (spanningRestriction ((A⊔B)⊔C) Inner).degree x+(spanningRestriction (D⊔Del) Inner).degree x:=by exact_mod_cast h1
  have h2':((spanningRestriction ((A⊔B)⊔C) Inner).degree x:ℝ)≤
      (spanningRestriction (A⊔B) Inner).degree x+(spanningRestriction C Inner).degree x:=by exact_mod_cast h2
  have h3':((spanningRestriction (A⊔B) Inner).degree x:ℝ)≤
      (spanningRestriction A Inner).degree x+(spanningRestriction B Inner).degree x:=by exact_mod_cast h3
  have h4':((spanningRestriction (D⊔Del) Inner).degree x:ℝ)≤
      (spanningRestriction D Inner).degree x+(spanningRestriction Del Inner).degree x:=by exact_mod_cast h4
  dsimp [A,B,C] at h3' h2'
  nlinarith [hA,hB,hC,hD,hDel']
end Oberwolfach
