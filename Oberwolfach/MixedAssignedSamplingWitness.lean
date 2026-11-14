module

public import Oberwolfach.MixedAssignedSamplingRecipes

@[expose] public section
/-! All actual classes admit compatible categorical probabilities on one
physical exposure, using their own original interval and spoke recipes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem mixed_assigned_classes_sampling_witness {I:Type} [Fintype I]
    {U:I→Type} [∀i,Fintype (U i)] {n:ℕ} (hn:0<n)
    (K m d:ℕ) (hK:0<K) (hm:7≤m) (hd:2≤d)
    (label:I→Option (Fin K)) (F:∀i,U i→SimpleGraph (Fin n))
    (hF:∀i w,(F i w).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀i w,AllowedCycleLengths (F i w) Allowed)
    (hclass:∀i w,factorPreparationClass (F i w) K=label i)
    (s θ ρ₀ D:ℝ) (ρ:I→ℝ) (hs0:0≤s) (hs1:s≤1/100)
    (hsclass:s≤1/(2*(K:ℝ))) (hθ:0<θ) (hθ1:θ≤1/100)
    (hda:1/θ≤d) (hcut:(1/((m:ℝ)+1))/(d:ℝ)≤θ)
    (hρ₀:0<ρ₀) (hρlo:∀i,ρ₀≤ρ i) (hρhi:∀i,ρ i≤1) (hD:0<D)
    (hsize:∀i,ρ i*D=2*Fintype.card (U i)):
    let q:=mixedAssignedIntervalProbability K m θ label F hF
    let sco:=mixedAssignedSpokeProbability K m s θ label F hF;
    ∃ (p k p₂ k₂ udens:I→ℝ),
      (∀i,0≤p i ∧ 0≤k i ∧ 0≤p₂ i ∧ 0≤k₂ i ∧ 0≤udens i ∧
        2*p i+2*k i+2*p₂ i+2*k₂ i+udens i=ρ i) ∧
      (∀i w j,0≤q i w j) ∧ (∀i w,∑j,q i w j≤1/8) ∧
      (∀i w j,0≤sco i w j) ∧ (∀i w,∑j,sco i w j≤ intervalUncoveredProbability d (∑j,q i w j)) ∧
      (∀i,label i=none→2*p i=ρ i*(1/100:ℝ) ∧ 2*k i=ρ i*((1/100:ℝ)/(m:ℝ)) ∧
        ρ₀/8≤p₂ i ∧ ρ₀/(6*((m:ℝ)+1))≤k₂ i ∧
        p₂ i*D=∑w,longAssignedApproxOrdinaryWeight (F i) (hF i) K m θ w ∧
        k₂ i*D=∑w,longAssignedApproxMarkedWeight (F i) (hF i) K m θ w ∧
        udens i*D=2*∑w,(1-(1/100:ℝ)-(1/100:ℝ)/(m:ℝ)-longAssignedApproxMarkedWeight (F i) (hF i) K m θ w-longAssignedApproxOrdinaryWeight (F i) (hF i) K m θ w) ∧
        ρ₀*((1/100:ℝ)/(m:ℝ))/2≤k i ∧
        ∀w,q i w false=(1/100:ℝ)/(m:ℝ) ∧ sco i w false=1/100) ∧
      (∀i j,label i=some j→k i=0 ∧ k₂ i=0 ∧ 2*p i=ρ i*s ∧ ρ i/4≤p₂ i ∧
        p₂ i*D=∑w,(ordinaryAssignedLongWeight (F i) (hF i) K θ ((m:ℝ)+1) w+ordinaryAssignedShortWeight (F i) (hF i) K j s θ ((m:ℝ)+1) w) ∧
        udens i*D=2*∑w,(1-s-ordinaryAssignedLongWeight (F i) (hF i) K θ ((m:ℝ)+1) w-ordinaryAssignedShortWeight (F i) (hF i) K j s θ ((m:ℝ)+1) w) ∧
        ∀w,q i w false=0 ∧ sco i w false=s) :=by
  intro q sco
  have hc:8≤(m:ℝ)+1:=by exact_mod_cast (show 8≤m+1 by omega)
  have hex:∀i,∃p k p₂ k₂ udens:ℝ,
      0≤p ∧ 0≤k ∧ 0≤p₂ ∧ 0≤k₂ ∧ 0≤udens ∧
      2*p+2*k+2*p₂+2*k₂+udens=ρ i ∧
      (∀w j,0≤q i w j) ∧ (∀w,∑j,q i w j≤1/8) ∧
      (∀w j,0≤sco i w j) ∧ (∀w,∑j,sco i w j≤ intervalUncoveredProbability d (∑j,q i w j)) ∧
      (label i=none→2*p=ρ i*(1/100:ℝ) ∧ 2*k=ρ i*((1/100:ℝ)/(m:ℝ)) ∧
        ρ₀/8≤p₂ ∧ ρ₀/(6*((m:ℝ)+1))≤k₂ ∧
        p₂*D=∑w,longAssignedApproxOrdinaryWeight (F i) (hF i) K m θ w ∧
        k₂*D=∑w,longAssignedApproxMarkedWeight (F i) (hF i) K m θ w ∧
        udens*D=2*∑w,(1-(1/100:ℝ)-(1/100:ℝ)/(m:ℝ)-longAssignedApproxMarkedWeight (F i) (hF i) K m θ w-longAssignedApproxOrdinaryWeight (F i) (hF i) K m θ w) ∧
        ρ₀*((1/100:ℝ)/(m:ℝ))/2≤k ∧
        ∀w,q i w false=(1/100:ℝ)/(m:ℝ) ∧ sco i w false=1/100) ∧
      (∀j,label i=some j→k=0 ∧ k₂=0 ∧ 2*p=ρ i*s ∧ ρ i/4≤p₂ ∧
        p₂*D=∑w,(ordinaryAssignedLongWeight (F i) (hF i) K θ ((m:ℝ)+1) w+ordinaryAssignedShortWeight (F i) (hF i) K j s θ ((m:ℝ)+1) w) ∧
        udens*D=2*∑w,(1-s-ordinaryAssignedLongWeight (F i) (hF i) K θ ((m:ℝ)+1) w-ordinaryAssignedShortWeight (F i) (hF i) K j s θ ((m:ℝ)+1) w) ∧
        ∀w,q i w false=0 ∧ sco i w false=s) :=by
    intro i
    cases hl:label i with
    | none =>
      have hclass':∀w,factorPreparationClass (F i w) K=none:=by intro w;simpa [hl] using hclass i w
      obtain ⟨p,k,p₂,k₂,udens,hp,hk,hp₂,hk₂,hu,hbal,hps,hks,hp₂lo,hk₂lo,hp₂eq,hk₂eq,hueq,_,hklo,hq,hQ,hs,hS,hcol⟩:=
        long_assigned_class_sampling_witness hn (F i) (hF i) Allowed (hAllowed i) K hK m d hm hd θ ρ₀ (ρ i) D
          hθ.le hθ1 hρ₀ (hρlo i) (hρhi i) hD (hsize i) hcut hclass'
      refine ⟨p,k,p₂,k₂,udens,hp,hk,hp₂,hk₂,hu,hbal,?_,?_,?_,?_,?_,?_⟩
      · simpa [q,mixedAssignedIntervalProbability,hl] using hq
      · simpa [q,mixedAssignedIntervalProbability,hl] using hQ
      · simpa [sco,mixedAssignedSpokeProbability,hl] using hs
      · simpa [q,sco,mixedAssignedIntervalProbability,mixedAssignedSpokeProbability,hl] using hS
      · intro _
        refine ⟨hps,hks,hp₂lo,hk₂lo,hp₂eq,hk₂eq,hueq,hklo,?_⟩
        simpa [q,sco,mixedAssignedIntervalProbability,mixedAssignedSpokeProbability,hl] using hcol
      · intro j hj
        simp [hl] at hj
    | some j =>
      have hclass':∀w,factorPreparationClass (F i w) K=some j:=by intro w;simpa [hl] using hclass i w
      obtain ⟨p,p₂,udens,hp,hp₂,hu,hbal,hps,hp₂lo,hp₂eq,hueq,hq,hQ,hs,hS,hcol⟩:=
        ordinary_assigned_class_sampling_witness hn (F i) (hF i) Allowed (hAllowed i) K hK j s θ ((m:ℝ)+1) (ρ i) D d hd
          hs0 hs1 hθ hθ1 hc hda (hρ₀.trans_le (hρlo i)) (hρhi i) hD (hsize i) hsclass hclass'
      refine ⟨p,0,p₂,0,udens,hp,le_rfl,hp₂,le_rfl,hu,by linarith,?_,?_,?_,?_,?_,?_⟩
      · simpa [q,mixedAssignedIntervalProbability,hl] using hq
      · simpa [q,mixedAssignedIntervalProbability,hl] using hQ
      · simpa [sco,mixedAssignedSpokeProbability,hl] using hs
      · simpa [q,sco,mixedAssignedIntervalProbability,mixedAssignedSpokeProbability,hl] using hS
      · intro he
        simp [hl] at he
      · intro j' hj
        have hj':j'=j:=Option.some.inj ((by simpa [hl] using hj) : some j=some j') |>.symm
        subst j'
        refine ⟨rfl,rfl,hps,hp₂lo,hp₂eq,hueq,?_⟩
        simpa [q,sco,mixedAssignedIntervalProbability,mixedAssignedSpokeProbability,hl] using hcol
  choose p k p₂ k₂ udens h using hex
  refine ⟨p,k,p₂,k₂,udens,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i;exact ⟨(h i).1,(h i).2.1,(h i).2.2.1,(h i).2.2.2.1,(h i).2.2.2.2.1,(h i).2.2.2.2.2.1⟩
  · intro i;exact (h i).2.2.2.2.2.2.1
  · intro i;exact (h i).2.2.2.2.2.2.2.1
  · intro i;exact (h i).2.2.2.2.2.2.2.2.1
  · intro i;exact (h i).2.2.2.2.2.2.2.2.2.1
  · intro i;exact (h i).2.2.2.2.2.2.2.2.2.2.1
  · intro i;exact (h i).2.2.2.2.2.2.2.2.2.2.2
end Oberwolfach
