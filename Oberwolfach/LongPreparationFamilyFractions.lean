module

public import Oberwolfach.LongPreparationFactorFractions

@[expose] public section
/-! The long-factor family provides exactly the frequency hypotheses used by
its interval-marginal calculation. Each frequency counts actual vertices. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_preparation_family_fractions {U:Type*} [Fintype U] {n:ℕ} (hn:0<n)
    (F:U→SimpleGraph (Fin n)) (hF:∀ u,(F u).IsRegularOfDegree 2)
    (K:ℕ) (hK:0<K) (θ:ℝ) (hθ:0≤θ)
    (hlong:∀ u,(1/2:ℝ)≤
      ((Finset.univ.filter (fun v=>K<Fintype.card ((F u).connectedComponentMk v))).card:ℝ)/n):
    let fraction:=fun (u:U) (j:Option (Fin K))=>
      ((Finset.univ.filter (fun v=>longPreparationCycleClass (F u) (hF u) K v=j)).card:ℝ)/n
    let retained:=fun (u:U)=>Finset.univ.filter (fun i=>θ/(100*(K:ℝ))≤fraction u (some i))
    let long:=fun u=>fraction u none
    let rare:=fun u=>∑ i∈Finset.univ\retained u,fraction u (some i)
    let f:=fun (i:Fin K) u=>if i∈retained u then fraction u (some i) else 0;
    (∀ u,1/2≤long u ∧ long u≤1) ∧ (∀ u,0≤rare u ∧ rare u≤θ/100) ∧
    (∀ i u,0≤f i u) ∧ (∀ u,long u+(∑ i,f i u)+rare u=1) ∧
    (∀ u i,i∈retained u→θ/(100*(K:ℝ))≤f i u):=by
  intro fraction retained long rare f
  have H (u:U):=(long_preparation_factor_fractions hn (F u) (hF u) K hK θ hθ)
  have hdata (u:U):
      (∀ j,0≤fraction u j) ∧
      (∀ i∈retained u,θ/(100*(K:ℝ))≤fraction u (some i)) ∧
      0≤rare u ∧ rare u≤θ/100 ∧ long u+(∑ i∈retained u,fraction u (some i))+rare u=1:=by
    have hh:=H u
    dsimp only at hh
    simpa [fraction,retained,long,rare] using hh.2.2
  have hlong' (u:U):1/2≤long u:=by
    have heq: (Finset.univ.filter (fun v=>longPreparationCycleClass (F u) (hF u) K v=none))=
        (Finset.univ.filter (fun v=>K<Fintype.card ((F u).connectedComponentMk v))):=by
      apply Finset.filter_congr
      intro v _
      exact (long_preparation_cycle_class (F u) (hF u) K v).1
    simpa [long,fraction,heq] using hlong u
  have hsum (u:U):(∑ i,f i u)=∑ i∈retained u,fraction u (some i):=by
    simp [f,Finset.sum_filter]
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro u
    have hf0:0≤∑ i∈retained u,fraction u (some i):=
      Finset.sum_nonneg (fun i _=>(hdata u).1 _)
    exact ⟨hlong' u,by have hr:=(hdata u).2.2.1;have hs:=(hdata u).2.2.2.2;linarith⟩
  · intro u
    exact ⟨(hdata u).2.2.1,(hdata u).2.2.2.1⟩
  · intro i u
    dsimp [f]
    split
    · exact (hdata u).1 _
    · exact le_refl _
  · intro u
    rw [hsum]
    exact (hdata u).2.2.2.2
  · intro u i hi
    simp only [f,if_pos hi]
    exact (hdata u).2.1 i hi
end Oberwolfach
