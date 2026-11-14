module

public import Oberwolfach.OrdinarySpokePotentialIdentity
public import Oberwolfach.OrdinaryRobustLocalFactor
public import Oberwolfach.HubCoverByIncidence

@[expose] public section

/-! Successive physical hub covers directly from root-spoke-omitted loads.
The fixed cycle coefficients are used in every factor construction. Earlier
hub wheels are charged by their actual rim-vertex incidence. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 2500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_hub_cover_from_spoke_potentials (m:ℕ) (hm:2≤m) (α p b B:ℝ)
    (hα:0<α) (hp:0<p) (hp1:p≤1) (hb:0<b) (hB:0≤B):
    ∃ θ:ℝ,0<θ ∧ ∃ N:ℕ,
    ∀ (V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
    ∀ (P Q F:SimpleGraph V) (H:V→U→Prop) (q s:ℝ),N≤Fintype.card V →
      Q≤P → p≤q → p≤s →
      (∀ v,(ordinaryLocalBaseDegree m+α)*Fintype.card V≤(P.degree v:ℝ)) →
      (∀ v,(F.degree v:ℝ)≤θ*Fintype.card V) →
      (∀ u,∀ S:Finset V,S.card≤ordinaryLocalRootBound m →
        q^S.card*s*((common Finset.univ S (fun x=>(P\F).neighborFinset x)).card:ℝ)-
          θ*Fintype.card V≤((common (Finset.univ.filter (fun v=>H v u)) S (fun x=>Q.neighborFinset x)).card:ℝ)) →
    ∀ φ:OrdinaryCycle P (m+1)→ℝ,
      (∀ C,b/(Fintype.card V:ℝ)^m≤φ C ∧ φ C≤B/(Fintype.card V:ℝ)^m) →
      (∀ v u,|ordinaryPotentialLoad (ordinaryCycleWheelWeight P F (m+1) φ 1) (Sum.inr (v,u)) Q H-1|≤θ) →
    ∀ (n:ℕ) (u:Fin n→U),Function.Injective u →
      (∀ v,(2*(Finset.univ.filter (fun i=>H v (u i))).card:ℝ)≤θ*Fintype.card V) →
      (∀ i,(m+1)∣(Finset.univ.filter (fun v=>H v (u i))).card) →
      ∃ M:Finset (OrdinaryWheel Q F H (m+1)),
        (∀ W∈M,∀ Z∈M,W≠Z→Disjoint (ordinaryWheelResources W) (ordinaryWheelResources Z)) ∧
        M.biUnion ordinaryWheelResources=(ordinaryWheelRimGraph M).edgeFinset.image Sum.inl ∪
          Finset.univ.biUnion (fun i=>(Finset.univ.filter (fun v=>H v (u i))).image (fun v=>Sum.inr (v,u i))) ∧
        (∀ v,(ordinaryWheelRimGraph M).degree v≤2*(Finset.univ.filter (fun i=>H v (u i))).card) ∧
        (∀ i,∀ v,H v (u i)→∃! W:M,Sum.inr (v,u i)∈ordinaryWheelResources W.val):=by
  obtain ⟨θ,hθ,N,hfactor⟩:=ordinary_robust_local_factor m hm α p b B hα hp hp1 hb hB
  refine ⟨θ,hθ,N,?_⟩
  intro V U _ _ _ _ P Q F H q s hn hQP hq hs hP hF hcounts φ hφ hpot n u hu hinc hdiv
  let T:=fun i=>Finset.univ.filter (fun v=>H v (u i))
  have hlocal (i:Fin n) (v:V):|ordinaryLocalPotential P Q F (T i) φ v-1|≤θ:=by
    have he:=ordinary_spoke_potential_eq_local P Q F H φ 1 v (u i)
    have hh:=hpot v (u i)
    rw [he] at hh
    simpa only [div_one] using hh
  have hh:=sequential_ordinary_hub_wheels_by_incidence u hu T
    (fun i v hv=>(Finset.mem_filter.mp hv).2) (by
      intro i D hD
      refine hfactor V hn P Q F (T i) 1 q s hQP (by omega) hq hs hP hF ?_ (hdiv i) φ hφ (hlocal i) D ?_
      · intro S hS
        simpa only [pow_one] using hcounts (u i) S hS
      · intro v
        have hd:(D.degree v:ℝ)≤2*(Finset.univ.filter (fun i=>v∈T i)).card:=by exact_mod_cast hD v
        exact hd.trans (by simpa only [T,Finset.mem_filter,Finset.mem_univ,true_and] using hinc v))
  simpa only [T,Finset.mem_filter,Finset.mem_univ,true_and] using hh

end Oberwolfach
