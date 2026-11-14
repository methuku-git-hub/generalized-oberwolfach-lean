module

public import Oberwolfach.OrdinaryHubCoverAfterChanges
public import Oberwolfach.OrdinaryFullHostLoadProbability
public import Oberwolfach.OrdinaryFullHostSeedBounds
public import Oberwolfach.TriangleDomainNeighbourhoodEvent
public import Oberwolfach.AlmostSpanningCyclePacking
public import Oberwolfach.OrdinaryLocalFactorFromWeights
public import Oberwolfach.OrdinaryConflictDeletion

@[expose] public section

/-! Actual successive hub covers on one original-law event. Positive parent
cycle weights are constructed from the threshold hypothesis, before sampling.
The same event permits every later bounded modification and every hub list
satisfying the explicit incidence and divisibility conditions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 4500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_hub_cover_common_event (m:ℕ) (hm:2≤m) (α p ω:ℝ)
    (hα:0<α) (hp:0<p) (hp1:p≤1) (hω:0<ω):
    ∃ ε₀ ρ:ℝ,0<ε₀ ∧ 0<ρ ∧ ∀ Dmax:ℝ,0≤Dmax →
    ∀ d q₀:ℕ,∀ hd:2≤d,∃ N:ℕ,
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],
    ∀ P:SimpleGraph V,N≤Fintype.card V →
      ω*Fintype.card V≤(Fintype.card U:ℝ) → Fintype.card U≤Fintype.card V →
      (∀ v,(cycleThreshold (m+1)+α)*Fintype.card V≤(P.degree v:ℝ)) →
    ∀ (F:SimpleGraph V) (π:Equiv.Perm V),(∀ v,(F.degree v:ℝ)≤Dmax) →
      permutationConflictGraph π (3*d)≤F → (∀ z l,0<l→l<2*d+1→(π^l) z≠z) →
    ∀ (pR pH D ε:ℝ) (hpR:p≤pR) (hpR1:pR≤1),p≤pH → pH≤1 →
      (Fintype.card V:ℝ)/2≤D → 0≤ε → ε≤ε₀ →
      (∀ v,|(P.degree v:ℝ)-D|≤ε*Fintype.card V) → pR*D=2*Fintype.card U*pH →
    ∀ (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (j:Color),(∀ u,s u j=pH) →
    1-1/(Fintype.card V:ℝ)^q₀≤
      (FiniteLaw.pi (rawWheelLaw (fun _=>pR) (fun _=>hp.le.trans hpR) (fun _=>hpR1) d hd q hq hQ s hs hS)).probability
      (fun σ=>
      let R:=rawWheelGraph P σ
      let H:=rawWheelSpokes π d σ j
    ∀ (Q:SimpleGraph V) (H':V→U→Prop) (L:ℝ),Q≤P → 0≤L → L≤ρ*Fintype.card V →
      (∀ v,(F.degree v:ℝ)≤L) →
      (∀ v,((changed (R.neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L) →
      (∀ v,((changed (Finset.univ.filter (H v)) (Finset.univ.filter (H' v))).card:ℝ)≤L) →
      (∀ u,((changed (Finset.univ.filter (fun v=>H v u)) (Finset.univ.filter (fun v=>H' v u))).card:ℝ)≤L) →
    ∀ (n:ℕ) (u:Fin n→U),Function.Injective u →
      (∀ v,(2*(Finset.univ.filter (fun i=>H' v (u i))).card:ℝ)≤ρ*Fintype.card V) →
      (∀ i,(m+1)∣(Finset.univ.filter (fun v=>H' v (u i))).card) →
      ∃ M:Finset (OrdinaryWheel Q F H' (m+1)),
        (∀ W∈M,∀ Z∈M,W≠Z→Disjoint (ordinaryWheelResources W) (ordinaryWheelResources Z)) ∧
        M.biUnion ordinaryWheelResources=(ordinaryWheelRimGraph M).edgeFinset.image Sum.inl ∪
          Finset.univ.biUnion (fun i=>(Finset.univ.filter (fun v=>H' v (u i))).image (fun v=>Sum.inr (v,u i))) ∧
        (∀ v,(ordinaryWheelRimGraph M).degree v≤2*(Finset.univ.filter (fun i=>H' v (u i))).card) ∧
        (∀ i,∀ v,H' v (u i)→∃! W:M,Sum.inr (v,u i)∈ordinaryWheelResources W.val) ) :=by
  obtain ⟨c,B,hc,hB,Nw,_hNw,hweights⟩:=positive_ordinary_fractional_cycle_weights (m+1) (by omega) α hα
  let B₁:=B/(ω*p^(2*(m+1)-1))
  have hB₁:0<B₁:=by dsimp [B₁];positivity
  obtain ⟨η,ρ,hη,hρ,Na,hafter⟩:=ordinary_hub_cover_after_changes m hm α p c B₁ hα hp hp1 hc hB₁.le
  obtain ⟨ε₀,hε₀,hload⟩:=ordinaryFullHostSeed_uniform_probability (m+1) (by omega) p ω c B η hp hω hc.le hB hη
  refine ⟨ε₀,ρ,hε₀,hρ,?_⟩
  intro Dmax hDmax d q₀ hd
  obtain ⟨Nl,hl⟩:=hload Dmax hDmax d (q₀+1) hd
  obtain ⟨Nc,hcounts⟩:=triangle_domain_neighbourhood_common_event 1 ω η le_rfl hω hη d (q₀+1) hd
  refine ⟨max 2 (max Nw (max Na (max Nl Nc))),?_⟩
  intro V U Γ Color _ _ _ _ _ _ P hn hUlo hU hP
  obtain ⟨weight,hw,he⟩:=hweights V (by omega) P hP
  have he':=ordinary_cycle_incidence_load_adjacency P (m+1) weight he
  intro F π hF hclose hnoshort pR pH D ε hpR hpR1 hpH hpH1 hD hε hεsmall hreg hbalance q hq hQ s hs hS j hj
  have hnN:0<Fintype.card V:=by omega
  have hnR:(0:ℝ)<Fintype.card V:=Nat.cast_pos.mpr hnN
  have hmU:(0:ℝ)<Fintype.card U:=(mul_pos hω hnR).trans_le hUlo
  let φ:=fun C:OrdinaryCycle P (m+1)=>weight C/((Fintype.card U:ℝ)*pR^m*pH^(m+1))
  have hφ (C:OrdinaryCycle P (m+1)):
      c/(Fintype.card V:ℝ)^m≤φ C ∧ φ C≤B₁/(Fintype.card V:ℝ)^m:=by
    have hh:=ordinary_seed_coefficient_bounds (m+1) (by omega) (Fintype.card V) (Fintype.card U)
      ω p pR pH c B (weight C) hnR hmU hω hp hUlo (Nat.cast_le.mpr hU)
      hpR hpR1 hpH hpH1 hc.le hB.le (hw C).1 (hw C).2
    simpa only [Nat.add_sub_cancel] using hh
  have hbase (v:V):(ordinaryLocalBaseDegree m+α)*Fintype.card V≤(P.degree v:ℝ):=by
    have hh:ordinaryLocalBaseDegree m+α≤cycleThreshold (m+1)+α:=by
      linarith only [ordinaryLocalBaseDegree_le_cycleThreshold m hm]
    exact (mul_le_mul_of_nonneg_right hh hnR.le).trans (hP v)
  have hcprob:=hcounts V U Γ Color P F π Finset.univ Finset.univ (by simpa only [Finset.card_univ] using (show Nc≤Fintype.card V by omega))
    (by simp) (by simpa using (Nat.cast_le.mpr hU: (Fintype.card U:ℝ)≤Fintype.card V))
    (by simpa only [Finset.card_univ] using hUlo) hclose hnoshort pR (hp.le.trans hpR) hpR1 q hq hQ s hs hS j pH hj
  have hlprob:=hl V U Γ Color (by omega) hUlo hU P F π hF hclose hnoshort
    pR pH D ε hpR hpR1 hpH hpH1 hD hε hεsmall hreg hbalance q hq hQ s hs hS j hj weight hw he'
  have hjoint:=finiteLaw_good_intersection
    (FiniteLaw.pi (rawWheelLaw (fun _:Sym2 V=>pR) (fun _=>hp.le.trans hpR) (fun _=>hpR1) d hd q hq hQ s hs hS))
    (fun σ=>RawOrdinaryRows P π d 3 Finset.univ pR s j (η*Fintype.card V) σ ∧
      RawOrdinaryDomainIndices F π d 3 Finset.univ pH j (η*Fintype.card U) σ)
    _ (1/(Fintype.card V:ℝ)^(q₀+1)) hlprob
  have hnum:=scaled_inverse_power_le (Fintype.card V) q₀ hnN 2 (by exact_mod_cast (show 2≤Fintype.card V by omega))
  have hprob:1-1/(Fintype.card V:ℝ)^q₀≤
      (FiniteLaw.pi (rawWheelLaw (fun _:Sym2 V=>pR) (fun _=>hp.le.trans hpR) (fun _=>hpR1) d hd q hq hQ s hs hS)).probability
        (fun σ=>(RawOrdinaryRows P π d 3 Finset.univ pR s j (η*Fintype.card V) σ ∧
          RawOrdinaryDomainIndices F π d 3 Finset.univ pH j (η*Fintype.card U) σ) ∧
          ((∀ x y,P.Adj x y→¬F.Adj x y→|ordinaryPotentialLoad (ordinaryFullHostSeed (U:=U) P F (m+1) weight pR pH)
            (Sum.inl s(x,y)) (rawWheelGraph P σ\F) (rawWheelSpokes π d σ j)-1|≤η) ∧
          (∀ v u,|ordinaryPotentialLoad (ordinaryFullHostSeed (U:=U) P F (m+1) weight pR pH)
            (Sum.inr (v,u)) (rawWheelGraph P σ\F) (rawWheelSpokes π d σ j)-1|≤η))):=by
    have hcprob':=hcprob
    simp only [Finset.card_univ] at hcprob'
    have hnum':2*(1/(Fintype.card V:ℝ)^(q₀+1))≤1/(Fintype.card V:ℝ)^q₀:=by convert hnum using 1 <;> ring
    linarith only [hjoint,hcprob',hnum']
  apply hprob.trans
  apply finiteLaw_probability_mono
  intro σ hσ
  refine hafter V U (by omega) hU P (rawWheelGraph P σ) F (rawWheelSpokes π d σ j)
    pR pH hpR hpH hbase ?_ φ hφ ?_
  · intro u S hS'
    have hh:=(hσ.1.1 S {u} hS' (by simp)).le
    simpa only [Finset.prod_singleton,hj,Finset.card_univ] using hh
  · intro v u
    have hh:=hσ.2.2 v u
    rw [ordinaryPotentialLoad_delete_conflicts] at hh
    have hseed:ordinaryCycleWheelWeight (U:=U) P F (m+1) φ 1=
        ordinaryFullHostSeed (U:=U) P F (m+1) weight pR pH:=by
      funext W
      simp only [ordinaryFullHostSeed,ordinaryCycleWheelWeight,φ,Nat.add_sub_cancel,div_one]
    rw [hseed]
    convert hh using 1 <;> congr!

end Oberwolfach
