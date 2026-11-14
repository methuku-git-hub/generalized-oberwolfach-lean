module

public import Oberwolfach.OrdinaryRobustLocalFactor
public import Oberwolfach.OrdinaryHubWheelPacking
public import Oberwolfach.OrdinaryLocalFactorFromWeights

@[expose] public section

/-! The hub step of ordinary cover-down from the manuscript's fixed cycle
weighting and original potential targets. Earlier wheels are an actual
rim deletion. The theorem proves the required factors instead of assuming
a factor oracle, and covers each prescribed spoke exactly once. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 4500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_hub_cover_from_fixed_weights (m : ℕ) (hm : 2≤m) (α p cLo cHi : ℝ)
    (hα : 0<α) (hp : 0<p) (hp1 : p≤1) (hcLo : 0<cLo) (hcHi : 0≤cHi) :
    ∃ θ : ℝ,0<θ ∧ ∃ N : ℕ,
      ∀ (V U : Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
      N≤Fintype.card V → ∀ (n : ℕ) (u : Fin n→U),Function.Injective u →
      (2*n:ℝ)≤θ*Fintype.card V →
      ∀ (P Q F : SimpleGraph V) (H : V→U→Prop) (T : Fin n→Finset V) (q s D δ ξ L : ℝ),
      Q≤P → p≤q → q≤1 → p≤s → s≤1 → 0≤δ → 0≤L → L≤θ*Fintype.card V →
      (Fintype.card V:ℝ)/2≤D → D≤2*Fintype.card V →
      (∀ v,(cycleThreshold (m+1)+α)*Fintype.card V≤(P.degree v:ℝ)) →
      (∀ v,|(P.degree v:ℝ)-D|≤δ*Fintype.card V) → (∀ v,(F.degree v:ℝ)≤L) →
      (∀ i,∀ v∈T i,H v (u i)) → (∀ i,(m+1)∣(T i).card) →
      (∀ i,∀ S : Finset V,S.card≤ordinaryLocalRootBound m →
        q^S.card*s*((common Finset.univ S (fun x=>(P\F).neighborFinset x)).card:ℝ)-
          θ*Fintype.card V≤((common (T i) S (fun x=>Q.neighborFinset x)).card:ℝ)) →
      ∀ weight : OrdinaryCycle P (m+1)→ℝ,
      (∀ C,cLo/(Fintype.card V:ℝ)^(m-1)≤weight C ∧ weight C≤cHi/(Fintype.card V:ℝ)^(m-1)) →
      (∀ x y,(∑ C,if C.val.val.Adj x y then weight C else 0)=if P.Adj x y then 1 else 0) →
      (∀ i v,|ordinaryLocalPotential P Q F (T i) (fun C=>2*weight C/(D*q^(m+1)*s^m)) v-
        ordinaryLocalTarget P F weight D v|≤ξ) →
      2*δ+12*(m+1:ℝ)^4*cHi*L/Fintype.card V+ξ≤θ →
      ∃ M : Finset (OrdinaryWheel Q F H (m+1)),
        (∀ W∈M,∀ Z∈M,W≠Z → Disjoint (ordinaryWheelResources W) (ordinaryWheelResources Z)) ∧
        M.biUnion ordinaryWheelResources=(ordinaryWheelRimGraph M).edgeFinset.image Sum.inl ∪
          Finset.univ.biUnion (fun i=>(T i).image (fun v=>Sum.inr (v,u i))) ∧
        (∀ v,(ordinaryWheelRimGraph M).degree v≤2*n) ∧
        (∀ i,∀ v∈T i,∃! W : M,Sum.inr (v,u i)∈ordinaryWheelResources W.val) := by
  let B:=4*cHi/p^(3*m+1)
  have hB : 0≤B:=by dsimp [B];positivity
  obtain ⟨θ,hθ,N,hfactor⟩:=ordinary_robust_local_factor m hm α p cLo B hα hp hp1 hcLo hB
  refine ⟨θ,hθ,max N 1,?_⟩
  intro V U _ _ _ _ hn n u hu hnθ P Q F H T q s D δ ξ L hQP hq hq1 hs hs1 hδ hL hLθ
    hD hD' hP hreg hF hH hdiv hrel weight hweight hedge hpotential herr
  have hnV : 0<Fintype.card V:=by have h:=(le_max_right N 1).trans hn;omega
  have hnR : (0:ℝ)<Fintype.card V:=Nat.cast_pos.mpr hnV
  let φ : OrdinaryCycle P (m+1)→ℝ:=fun C=>2*weight C/(D*q^(m+1)*s^m)
  have hφ (C : OrdinaryCycle P (m+1)) :
      cLo/(Fintype.card V:ℝ)^m≤φ C ∧ φ C≤B/(Fintype.card V:ℝ)^m := by
    simpa only [one_mul] using ordinary_local_coefficient_bounds m 1 (by omega) _ D p q s cLo cHi _
      hnR hp hp1 hq hq1 hs hs1 (by omega) hD hD' hcLo hcHi (hweight C)
  have hP' (v : V) : (ordinaryLocalBaseDegree m+α)*Fintype.card V≤(P.degree v:ℝ) := by
    have hcoef : ordinaryLocalBaseDegree m+α≤cycleThreshold (m+1)+α := by
      linarith only [ordinaryLocalBaseDegree_le_cycleThreshold m hm]
    exact (mul_le_mul_of_nonneg_right hcoef hnR.le).trans (hP v)
  have hpot (i : Fin n) (v : V) : |ordinaryLocalPotential P Q F (T i) φ v-1|≤θ := by
    have ht:=ordinaryLocalTarget_error P F (show 2≤m+1 by omega) hnV weight
      (fun C=>(div_pos hcLo (pow_pos hnR _)).le.trans (hweight C).1) cHi L D δ hcHi hL hδ
      (by simpa only [show m+1-2=m-1 by omega] using fun C=>(hweight C).2) hF hedge hD v (hreg v)
    have hcast : ((m+1:ℕ):ℝ)=(m+1:ℝ):=by norm_cast
    rw [hcast] at ht
    have hp0 : |ordinaryLocalPotential P Q F (T i) φ v-ordinaryLocalTarget P F weight D v|≤ξ:=hpotential i v
    exact (abs_sub_le _ _ _).trans ((add_le_add hp0 ht).trans (by linarith only [herr]))
  apply sequential_ordinary_hub_wheels u hu T hH
  intro i K hK
  refine hfactor V ((le_max_left N 1).trans hn) P Q F (T i) 1 q s hQP (by omega) hq hs hP'
    (fun v=>(hF v).trans hLθ) ?_ (hdiv i) φ hφ (hpot i) K ?_
  · intro S hS
    simpa only [pow_one] using hrel i S hS
  · intro v
    have hkr : (K.degree v:ℝ)≤2*(n:ℝ):=by exact_mod_cast hK v
    exact hkr.trans hnθ

end Oberwolfach
