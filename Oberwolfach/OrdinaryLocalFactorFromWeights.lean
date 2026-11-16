module

public import Oberwolfach.OrdinaryRelativeLocalFactor
public import Oberwolfach.OrdinaryLocalTargetError
public import Oberwolfach.OrdinaryLocalWeightBounds
public import Oberwolfach.OddSharpThreshold
public import Oberwolfach.TwoComponentLower

@[expose] public section

/-! The ordinary local-factor conclusion from the original fractional
cycle decomposition, its fixed normalization, and the root-omitted load
estimate. No absorber or factor-existence premise is introduced. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinaryLocalBaseDegree_le_cycleThreshold (m : ℕ) (hm : 2≤m) :
    ordinaryLocalBaseDegree m≤cycleThreshold (m+1) := by
  by_cases hm2 : m=2
  · subst m
    simpa only [ordinaryLocalBaseDegree,ite_true] using cycleThreshold_triangle_lower
  · simpa only [ordinaryLocalBaseDegree,if_neg hm2] using cycleThreshold_half_le (show 3≤m+1 by omega)

theorem ordinary_local_factor_from_fixed_weights (m : ℕ) (hm : 2≤m) (α p cLo cHi : ℝ)
    (hα : 0<α) (hp : 0<p) (hp1 : p≤1) (hcLo : 0<cLo) (hcHi : 0≤cHi) :
    ∃ ε₀ η : ℝ,0<ε₀ ∧ 0<η ∧ ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V],N≤Fintype.card V →
      ∀ (P Q F : SimpleGraph V) (T : Finset V) (j : ℕ) (q s ε D δ ξ L : ℝ),
      Q≤P → j≤2 → p≤q → q≤1 → p≤s → s≤1 → ε≤ε₀ →
      0≤δ → 0≤L → L≤ε₀*Fintype.card V →
      (Fintype.card V:ℝ)/2≤D → D≤2*Fintype.card V →
      (∀ v,(cycleThreshold (m+1)+α)*Fintype.card V≤(P.degree v:ℝ)) →
      (∀ v,|(P.degree v:ℝ)-D|≤δ*Fintype.card V) →
      (∀ v,(F.degree v:ℝ)≤L) →
      (∀ S : Finset V,S.card≤ordinaryLocalRootBound m →
        q^S.card*s^j*((common Finset.univ S (fun x=>(P\F).neighborFinset x)).card:ℝ)-
          ε*Fintype.card V≤((common T S (fun x=>Q.neighborFinset x)).card:ℝ)) →
      (m+1)∣T.card → ∀ weight : OrdinaryCycle P (m+1)→ℝ,
      (∀ C,cLo/(Fintype.card V:ℝ)^(m-1)≤weight C ∧ weight C≤cHi/(Fintype.card V:ℝ)^(m-1)) →
      (∀ x y,(∑ C,if C.val.val.Adj x y then weight C else 0)=if P.Adj x y then 1 else 0) →
      (∀ v,|ordinaryLocalPotential P Q F T (fun C=>2*weight C/(D*q^(m+1)*s^(j*m))) v-
        ordinaryLocalTarget P F weight D v|≤ξ) →
      2*δ+12*(m+1:ℝ)^4*cHi*L/Fintype.card V+ξ≤η →
      HasResourceDecomposition (localOrdinaryVertices (Q:=Q) (F:=F) (T:=T) (r:=m+1)) T := by
  let B := 4*cHi/p^(3*m+1)
  have hB : 0≤B := by dsimp [B];positivity
  obtain ⟨ε₀,η,hε₀,hη,N,hfactor⟩ := ordinary_relative_local_factor m hm α p cLo B hα hp hp1 hcLo hB
  refine ⟨ε₀,η,hε₀,hη,max N 1,?_⟩
  intro V _ _ hn P Q F T j q s ε D δ ξ L hQP hj hq hq1 hs hs1 hε hδ hL hLε hD hD'
    hP hreg hF hrel hdiv weight hweight hedge hpotential herr
  have hnV : 0<Fintype.card V := by have hh:=(le_max_right N 1).trans hn;omega
  have hnR : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr hnV
  let φ : OrdinaryCycle P (m+1)→ℝ := fun C=>2*weight C/(D*q^(m+1)*s^(j*m))
  let wt : LocalOrdinaryCycle Q F T (m+1)→ℝ := fun C=>φ (localOrdinaryParent hQP C)
  have hwt (C : LocalOrdinaryCycle Q F T (m+1)) :
      cLo/(Fintype.card V:ℝ)^m≤wt C ∧ wt C≤B/(Fintype.card V:ℝ)^m :=
    ordinary_local_coefficient_bounds m j (by omega) _ D p q s cLo cHi _ hnR hp hp1 hq hq1 hs hs1 hj hD hD'
      hcLo hcHi (hweight _)
  have hP' (v : V) : (ordinaryLocalBaseDegree m+α)*Fintype.card V≤(P.degree v:ℝ) := by
    have hc : ordinaryLocalBaseDegree m+α≤cycleThreshold (m+1)+α := by
      linarith [ordinaryLocalBaseDegree_le_cycleThreshold m hm]
    exact (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _)).trans (hP v)
  apply hfactor V ((le_max_left N 1).trans hn) P Q F T j q s ε hj hq hs hε hP'
    (fun v=>(hF v).trans hLε) hrel hdiv wt hwt
  intro v hv
  have ht := ordinaryLocalTarget_error P F (show 2≤m+1 by omega) hnV weight
    (fun C=>(div_pos hcLo (pow_pos hnR _)).le.trans (hweight C).1) cHi L D δ hcHi hL hδ
    (by simpa only [show m+1-2=m-1 by omega] using fun C=>(hweight C).2) hF hedge hD v (hreg v)
  have hid := ordinaryLocalPotential_present P Q F T hQP φ v hv
  have hpot := hpotential v
  change |ordinaryLocalPotential P Q F T φ v-ordinaryLocalTarget P F weight D v|≤ξ at hpot
  have htriangle := abs_sub_le (ordinaryLocalPotential P Q F T φ v) (ordinaryLocalTarget P F weight D v) 1
  rw [hid] at hpot htriangle
  rw [abs_sub_comm]
  have he : (m+1:ℝ)=((m+1:ℕ):ℝ) := by norm_cast
  rw [← he] at ht
  have hfinal := htriangle.trans ((add_le_add hpot ht).trans (show ξ+(2*δ+12*(m+1:ℝ)^4*cHi*L/Fintype.card V)≤η by linarith only [herr]))
  set_option backward.isDefEq.respectTransparency true in
    convert hfinal using 1 <;> congr!

end Oberwolfach
