module

public import Oberwolfach.OrdinaryLocalDeletion
public import Oberwolfach.OrdinaryRelativeLocalFactor

@[expose] public section

/-! The ordinary local factor survives every realised rim deletion of
small maximum degree. Constants precede the graph, the fixed coefficients,
and the deletion; no separate event is chosen for each deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 3500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_robust_local_factor (m : ℕ) (hm : 2≤m) (α p b B : ℝ)
    (hα : 0<α) (hp : 0<p) (hp1 : p≤1) (hb : 0<b) (hB : 0≤B) :
    ∃ θ : ℝ,0<θ ∧ ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V],N≤Fintype.card V →
      ∀ (P Q F : SimpleGraph V) (T : Finset V) (j : ℕ) (q s : ℝ),
      Q≤P → j≤2 → p≤q → p≤s →
      (∀ v,(ordinaryLocalBaseDegree m+α)*Fintype.card V≤(P.degree v:ℝ)) →
      (∀ v,(F.degree v:ℝ)≤θ*Fintype.card V) →
      (∀ S : Finset V,S.card≤ordinaryLocalRootBound m →
        q^S.card*s^j*((common Finset.univ S (fun x=>(P\F).neighborFinset x)).card:ℝ)-
          θ*Fintype.card V≤((common T S (fun x=>Q.neighborFinset x)).card:ℝ)) →
      (m+1)∣T.card → ∀ φ : OrdinaryCycle P (m+1)→ℝ,
      (∀ C,b/(Fintype.card V:ℝ)^m≤φ C ∧ φ C≤B/(Fintype.card V:ℝ)^m) →
      (∀ v,|ordinaryLocalPotential P Q F T φ v-1|≤θ) →
      ∀ D : SimpleGraph V,(∀ v,(D.degree v:ℝ)≤θ*Fintype.card V) →
      HasResourceDecomposition (localOrdinaryVertices (Q:=Q\D) (F:=F) (T:=T) (r:=m+1)) T := by
  obtain ⟨ε₀,η,hε₀,hη,N,hfactor⟩:=ordinary_relative_local_factor m hm α p b B hα hp hp1 hb hB
  let C : ℝ:=3*(m+1:ℝ)^4*B
  have hC : 0≤C:=by dsimp [C];positivity
  let θ:=min (ε₀/4) (η/(1+C))
  have hθ : 0<θ:=lt_min (by positivity) (div_pos hη (by linarith))
  have hθε : 4*θ≤ε₀:=by have hh:=min_le_left (ε₀/4) (η/(1+C));dsimp only [θ];linarith only [hh]
  have hθη : (1+C)*θ≤η:=by
    have hh:=min_le_right (ε₀/4) (η/(1+C))
    have hc:= (le_div_iff₀ (show 0<1+C by linarith only [hC])).mp hh
    dsimp only [θ];nlinarith only [hc]
  refine ⟨θ,hθ,max N 1,?_⟩
  intro V _ _ hn P Q F T j q s hQP hj hq hs hP hF hrel hdiv φ hφ hpotential D hD
  have hnV : 0<Fintype.card V:=by have h:=(le_max_right N 1).trans hn;omega
  have hnR : (0:ℝ)<Fintype.card V:=Nat.cast_pos.mpr hnV
  have hθle : θ≤ε₀:=by linarith only [hθε,hθ]
  have hQD : Q\D≤P:=sdiff_le.trans hQP
  let wt : LocalOrdinaryCycle (Q\D) F T (m+1)→ℝ:=fun C=>φ (localOrdinaryParent hQD C)
  apply hfactor V ((le_max_left N 1).trans hn) P (Q\D) F T j q s (4*θ) hj hq hs hθε hP
    (fun v=>(hF v).trans (mul_le_mul_of_nonneg_right hθle hnR.le)) ?_ hdiv wt
    (fun C=>hφ _) ?_
  · intro S hS
    have hroot : ordinaryLocalRootBound m≤3:=by unfold ordinaryLocalRootBound;split_ifs <;> omega
    have hS3 : (S.card:ℝ)≤3:=by exact_mod_cast hS.trans hroot
    have hdel : |((common T S (fun v=>(Q\D).neighborFinset v)).card:ℝ)-
        (common T S (fun v=>Q.neighborFinset v)).card|≤S.card*(θ*Fintype.card V) := by
      convert ordinary_common_sdiff_bound Q D T S (θ*Fintype.card V) hD using 1 <;> congr!
    have hrel' : q^S.card*s^j*((common Finset.univ S (fun x=>(P\F).neighborFinset x)).card:ℝ)-
        θ*Fintype.card V≤((common T S (fun x=>Q.neighborFinset x)).card:ℝ) := by
      convert hrel S hS using 1 <;> congr!
    suffices hnew : q^S.card*s^j*((common Finset.univ S (fun x=>(P\F).neighborFinset x)).card:ℝ)-
        (4*θ)*Fintype.card V≤((common T S (fun x=>(Q\D).neighborFinset x)).card:ℝ) by
      convert hnew using 1 <;> congr!
    have hlow:=(abs_le.mp hdel).1
    have hcost:=mul_le_mul_of_nonneg_right hS3 (mul_nonneg hθ.le hnR.le)
    nlinarith only [hrel',hlow,hcost]
  · intro v hv
    have hφ0 : ∀ C,0≤φ C:=fun C=>(div_pos hb (pow_pos hnR _)).le.trans (hφ C).1
    have hloss:=ordinaryLocalPotential_sdiff_bound P Q F D T (by omega) hnV φ hφ0 B
      (θ*Fintype.card V) hB (by simpa using fun C=>(hφ C).2) hD v
    have he : 3*(m+1:ℝ)^4*B*(θ*Fintype.card V)/Fintype.card V=C*θ:=by
      dsimp [C];field_simp [ne_of_gt hnR] <;> ring
    have hcast : ((m+1:ℕ):ℝ)=(m+1:ℝ):=by norm_cast
    rw [hcast,he] at hloss
    have hpot:=target_stability hloss (hpotential v)
    have heq:=ordinaryLocalPotential_present P (Q\D) F T hQD φ v hv
    rw [heq,abs_sub_comm] at hpot
    have hpot' : |1-hypergraphWeightedDegree localOrdinaryVertices wt v|≤θ+C*θ := by
      convert hpot using 1 <;> congr!
    exact hpot'.trans (by nlinarith only [hθη])

end Oberwolfach
