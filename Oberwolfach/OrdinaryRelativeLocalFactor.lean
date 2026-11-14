module

public import Oberwolfach.OrdinarySparseLocalFactor
public import Oberwolfach.OrdinaryLocalNeighbourhoods

@[expose] public section

/-! Exact ordinary local factors from the lower relative-neighbourhood
hypothesis used in the manuscript. Constants are uniform over both spoke
counts, both densities and all graphs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 3800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_relative_local_factor (m : ℕ) (hm : 2≤m) (α p b B : ℝ)
    (hα : 0<α) (hp : 0<p) (hp1 : p≤1) (hb : 0<b) (hB : 0≤B) :
    ∃ ε₀ η : ℝ,0<ε₀ ∧ 0<η ∧ ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V],N≤Fintype.card V →
      ∀ (P Q F : SimpleGraph V) (T : Finset V) (j : ℕ) (q s ε : ℝ),
      j≤2 → p≤q → p≤s → ε≤ε₀ →
      (∀ v,(ordinaryLocalBaseDegree m+α)*Fintype.card V≤(P.degree v:ℝ)) →
      (∀ v,(F.degree v:ℝ)≤ε₀*Fintype.card V) →
      (∀ S : Finset V,S.card≤ordinaryLocalRootBound m →
        q^S.card*s^j*((common Finset.univ S (fun x=>(P\F).neighborFinset x)).card:ℝ)-
          ε*Fintype.card V≤((common T S (fun x=>Q.neighborFinset x)).card:ℝ)) →
      (m+1)∣T.card → ∀ wt : LocalOrdinaryCycle Q F T (m+1)→ℝ,
      (∀ C,b/(Fintype.card V:ℝ)^m≤wt C ∧ wt C≤B/(Fintype.card V:ℝ)^m) →
      (∀ v∈T,|1-hypergraphWeightedDegree localOrdinaryVertices wt v|≤η) →
      HasResourceDecomposition (localOrdinaryVertices (Q:=Q) (F:=F) (T:=T) (r:=m+1)) T := by
  let u := min α (1/4)
  have hu : 0<u := lt_min hα (by norm_num)
  let μ := u/2
  have hμ : 0<μ := by dsimp [μ];positivity
  let δ := ordinaryLocalBaseDegree m+μ
  obtain ⟨hδ,hmargin⟩ := ordinary_local_margin m α hα
  change δ≤1 at hδ
  change 0<1-(ordinaryLocalRootBound m:ℝ)*(1-δ) at hmargin
  let γ := p^(ordinaryLocalRootBound m+2)*(1-(ordinaryLocalRootBound m:ℝ)*(1-δ))/2
  have hγ : 0<γ := by dsimp [γ];positivity
  obtain ⟨εf,η,hεf,hη,N,hfactor⟩ := ordinary_sparse_local_factor m hm γ γ b B hγ hγ hb hB
  let ε₀ := min εf (min μ γ)
  have hε₀ : 0<ε₀ := lt_min hεf (lt_min hμ hγ)
  refine ⟨ε₀,η,hε₀,hη,N,?_⟩
  intro V _ _ hn P Q F T j q s ε hj hq hs hε hP hF hrel hdiv wt hw herr
  have heμ : ε₀≤μ := (min_le_right εf _).trans (min_le_left μ γ)
  have heγ : ε₀≤γ := (min_le_right εf _).trans (min_le_right μ γ)
  have heF : ε₀≤εf := min_le_left _ _
  have hP' (v : V) : (δ+μ)*Fintype.card V≤(P.degree v:ℝ) := by
    have huα : u≤α := min_le_left _ _
    have hcoef : δ+μ≤ordinaryLocalBaseDegree m+α := by dsimp [δ,μ];linarith
    exact (mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _)).trans (hP v)
  have hF' (v : V) : (F.degree v:ℝ)≤μ*Fintype.card V :=
    (hF v).trans (mul_le_mul_of_nonneg_right heμ (Nat.cast_nonneg _))
  have hc (S : Finset V) (hS : S.card≤ordinaryLocalRootBound m) :
      γ*Fintype.card V≤((common T S (fun x=>Q.neighborFinset x)).card:ℝ) := by
    have hh := ordinary_relative_common_lower P Q F T S (ordinaryLocalRootBound m) j δ μ p q s ε
      hδ hμ.le hp hp1 hq hs hS hj hP' hF' hmargin.le (hrel S hS)
    have hεγ := hε.trans heγ
    have hcoef : γ≤p^(ordinaryLocalRootBound m+2)*(1-(ordinaryLocalRootBound m:ℝ)*(1-δ))-ε := by
      dsimp [γ] at *;linarith only [hεγ]
    exact (mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _)).trans hh
  have hsize : γ*Fintype.card V≤(T.card:ℝ) := by
    simpa [common] using
      hc ∅ (by simp [ordinaryLocalRootBound])
  exact hfactor V hn Q F T hsize hdiv
    (fun v=>(hF v).trans (mul_le_mul_of_nonneg_right heF (Nat.cast_nonneg _)))
    (fun S hS=>hc S hS) wt hw herr

end Oberwolfach
