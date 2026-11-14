module

public import Oberwolfach.ProtectedFactorPreparation
public import Oberwolfach.CoordinateLocalLemma

@[expose] public section
/-! A density-one preparation event decomposes the entire host into the
specified family; positive probability suffices because the sample is fixed. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem protected_preparation_density_one_decomposition {n D:ℕ}
    (G:SimpleGraph (Fin n)) (F:Fin (D/2)→SimpleGraph (Fin n)) (hEven:Even D)
    (hG:G.IsRegularOfDegree D) (I:Finset (Fin n)) (ξ:ℝ) (hξ:0≤ξ) (B:ℕ)
    (hPrep:ProtectedFactorPreparation G G I ξ B F):HasFactorDecomposition G F :=by
  obtain ⟨A,hA,hAcap,hRobust⟩:=hPrep
  have hDhalf:2*(D/2)=D:=by have hdiv:=hEven.two_dvd;omega
  have hreg:G.IsRegularOfDegree (2*(D/2)):=by simpa only [hDhalf] using hG
  have hDiff:∀x:Fin n,((Finset.univ.filter (fun y=>Xor (G.Adj x y) (G.Adj x y))).card:ℝ)≤ξ*n:=by
    intro x
    have hEmpty:(Finset.univ.filter (fun y=>Xor (G.Adj x y) (G.Adj x y)))=∅:=by ext y;simp [Xor]
    rw [hEmpty]
    simp only [Finset.card_empty,Nat.cast_zero]
    positivity
  exact hRobust G le_rfl hreg hA (by intros;rfl) hDiff

theorem protected_preparation_density_one_probability_decomposition {n D:ℕ}
    (G:SimpleGraph (Fin n)) (F:Fin (D/2)→SimpleGraph (Fin n)) (hEven:Even D)
    (hG:G.IsRegularOfDegree D) (I:Finset (Fin n)) (ξ:ℝ) (hξ:0≤ξ) (B:ℕ)
    (hProb:0<(FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin 1 (by norm_num) (by norm_num))).probability
      (fun σ=>ProtectedFactorPreparation G (retainedGraph G σ) I ξ B F)):
    HasFactorDecomposition G F :=by
  let μ:=FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin 1 (by norm_num) (by norm_num))
  obtain ⟨σ,hMass,hPrep⟩:=finiteLaw_positive_event_exists μ _ hProb
  have htrue:∀e,σ e=true:=by
    intro e
    by_contra h
    have he:σ e=false:=by cases hs:σ e <;> simp_all
    have hz:μ.mass σ=0:=by
      change (∏e, (FiniteLaw.retentionCoin 1 (by norm_num) (by norm_num)).mass (σ e))=0
      apply Finset.prod_eq_zero (Finset.mem_univ e)
      simp [FiniteLaw.retentionCoin,he]
    linarith
  have hGraph:retainedGraph G σ=G:=by ext x y;simp [retainedGraph,htrue]
  rw [hGraph] at hPrep
  exact protected_preparation_density_one_decomposition G F hEven hG I ξ hξ B hPrep
end Oberwolfach
