module

public import Oberwolfach.SubsetCentredMoments
public import Oberwolfach.FiniteCoordinateMoments
public import Oberwolfach.GoodAveraging

@[expose] public section

/-! The signed root coefficients in the correction of vertex sums.
The root is sampled by an independent uniform fixed-size subset in each
class, exactly as in the manuscript. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
    {V : I → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]

def profileDemandMultiplier (a : I → ℕ) (i : I) : ℝ :=
  (Fintype.card (V i):ℝ)*(Fintype.card (V i)-1)/
    ((a i:ℝ)*(Fintype.card (V i)-a i))

def profileDemandCoefficient (a : I → ℕ) (k mean : ℝ) (y : ∀ i,V i → ℝ)
    (σ : ∀ i,FixedSubset (V i) (a i)) : ℝ :=
  k*mean+∑ i,profileDemandMultiplier (V:=V) a i*(∑ v∈(σ i).val,y i v)

theorem profileDemandCoefficient_vertex_identity (a : I → ℕ)
    [∀ i,Nonempty (FixedSubset (V i) (a i))]
    (k mean : ℝ) (hk : 1 < k) (ha : ∀ i,1 ≤ a i)
    (hn : ∀ i,(Fintype.card (V i):ℝ)=(a i:ℝ)*k)
    (y : ∀ i,V i → ℝ) (hy : ∀ i,∑ v,y i v=0) (i : I) (v : V i) :
    (FiniteLaw.pi (fun j => FiniteLaw.uniform (FixedSubset (V j) (a j)))).expectation
      (fun σ => (if v∈(σ i).val then (1:ℝ) else 0)*profileDemandCoefficient a k mean y σ)=mean+y i v := by
  let μ := fun j => FiniteLaw.uniform (FixedSubset (V j) (a j))
  let ν := FiniteLaw.pi μ
  let ind := fun σ : ∀ j,FixedSubset (V j) (a j) => if v∈(σ i).val then (1:ℝ) else 0
  have haR (j : I) : (0:ℝ)<a j := by exact_mod_cast (show 0<a j by have hh:=ha j;omega)
  have hnR (j : I) : (1:ℝ)<Fintype.card (V j) := by
    rw [hn j]
    have h₁ : (1:ℝ) ≤ a j := by exact_mod_cast ha j
    nlinarith [haR j]
  have hr (j : I) : a j ≤ Fintype.card (V j) := by
    have hh : (a j:ℝ) ≤ Fintype.card (V j) := by rw [hn j];nlinarith [haR j]
    exact_mod_cast hh
  let : ∀ j,MeasurableSpace (FixedSubset (V j) (a j)) := fun _ => ⊤
  let : ∀ j,MeasurableSingletonClass (FixedSubset (V j) (a j)) := fun _ => ⟨fun _ => trivial⟩
  have hind : ν.expectation ind=(a i:ℝ)/Fintype.card (V i) := by
    rw [finiteLaw_coordinate_expectation μ i (fun S => if v∈S.val then (1:ℝ) else 0)]
    have hh := finiteLaw_expectation_indicator_value (μ i) (fun S => v∈S.val) 1
    simpa only [μ,one_mul,fixedSubset_vertex_probability (hr i)] using hh
  have hterm (j : I) : ν.expectation (fun σ => ind σ*(∑ u∈(σ j).val,y j u))=
      if j=i then ((a i:ℝ)*(Fintype.card (V i)-a i)/
        ((Fintype.card (V i):ℝ)*(Fintype.card (V i)-1)))*y i v else 0 := by
    by_cases hji : j=i
    · subst j
      have he (σ : ∀ j,FixedSubset (V j) (a j)) : ind σ*(∑ u∈(σ i).val,y i u)=
          if v∈(σ i).val then (∑ u∈(σ i).val,y i u) else 0 := by simp [ind]
      simp_rw [he]
      have hcoord := finiteLaw_coordinate_expectation μ i
        (fun S => if v∈S.val then (∑ u∈S.val,y i u) else 0)
      have hh := fixedSubset_centred_moment (hr i)
        (show 2 ≤ Fintype.card (V i) by exact_mod_cast hnR i) (y i) (hy i) v
      simp only [ite_true]
      convert hcoord.trans hh using 1 <;> congr!
    · have hh := finiteLaw_two_coordinate_product μ i j (Ne.symm hji)
        (fun S => if v∈S.val then (1:ℝ) else 0) (fun S => ∑ u∈S.val,y j u)
      have hz : (μ j).expectation (fun S => ∑ u∈S.val,y j u)=0 := by
        rw [fixedSubset_weighted_mean (hr j),hy j,mul_zero]
      rw [hz,mul_zero] at hh
      simpa only [hji,ite_false] using hh
  have heq (σ : ∀ j,FixedSubset (V j) (a j)) : ind σ*profileDemandCoefficient a k mean y σ=
      (k*mean)*ind σ+∑ j,profileDemandMultiplier (V:=V) a j*(ind σ*(∑ u∈(σ j).val,y j u)) := by
    simp only [profileDemandCoefficient,mul_add,Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl;intro j _;ring
  change ν.expectation (fun σ => ind σ*profileDemandCoefficient a k mean y σ)=_
  simp_rw [heq]
  rw [finiteLaw_expectation_add,finiteLaw_expectation_const_mul,finiteLaw_expectation_sum]
  simp_rw [finiteLaw_expectation_const_mul,hterm,hind,mul_ite,mul_zero]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  have hn0 : (Fintype.card (V i):ℝ)≠0 := by linarith [hnR i]
  have hn1 : (Fintype.card (V i):ℝ)-1≠0 := by linarith [hnR i]
  have hna : (Fintype.card (V i):ℝ)-a i≠0 := by rw [hn i];nlinarith [haR i]
  have ha0 : (a i:ℝ)≠0 := (haR i).ne'
  dsimp [profileDemandMultiplier]
  field_simp
  rw [hn i]
  ring

end Oberwolfach
