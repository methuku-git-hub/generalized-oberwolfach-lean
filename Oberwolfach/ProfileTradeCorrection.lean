module

public import Oberwolfach.ProfileRootSampling
public import Oberwolfach.ProfileWeightDefects
public import Oberwolfach.FiniteTradeCorrection

@[expose] public section

/-! Exact correction on prescribed vertex classes, using the explicit
uniform-root coefficients and signed absorber trades. The displayed
trade spread is a separate combinatorial counting input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I C : Type*} [Fintype I] [Fintype C] [DecidableEq I] [Nonempty I]
    {V : I → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]

theorem profile_trade_correction (a : I → ℕ) [∀ i,Nonempty (FixedSubset (V i) (a i))]
    (q : ℕ) (ha : ∀ i,1 ≤ a i) (hsize : ∑ i,a i=q+1)
    (k η K : ℝ) (hk : 2 ≤ k) (hη : 0 ≤ η) (hK : 0 ≤ K)
    (hn : ∀ i,(Fintype.card (V i):ℝ)=(a i:ℝ)*k)
    (R : C → Finset (Σ i,V i)) (w : C → ℝ)
    (hR : ∀ C₀ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈R C₀)).card=a i)
    (herr : ∀ i v,|1-hypergraphWeightedDegree R w ⟨i,v⟩| ≤ η)
    (T : (∀ i,FixedSubset (V i) (a i)) → C → ℝ)
    (hT : ∀ σ v,hypergraphWeightedDegree R (T σ) v=if v∈profileRootSet σ then 1 else 0)
    (hspread : ∀ σ C₀,|T σ C₀| ≤ K/k^(q+1)+
      (if (R C₀∩profileRootSet σ).Nonempty then K/k^q else 0)) :
    ∃ ψ : C → ℝ,(∀ v,hypergraphWeightedDegree R ψ v=1) ∧
      ∀ C₀,|ψ C₀-w C₀| ≤ (1+4*(∑ i,(a i:ℝ)))*K*(q+2)*η/k^q := by
  let μ := FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (V i) (a i)))
  let m := 1-(∑ C₀,w C₀)/k
  let y := fun i (v : V i) => 1-hypergraphWeightedDegree R w ⟨i,v⟩-m
  let t := profileDemandCoefficient a k m y
  let D := 1+4*(∑ i,(a i:ℝ))
  have hk0 : 0 < k := by linarith
  have hk1 : 1 < k := by linarith
  obtain ⟨hm,hy,hymag⟩ := profile_defect_centred_data R w a hR k η hk0 ha hn herr
  change |m| ≤ η at hm
  change ∀ i,∑ v,y i v=0 at hy
  change ∀ i v,|y i v| ≤ 2*η at hymag
  have ht : ∀ v,μ.expectation (fun σ => t σ*(if v∈profileRootSet σ then 1 else 0))=
      1-hypergraphWeightedDegree R w v := by
    rintro ⟨i,v⟩
    have hh := profileDemandCoefficient_vertex_identity a k m hk1 ha hn y hy i v
    have he : m+y i v=1-hypergraphWeightedDegree R w ⟨i,v⟩ := by dsimp [y];ring
    rw [he] at hh
    convert hh using 1
    apply congrArg μ.expectation
    funext σ
    simp only [profileRootSet_mem]
    dsimp [t]
    ring
  have htmag (σ : ∀ i,FixedSubset (V i) (a i)) : |t σ| ≤ D*η*k :=
    profileDemandCoefficient_bound a k m η hk hη ha hn hm y hymag σ
  have hcard (C₀ : C) : (R C₀).card=q+1 := by rw [sigma_finset_card];simp only [hR];exact hsize
  have hprob (C₀ : C) : μ.probability (fun σ => (R C₀∩profileRootSet σ).Nonempty) ≤ (q+1)/k := by
    have hh := profileRootSet_hit_probability a k hk1 ha hn (R C₀)
    simpa only [hcard,Nat.cast_add,Nat.cast_one] using hh
  have hTavg (C₀ : C) : μ.expectation (fun σ => |T σ C₀|) ≤ K*(q+2)/k^(q+1) := by
    have hh := finiteLaw_trade_bound_from_hit_probability μ T
      (fun C₀ σ => (R C₀∩profileRootSet σ).Nonempty) (K/k^(q+1)) (K/k^q) ((q+1)/k)
      (by positivity) (by intro σ C₀; convert hspread σ C₀ using 1 <;> congr!) hprob C₀
    have he : K/k^(q+1)+(K/k^q)*((q+1)/k)=K*(q+2)/k^(q+1) := by
      rw [pow_succ]
      field_simp
      <;> ring
    rwa [he] at hh
  refine ⟨correctedTradeWeight μ w t T,correctedTradeWeight_exact μ R profileRootSet w t T hT ht,?_⟩
  intro C₀
  have hh := correctedTradeWeight_difference μ w t T (D*η*k) (K*(q+2)/k^(q+1))
    (by dsimp [D];positivity) htmag hTavg C₀
  have he : (D*η*k)*(K*(q+2)/k^(q+1))=D*K*(q+2)*η/k^q := by
    rw [pow_succ]
    field_simp
    <;> ring
  rwa [he] at hh

end Oberwolfach
