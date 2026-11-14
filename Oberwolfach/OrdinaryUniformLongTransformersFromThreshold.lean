module

public import Oberwolfach.OrdinaryRelativeHostTransformerFromSampledInputs
public import Oberwolfach.OrdinaryAbsorberSlackChoice
public import Oberwolfach.OrdinaryUniformLongAbsorberFromThreshold
public import Oberwolfach.OrdinaryLongAmbientAbsorberFromSampledInputs
public import Oberwolfach.OrdinaryUniformFourCycleAbsorberFromThreshold
public import Oberwolfach.OrdinaryFourCycleTripleMargin
public import Oberwolfach.OrdinaryUniformLongSampledAbsorberInputsWithRows
public import Oberwolfach.OrdinaryPositiveHubDensity
public import Oberwolfach.FourSharpThreshold
public import Oberwolfach.PositiveOrdinaryCycleWeights
public import Oberwolfach.AlmostSpanningCyclePacking
public import Oberwolfach.OrdinaryUniformLongSampledAbsorberInputs
public import Oberwolfach.OrdinaryPreparationProbability
public import Oberwolfach.OrdinaryIndexHubBoundFromDensity
public import Oberwolfach.OrdinaryUniformProfilePairProfilesAndInputsJointSmallBeta
public import Oberwolfach.OrdinaryUniformSampledProfileJointSmallBeta
public import Oberwolfach.OrdinaryUniformSampledProfileJointFixedBeta
public import Oberwolfach.OrdinaryUniformSampledProfileExistsFixedBeta
public import Oberwolfach.OrdinaryUniformSampledProfileExists
public import Oberwolfach.OrdinarySampledPropertyToProfiles

@[expose] public section
/-! Choose all error constants before the order threshold, then obtain an
actual sample supplying all two-hub profile inputs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_uniform_sampled_long_transformers_from_threshold
    (k d:ℕ) (hk:4≤k) (hd:2≤d) (α pmin smin L ω:ℝ)
    (hα:0<α) (hpmin:0<pmin) (hsmin:0<smin) (hsmin1:smin≤1) (hω:0<ω) (hL:0≤L):
    ∃ εtrans εsample:ℝ,0<εtrans ∧ 0<εsample ∧ ∀ m:ℕ,∃ t:ℕ,1≤t ∧ ∀ f:ℕ,∃ N:ℕ,
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],
    N≤Fintype.card V → Fintype.card U≤Fintype.card V → ω*Fintype.card V≤(Fintype.card U:ℝ) →
    ∀ (P F:SimpleGraph V) (π:Equiv.Perm V),
    permutationConflictGraph π (3*d)≤F →
    (∀ x k,0<k→k<2*d+1→(π^k) x≠x) →
    (∀ v,(F.degree v:ℝ)≤L) →
    (∀ v,(cycleThreshold (k+1)+α)*Fintype.card V≤(P.degree v:ℝ)) →
    ∀ D:ℝ,(Fintype.card V:ℝ)/2≤D → D≤2*Fintype.card V →
    (∀ v,|(P.degree v:ℝ)-D|≤εsample*Fintype.card V) →
    ∀ (p:ℝ) (hp:pmin≤p) (hp1:p≤1),
    ∀ (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g)) (j:Color),
    (∀ u,smin≤s u j) → (∀ u,s u j≤1) →
    ∀ pH:ℝ,smin≤pH → (∀ u,s u j=pH) →
    ∃ σ:RawWheelOutcome V U Γ Color,
      ∀ (G:SimpleGraph V) (H₀:V→U→Prop) (φ:V→V) (ψ:U→U)
      (A Z R W:Finset V) (B:Finset U) (L:Finset (Sym2 V⊕(V×U))),
      A=Finset.univ\Z→(Z.card:ℝ)≤εtrans*Fintype.card V→
      ordinaryResourceRows L⊆W→ ordinaryResourceHubs L⊆B→R⊆W→
      R.card≤m→W.card≤f→(B.card:ℝ)≤εtrans*Fintype.card V+f→
      (∀ v,G.degree v=2*((Finset.univ:Finset U).filter (H₀ v)).card)→
      (∀ u,k+1∣((Finset.univ:Finset V).filter (fun v=>H₀ v u)).card)→
      (∀ u,((Finset.univ:Finset V).filter (fun v=>H₀ v u)).card≤m)→
      Fintype.card {u:U // ∃ v,H₀ v u}≤m→
      (∀ v∈G.support,v∈R∧φ v∈R)→
      (∀ v∈G.support,∀ w∈G.support,φ v≠w)→
      (∀ u,(∃ v,H₀ v u)→u≠ψ u)→
      G≤rawWheelGraph P σ\F→(∀ v w,G.Adj v w→(rawWheelGraph P σ\F).Adj (φ v) (φ w))→
      Function.Injective (fun i:G.edgeFinset=>s(φ i.val.out.1,φ i.val.out.2))→
      Function.Injective (fun i:{e:V×U // H₀ e.1 e.2}=>(φ i.val.1,ψ i.val.2))→
      (∀ v u,H₀ v u→ rawWheelSpokes π d σ j v u∧rawWheelSpokes π d σ j (φ v) (ψ u))→
      (∀ e:{e:V×U // H₀ e.1 e.2},e.val.2∈B∧ψ e.val.2∈B)→
      (∀ v w,G.Adj v w→∀ a∈({v,w,φ v,φ w}:Finset V),
        ∀ c∈({v,w,φ v,φ w}:Finset V),¬F.Adj a c)→
      
      ∃ N:Finset V,∃ K:Finset (Sym2 V⊕(V×U)),
        N.card≤m*(k+1)*(t+5*m)∧
        IsResourceTransformer (ordinaryWheelResources (P:=rawWheelGraph P σ\F) (F:=F) (Hbase:=rawWheelSpokes π d σ j) (r:=k+1))
          (ordinaryHostResources G H₀) (transformerImageResources G H₀ φ ψ) K∧
        K⊆ordinaryHostResources (rawWheelGraph P σ\F) (rawWheelSpokes π d σ j)∧
        (∀ v v',Sum.inl s(v,v')∈K→v∈N∧v'∈N)∧
        (∀ v a,Sum.inr (v,a)∈K→v∈N)∧
        (∀ v∈R,∀ v'∈R,Sum.inl s(v,v')∉K)∧
        (∀ v∈R,∀ a∈B,Sum.inr (v,a)∉K)∧
        ∃ B':Finset U,B'.card≤m*(m+2)∧
          (∀ v a,Sum.inr (v,a)∈K→a∈B')∧
          (∀ v∈W,∀ v',Sum.inl s(v,v')∈K→v∈R)∧
          (∀ v∈W,∀ a,Sum.inr (v,a)∈K→v∈R)∧
          (∀ v a,Sum.inr (v,a)∈K→a∈B→∃ i:{u:U // ∃ v,H₀ v u},a=i.val∨a=ψ i.val)∧
          (ordinaryPhysicalGraph (ordinaryResourceRim (rawWheelGraph P σ\F) K) (fun v u=>Sum.inr (v,u)∈K)).support.toFinset.card≤
            m*((k+1)*(t+5*m)+m+2)∧N⊆R∪A∧Disjoint K L := by
  obtain ⟨a,b,ha,hb,hSample⟩:=ordinary_uniform_sampled_long_absorber_inputs_from_threshold k d (by omega) hd α pmin smin L ω hα hpmin hsmin hsmin1 hω hL
  obtain ⟨β,hβ,hβmax,hβhub⟩:=ordinary_long_absorber_slack_choice (k+7) α pmin smin ω hα hpmin hsmin hω
  obtain ⟨η,εtrans,hη,hεtrans,hεβ,hTrans⟩:=ordinary_relative_host_transformer_from_sampled_inputs k (by omega) β a b pmin smin hβ ha hb hpmin hsmin
  obtain ⟨εsample,hεsample,Nsample,hSample⟩:=hSample β hβ hβmax hβhub η hη
  refine ⟨εtrans,εsample,hεtrans,hεsample,?_⟩
  intro m
  obtain ⟨t,ht,hTrans⟩:=hTrans m
  refine ⟨t,ht,?_⟩
  intro f
  obtain ⟨Ntrans,hTrans⟩:=hTrans f L hL
  refine ⟨max Nsample (max Ntrans 1),?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hu hlo P F π hF hnoshort hdeg hP D hD hDhi hnear p hp hp1 q hq hQ s hs hS j hslo hshi pH hpH hj
  obtain ⟨σ,hσ,hprofiles,hhub⟩:=hSample V U Γ Color (by omega) hu hlo P F π hF hnoshort hdeg hP D hD hDhi hnear p hp hp1 q hq hQ s hs hS j hslo hshi pH hpH hj
  have hn0:0<Fintype.card V:=by omega
  letI:Nonempty U:=ordinary_positive_hub_density_nonempty V U ω hω hn0 hlo
  refine ⟨σ,?_⟩
  intro G H₀ φ ψ A Z R W B Lr hA hZ hrows hhubs hRW hRcard hWcard hBcard
    hbalance hdiv hq hnU hroot hcross hu' hQ' hφQ hφedge hψedge hH hB hFroots
  apply hTrans V U Γ Color (by omega) G (rawWheelGraph P σ\F) F H₀ (rawWheelSpokes π d σ j) φ ψ A Z R W B Lr P π d σ j rfl rfl
    hA hZ hrows hhubs hRW hRcard hWcard hBcard hbalance hdiv hq hnU hroot hcross hu' hQ' hφQ hφedge hψedge hH hB hFroots hdeg
  · intro impossible
    omega
  · exact hhub
  · exact hσ
end Oberwolfach
