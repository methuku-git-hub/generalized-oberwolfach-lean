module

public import Oberwolfach.OrdinaryUniformFourInputsWithExtraEventFromThreshold
public import Oberwolfach.OrdinaryUniformFourCycleAbsorberFromThreshold
public import Oberwolfach.OrdinarySampledProfileToleranceMono
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

theorem ordinary_uniform_sampled_four_cycle_absorbers_and_transformers_with_extra_event
    (d:ℕ) (hd:2≤d) (α pmin smin L ω:ℝ)
    (hα:0<α) (hpmin:0<pmin) (hsmin:0<smin) (hsmin1:smin≤1) (hω:0<ω) (hL:0≤L):
    ∃ εabs εtrans εsample:ℝ,0<εabs ∧ 0<εtrans ∧ 0<εsample ∧ ∀ m:ℕ,∃ a₀ b₀ t:ℕ,1≤t ∧ ∀ f:ℕ,∃ N:ℕ,
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],
    N≤Fintype.card V → Fintype.card U≤Fintype.card V → ω*Fintype.card V≤(Fintype.card U:ℝ) →
    ∀ (P F:SimpleGraph V) (π:Equiv.Perm V),
    permutationConflictGraph π (3*d)≤F →
    (∀ x k,0<k→k<2*d+1→(π^k) x≠x) →
    (∀ v,(F.degree v:ℝ)≤L) →
    (∀ v,(cycleThreshold 4+α)*Fintype.card V≤(P.degree v:ℝ)) →
    ∀ D:ℝ,(Fintype.card V:ℝ)/2≤D → D≤2*Fintype.card V →
    (∀ v,|(P.degree v:ℝ)-D|≤εsample*Fintype.card V) →
    ∀ (p:ℝ) (hp:pmin≤p) (hp1:p≤1),
    ∀ (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g)) (j:Color),
    (∀ u,smin≤s u j) → (∀ u,s u j≤1) →
    ∀ pH:ℝ,smin≤pH → (∀ u,s u j=pH) →
    let μ:=FiniteLaw.pi (rawWheelLaw (fun _ : Sym2 V=>p) (fun _=>le_trans (le_of_lt hpmin) hp) (fun _=>hp1) d hd q hq hQ s hs hS);
    ∀ Extra:RawWheelOutcome V U Γ Color→Prop,
      1/(Fintype.card V:ℝ)+2/(Fintype.card V:ℝ)^2 < μ.probability Extra →
    ∃ σ:RawWheelOutcome V U Γ Color, Extra σ ∧
      (∀ (G:SimpleGraph V) (Hs:V→U→Prop) (A Z W:Finset V) (B₀:Finset U),
      (ordinaryPhysicalGraph G Hs).support.toFinset.card≤m →
      (∀ v,G.degree v=2*(Finset.univ.filter (Hs v)).card) →
      (∀ u,4∣(Finset.univ.filter (fun v=>Hs v u)).card) →
      G≤rawWheelGraph P σ\F → (∀ v u,Hs v u→ rawWheelSpokes π d σ j v u) →
      (∀ u,(∃ v,Hs v u)→u∈B₀) →
      A=Finset.univ\Z → (Z.card:ℝ)≤εabs*Fintype.card V → W.card≤f → (B₀.card:ℝ)≤εabs*Fintype.card V+f →
      ∃ C:Finset (Sym2 V⊕(V×U)),
        IsResourceAbsorber (ordinaryWheelResources (P:=rawWheelGraph P σ\F) (F:=F) (Hbase:=rawWheelSpokes π d σ j) (r:=4))
          (ordinaryHostResources G Hs) C ∧
        C⊆ordinaryHostResources (rawWheelGraph P σ\F) (rawWheelSpokes π d σ j) ∧
        (ordinaryResourceRows C).card≤a₀ ∧ (ordinaryResourceHubs C).card≤b₀ ∧
        ordinaryResourceRows C⊆G.support.toFinset∪A ∧
        (∀ v∈ordinaryResourceRows C,v∈W→v∈G.support.toFinset) ∧
        (∀ u∈ordinaryResourceHubs C,u∈B₀→u∈Finset.univ.filter (fun u=>∃ v,Hs v u)) ∧
        Disjoint C (ordinaryRootResources W B₀)) ∧
      (∀ (G:SimpleGraph V) (H₀:V→U→Prop) (φ:V→V) (ψ:U→U)
      (A Z R W:Finset V) (B:Finset U) (L:Finset (Sym2 V⊕(V×U))),
      A=Finset.univ\Z→(Z.card:ℝ)≤εtrans*Fintype.card V→
      ordinaryResourceRows L⊆W→ ordinaryResourceHubs L⊆B→R⊆W→
      R.card≤m→W.card≤f→(B.card:ℝ)≤εtrans*Fintype.card V+f→
      (∀ v,G.degree v=2*((Finset.univ:Finset U).filter (H₀ v)).card)→
      (∀ u,4∣((Finset.univ:Finset V).filter (fun v=>H₀ v u)).card)→
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
        N.card≤m*(4)*(t+5*m)∧
        IsResourceTransformer (ordinaryWheelResources (P:=rawWheelGraph P σ\F) (F:=F) (Hbase:=rawWheelSpokes π d σ j) (r:=4))
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
            m*((4)*(t+5*m)+m+2)∧N⊆R∪A∧Disjoint K L) := by
  obtain ⟨a,b,β,ha,hb,hβ,hSample⟩:=ordinary_uniform_sampled_four_cycle_inputs_with_extra_event_from_threshold d hd α pmin smin L ω hα hpmin hsmin hsmin1 hω hL
  obtain ⟨ηA,εabs,hηA,hεabs,hεβA,hAbs⟩:=ordinary_long_cycle_ambient_absorber_from_sampled_inputs 3 (by omega) β a b pmin smin hβ ha hb hpmin hsmin
  obtain ⟨ηT,εtrans,hηT,hεtrans,hεβT,hTrans⟩:=ordinary_relative_host_transformer_from_sampled_inputs 3 (by omega) β a b pmin smin hβ ha hb hpmin hsmin
  let η:=min ηA ηT
  have hη:0<η:=lt_min hηA hηT
  obtain ⟨εsample,hεsample,Nsample,hSample⟩:=hSample η hη
  refine ⟨εabs,εtrans,εsample,hεabs,hεtrans,hεsample,?_⟩
  intro m
  obtain ⟨a₀,b₀,hAbs⟩:=hAbs m
  obtain ⟨t,ht,hTrans⟩:=hTrans m
  refine ⟨a₀,b₀,t,ht,?_⟩
  intro f
  obtain ⟨Nabs,hAbs⟩:=hAbs f L hL
  obtain ⟨Ntrans,hTrans⟩:=hTrans f L hL
  refine ⟨max Nsample (max Nabs (max Ntrans 1)),?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hu hlo P F π hF hnoshort hdeg hP D hD hDhi hnear p hp hp1 q hq hQ s hs hS j hslo hshi pH hpH hj μ Extra hExtra
  obtain ⟨σ,hExtraσ,hσ,hprofiles,hhub,hthree⟩:=hSample V U Γ Color (by omega) hu hlo P F π hF hnoshort hdeg hP D hD hDhi hnear p hp hp1 q hq hQ s hs hS j hslo hshi pH hpH hj Extra hExtra
  have hn0:0<Fintype.card V:=by omega
  letI:Nonempty U:=ordinary_positive_hub_density_nonempty V U ω hω hn0 hlo
  have hσA:=ordinary_sampled_profile_tolerance_mono (4) P F π d σ pmin smin j β η ηA a b (min_le_left _ _) hσ
  have hσT:=ordinary_sampled_profile_tolerance_mono (4) P F π d σ pmin smin j β η ηT a b (min_le_right _ _) hσ
  refine ⟨σ,hExtraσ,?_,?_⟩
  · intro G Hs A Z W B₀ hm hbal hdiv hG hHs hB₀ hA hZ hW hBsize
    apply hAbs V U Γ Color (by omega) G Hs (rawWheelGraph P σ\F) F (rawWheelSpokes π d σ j) A Z W B₀ P π d σ j rfl rfl
      hm hbal hdiv hG hHs hB₀ hA hZ hW hBsize hdeg
    · intro _ x y z
      have hh:=hthree x y z
      convert hh using 1 <;> try (congr 1; congr 1; ext t; simp)
    · exact hhub
    · exact hσA
  · intro G H₀ φ ψ A Z R W B Lr hA hZ hrows hhubs hRW hRcard hWcard hBcard
      hbalance hdiv hq hnU hroot hcross hu' hQ' hφQ hφedge hψedge hH hB hFroots
    apply hTrans V U Γ Color (by omega) G (rawWheelGraph P σ\F) F H₀ (rawWheelSpokes π d σ j) φ ψ A Z R W B Lr P π d σ j rfl rfl
      hA hZ hrows hhubs hRW hRcard hWcard hBcard hbalance hdiv hq hnU hroot hcross hu' hQ' hφQ hφedge hψedge hH hB hFroots hdeg
    · intro _ x y z
      have hh:=hthree x y z
      convert hh using 1 <;> try (congr 1; congr 1; ext t; simp)
    · exact hhub
    · exact hσT
end Oberwolfach
