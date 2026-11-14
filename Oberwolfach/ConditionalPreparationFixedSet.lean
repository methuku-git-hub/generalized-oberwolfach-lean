module

public import Oberwolfach.OriginalMarginAllClassesOrdinaryReduction
public import Oberwolfach.ConditionalPreparationVariableClassSelector
public import Oberwolfach.PreparationClassProtectedSetBudget
public import Oberwolfach.PreparationClassFailureBudget
public import Oberwolfach.FactorPrunedClassSpecificDensity

@[expose] public section
/-! Assemble the checked ordinary and long preparation interfaces into the
fixed-set theorem, conditional on both preparation propositions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
set_option maxRecDepth 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance conditionalFixedFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _
local instance (priority := 2000) conditionalFixedSym2 (n:ℕ):DecidableEq (Sym2 (Fin n)):=@Sym2.instDecidableEq (Fin n) (instDecidableEqFin n)
local instance (priority := 2000) conditionalFixedOption (k:ℕ):DecidableEq (Option (Fin k)):=@Option.instDecidableEq (Fin k) (instDecidableEqFin k)

theorem conditional_preparation_fixed_set
    (hOrd:OrdinaryProtectedPreparation) (hLong:LongProtectedPreparation):FixedSetTheorem :=by
  intro Allowed hAllowed hValid α hα
  let θ:=allowedThreshold Allowed
  have hθ:(1/2:ℝ)≤θ:=allowedThreshold_half_le hAllowed hValid
  by_cases hθ1:θ<1
  · let κL:ℝ:=min (α/2000) (1/4)
    have hκL:0<κL:=by dsimp [κL];positivity
    have hκL1:κL≤1:=by dsimp [κL];linarith [min_le_right (α/2000) (1/4:ℝ)]
    have hκLcap:κL≤α/1000:=by dsimp [κL];linarith [min_le_left (α/2000) (1/4:ℝ)]
    let εL:ℝ:=α/400000
    have hεL:0<εL:=by dsimp [εL];positivity
    obtain ⟨K₀,_,hK₀,hSelector⟩:=conditional_preparation_variable_class_selector hOrd hLong θ (α/2) εL κL
      hθ hθ1 (by positivity) hεL hκL hκL1 0
    obtain ⟨K,hKK₀,hK,hAll⟩:=original_margin_all_classes_ordinary_reduction hOrd Allowed hAllowed hValid α hα K₀
    let κS:ℝ:=min (α/(2000*(K:ℝ))) (1/4)
    have hκS:0<κS:=by dsimp [κS];positivity
    have hκS1:κS≤1:=by dsimp [κS];linarith [min_le_right (α/(2000*(K:ℝ))) (1/4:ℝ)]
    have hκScap:κS≤α/(1000*(K:ℝ)):=by
      have hKr:0<(K:ℝ):=by exact_mod_cast (show 0<K by omega)
      dsimp [κS]
      have hh:=min_le_left (α/(2000*(K:ℝ))) (1/4:ℝ)
      have hcmp:α/(2000*(K:ℝ))≤α/(1000*(K:ℝ)):=by
        apply div_le_div_of_nonneg_left hα.le (by positivity) (by nlinarith)
      exact hh.trans hcmp
    let εS:ℝ:=α/(400000*((K:ℝ)+1))
    have hεS:0<εS:=by dsimp [εS];positivity
    obtain ⟨ξ,hξ,hPrep⟩:=hSelector K hKK₀ εS hεS κS hκS hκS1
    obtain ⟨χ,hχ,hχ1,Nfail,hFail⟩:=preparation_class_failure_budget K
    obtain ⟨Bclass,Nclass,hBclass,hNclass,hPrepared⟩:=hPrep χ hχ hχ1
    let Btotal:ℕ:=(K+1)*Bclass
    obtain ⟨Nall,hAll⟩:=hAll κL κS ξ hκL hκS hξ hκLcap hκScap Btotal
    refine ⟨max (max Nall Nclass) (max Nfail 1),?_⟩
    intro n hn D hEven hdegree F hF G hG
    have hn0:0<n:=by omega
    let v:Fin n:=⟨0,hn0⟩
    have hDn:D≤n:=by
      have hh:=Finset.card_le_univ (G.neighborFinset v)
      simpa only [SimpleGraph.card_neighborFinset_eq_degree,hG v,Fintype.card_fin] using hh
    let classify:=fun w:Fin (D/2)=>factorPreparationClass (F w) K
    let fibres:=fun j:Option (Fin K)=>Finset.univ.filter (fun w=>classify w=j)
    let cutoff:=fun j:Option (Fin K)=>if j=none then κL else κS
    let small:=fun j:Option (Fin K)=>((fibres j).card:ℝ)<cutoff j*n
    let removed:=Finset.univ.filter (fun w=>small (classify w))
    let remaining:={w:Fin (D/2) // w∉removed}
    let cf:=fun w:remaining=>classify w.val
    let D0:=D-2*removed.card
    let fibres0:=fun j:Option (Fin K)=>Finset.univ.filter (fun w:remaining=>cf w=j)
    let C:=Finset.univ.filter (fun j=>(fibres0 j).Nonempty)
    let k:=C.card
    let e:Fin k≃↥C:=(Fintype.equivFinOfCardEq (Fintype.card_coe C)).symm
    let m:=fun a:Fin k=>(fibres0 (e a).val).card
    let ρ:=fun a:Fin k=>2*(m a:ℝ)/(D0:ℝ)
    let eF:=fun a:Fin k=>factorClassFibreEquiv cf (e a).val
    let Fc:∀a,Fin (m a)→SimpleGraph (Fin n):=fun a j=>F ((eF a j).val).val
    have hParameters:=factor_pruned_class_indices hn0 K (by omega) classify D hEven (by simp) hDn θ α κL κS
      (by linarith) hα hκL hκS hκLcap hκScap hdegree
    have hSpecific:=factor_pruned_class_specific_density hn0 K (by omega) classify D hEven (by simp) hDn θ α κL κS
      (by linarith) hα hκL.le hκS.le hκLcap hκScap hdegree
    have hEven0:Even D0:=hParameters.2.1
    have hk:k≤K+1:=hParameters.2.2.2.1
    have hρpos:∀a,0≤ρ a:=fun a=>(hParameters.2.2.2.2.2.2.1 a).le
    have hρsum:∑a,ρ a=1:=hParameters.2.2.2.2.2.2.2.1
    let label:Fin k↪Option (Fin K):=⟨fun a=>(e a).val,fun a b hab=>e.injective (Subtype.ext hab)⟩
    apply hAll n (by omega) D G F hG hEven hdegree (fun w=>(hF w).1) (fun w=>(hF w).2)
    intro R hR hRG hmargin
    have hEach:∀a:Fin k,∃I:Finset (Fin n),
        (I.card:ℝ)≤(if label a=none then εL else εS)*n ∧
        1-χ-1/(n:ℝ)^10≤(FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin (ρ a) (hρpos a)
          (by have hh:=Finset.single_le_sum (fun b _=>hρpos b) (Finset.mem_univ a);linarith))).probability
            (fun σ=>ProtectedFactorPreparation R (retainedGraph R σ) I ξ Bclass (Fc a)):=by
      intro a
      have hρhi:ρ a≤1:=by have hh:=Finset.single_le_sum (fun b _=>hρpos b) (Finset.mem_univ a);linarith
      have hFca:∀j,(Fc a j).IsRegularOfDegree 2:=fun j=>(hF ((eF a j).val).val).1
      have hAca:∀j,AllowedCycleLengths (Fc a j) Allowed:=fun j=>(hF ((eF a j).val).val).2
      have hCca:∀j,factorPreparationClass (Fc a j) K=label a:=fun j=>(eF a j).property
      have hLd:label a=none→κL≤ρ a:=by
        intro ha
        have hh:=hSpecific.1 a ha
        linarith
      have hSd:∀i,label a=some i→κS≤ρ a:=by
        intro i ha
        have hh:=hSpecific.2 a i ha
        linarith
      exact hPrepared n (by omega) R D0 (m a) hR hEven0 hmargin (hρpos a) hρhi Allowed (Fc a) (le_refl _) hFca hAca (label a) hCca hLd hSd
    choose I hI hProb using hEach
    let Ba:Fin k→ℕ:=fun _=>Bclass
    let err:Fin k→ℝ:=fun _=>χ+1/(n:ℝ)^10
    refine ⟨I,Ba,err,?_,?_,?_,?_⟩
    · have hbudget:=preparation_class_protected_set_budget label I εL εS hεL.le hεS.le hk hI
      have hconstant:εL+((K:ℝ)+1)*εS=(α/2)/100000:=by
        dsimp [εL,εS]
        have hkp:((K:ℝ)+1)≠0:=by positivity
        field_simp
        ring
      simpa [hconstant] using hbudget
    · change (∑_a:Fin k,Bclass)≤(K+1)*Bclass
      calc
        (∑_a:Fin k,Bclass) = k*Bclass := by simp
        _ ≤ (K+1)*Bclass := Nat.mul_le_mul_right Bclass hk
    · dsimp [err]
      simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hFail n (by omega) k hk
    · intro hρ' hsum' a
      have hh:=hProb a
      dsimp [err]
      linarith
  · refine ⟨1,?_⟩
    intro n hn D hEven hdegree F hF G hG
    have hn0:0<n:=by omega
    let v:Fin n:=⟨0,hn0⟩
    have hDn:D≤n:=by
      have hh:=Finset.card_le_univ (G.neighborFinset v)
      simpa only [SimpleGraph.card_neighborFinset_eq_degree,hG v,Fintype.card_fin] using hh
    have hnR:0<(n:ℝ):=by exact_mod_cast hn0
    have hdn:(D:ℝ)≤n:=by exact_mod_cast hDn
    have hθge:1≤θ:=le_of_not_gt hθ1
    have : (n:ℝ)<(θ+α)*n:=by nlinarith
    linarith
end Oberwolfach
