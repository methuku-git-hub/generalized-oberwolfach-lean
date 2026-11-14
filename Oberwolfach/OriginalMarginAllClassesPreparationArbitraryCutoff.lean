module

public import Oberwolfach.ProtectedPreparationDensityOneProbability
public import Oberwolfach.PrunedCutoffRepresentation
public import Oberwolfach.OriginalMarginPrunedLongRemainingArbitraryCutoff
public import Oberwolfach.FactorPrunedPreparedFamilyDecomposition

@[expose] public section
/-! Original-margin reduction to ordinary small-class copies and protected
preparation probability bounds for the retained classes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance allClassesPreparationArbitraryFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _
local instance (priority := 2000) allClassesPreparationArbitrarySym2 (n:ℕ):DecidableEq (Sym2 (Fin n)):=@Sym2.instDecidableEq (Fin n) (instDecidableEqFin n)
local instance (priority := 2000) allClassesPreparationArbitraryOption (k:ℕ):DecidableEq (Option (Fin k)):=@Option.instDecidableEq (Fin k) (instDecidableEqFin k)

theorem original_margin_all_classes_preparation_arbitrary_cutoff (α:ℝ) (hα:0<α) (KExtra:ℕ):
    ∃K:ℕ,KExtra≤K ∧ 3≤K ∧ ∀κL κS ξ:ℝ,0<κL→0<κS→0<ξ→
      κL≤α/1000→κS≤α/(1000*(K:ℝ))→∀B:ℕ,∃N:ℕ,
    ∀n≥N,∀Allowed:Set ℕ,Allowed.Nonempty→(∀s∈Allowed,3≤s)→
    ∀(D:ℕ) (G:SimpleGraph (Fin n)) (F:Fin (D/2)→SimpleGraph (Fin n)),
      G.IsRegularOfDegree D→Even D→(allowedThreshold Allowed+α)*(n:ℝ)≤D→
      (∀w,(F w).IsRegularOfDegree 2)→(∀w,AllowedCycleLengths (F w) Allowed)→
    let classify:=fun w=>factorPreparationClass (F w) K
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
    let Fc:∀a,Fin (m a)→SimpleGraph (Fin n):=fun a j=>F ((eF a j).val).val;
    (∀P:SimpleGraph (Fin n),∀d:ℕ,P.IsRegularOfDegree d→Even d→
      (allowedThreshold Allowed+α/2)*(n:ℝ)≤d→∀w∈removed,classify w≠none→
      ∃(Iord:Finset (Fin n)) (ξord:ℝ) (Bord:ℕ),0≤ξord ∧
        0<(FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin 1 (by norm_num) (by norm_num))).probability
          (fun σ=>ProtectedFactorPreparation P (retainedGraph P σ) Iord ξord Bord (fun _:Fin (d/2)=>F w)))→
    (∀R:SimpleGraph (Fin n),R.IsRegularOfDegree D0→R≤G→
      (allowedThreshold Allowed+α/2)*(n:ℝ)≤(D0:ℝ)→
      ∃(I:Fin k→Finset (Fin n)) (Ba:Fin k→ℕ) (err:Fin k→ℝ),
        ((∑a,(I a).card:ℕ):ℝ)≤(α/2)/100000*n ∧ (∑a,Ba a≤B) ∧
        1/(n:ℝ)^10+(∑a,err a)<1 ∧
        ∀(hρ:∀a,0≤ρ a) (htotal:∑a,ρ a=1),∀a,1-err a≤
          (FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin (ρ a) (hρ a)
            (by have h:=Finset.single_le_sum (fun b _=>hρ b) (Finset.mem_univ a);linarith))).probability
              (fun σ=>ProtectedFactorPreparation R (retainedGraph R σ) (I a) ξ (Ba a) (Fc a)))→
    HasFactorDecomposition G F :=by
  obtain ⟨K,Nbase,hKExtra,hK,hRemove⟩:=original_margin_pruned_long_remaining_arbitrary_cutoff α hα KExtra
  refine ⟨K,hKExtra,hK,?_⟩
  intro κL κS ξ hL0 hS0 hξ hL hS B
  obtain ⟨Npart,hPart⟩:=factor_pruned_protected_preparations_decompose_remaining_family K (by omega) α κL κS ξ hα hL0 hS0 hξ hL hS B
  refine ⟨max (max Nbase Npart) 1,?_⟩
  intro n hn Allowed hAllowed hValid D G F hG hEven hdegree hF hFAllowed classify fibres cutoff small removed remaining cf D0 fibres0 C k e m ρ eF Fc hOrdPrep hPrep
  have hn0:0<n:=by omega
  let v:Fin n:=⟨0,hn0⟩
  have hDn:D≤n:=by
    have hh:=Finset.card_le_univ (G.neighborFinset v)
    simpa only [SimpleGraph.card_neighborFinset_eq_degree,hG v,Fintype.card_fin] using hh
  have hhalf:1/2≤allowedThreshold Allowed:=allowedThreshold_half_le hAllowed hValid
  let removedOld:Finset (Fin (D/2)):=Finset.univ.filter (fun w=>
      (((Finset.univ.filter (fun v=>classify v=classify w)).card):ℝ)<
        (if classify w=none then κL*(n:ℝ) else κS*(n:ℝ)))
  have hRem:removedOld=removed:=by
    simpa only [removedOld,removed,small,fibres,cutoff] using
      (pruned_cutoff_removed_sets_equal K classify κL κS (n:ℝ))
  apply hRemove n (by omega) Allowed hAllowed hValid D G F hG hEven hdegree hF hFAllowed κL κS hL0.le hS0.le hL hS
  · intro P d hp he hd w hw hshort
    have hwOld:w∈removedOld:=by
      simpa only [classify,fibres,small,cutoff,removedOld,ite_mul] using hw
    have hw':w∈removed:=by simpa only [hRem] using hwOld
    have hshort':classify w≠none:=by simpa only [classify] using hshort
    obtain ⟨Iord,ξord,Bord,hξord,hProbOrd⟩:=hOrdPrep P d hp he hd w hw' hshort'
    have hδ:0≤allowedThreshold Allowed:=allowedThreshold_nonneg hAllowed
    have hnR:0<(n:ℝ):=by exact_mod_cast hn0
    have hbound:0<(allowedThreshold Allowed+α/2)*(n:ℝ):=mul_pos (by linarith) hnR
    have hdpos:0<d:=by exact_mod_cast (lt_of_lt_of_le hbound hd)
    exact protected_preparation_density_one_probability_copy P (F w) hdpos he hp (hF w) Iord ξord hξord Bord hProbOrd
  · intro R hR hRG hmargin
    have hR':R.IsRegularOfDegree D0:=by
      change R.IsRegularOfDegree (D-2*removedOld.card) at hR
      rw [hRem] at hR
      exact hR
    have hm':(allowedThreshold Allowed+α/2)*(n:ℝ)≤(D0:ℝ):=by
      change (allowedThreshold Allowed+α/2)*(n:ℝ)≤((D-2*removedOld.card:ℕ):ℝ) at hmargin
      rw [hRem] at hmargin
      exact hmargin
    obtain ⟨I,Ba,err,hI,hB,hbudget,hProb⟩:=hPrep R hR' hRG hm'
    obtain ⟨hρ,htotal,hPrepared⟩:=hPart (W:=Fin (D/2)) (n:=n) (by omega) hn0 classify D hEven (by simp) hDn
      (allowedThreshold Allowed) hhalf hdegree R hR' I hI F
    obtain ⟨c,hclasses,hdec⟩:=hPrepared Ba err hB (hProb hρ htotal) hbudget
    have hFinEq:allClassesPreparationArbitraryFin (D/2)=instDecidableEqFin (D/2):=Subsingleton.elim _ _
    rw [←hFinEq]
    change HasFactorDecomposition R (fun j:Fin (Fintype.card {i:Fin (D/2) // i∉removedOld})=>
      F ((Fintype.equivFin {i:Fin (D/2) // i∉removedOld}).symm j).val)
    rw [hRem]
    exact hdec
end Oberwolfach
