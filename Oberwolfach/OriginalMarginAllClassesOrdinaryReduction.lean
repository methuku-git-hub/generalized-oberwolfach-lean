module

public import Oberwolfach.OriginalMarginAllClassesPreparationArbitraryCutoff
public import Oberwolfach.OrdinaryShortClassPreparationReduction

@[expose] public section
/-! Conditional fixed-set reduction: ordinary preparation discharges every
short removed class. Retained-class probability bounds remain explicit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance ordinaryAllClassesFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _
local instance (priority := 2000) ordinaryAllClassesSym2 (n:ℕ):DecidableEq (Sym2 (Fin n)):=@Sym2.instDecidableEq (Fin n) (instDecidableEqFin n)
local instance (priority := 2000) ordinaryAllClassesOption (k:ℕ):DecidableEq (Option (Fin k)):=@Option.instDecidableEq (Fin k) (instDecidableEqFin k)

theorem original_margin_all_classes_ordinary_reduction (hOrd:OrdinaryProtectedPreparation)
    (Allowed:Set ℕ) (hAllowed:Allowed.Nonempty) (hValid:∀s∈Allowed,3≤s)
    (α:ℝ) (hα:0<α) (KExtra:ℕ):
    ∃K:ℕ,KExtra≤K ∧ 3≤K ∧ ∀κL κS ξ:ℝ,0<κL→0<κS→0<ξ→
      κL≤α/1000→κS≤α/(1000*(K:ℝ))→∀B:ℕ,∃N:ℕ,
    ∀n≥N,∀(D:ℕ) (G:SimpleGraph (Fin n)) (F:Fin (D/2)→SimpleGraph (Fin n)),
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
  obtain ⟨K,hExtra,hK,hAll⟩:=original_margin_all_classes_preparation_arbitrary_cutoff α hα KExtra
  obtain ⟨Nord,hOrdShort⟩:=ordinary_short_class_preparation_reduction hOrd Allowed hAllowed hValid α hα K hK
  refine ⟨K,hExtra,hK,?_⟩
  intro κL κS ξ hL hS hξ hLcap hScap B
  obtain ⟨N,hN⟩:=hAll κL κS ξ hL hS hξ hLcap hScap B
  refine ⟨max N Nord,?_⟩
  intro n hn D G F hG hEven hdegree hF hFAllowed classify fibres cutoff small removed remaining cf D0 fibres0 C k e m ρ eF Fc hRetained
  apply hN n (by omega) Allowed hAllowed hValid D G F hG hEven hdegree hF hFAllowed
  · intro P d hP hdEven hd w hw hshort
    exact hOrdShort n (by omega) P (F w) d hP hdEven hd (hF w) (hFAllowed w) hshort
  · exact hRetained
end Oberwolfach
