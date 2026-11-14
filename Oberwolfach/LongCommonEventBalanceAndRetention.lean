module

public import Oberwolfach.LongMatchingExactEncodedReservedActualChangeRates

@[expose] public section
/-! Extract the full restricted balance and the retained row and column
changes from the same common event, before choosing the corrected matching. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance commonBalanceRetentionFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_common_event_balance_and_retention
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (G:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r K h DQ mm:ℕ)
    (hh:1≤h) (β εQ:ℝ) (Q:Vortex U G DQ β εQ mm)
    (hpres:∀i v,π v∈Q.extendedVertices i↔v∈Q.extendedVertices i)
    (L sizeCommon aCommon bCommon eCommon aRob bRob eRob fCommon:ℕ)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (θ ρHost:ℝ) (hρHost:0<ρHost) (hsizeHost:ρHost*DQ=2*Fintype.card U)
    (βCommonEvent βCommonRef εAbsEvent εRobEvent ζRobEvent εRefEvent δRefEvent γRich tstarEvent ζEvent
      εBalEvent ζBalEvent εNbrEvent ζNbrEvent BloadEvent εLoadEvent ζLoadEvent ζLocalEvent ζConfigEvent
      ρ₀Event sstarEvent kstarEvent τLevelEvent ηBalance:ℝ)
    (hγRich:0≤γRich)
    (levelWeight:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
    (z:MarkedExpandedActualOutcome (U:=U) π d)
    (hCommon:LongMatchingCommonEvent G π DQ mm β εQ Q hpres r K d sizeCommon aCommon bCommon eCommon aRob bRob eRob fCommon L h
      F hF θ ρHost βCommonEvent βCommonRef εAbsEvent εRobEvent ζRobEvent εRefEvent δRefEvent γRich tstarEvent ζEvent
      εBalEvent ζBalEvent εNbrEvent ζNbrEvent BloadEvent εLoadEvent ζLoadEvent ζLocalEvent ζConfigEvent
      ρ₀Event sstarEvent kstarEvent τLevelEvent levelWeight (markedExpandedActualSelected π d z))
    (κaux κref ζret:ℝ) (hηBalance:0<ηBalance) (hκaux:0<κaux) (hκref:0≤κref) (hκrefCap:κref≤κaux)
    (hεRefEq:εRefEvent=κref/4) (hεNbr0:0≤εNbrEvent) (hεNbrCap:εNbrEvent≤κaux)
    (hκauxCap:κaux≤ηBalance/(8*((((r+4):ℕ):ℝ)+1))) (hUcard:Fintype.card U≤n)
    (hκauxRet:κaux≤ζret):
    let σ:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (z.1 e)
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (z.1 e)
    let t:=startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)
    let H:=retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t z.2 false false;
    MarkedRestrictedBalanceWithSpokes G π d (r+4) Finset.univ Finset.univ (ηBalance*n) σ H ∧
    (∀v,((Finset.univ.filter (fun w=>¬(H false v w↔rawMarkedPairSpokes π d raw false false false v w))).card:ℝ)≤ζret*n) ∧
    (∀w,((Finset.univ.filter (fun v=>¬(H false v w↔rawMarkedPairSpokes π d raw false false false v w))).card:ℝ)≤ζret*n) :=by
  intro σ raw t H
  obtain ⟨_,_,hGlobalBudget⟩:=marked_common_selector_global_balance_budget r ηBalance κaux κref εRefEvent εNbrEvent
    hηBalance hκaux hκref hκrefCap hεRefEq hεNbr0 hεNbrCap hκauxCap
  obtain ⟨hCommonBudget,hCommonMarked,hCommonColumn⟩:=hGlobalBudget n U hUcard
  have hn:1≤n:=by
    have hh':0<Fintype.card (Fin n):=Fintype.card_pos
    simp only [Fintype.card_fin] at hh'
    omega
  have hbal:=marked_long_common_agreement_full_restricted_balance hn G π DQ mm β εQ Q hpres
    r K d sizeCommon aCommon bCommon eCommon aRob bRob eRob fCommon L h hh F hF θ ρHost hρHost hsizeHost
    βCommonEvent βCommonRef εAbsEvent εRobEvent ζRobEvent εRefEvent δRefEvent γRich tstarEvent ζEvent εBalEvent ζBalEvent εNbrEvent ζNbrEvent BloadEvent εLoadEvent ζLoadEvent ζLocalEvent ζConfigEvent ρ₀Event sstarEvent kstarEvent τLevelEvent ηBalance
    hγRich levelWeight (markedExpandedActualSelected π d z) hCommon hCommonBudget hCommonMarked hCommonColumn
  obtain ⟨hLossRow,hLossCol⟩:=marked_common_retained_spoke_budget h εNbrEvent ζret hεNbr0 (hεNbrCap.trans hκauxRet) n U hUcard
  have hspokeBounds:=long_matching_common_event_retained_spoke_bounds G π DQ mm β εQ Q hpres
    r K d sizeCommon aCommon bCommon eCommon aRob bRob eRob fCommon L h F hF θ ρHost
    βCommonEvent βCommonRef εAbsEvent εRobEvent ζRobEvent εRefEvent δRefEvent γRich tstarEvent ζEvent
    εBalEvent ζBalEvent εNbrEvent ζNbrEvent BloadEvent εLoadEvent ζLoadEvent ζLocalEvent ζConfigEvent
    ρ₀Event sstarEvent kstarEvent τLevelEvent levelWeight (markedExpandedActualSelected π d z) hCommon
  refine ⟨?_,?_,?_⟩
  · dsimp only [σ,raw,t,H,markedExpandedActualSelected,rawExpandedApproximateCollapse,rawExpandedMarkedCollapse] at hbal ⊢
    convert hbal using 1 <;> congr! 8 <;> first | rfl | exact Subsingleton.elim _ _
  · intro v
    have hh':=(hspokeBounds.1 v).trans hLossRow
    dsimp only [H,t,raw,σ,markedExpandedActualSelected,rawMarkedPairSpokes,rawExpandedApproximateCollapse,rawExpandedMarkedCollapse] at hh' ⊢
    convert hh' using 1 <;> congr! 8 <;> first | rfl | exact Subsingleton.elim _ _
  · intro w
    have hh':=(hspokeBounds.2 w).trans (by simpa only [Fintype.card_fin] using hLossCol)
    dsimp only [H,t,raw,σ,markedExpandedActualSelected,rawMarkedPairSpokes,rawExpandedApproximateCollapse,rawExpandedMarkedCollapse] at hh' ⊢
    convert hh' using 1 <;> congr! 8 <;> first | rfl | exact Subsingleton.elim _ _
end Oberwolfach
