module

public import Oberwolfach.LongCommonEventBalanceAndRetention
public import Oberwolfach.FiniteLawIntersectionLower

@[expose] public section
/-! Lift the existing pointwise balance and retention conclusion to the
same high-probability sample event, without selecting a new outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longCommonProbabilityFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

def LongCommonBalanceRetentionEvent {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (G:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r:ℕ) (ηBalance ζret:ℝ)
    (z:MarkedExpandedActualOutcome (U:=U) π d):Prop :=
  let σ:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (z.1 e)
  let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (z.1 e)
  let t:=startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)
  let H:=retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t z.2 false false;
  MarkedRestrictedBalanceWithSpokes G π d (r+4) Finset.univ Finset.univ (ηBalance*n) σ H ∧
  (∀v,((Finset.univ.filter (fun w=>¬(H false v w↔rawMarkedPairSpokes π d raw false false false v w))).card:ℝ)≤ζret*n) ∧
  (∀w,((Finset.univ.filter (fun v=>¬(H false v w↔rawMarkedPairSpokes π d raw false false false v w))).card:ℝ)≤ζret*n)

theorem long_common_balance_retention_probability
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
    (κaux κref ζret:ℝ) (hηBalance:0<ηBalance) (hκaux:0<κaux) (hκref:0≤κref) (hκrefCap:κref≤κaux)
    (hεRefEq:εRefEvent=κref/4) (hεNbr0:0≤εNbrEvent) (hεNbrCap:εNbrEvent≤κaux)
    (hκauxCap:κaux≤ηBalance/(8*((((r+4):ℕ):ℝ)+1))) (hUcard:Fintype.card U≤n)
    (hκauxRet:κaux≤ζret)
    (μ:FiniteLaw (MarkedExpandedActualOutcome (U:=U) π d))
    (E:MarkedExpandedActualOutcome (U:=U) π d→Prop) (b:ℝ)
    (hE:b≤μ.probability E)
    (hCommon:∀z,E z→LongMatchingCommonEvent G π DQ mm β εQ Q hpres r K d sizeCommon aCommon bCommon eCommon aRob bRob eRob fCommon L h
      F hF θ ρHost βCommonEvent βCommonRef εAbsEvent εRobEvent ζRobEvent εRefEvent δRefEvent γRich tstarEvent ζEvent
      εBalEvent ζBalEvent εNbrEvent ζNbrEvent BloadEvent εLoadEvent ζLoadEvent ζLocalEvent ζConfigEvent
      ρ₀Event sstarEvent kstarEvent τLevelEvent levelWeight (markedExpandedActualSelected π d z)):
    b≤μ.probability (fun z=>E z ∧ LongCommonBalanceRetentionEvent G π d r ηBalance ζret z) :=by
  apply hE.trans
  apply finiteLaw_probability_mono
  intro z hz
  refine ⟨hz,?_⟩
  exact long_common_event_balance_and_retention G π d r K h DQ mm hh β εQ Q hpres L sizeCommon aCommon bCommon eCommon aRob bRob eRob fCommon F hF θ ρHost hρHost hsizeHost
    βCommonEvent βCommonRef εAbsEvent εRobEvent ζRobEvent εRefEvent δRefEvent γRich tstarEvent ζEvent εBalEvent ζBalEvent εNbrEvent ζNbrEvent BloadEvent εLoadEvent ζLoadEvent ζLocalEvent ζConfigEvent ρ₀Event sstarEvent kstarEvent τLevelEvent ηBalance
    hγRich levelWeight z (hCommon z hz) κaux κref ζret hηBalance hκaux hκref hκrefCap hεRefEq hεNbr0 hεNbrCap hκauxCap hUcard hκauxRet
end Oberwolfach
