module

public import Oberwolfach.RawOrdinaryNamedSeedActiveTargets
public import Oberwolfach.LongRawHubContext
public import Oberwolfach.LongAssignedSeedFunctionBounds
public import Oberwolfach.LongAssignedSeedTargets

@[expose] public section
/-! The original ordinary assigned seed supplies its active-root target,
conditional on the original fractional-cycle equations and error budgets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_assigned_ordinary_named_seed_active_targets
    (hn:0<n) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (K m d:ℕ) (hd:2≤d) (θ D k:ℝ) (hθ0:0≤θ) (hθ1:θ≤1) (hD:0<D)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (ni:Fin K→ℕ) (hni:∀i,1≤ni i)
    (w:∀i,OrdinaryCycle P (ni i+2)→ℝ) (i:Fin K) (B τ ε t:ℝ) (hB:0≤B)
    (hw:∀C,0≤w i C) (hb:∀C,w i C≤B/(n:ℝ)^(ni i))
    (he:∀x y,(∑C,if C.val.val.Adj x y then w i C else 0)=if P.Adj x y then 1 else 0)
    (hdeg:∀x,|(P.degree x:ℝ)-D|≤ε*n)
    (hbudgetV:6*((ni i+2:ℕ):ℝ)^4*B*(2*(3*d))+ε*n≤τ*D)
    (hbudgetE:5*((ni i+2:ℕ):ℝ)^4*B*(2*(3*d))/n≤τ)
    (hk:0≤k) (hpos:∀u,0<longAssignedApproxOrdinaryWeight F hF K m θ u)
    (hp:0<(∑u,longAssignedApproxOrdinaryWeight F hF K m θ u)/D)
    (hsum:2*((∑u,longAssignedApproxOrdinaryWeight F hF K m θ u)/D)+2*k≤1)
    (hq:∀u g,0≤longAssignedIntervalProbability F hF K m θ u g)
    (hQ:∀u,∑g,longAssignedIntervalProbability F hF K m θ u g≤1/8)
    (hs:∀u j,0≤longAssignedSpokeProbability F hF K m θ u j)
    (hS:∀u,∑j,longAssignedSpokeProbability F hF K m θ u j≤
      intervalUncoveredProbability d (∑g,longAssignedIntervalProbability F hF K m θ u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (σ:RawMarkedOutcome (Fin n) U Bool Bool):
    let p:=(∑u,longAssignedApproxOrdinaryWeight F hF K m θ u)/D
    let q:=longAssignedIntervalProbability F hF K m θ
    let s:=longAssignedSpokeProbability F hF K m θ
    let state:=longRawHubState P π d σ true true
    rawOrdinarySeedConcentrated P π d (ni i+2) p k q s true true t
      (longAssignedOrdinarySeed F hF K m d θ D P π ni hni w i) σ →
    ∀root,state (ordinaryMarkedResourceEmbedding root)=true→
      |resourcePatternLoad orderedOrdinaryResources (longAssignedOrdinarySeed F hF K m d θ D P π ni hni w i)
        (fun _ _=>true) root (fun x=>state (ordinaryMarkedResourceEmbedding x))-
        ordinarySeedRootTarget D p θ (longAssignedKeptFraction F hF K θ i)
          (fun u=>longAssignedKeptOrdinaryContribution F hF K θ i u/
            longAssignedApproxOrdinaryWeight F hF K m θ u) root|≤
        t+τ*ordinarySeedRootTarget D p θ (longAssignedKeptFraction F hF K θ i)
          (fun u=>longAssignedKeptOrdinaryContribution F hF K θ i u/
            longAssignedApproxOrdinaryWeight F hF K m θ u) root :=by
  intro p q s state hconc
  letI : Nonempty (Fin n):=⟨⟨0,hn⟩⟩
  have hspos:∀u,0<s u true:=by intro u;simpa [s,longAssignedSpokeProbability] using hpos u
  have hf:∀u,0≤longAssignedKeptFraction F hF K θ i u:=by
    intro u
    unfold longAssignedKeptFraction
    split_ifs with h
    · exact le_trans (by positivity) h
    · exact le_refl _
  have hη:∀u,0≤longAssignedKeptOrdinaryContribution F hF K θ i u/
      longAssignedApproxOrdinaryWeight F hF K m θ u:=by
    intro u
    rw [long_assigned_kept_fraction_contribution]
    exact div_nonneg (mul_nonneg (sub_nonneg.mpr hθ1) (hf u)) (hpos u).le
  have hηeq:∀u,longAssignedKeptOrdinaryContribution F hF K θ i u/
      longAssignedApproxOrdinaryWeight F hF K m θ u =
      (1-θ)*longAssignedKeptFraction F hF K θ i u/s u true:=by
    intro u
    rw [long_assigned_kept_fraction_contribution]
    rfl
  have hh:=raw_ordinary_named_seed_active_targets (V:=Fin n) (U:=U) P π d (ni i) hd (hni i)
  have hdec : (fun a b : Fin n => Classical.propDecidable (a=b)) = instDecidableEqFin n :=
    Subsingleton.elim _ _
  rw [hdec] at hh
  have hh:=hh p k hp hk hsum
    q hq hQ s hs hS hnoshort true true D τ ε θ B t hD hB hspos
    (fun u=>longAssignedKeptOrdinaryContribution F hF K θ i u/
      longAssignedApproxOrdinaryWeight F hF K m θ u)
    (longAssignedKeptFraction F hF K θ i) hη hηeq (w i) hw
    (by simpa only [Fintype.card_fin] using hb)
    he (by simpa only [Fintype.card_fin] using hdeg)
    (by simpa only [Fintype.card_fin] using hbudgetV)
    (by simpa only [Fintype.card_fin] using hbudgetE) σ
  have hseed:=hh hconc
  intro root hroot
  have h:=hseed root hroot
  dsimp only [state,longRawHubState,longAssignedOrdinarySeed,s,longAssignedSpokeProbability,p] at h ⊢
  convert h using 1 <;> congr 4 <;>
    first | rfl | exact Subsingleton.elim _ _ | (funext x; rfl)
end Oberwolfach
