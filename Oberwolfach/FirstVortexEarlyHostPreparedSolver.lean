module

public import Oberwolfach.FirstVortexEarlyHostPreparedCap
public import Oberwolfach.LongBoundaryPreparedSolverFromConcreteEvent

@[expose] public section
/-! The early host hierarchy supplies the uniform concrete boundary solver,
without moving the event-dependent parameter choices earlier. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 80000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance earlyPreparedSolverFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_early_host_parameters_with_prepared_solver
    (r:ℕ) (γList pstar ρ₀ βFinalCap:ℝ) (hγ:0<γList) (hp:0<pstar) (hρ:0<ρ₀) (hCap:0<βFinalCap) (hρhi:ρ₀≤1) (hm:7≤r+4):
    ∃βlist lamList ζList βfinal δglobal δold δlocal θ bmatch:ℝ,
      0<βlist ∧ βlist≤1 ∧ 0<lamList ∧ lamList≤1/100 ∧ 0<ζList ∧
      0<βfinal ∧ βfinal≤lamList/4 ∧ βfinal≤1 ∧ βfinal≤βFinalCap ∧
      0<δglobal ∧ δglobal≤(βfinal/200)^2 ∧ δglobal≤(βfinal/100)^2 ∧ δglobal≤1/100 ∧
      0<δold ∧ δold≤1 ∧ δold<δlocal ∧ 0<θ ∧ θ≤1/100 ∧ 10*θ≤δold ∧ θ≤δold/32 ∧ 10*θ≤δglobal ∧
      0<bmatch ∧ bmatch≤((ρ₀/4)/40000)/16 ∧
      ∃d K:ℕ, 3≤d ∧ (r+4)+2≤d ∧ 3≤K ∧
        1/(d:ℝ)≤θ/1024 ∧ (1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ ∧
        5/(((((r+4):ℕ):ℝ)+1)*(d:ℝ)+5)+((((r+4):ℕ):ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2 ∧
      ∃ζret:ℝ,0<ζret ∧ ζret≤θ/4096 ∧ ∃Nret Nlist:ℕ,
        (∀n:ℕ,Nret≤n→∀q errOrd:ℝ,
          q≤1/((((r+4):ℕ):ℝ)+1)→errOrd≤θ*n→
          (n:ℝ)*q/d+(((((r+4)+1)*d-1:ℕ):ℝ))*(2*((n:ℝ)^(3/4:ℝ)/d)+ζret*n)+errOrd≤4*θ*n) ∧
        (∀n≥Nlist,
          (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γList*pstar^2*n ∧
          βlist*n+(n:ℝ)^(3/4:ℝ)≤γList*pstar^2*n*(1/100:ℝ) ∧
          (lamList+2*ζList)*n≤βlist*n) ∧
      ∀C₀ εAbs εOther ξUpper:ℝ,1≤C₀→0<εAbs→0<εOther→0<ξUpper→∃αMatch εQ lam lamAssign ξCap:ℝ,
        0<αMatch ∧ (2*αMatch)/16≤bmatch ∧
        (2*αMatch)/16≤((ρ₀/4)/40000)*θ/1024 ∧ 2*αMatch≤4*δglobal ∧
        0<εQ ∧ εQ≤εAbs ∧ εQ≤εOther ∧ εQ<1/4 ∧ εQ≤δglobal ∧ βfinal+εQ≤lamList ∧
        εQ≤αMatch/(1000*C₀) ∧ εQ≤αMatch/1000 ∧ εQ≤(ρ₀/4)/80000 ∧ εQ≤((ρ₀/4)/40000)/8192 ∧
        0<lam ∧ lam≤θ ∧ lam≤αMatch/128 ∧ lam≤δold*εQ/32 ∧ lam<lamAssign ∧
        0<ξCap ∧ ξCap≤ξUpper ∧
        (∀ξ':ℝ,ξ'≤ξCap→lam+ξ'≤((ρ₀/4)/40000)*θ/4096 ∧
          ξ'/2≤(lamAssign-lam)*εQ ∧ ξ'≤αMatch/32 ∧
          ∀n:ℕ,∀(U:Type) [Fintype U] (G:SimpleGraph (Fin n)) (D mm:ℕ) (β:ℝ)
            (Q:Vortex U G D β εQ mm),0<mm→ξ'*n≤(δlocal-δold)*((Q.extendedVertices 1).card:ℝ)) ∧
        ∀(eps ξPrep ξPart:ℝ),0<eps→3*eps≤lam*(θ/(100*(K:ℝ)^2))→
          4*ξPrep≤eps/2→0≤ξPrep→ξPart≤ξCap→
    ∃N:ℕ,∀n:ℕ,N≤n→∀ [Nonempty (Fin n)] (U:Type) [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (Dv mm:ℕ) (β:ℝ) (Vort:Vortex U P Dv β εQ mm)
    (hreg:P.IsRegularOfDegree Dv) (hDv:0<Dv) (hρhi:initialIndexDensity U Dv≤1)
    (hρlo:ρ₀ ≤ initialIndexDensity U Dv) (hDlo:(n:ℝ)/2≤Dv) (hDhi:(Dv:ℝ)≤2*n) (hmm:0<mm)
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (hclass:∀u,factorPreparationClass (F u) K=none)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (a γ ρ Δ ξSeed ΔSeed:ℝ)
    (haEq:a=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2)))
    (hγEq:γ=min (eps/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10))))
    (hρEq:ρ=θ/4096) (hΔeps:Δ≤eps/8)
    (hξSeed:ξSeed≤ξPrep) (hΔSeed:Δ≤ΔSeed) (heps1:eps≤1)
    (τ Asrc BM:ℝ) (hBM:0<BM) (weight:(Fin ((r+4)+1)→Fin n)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π (3*d) Dv τ Asrc BM weight)
    (BO:Fin K→ℝ) (hBO:∀i,0<BO i)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ) (hw0:∀i C,0≤w i C)
    (hwupper:∀i C,w i C≤BO i/(n:ℝ)^(longPaddedSeedExponent i))
    (ζselect:ℝ) (hζselect:ζselect≤ζret) (Inner:Finset (Fin n)) (βList:ℝ)
    (terr τerr:ℝ) (hτerr:0≤τerr) (γLoss σLoss:ℝ),
    ∀z:MarkedExpandedActualOutcome (U:=U) π d,
    FirstVortexConcreteBoundaryEvent P π d r Dv mm β εQ Vort θ ρ₀ BM BO F hF weight w
      a γ eps Δ ξSeed ΔSeed ζret ζselect βList terr τerr z Inner →
    ∀(D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
      (CReserve:Finset (Finset (Fin n)⊕(Fin n×U))),
    LongEveryClassMatchingResult Δ P π d r γLoss σLoss ξPart z (Vort.extendedVertices 1) K θ Dv a γ eps βList F hF weight w D₀ CReserve →
    LongBoundaryPreparedClasses P π d r Dv mm β εQ Vort z θ a γ eps βList ξPart Δ
      lamAssign δlocal δglobal αMatch bmatch ρ₀ ξPrep F hF weight w D₀ CReserve :=by
  obtain ⟨βlist,lamList,ζList,βfinal,δglobal,δold,δlocal,θ,bmatch,
    hβ,hβ1,hlamList,hlamList1,hζ,hβfinal,hβbound,hβfinal1,hβcap,hδglobal,hδstrong,hδbound,hδglobal1,
    hδold,hδold1,hgap,hθ,hθhi,hθδ,hθlocal,hθglobal,hbmatch,hbd,
    d,K,hd,hdlarge,hK,hspacing,hcut,hcutHost,ζret,hζret,hζretBound,Nret,Nlist,hNret,hNlist,hchoose⟩:=
    first_vortex_early_host_parameters_with_prepared_cap r γList pstar ρ₀ βFinalCap hγ hp hρ hCap
  refine ⟨βlist,lamList,ζList,βfinal,δglobal,δold,δlocal,θ,bmatch,
    hβ,hβ1,hlamList,hlamList1,hζ,hβfinal,hβbound,hβfinal1,hβcap,hδglobal,hδstrong,hδbound,hδglobal1,
    hδold,hδold1,hgap,hθ,hθhi,hθδ,hθlocal,hθglobal,hbmatch,hbd,
    d,K,hd,hdlarge,hK,hspacing,hcut,hcutHost,ζret,hζret,hζretBound,Nret,Nlist,hNret,hNlist,?_⟩
  intro C₀ εAbs εOther ξUpper hC hAbs hOther hξUpper
  obtain ⟨αMatch,εQ,lam,lamAssign,ξCap,hα,hαb,hαsmall,hαglobal,hε,hεAbs,hεOther,hεsmall,hεδ,htrim,
    hεα,hεαsimple,hεsmallρ,hεprecise,hlam,hlamθ,hlamα,hlamδ,hAssign,hξCap,hξUpperCap,hClassCap⟩:=
    hchoose C₀ εAbs εOther ξUpper hC hAbs hOther hξUpper
  refine ⟨αMatch,εQ,lam,lamAssign,ξCap,hα,hαb,hαsmall,hαglobal,hε,hεAbs,hεOther,hεsmall,hεδ,htrim,
    hεα,hεαsimple,hεsmallρ,hεprecise,hlam,hlamθ,hlamα,hlamδ,hAssign,hξCap,hξUpperCap,hClassCap,?_⟩
  intro eps ξPrep ξPart heps hepsRate hξ hξ0 hξPart
  obtain ⟨N,hN⟩:=long_boundary_prepared_solver_from_concrete_event αMatch lam lamAssign εQ δold δlocal δglobal θ eps ξPrep ρ₀ bmatch ξPart ζret d K r
    hα hlam hε hδold hδold1 hθ heps hρ hbmatch hαb hbd hεsmallρ hθδ hθlocal hθhi hlamδ hspacing hd hK hm hepsRate hξ hξ0
    hρhi hδglobal hθglobal hεprecise ξCap hξPart hClassCap hlamθ hdlarge Nret hNret
  refine ⟨N,?_⟩
  intro n hn _ U _ _ P π Dv mm β Vort hreg hDv hρhiHost hρlo hDlo hDhi hmm F hF Allowed hAllowed hclass hnoshort
    a γ ρ Δ ξSeed ΔSeed haEq hγEq hρEq hΔeps hξSeed hΔSeed heps1 τ Asrc BM hBM weight hw BO hBO w hw0 hwupper
    ζselect hζselect Inner βList terr τerr hτerr γLoss σLoss
  have hN':=hN n hn
  have hdec:longPreparedSolverFin n=earlyPreparedSolverFin n:=Subsingleton.elim _ _
  have hdecK:longPreparedSolverFin K=earlyPreparedSolverFin K:=Subsingleton.elim _ _
  try rw [hdec] at hN'
  try rw [hdecK] at hN'
  have hcut':(1/(((r+4):ℝ)+1))/(d:ℝ)≤θ:=by simpa only [Nat.cast_add,Nat.cast_ofNat] using hcut
  have hcutHost':5/((((r+4):ℝ)+1)*(d:ℝ)+5)+(((r+4):ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2:=by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hcutHost
  exact hN' U P π Dv mm β Vort hreg hDv hρhiHost hρlo hDlo hDhi hmm F hF Allowed hAllowed hclass hcut' hcutHost' hnoshort
    hεαsimple hlamα a γ ρ Δ ξSeed ΔSeed haEq hγEq hρEq hΔeps hξSeed hΔSeed heps1 hζretBound hζret.le τ Asrc BM hBM weight hw BO hBO w hw0 hwupper
    ζselect hζselect Inner βList terr τerr hτerr γLoss σLoss
end Oberwolfach
