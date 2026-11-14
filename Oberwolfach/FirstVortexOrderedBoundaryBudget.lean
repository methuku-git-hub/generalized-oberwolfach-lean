module

public import Oberwolfach.FirstVortexOrderedPreciseRetentionBudget
public import Oberwolfach.FirstVortexClassEditCapForSelector

@[expose] public section
/-! Ordered quantitative choices for the boundary-based all-hub route.
The global loss is fixed before the vortex parameter; the later class edit
cap simultaneously supplies both local and precise degree margins. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
local instance orderedBoundaryBudgetDecEq {V:Type}:DecidableEq V:=orderedPreciseRetentionBudgetDecEq

theorem first_vortex_ordered_boundary_parameters_budget
    (a α C₀ εupper δglobal:ℝ) (m:ℕ)
    (ha:0<a) (hα:0<α) (hC:0<C₀) (hupper:0<εupper)
    (hglobal:0<δglobal) (hglobal1:δglobal≤1) (hm:0<m):
    ∃δold δlocal ε:ℝ,0<δold ∧ δold<δlocal ∧ δold≤1 ∧
      0<ε ∧ ε≤εupper ∧ ε≤δglobal ∧ ε≤1/4 ∧ ε≤a/8192 ∧ ε≤α/(1000*C₀) ∧
    ∀cap θupper:ℝ,0<cap→0<θupper→
    ∃θmax:ℝ,0<θmax ∧ θmax≤θupper ∧ θmax≤1/100 ∧
      10*θmax≤δold ∧ θmax≤δold/32 ∧ 10*θmax≤δglobal ∧
    ∀θ:ℝ,0<θ→θ≤θmax→∀dmin:ℕ,
    ∃d:ℕ,dmin≤d ∧ 3≤d ∧ 1/(d:ℝ)≤θ/1024 ∧
    ∃ζglobal ζlocal:ℝ,0<ζglobal ∧ 0<ζlocal ∧ ζglobal≤θ/4096 ∧ ζlocal≤cap/128 ∧ ζglobal≤ζlocal*ε/2 ∧ ζglobal≤min cap (1:ℝ)/1024 ∧
      (∃Nret:ℕ,∀n:ℕ,Nret≤n→∀q errOrd:ℝ,
        q≤1/((m:ℝ)+1)→errOrd≤θ*n→
        (n:ℝ)*q/d+(((m+1)*d-1:ℕ):ℝ)*(2*((n:ℝ)^(3/4:ℝ)/d)+ζglobal*n)+errOrd≤4*θ*n) ∧
      (∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
        [LinearOrder V] [DecidableEq U],
       ∀(G:SimpleGraph V) (D mm:ℕ) (β:ℝ) (Q:Vortex U G D β ε mm) (hmm:0<mm)
        (π:Equiv.Perm V) (σ:RawIntervalFamilyOutcome V U Γ Color) (g:Γ) (t:ℕ)
        (J:StartRetentionOutcome (rawStartHubSet π d σ g) t),
       RetainedRestrictionGood π d σ g t (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζglobal J→
       RetainedRestrictionLocalGood π d σ g t (Q.extendedVertices 1) Finset.univ ζlocal J) ∧
    ∀upper:ℝ,0<upper→
    ∃lamBase lamAssign ξCap:ℝ,
      0<lamBase ∧ 0<lamAssign ∧ lamBase≤lamAssign ∧ lamAssign≤upper ∧
      lamAssign≤1 ∧ lamAssign≤θ ∧ lamAssign≤α/128 ∧ lamAssign≤cap*a/4096 ∧
      lamBase≤δold*ε/32 ∧ 0<ξCap ∧
      (∀ξ:ℝ,ξ≤ξCap→lamBase+ξ≤a*θ/4096 ∧ ξ/2≤(lamAssign-lamBase)*ε ∧ ξ≤α/32 ∧
        ∀n:ℕ,∀(U:Type) [Fintype U] (G:SimpleGraph (Fin n))
          (D mm:ℕ) (β:ℝ) (Q:Vortex U G D β ε mm),0<mm→
          ξ*n≤(δlocal-δold)*((Q.extendedVertices 1).card:ℝ)) ∧
      ∃N:ℕ,∀n:ℕ,N≤n→0<n→∀(a' γ:ℝ),max a' γ≤1/(10*(d:ℝ))→
        2*((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/(d:ℝ)+2*max a' γ*n≤cap*(ε*n)/128 ∧
        ∀E:ℕ,(E:ℝ)≤(θ*ε^2+lamAssign*ε)*(n:ℝ)^2+24*d*n→
          2*(⌈4*(E:ℝ)/(a*n)⌉₊:ℕ)≤cap*(ε*n)/128 :=by
  let δold:ℝ:=δglobal/4
  let δlocal:ℝ:=δglobal/2
  have hold:0<δold:=by dsimp [δold]; positivity
  have hgap:δold<δlocal:=by dsimp [δold,δlocal]; linarith
  have hold1:δold≤1:=by dsimp [δold]; linarith
  obtain ⟨ε,hε,hεup,hεquarter,hεa,hεα,hChoice⟩:=
    first_vortex_ordered_precise_retention_parameters_budget a α C₀ (min εupper δglobal) m ha hα hC (by positivity) hm
  refine ⟨δold,δlocal,ε,hold,hgap,hold1,hε,hεup.trans (min_le_left _ _),hεup.trans (min_le_right _ _),hεquarter,hεa,hεα,?_⟩
  intro cap θupper hcap hθupper
  obtain ⟨θmax,hθmax,hθup,hθsmall,hθ⟩:=
    hChoice cap (min θupper (δglobal/128)) hcap (by positivity)
  have hθg:θmax≤δglobal/128:=hθup.trans (min_le_right _ _)
  refine ⟨θmax,hθmax,hθup.trans (min_le_left _ _),hθsmall,?_,?_,?_,?_⟩
  · dsimp [δold]; linarith
  · dsimp [δold]; linarith
  · linarith
  intro θ hθ0 hθmax' dmin
  obtain ⟨d,hdmin,hd,hspacing,ζglobal,ζlocal,hζglobal,hζlocal,hζθ,hζcap,hscale,hbudget,hNret,hRet,hRates⟩:=hθ θ hθ0 hθmax' dmin
  refine ⟨d,hdmin,hd,hspacing,ζglobal,ζlocal,hζglobal,hζlocal,hζθ,hζcap,hscale,hbudget,hNret,hRet,?_⟩
  intro upper hupper'
  obtain ⟨lamBase,lamAssign,ξold,hbase,hassign,hba,haUpper,ha1,haθ,haα,hacap,hξold,hξbounds,hN⟩:=
    hRates (min upper (δold*ε/32)) (by positivity)
  obtain ⟨ξcap,hξcap,hξoldcap,hξmargin⟩:=
    first_vortex_class_edit_cap_for_selector α ε δold δlocal ξold hα hε hgap hξold
  refine ⟨lamBase,lamAssign,ξcap,hbase,hassign,hba,haUpper.trans (min_le_left _ _),ha1,haθ,haα,hacap,?_,hξcap,?_,hN⟩
  · exact hba.trans (haUpper.trans (min_le_right _ _))
  · intro ξ hξ
    obtain ⟨hsmall,hedge⟩:=hξbounds ξ (hξ.trans hξoldcap)
    obtain ⟨hdegree,hload⟩:=hξmargin ξ hξ
    exact ⟨hsmall,hedge,hdegree,hload⟩
end Oberwolfach
