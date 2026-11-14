module

public import Mathlib.Tactic

@[expose] public section
/-! Choose the remaining local scales below any earlier positive caps; these
    are auxiliary choices, not additional host assumptions. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_prepared_local_choices_with_global_bound
    (ρ₀ δglobal εInner αUpper εUpper:ℝ)
    (hρ:0<ρ₀) (hδ:0<δglobal) (hInner:0<εInner) (hαUpper:0<αUpper) (hεUpper:0<εUpper):
    ∃α ε δold δlocal bmatch:ℝ,
      0<α ∧ α≤αUpper ∧ 0<ε ∧ ε<1/4 ∧ ε≤εInner ∧ ε≤εUpper ∧
      0<δold ∧ δold≤1 ∧ δold≤δglobal ∧ δold<δlocal ∧ δlocal=2*δold ∧ δlocal≤δglobal ∧
      0<bmatch ∧ (2*α)/16≤bmatch ∧ bmatch≤((ρ₀/4)/40000)/16 ∧
      ε≤(ρ₀/4)/80000 ∧ ε≤((ρ₀/4)/40000)/8192 ∧ ε≤α/100000 ∧ ε≤α/1000 :=by
  let bound:ℝ:=((ρ₀/4)/40000)/16
  let bmatch:ℝ:=bound/2
  let α:ℝ:=min αUpper (4*bmatch)
  let δold:ℝ:=min (δglobal/2) (1/2:ℝ)
  let δlocal:ℝ:=2*δold
  let precise:ℝ:=((ρ₀/4)/40000)/8192
  let ε:ℝ:=min (1/8:ℝ) (min εInner (min εUpper (min ((ρ₀/4)/160000) (min (precise/2) (α/200000)))))
  have hbound:0<bound:=by dsimp [bound];positivity
  have hb:0<bmatch:=by dsimp [bmatch];positivity
  have hα:0<α:=by dsimp [α];positivity
  have hαCap:α≤αUpper:=min_le_left _ _
  have hαb:α≤4*bmatch:=min_le_right _ _
  have hδold:0<δold:=by dsimp [δold];positivity
  have hδoldOne:δold≤1:=by
    have h:=min_le_right (δglobal/2) (1/2:ℝ)
    dsimp [δold];linarith
  have hδoldGlobal:δold≤δglobal:=by
    have h:=min_le_left (δglobal/2) (1/2:ℝ)
    dsimp [δold];linarith
  have hgap:δold<δlocal:=by dsimp [δlocal];linarith
  have hlocalGlobal:δlocal≤δglobal:=by
    have hh:=min_le_left (δglobal/2) (1/2:ℝ)
    dsimp [δlocal,δold]
    linarith
  have hprecise:0<precise:=by dsimp [precise];positivity
  have hε:0<ε:=by dsimp [ε];positivity
  have hεquarter:ε<1/4:=by
    have h:=min_le_left (1/8:ℝ) (min εInner (min εUpper (min ((ρ₀/4)/160000) (min (precise/2) (α/200000)))))
    dsimp [ε];linarith
  have hεInner:ε≤εInner:=(min_le_right _ _).trans (min_le_left _ _)
  have hεUpper:ε≤εUpper:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hερ:ε≤(ρ₀/4)/80000:=by
    have h:ε≤(ρ₀/4)/160000:=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    linarith
  have hεprecise:ε≤((ρ₀/4)/40000)/8192:=by
    have h:ε≤precise/2:=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
    dsimp [precise] at *
    linarith
  have hεαstrong:ε≤α/100000:=by
    have h:ε≤α/200000:=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
    linarith
  have hεα:ε≤α/1000:=by linarith
  refine ⟨α,ε,δold,δlocal,bmatch,hα,hαCap,hε,hεquarter,hεInner,hεUpper,hδold,hδoldOne,hδoldGlobal,hgap,rfl,hlocalGlobal,hb,?_,?_,hερ,hεprecise,hεαstrong,hεα⟩
  · linarith
  · dsimp [bmatch,bound];linarith
end Oberwolfach
