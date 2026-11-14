module

public import Oberwolfach.FiniteLawAttachConditionalEvent
public import Oberwolfach.FiniteSigmaFirstMap

@[expose] public section
/-! Sequentially expose fresh finite randomness while retaining the entire
state. Conditional failure bounds add over adaptive stages, and any fixed
component preserved by the updates keeps its original marginal law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Ω Γ Ξ:Type} [Fintype Ω] [Fintype Γ] [Fintype Ξ]

def finiteAdaptiveStateLaw (μ:FiniteLaw Ω) (ν:ℕ→Ω→FiniteLaw Γ) (step:ℕ→Ω→Γ→Ω):ℕ→FiniteLaw Ω
  | 0=>μ
  | n+1=>((finiteAdaptiveStateLaw μ ν step n).sigma (ν n)).map (fun z=>step n z.1 z.2)

theorem finite_adaptive_state_survival
    (μ:FiniteLaw Ω) (ν:ℕ→Ω→FiniteLaw Γ) (step:ℕ→Ω→Γ→Ω)
    (E:ℕ→Ω→Prop) (e:ℝ) (δ:ℕ→ℝ) (hδ:∀i,0≤δ i)
    (hinit:1-e≤μ.probability (E 0))
    (hstep:∀i ω,E i ω→1-δ i≤(ν i ω).probability (fun c=>E (i+1) (step i ω c))):
    ∀n,1-(e+∑i∈Finset.range n,δ i)≤(finiteAdaptiveStateLaw μ ν step n).probability (E n):=by
  intro n
  induction n with
  | zero => simpa [finiteAdaptiveStateLaw] using hinit
  | succ n ih =>
    let μn:=finiteAdaptiveStateLaw μ ν step n
    let En:=E n
    let A:(Σω:Ω,Γ)→Prop:=fun z=>En z.1
    let S:∀ω:Ω,Γ→Prop:=fun ω c=>E (n+1) (step n ω c)
    have hA:1-(e+∑i∈Finset.range n,δ i)≤(μn.sigma (ν n)).probability A:=by
      rw [finiteLaw_sigma_first_probability]
      exact ih
    have hattach:=finiteLaw_attach_conditional_event μn (ν n) En A S
      (e+∑i∈Finset.range n,δ i) (δ n) (hδ n) hA (by intro z hz;exact hz) (hstep n)
    have hmono:(μn.sigma (ν n)).probability (fun z=>A z∧S z.1 z.2)≤
        (μn.sigma (ν n)).probability (fun z=>S z.1 z.2):=by
      apply finiteLaw_probability_mono
      intro z hz
      exact hz.2
    have hnext:1-((e+∑i∈Finset.range n,δ i)+δ n)≤
        (μn.sigma (ν n)).probability (fun z=>S z.1 z.2):=le_trans hattach hmono
    change 1-(e+∑i∈Finset.range (n+1),δ i)≤
      ((μn.sigma (ν n)).map (fun z=>step n z.1 z.2)).probability (E (n+1))
    rw [finiteLaw_map_probability,Finset.sum_range_succ]
    dsimp [S] at hnext
    linarith only [hnext]

theorem finite_adaptive_state_preserves_marginal
    (μ:FiniteLaw Ω) (ν:ℕ→Ω→FiniteLaw Γ) (step:ℕ→Ω→Γ→Ω) (base:Ω→Ξ)
    (hbase:∀i ω c,base (step i ω c)=base ω):
    ∀n,(finiteAdaptiveStateLaw μ ν step n).map base=μ.map base:=by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change (((finiteAdaptiveStateLaw μ ν step n).sigma (ν n)).map (fun z=>step n z.1 z.2)).map base=μ.map base
    rw [finiteLaw_map_map]
    have heq:(fun z:(Σω:Ω,Γ)=>base (step n z.1 z.2))=(fun z=>base z.1):=by
      funext z
      exact hbase n z.1 z.2
    rw [heq,←finiteLaw_map_map,finiteLaw_sigma_map_first_dependent,ih]
end Oberwolfach
