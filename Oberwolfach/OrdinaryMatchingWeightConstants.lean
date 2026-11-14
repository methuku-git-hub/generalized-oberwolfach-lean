module

public import Oberwolfach.CandidateOrdinaryAssignedNamedSeedsDirectReserve
public import Oberwolfach.SuccessorPreweightExistence

@[expose] public section
/-! Uniform sampled-weight and pair bounds are chosen from the original host
weight constants before the later matching tolerance and random sample. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem ordinary_matching_weight_constants
    (K m k:ℕ) (α ρ₀:ℝ) (hα:0<α) (hρ:0<ρ₀) (B:Fin K→ℝ) (hB:∀i,0<B i):
    ∃p₀ BM:ℝ,∃BO:Fin K→ℝ,∃Kcd:ℝ,
      p₀=min (1/2:ℝ) (ρ₀/4) ∧ 0<p₀ ∧
      BM=2*(successorWeightUpper k (α/4))/p₀^(2*m+1) ∧ 0<BM ∧
      (∀i,BO i=2*B i/p₀^(2*(longPaddedSeedExponent i+2))) ∧ (∀i,0<BO i) ∧
      0<Kcd ∧
      (∑i:Option (Fin K),(16:ℝ)*(match i with
        | none=>((m:ℝ)+1)^4*BM
        | some i=>((longPaddedSeedExponent i:ℝ)+2)^3*BO i))≤Kcd :=by
  let p₀:ℝ:=min (1/2:ℝ) (ρ₀/4)
  have hp:0<p₀:=by dsimp [p₀];positivity
  have hUpper:0<successorWeightUpper k (α/4):=(successorWeightConstants_pos k (α/4) (by positivity)).2
  let BM:ℝ:=2*(successorWeightUpper k (α/4))/p₀^(2*m+1)
  let BO:Fin K→ℝ:=fun i=>2*B i/p₀^(2*(longPaddedSeedExponent i+2))
  have hBM:0<BM:=by dsimp [BM];positivity
  have hBO:∀i,0<BO i:=by
    intro i
    have hBi:=hB i
    dsimp [BO]
    positivity
  let S:ℝ:=∑i:Option (Fin K),(16:ℝ)*(match i with
    | none=>((m:ℝ)+1)^4*BM
    | some i=>((longPaddedSeedExponent i:ℝ)+2)^3*BO i)
  have hS:0≤S:=by
    dsimp [S]
    apply Finset.sum_nonneg
    intro i hi
    cases i with
    | none=>positivity
    | some i=>have hh:=hBO i;positivity
  refine ⟨p₀,BM,BO,S+1,rfl,hp,rfl,hBM,(fun _=>rfl),hBO,by linarith,?_⟩
  dsimp [S]
  linarith
end Oberwolfach
