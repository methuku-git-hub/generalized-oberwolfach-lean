module

public import Oberwolfach.LongSelectedTypeEligibleCorrection
public import Oberwolfach.LongEligibleResidualStateSupply
public import Oberwolfach.LongApproximateStateLoss

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
local instance eligibleSampleDecEq : DecidableEq V := Classical.decEq V
local instance eligibleSampleArc (P:V×V→Prop):DecidableEq {e:V×V // P e}:=reservedCandidateArcDecEq P

theorem long_eligible_sample_types_correction
    (G Del Small OrdBad Bad Loss:SimpleGraph V)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (Mhost:V→V→ℕ) (Eligible:V×V→Prop)
    (hcorrect:orientationDisagreementGraph (longPhysicalStateGraph G ω {0,1,2,3,4}) (fun e=>(ω (Sum.inl e)).2) Mhost≤Del)
    (hcover:Small≤longPhysicalStateGraph G ω {2,3}⊔Loss)
    (hOrd:OrdBad≤Bad) (hAllowed:∀x y,G.Adj x y→¬Eligible (x,y)→Bad.Adj x y)
    (hhost:∀x y,Mhost x y=1→G.Adj x y)
    (L Lbad:ℝ) (hLoss:∀v,((Del⊔Loss⊔Bad).degree v:ℝ)≤L) (hBad:∀v,(Bad.degree v:ℝ)≤Lbad)
    (b₀ b₁:V→ℝ)
    (hraw₀:∀v,b₀ v≤((∑x,sampledColourOrientation G (fun e=>ω (Sum.inl e)) 0 x v:ℕ):ℝ))
    (hraw₁:∀v,b₁ v≤((∑x,sampledColourOrientation G (fun e=>ω (Sum.inl e)) 1 x v:ℕ):ℝ))
    (I:Finset V) (C:Finset (Finset V⊕(V×U))) (b:ℕ) (rho eta err:ℝ)
    (hrho:0<rho) (heta:0<eta) (hetaR:eta≤rho)
    (hraw:∀v,|((∑x,sampledColourOrientation G (fun e=>ω (Sum.inl e)) 1 x v:ℕ):ℝ)-(b:ℝ)|≤err)
    (hbudget:err+L≤eta*Fintype.card V)
    (hm₀:∀v,rho*Fintype.card V≤b₀ v-L-I.card-C.card-Lbad)
    (hm₁:∀v,rho*Fintype.card V≤b₁ v-L-I.card-C.card-Lbad):
    let P:=longEligibleResidualArc Mhost Small OrdBad
    let T₁:=longEligibleInitialMarked G (fun e=>ω (Sum.inl e)) Mhost Small OrdBad Eligible
    ∃M:Finset {e:V×V // P e},
      (∀v,directedInCount P M v=b) ∧ (∀e∈M,Eligible e.val) ∧
      (∀e,e.val.1∈I→(e∈M↔e∈T₁)) ∧
      (∀e,Sum.inl ({e.val.1,e.val.2}:Finset V)∈C→(e∈M↔e∈T₁)) ∧
      (∀v,((physicalEdgeGraph (changedDirectedPhysicalEdges P M T₁)).degree v:ℝ)≤
        (1+2/rho)*eta*Fintype.card V+(Fintype.card V:ℝ)^(3/5:ℝ)) :=by
  intro P T₁
  let S₀:Finset {e:V×V // P e}:=Finset.univ.filter (fun e=>sampledColourOrientation G (fun e=>ω (Sum.inl e)) 0 e.val.1 e.val.2=1 ∧ True)
  let S₁:=T₁
  have hs0:=long_approximate_embedding_state_loss G Small Loss ω 0 {2,3} (by decide) hcover
  have hs1:=long_approximate_embedding_state_loss G Small Loss ω 1 {2,3} (by decide) hcover
  have h₀:S₀⊆Finset.univ\T₁:=by
    intro e he
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro he1
    have hh0:sampledColourOrientation G (fun e=>ω (Sum.inl e)) 0 e.val.1 e.val.2=1:=(Finset.mem_filter.mp he).2.1
    have hh1:sampledColourOrientation G (fun e=>ω (Sum.inl e)) 1 e.val.1 e.val.2=1:=(Finset.mem_filter.mp he1).2.1
    have hx0:G.Adj e.val.1 e.val.2 ∧ ω (Sum.inl s(e.val.1,e.val.2))=(0,orientationBit e.val.1 e.val.2):=by
      by_contra h;simp [sampledColourOrientation,h] at hh0
    have hx1:G.Adj e.val.1 e.val.2 ∧ ω (Sum.inl s(e.val.1,e.val.2))=(1,orientationBit e.val.1 e.val.2):=by
      by_contra h;simp [sampledColourOrientation,h] at hh1
    have heq:(0:Fin 6)=1:=by simpa using congrArg Prod.fst (hx0.2.symm.trans hx1.2)
    exact (by decide : (0:Fin 6)≠1) heq
  have hEl:∀e∈T₁,Eligible e.val:=by intro e he;exact (Finset.mem_filter.mp he).2.2
  have hc0:=long_eligible_residual_selected_state_incoming_supply G Del Small OrdBad Bad Loss ω Mhost (fun _=>True) 0 (by decide) hcorrect hs0 hOrd (by simp)
  have hc1:=long_eligible_residual_selected_state_incoming_supply G Del Small OrdBad Bad Loss ω Mhost Eligible 1 (by decide) hcorrect hs1 hOrd hAllowed
  have hb₀:∀v,b₀ v-L≤(S₀.filter (fun e=>e.val.2=v)).card:=by
    intro v
    have hh:((∑x,sampledColourOrientation G (fun e=>ω (Sum.inl e)) 0 x v:ℕ):ℝ)≤
      (S₀.filter (fun e=>e.val.2=v)).card+(Del⊔Loss⊔Bad).degree v:=by
      have hc0':(∑x,sampledColourOrientation G (fun e=>ω (Sum.inl e)) 0 x v:ℕ)≤
          (S₀.filter (fun e=>e.val.2=v)).card+(Del⊔Loss⊔Bad).degree v:=by
        convert hc0 v using 1
        simp only [← SimpleGraph.ncard_neighborSet]
        congr 1
        apply congrArg Finset.card
        ext e
        simp [S₀]
      exact_mod_cast hc0'
    linarith only [hh,hraw₀ v,hLoss v]
  have hb₁:∀v,b₁ v-L≤(S₁.filter (fun e=>e.val.2=v)).card:=by
    intro v
    have hh:((∑x,sampledColourOrientation G (fun e=>ω (Sum.inl e)) 1 x v:ℕ):ℝ)≤
      (S₁.filter (fun e=>e.val.2=v)).card+(Del⊔Loss⊔Bad).degree v:=by
      exact_mod_cast hc1 v
    linarith only [hh,hraw₁ v,hLoss v]
  have hchange:=long_eligible_marked_incoming_change_bound G Del Small OrdBad Bad Loss ω Mhost Eligible hcorrect hs1 hOrd hAllowed
  have hdev:=marked_candidate_indegree_deviation_from_raw G (fun e=>ω (Sum.inl e)) P T₁ b err L hraw
    (fun v=>(hchange v).trans (hLoss v))
  apply long_selected_types_eligible_protected_correction P G Bad Eligible (fun e he=>hhost e.1 e.2 he.1) hAllowed S₀ S₁ T₁ hEl I C b rho eta hrho heta hetaR h₀ (by rfl)
    (fun v=>(hdev v).trans hbudget) (fun v=>b₀ v-L) (fun v=>b₁ v-L) Lbad hBad hb₀ hb₁ hm₀ hm₁
end Oberwolfach
