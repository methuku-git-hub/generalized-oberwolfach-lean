module

public import Oberwolfach.LongResidualTwoStateSupply
public import Oberwolfach.LongSelectedTypeProtectedCorrection

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
local instance residualTypeCorrectionDecEq : DecidableEq V := Classical.decEq V
local instance residualTypeCorrectionArc (P:V×V→Prop):DecidableEq {e:V×V // P e}:=reservedCandidateArcDecEq P

theorem long_residual_types_protected_correction
    (G Del Small Bad Loss:SimpleGraph V)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (Mhost:V→V→ℕ)
    (hcorrect:orientationDisagreementGraph (longPhysicalStateGraph G ω {0,1,2,3,4}) (fun e=>(ω (Sum.inl e)).2) Mhost≤Del)
    (hcover:Small≤longPhysicalStateGraph G ω {2,3}⊔Loss)
    (L:ℝ) (hLoss:∀v,((Del⊔Loss⊔Bad).degree v:ℝ)≤L)
    (b₀ b₁:V→ℝ)
    (hraw₀:∀v,b₀ v≤((∑x,sampledColourOrientation G (fun e=>ω (Sum.inl e)) 0 x v:ℕ):ℝ))
    (hraw₁:∀v,b₁ v≤((∑x,sampledColourOrientation G (fun e=>ω (Sum.inl e)) 1 x v:ℕ):ℝ))
    (I:Finset V) (C:Finset (Finset V⊕(V×U))) (b:ℕ) (rho eta:ℝ)
    (hrho:0<rho) (heta:0<eta) (hetaR:eta≤rho):
    let P:=longResidualHostArc Mhost Small Bad
    let T₁:=longResidualInitialMarked G (fun e=>ω (Sum.inl e)) Mhost Small Bad
    (∀v,|(directedInCount P T₁ v:ℝ)-(b:ℝ)|≤eta*Fintype.card V)→
    (∀v,rho*Fintype.card V≤b₀ v-L-I.card-C.card)→
    (∀v,rho*Fintype.card V≤b₁ v-L-I.card-C.card)→
    ∃M:Finset {e:V×V // P e},
      (∀v,directedInCount P M v=b) ∧
      (∀e,e.val.1∈I→(e∈M↔e∈T₁)) ∧
      (∀e,Sum.inl ({e.val.1,e.val.2}:Finset V)∈C→(e∈M↔e∈T₁)) ∧
      (∀v,((physicalEdgeGraph (changedDirectedPhysicalEdges P M T₁)).degree v:ℝ)≤
        (1+2/rho)*eta*Fintype.card V+(Fintype.card V:ℝ)^(3/5:ℝ)) :=by
  intro P T₁ hdev hm₀ hm₁
  let S₀:Finset {e:V×V // P e}:=Finset.univ.filter (fun e=>sampledColourOrientation G (fun e=>ω (Sum.inl e)) 0 e.val.1 e.val.2=1)
  let S₁:Finset {e:V×V // P e}:=Finset.univ.filter (fun e=>sampledColourOrientation G (fun e=>ω (Sum.inl e)) 1 e.val.1 e.val.2=1)
  have hs:=long_residual_two_selected_state_supply G Del Small Bad Loss ω Mhost hcorrect hcover L hLoss b₀ b₁ hraw₀ hraw₁
  have h₀:S₀⊆Finset.univ\T₁:=by
    intro e he
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro he1
    have h0:sampledColourOrientation G (fun e=>ω (Sum.inl e)) 0 e.val.1 e.val.2=1:=(Finset.mem_filter.mp he).2
    have h1:sampledColourOrientation G (fun e=>ω (Sum.inl e)) 1 e.val.1 e.val.2=1:=(Finset.mem_filter.mp he1).2
    have hh0:G.Adj e.val.1 e.val.2 ∧ ω (Sum.inl s(e.val.1,e.val.2))=(0,orientationBit e.val.1 e.val.2):=by
      by_contra h;simp [sampledColourOrientation,h] at h0
    have hh1:G.Adj e.val.1 e.val.2 ∧ ω (Sum.inl s(e.val.1,e.val.2))=(1,orientationBit e.val.1 e.val.2):=by
      by_contra h;simp [sampledColourOrientation,h] at h1
    have heq:(0:Fin 6)=1:=by simpa using congrArg Prod.fst (hh0.2.symm.trans hh1.2)
    exact (by decide : (0:Fin 6)≠1) heq
  have h₁:S₁⊆T₁:=by
    intro e he
    simpa only [S₁,T₁,longResidualInitialMarked,Finset.mem_filter,Finset.mem_univ,true_and] using he
  have hb₀:∀v,b₀ v-L≤(S₀.filter (fun e=>e.val.2=v)).card:=by
    intro v
    convert hs.2.2.1 v using 1 <;> congr 1 <;> ext e <;> simp [S₀]
  have hb₁:∀v,b₁ v-L≤(S₁.filter (fun e=>e.val.2=v)).card:=by
    intro v
    convert hs.2.2.2 v using 1 <;> congr 1 <;> ext e <;> simp [S₁]
  exact long_selected_types_protected_correction P S₀ S₁ T₁ I C b rho eta hrho heta hetaR h₀ h₁ hdev
    (fun v=>b₀ v-L) (fun v=>b₁ v-L) hb₀ hb₁ hm₀ hm₁
end Oberwolfach
