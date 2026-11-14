module

public import Oberwolfach.LongSelectedTypeDualCorrectionLocal
public import Oberwolfach.MarkedCandidateIncomingLocal
public import Oberwolfach.LongDualMarkedIncomingChange
public import Oberwolfach.LongEligibleResidualStateSupply
public import Oberwolfach.LongApproximateStateLoss

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
local instance dualSampleLocalDecEq : DecidableEq V := Classical.decEq V
local instance dualSampleLocalArc (P:V×V→Prop):DecidableEq {e:V×V // P e}:=reservedCandidateArcDecEq P

theorem long_dual_sample_types_correction_local
    (G Del Small Bad Loss:SimpleGraph V)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (Mhost:V→V→ℕ) (Ord Mark Eligible:V×V→Prop) (hEquiv:∀e,Eligible e↔Ord e∧Mark e)
    (hcorrect:orientationDisagreementGraph (longPhysicalStateGraph G ω {0,1,2,3,4}) (fun e=>(ω (Sum.inl e)).2) Mhost≤Del)
    (hcover:Small≤longPhysicalStateGraph G ω {2,3}⊔Loss)
    (hAllowed:∀x y,G.Adj x y→¬Eligible (x,y)→Bad.Adj x y)
    (hhost:∀x y,Mhost x y=1→G.Adj x y)
    (hFull:∀x y,Mhost x y=1→¬Small.Adj x y→Ord (x,y)∨Mark (x,y))
    (L Lbad:ℝ) (hLoss:∀v,((Del⊔Loss⊔Bad).degree v:ℝ)≤L) (hBad:∀v,(Bad.degree v:ℝ)≤Lbad)
    (b₀ b₁:V→ℝ)
    (hraw₀:∀v,b₀ v≤((∑x,sampledColourOrientation G (fun e=>ω (Sum.inl e)) 0 x v:ℕ):ℝ))
    (hraw₁:∀v,b₁ v≤((∑x,sampledColourOrientation G (fun e=>ω (Sum.inl e)) 1 x v:ℕ):ℝ))
    (I:Finset V) (C:Finset (Finset V⊕(V×U))) (b:ℕ) (rho eta err:ℝ)
    (hrho:0<rho) (heta:0<eta) (hetaR:eta≤rho)
    (hraw:∀v,|((∑x,sampledColourOrientation G (fun e=>ω (Sum.inl e)) 1 x v:ℕ):ℝ)-(b:ℝ)|≤err)
    (hbudget:err+L≤eta*Fintype.card V)
    (Llocal loc:ℝ) (hloc:0≤loc) (hlocGlobal:loc≤eta*Fintype.card V)
    (hLocalBudget:err+Llocal≤loc)
    (hLossLocal:∀v,v∉I→((Del⊔Loss⊔Bad).degree v:ℝ)≤Llocal)
    (hm₀:∀v,rho*Fintype.card V≤b₀ v-L-I.card-C.card-Lbad)
    (hm₁:∀v,rho*Fintype.card V≤b₁ v-L-I.card-C.card-Lbad):
    let P:=longEligibleResidualArc Mhost Small ⊥
    let T₁:=longDualInitialMarked G (fun e=>ω (Sum.inl e)) Mhost Small Ord Mark
    ∃M:Finset {e:V×V // P e},
      (∀v,directedInCount P M v=b) ∧ (∀e∈M,Mark e.val) ∧ (∀e,e∉M→Ord e.val) ∧
      (∀e,e.val.1∈I→(e∈M↔e∈T₁)) ∧
      (∀e,Sum.inl ({e.val.1,e.val.2}:Finset V)∈C→(e∈M↔e∈T₁)) ∧
      (∀v,((physicalEdgeGraph (changedDirectedPhysicalEdges P M T₁)).degree v:ℝ)≤
        (1+2/rho)*eta*Fintype.card V+1) ∧
      (∀v,v∉I→((physicalEdgeGraph (changedDirectedPhysicalEdges P M T₁)).degree v:ℝ)≤
        loc+((I.card:ℝ)*eta+loc)/rho+1) :=by
  intro P T₁
  let S₀:Finset {e:V×V // P e}:=Finset.univ.filter (fun e=>sampledColourOrientation G (fun e=>ω (Sum.inl e)) 0 e.val.1 e.val.2=1 ∧ Eligible e.val)
  let S₁:Finset {e:V×V // P e}:=Finset.univ.filter (fun e=>sampledColourOrientation G (fun e=>ω (Sum.inl e)) 1 e.val.1 e.val.2=1 ∧ Eligible e.val)
  have hs0:=long_approximate_embedding_state_loss G Small Loss ω 0 {2,3} (by decide) hcover
  have hs1:=long_approximate_embedding_state_loss G Small Loss ω 1 {2,3} (by decide) hcover
  have h₀:S₀⊆Finset.univ\T₁:=by
    intro e he
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro he1
    have hh0:sampledColourOrientation G (fun e=>ω (Sum.inl e)) 0 e.val.1 e.val.2=1:=(Finset.mem_filter.mp he).2.1
    have hflex:Ord e.val ∧ Mark e.val:=(hEquiv e.val).mp (Finset.mem_filter.mp he).2.2
    have hh1:sampledColourOrientation G (fun e=>ω (Sum.inl e)) 1 e.val.1 e.val.2=1:=by
      rcases (Finset.mem_filter.mp he1).2 with h|h
      · exact h.1
      · exact False.elim (h hflex.1)
    have hx0:G.Adj e.val.1 e.val.2 ∧ ω (Sum.inl s(e.val.1,e.val.2))=(0,orientationBit e.val.1 e.val.2):=by
      by_contra h;simp [sampledColourOrientation,h] at hh0
    have hx1:G.Adj e.val.1 e.val.2 ∧ ω (Sum.inl s(e.val.1,e.val.2))=(1,orientationBit e.val.1 e.val.2):=by
      by_contra h;simp [sampledColourOrientation,h] at hh1
    have heq:(0:Fin 6)=1:=by simpa using congrArg Prod.fst (hx0.2.symm.trans hx1.2)
    exact (by decide : (0:Fin 6)≠1) heq
  have h₁:S₁⊆T₁:=by
    intro e he
    have hh:=(Finset.mem_filter.mp he).2
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,Or.inl ⟨hh.1,((hEquiv e.val).mp hh.2).2⟩⟩
  have hMarked:∀e∈T₁,Mark e.val:=by
    intro e he
    rcases (Finset.mem_filter.mp he).2 with h|h
    · exact h.2
    · rcases hFull e.val.1 e.val.2 e.property.1 e.property.2.1 with ho|hm
      · exact False.elim (h ho)
      · exact hm
  have hForced:∀e:{a:V×V // P a},¬Ord e.val→e∈T₁:=by
    intro e he
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,Or.inr he⟩
  have hc0:=long_eligible_residual_selected_state_incoming_supply G Del Small ⊥ Bad Loss ω Mhost Eligible 0 (by decide) hcorrect hs0 bot_le hAllowed
  have hc1:=long_eligible_residual_selected_state_incoming_supply G Del Small ⊥ Bad Loss ω Mhost Eligible 1 (by decide) hcorrect hs1 bot_le hAllowed
  have hb₀:∀v,b₀ v-L≤(S₀.filter (fun e=>e.val.2=v)).card:=by
    intro v
    have hh:((∑x,sampledColourOrientation G (fun e=>ω (Sum.inl e)) 0 x v:ℕ):ℝ)≤
      (S₀.filter (fun e=>e.val.2=v)).card+(Del⊔Loss⊔Bad).degree v:=by
      exact_mod_cast hc0 v
    linarith only [hh,hraw₀ v,hLoss v]
  have hb₁:∀v,b₁ v-L≤(S₁.filter (fun e=>e.val.2=v)).card:=by
    intro v
    have hh:((∑x,sampledColourOrientation G (fun e=>ω (Sum.inl e)) 1 x v:ℕ):ℝ)≤
      (S₁.filter (fun e=>e.val.2=v)).card+(Del⊔Loss⊔Bad).degree v:=by
      exact_mod_cast hc1 v
    linarith only [hh,hraw₁ v,hLoss v]
  have hbad':∀x y,G.Adj x y→¬(Ord (x,y)∧Mark (x,y))→Bad.Adj x y:=by
    intro x y hg h;exact hAllowed x y hg (fun he=>h ((hEquiv _).mp he))
  have hchange:=long_dual_marked_incoming_change_bound G Del Small Bad Loss ω Mhost Ord Mark hcorrect hhost hs1 hbad'
  have hdev:=marked_candidate_indegree_deviation_from_raw G (fun e=>ω (Sum.inl e)) P T₁ b err L hraw
    (fun v=>(hchange v).trans (hLoss v))
  have hdevlocal:=marked_candidate_indegree_deviation_from_raw_local G (fun e=>ω (Sum.inl e)) P T₁ b err Llocal I hraw
    (by intro v hv;exact (hchange v).trans (hLossLocal v hv))
  exact long_selected_types_dual_eligible_correction_local P G Bad Ord Mark Eligible hEquiv (fun e he=>hhost e.1 e.2 he.1) hAllowed S₀ S₁ T₁ hMarked hForced I C b rho eta hrho heta hetaR h₀ h₁
    loc hloc hlocGlobal (by intro v hv;exact (hdevlocal v hv).trans hLocalBudget)
    (fun v=>(hdev v).trans hbudget) (fun v=>b₀ v-L) (fun v=>b₁ v-L) Lbad hBad hb₀ hb₁ hm₀ hm₁
end Oberwolfach
