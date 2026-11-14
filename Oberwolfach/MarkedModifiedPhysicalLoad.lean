module

public import Oberwolfach.MarkedRawStateChangeOnHost
public import Oberwolfach.MarkedRimFullIncidence

@[expose] public section
/-! Fixed retained-sample loads after any raw rim-state and typed spoke
changes supported on physical graphs with bounded degrees. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [Nonempty V] [LinearOrder V] [LinearOrder W]
  [DecidableEq U] [DecidableEq Z]

theorem marked_modified_local_load_from_physical_changes
    (F:W↪oV) (f:W≃V) (hf:∀ x,f x=F x) (g:Z≃U)
    (π:Equiv.Perm V) (ρ:Equiv.Perm W) (hc:∀ x,f (ρ x)=π (f x))
    (P:SimpleGraph V) (d m:ℕ) (hm:3≤m) (a c:Γ) (j:Color)
    (p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (σ':RawMarkedOutcome V U Γ Color) (H':Bool→V→U→Prop)
    (w:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ _=>True) (fun _ _=>True)→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
    (hu:Fintype.card U≤Fintype.card V)
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U))
    (deltaR deltaS:ℝ) (hR:0≤deltaR) (hS:0≤deltaS)
    (hdegR:∀ x,(DR.degree x:ℝ)≤deltaR)
    (hdegSrow:∀ x,(DS.degree (Sum.inl x):ℝ)≤deltaS)
    (hdegScol:∀ u,(DS.degree (Sum.inr u):ℝ)≤deltaS)
    (hraw:∀ e,e∈P.edgeFinset→z.1 (Sum.inl e)≠σ' (Sum.inl e)→e∈DR.edgeFinset):
    let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 c j
    let R:=rawMarkedPairRims P π d z.1
    let e:=f.prodCongr f
    let M:=markedWheelVertexEmbedding (m:=m) (b:=3*d) f.toEmbedding g.toEmbedding hc e e
      (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)
      (fun _ _ h=>h) (fun _ _ h=>h)
    (∀ b x u,¬(H b x u↔H' b x u)→DS.Adj (Sum.inl x) (Sum.inr u)) →
    ∀ error:ℝ,
    (∀ root,rawMarkedWheelMarginal P π d p k q s c j root≠0 →
      |typedMarkedPotentialLoad w R H root-1|≤error) →
    ∀ root,rawMarkedWheelMarginal (P.comap F) ρ d p k (fun u=>q (g u)) (fun u=>s (g u)) c j root≠0 →
      |typedMarkedPotentialLoad (fun W=>w (M W))
        (rawMarkedPairRims (P.comap F) ρ d (rawMarkedRestrictPair f g σ'))
        (fun b x u=>H' b (f x) (g u)) root-1|≤
        error+11*((m:ℝ)+1)^4*B*(2*deltaR+deltaS)/Fintype.card V := by
  intro H R e M hspoke error hload
  have hchange:=marked_rim_change_of_raw_state_on_host P π d z.1 σ' DR hraw
  obtain ⟨hout,hin⟩:=marked_rim_physical_change_incidence P π d z.1 σ' DR hchange deltaR hdegR
  obtain ⟨hsrow,hscol⟩:=marked_spoke_physical_change_incidence H H' DS hspoke
  have hloss:0≤2*deltaR+deltaS:=by positivity
  have hR':2*deltaR≤2*deltaR+deltaS:=by linarith
  have hS':deltaS≤2*deltaR+deltaS:=by linarith
  exact marked_modified_local_load_bridge F f hf g π ρ hc P d m hm a c j p k q s z σ' H' w B hB hw hu
    (2*deltaR+deltaS) hloss (fun x=>(hout x).trans hR') (fun x=>(hin x).trans hR')
    (fun b x=>(hsrow b x).trans ((hdegSrow x).trans hS'))
    (fun b u=>(hscol b u).trans ((hdegScol u).trans hS')) error hload
end Oberwolfach
