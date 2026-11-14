module

public import Oberwolfach.MarkedModifiedPhysicalUniform

@[expose] public section
/-! The same sample and the same fixed domains support both neighbourhood
and fixed-weight load estimates for every later admissible host. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [Nonempty V] [LinearOrder V] [LinearOrder W]
  [DecidableEq U] [DecidableEq Z]

theorem marked_modified_joint_estimates_on_one_sample
    (F:W↪oV) (f:W≃V) (hf:∀ x,f x=F x) (g:Z≃U)
    (π:Equiv.Perm V) (ρ:Equiv.Perm W) (hc:∀ x,f (ρ x)=π (f x))
    (P:SimpleGraph V) (d m h:ℕ) (hm:3≤m) (a c:Γ) (j:Color)
    (p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (A:Finset V) (C:Finset U)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (w:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ _=>True) (fun _ _=>True)→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
    (hu:Fintype.card U≤Fintype.card V)
    (deltaR deltaS:ℝ) (hR:0≤deltaR) (hS:0≤deltaS) (error errR errI:ℝ):
    let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 c j
    let R:=rawMarkedPairRims P π d z.1
    let e:=f.prodCongr f
    let M:=markedWheelVertexEmbedding (m:=m) (b:=3*d) f.toEmbedding g.toEmbedding hc e e
      (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)
      (fun _ _ h=>h) (fun _ _ h=>h)
    MarkedRowsWithSpokes P π d h A p k q s c j errR z.1 H →
    MarkedIndicesWithSpokes π d h C q s c j errI z.1 H →
    (∀ root,rawMarkedWheelMarginal P π d p k q s c j root≠0 →
      |typedMarkedPotentialLoad w R H root-1|≤error) →
    ∀ (σ':RawMarkedOutcome V U Γ Color) (H':Bool→V→U→Prop)
      (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)),
    (∀ x,(DR.degree x:ℝ)≤deltaR) →
    (∀ x,(DS.degree (Sum.inl x):ℝ)≤deltaS) →
    (∀ u,(DS.degree (Sum.inr u):ℝ)≤deltaS) →
    (∀ e,e∈P.edgeFinset→z.1 (Sum.inl e)≠σ' (Sum.inl e)→e∈DR.edgeFinset) →
    (∀ b x u,¬(H b x u↔H' b x u)→DS.Adj (Sum.inl x) (Sum.inr u)) →
    MarkedRowsWithSpokes P π d h A p k q s c j (errR+h*(deltaR+deltaS)) σ' H' ∧
    MarkedIndicesWithSpokes π d h C q s c j (errI+h*deltaS) σ' H' ∧
    ∀ root,rawMarkedWheelMarginal (P.comap F) ρ d p k (fun u=>q (g u)) (fun u=>s (g u)) c j root≠0 →
      |typedMarkedPotentialLoad (fun W=>w (M W))
        (rawMarkedPairRims (P.comap F) ρ d (rawMarkedRestrictPair f g σ'))
        (fun b x u=>H' b (f x) (g u)) root-1|≤
        error+11*((m:ℝ)+1)^4*B*(2*deltaR+deltaS)/Fintype.card V := by
  intro H R e M hrows hindices hload σ' H' DR DS hdegR hdegSrow hdegScol hraw hspoke
  have hchange:=marked_rim_change_of_raw_state_on_host P π d z.1 σ' DR hraw
  have hneigh:=marked_neighbourhoods_after_physical_change P π d h A C p k q s c j
    errR errI deltaR deltaS deltaS hR hS hS z.1 σ' H H' hrows hindices DR DS hchange hspoke
    hdegR hdegSrow hdegScol
  refine ⟨hneigh.1,hneigh.2,?_⟩
  exact marked_modified_local_load_uniform_physical_changes F f hf g π ρ hc P d m hm a c j p k q s z w B hB hw hu
    deltaR deltaS hR hS error hload σ' H' DR DS hdegR hdegSrow hdegScol hraw hspoke
end Oberwolfach
