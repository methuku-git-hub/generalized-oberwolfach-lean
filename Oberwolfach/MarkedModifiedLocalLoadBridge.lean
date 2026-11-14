module

public import Oberwolfach.MarkedRetainedModifiedLoad
public import Oberwolfach.MarkedModifiedPotentialRelabel

@[expose] public section
/-! A single fixed parent weight transfers the sampled load estimate through
actual typed host changes, including additions, and then to a full-domain
relabelled reference. The caller supplies the realized change bounds. -/
set_option autoImplicit false
set_option maxHeartbeats 3500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color : Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [Nonempty V] [LinearOrder V] [LinearOrder W]
  [DecidableEq U] [DecidableEq Z]

theorem marked_modified_local_load_bridge
    (F:W↪oV) (f:W≃V) (hf:∀ x,f x=F x) (g:Z≃U)
    (π:Equiv.Perm V) (ρ:Equiv.Perm W) (hc:∀ x,f (ρ x)=π (f x))
    (P:SimpleGraph V) (d m:ℕ) (hm:3≤m) (a c:Γ) (j:Color)
    (p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (σ':RawMarkedOutcome V U Γ Color) (H':Bool→V→U→Prop)
    (w:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ _=>True) (fun _ _=>True)→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
    (hu:Fintype.card U≤Fintype.card V) (loss:ℝ) (hloss:0≤loss) :
    let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 c j
    let R:=rawMarkedPairRims P π d z.1
    let R':=rawMarkedPairRims P π d σ'
    let e:=f.prodCongr f
    let M:=markedWheelVertexEmbedding (m:=m) (b:=3*d) f.toEmbedding g.toEmbedding hc e e
      (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)
      (fun _ _ h=>h) (fun _ _ h=>h)
    (∀ x,(∑ e,if ¬(R e↔R' e) ∧ Sum.elim Prod.fst Prod.fst e=x then (1:ℝ) else 0)≤loss) →
    (∀ x,(∑ e,if ¬(R e↔R' e) ∧ Sum.elim Prod.snd Prod.snd e=x then (1:ℝ) else 0)≤loss) →
    (∀ b x,(∑ u,bipAdj (fun x u=>¬(H b x u↔H' b x u)) x u)≤loss) →
    (∀ b u,(∑ x,bipAdj (fun x u=>¬(H b x u↔H' b x u)) x u)≤loss) →
    ∀ error:ℝ,
    (∀ root,rawMarkedWheelMarginal P π d p k q s c j root≠0 →
      |typedMarkedPotentialLoad w R H root-1|≤error) →
    ∀ root,rawMarkedWheelMarginal (P.comap F) ρ d p k (fun u=>q (g u)) (fun u=>s (g u)) c j root≠0 →
      |typedMarkedPotentialLoad (fun W=>w (M W))
        (rawMarkedPairRims (P.comap F) ρ d (rawMarkedRestrictPair f g σ'))
        (fun b x u=>H' b (f x) (g u)) root-1|≤
        error+11*((m:ℝ)+1)^4*B*loss/Fintype.card V := by
  intro H R R' e M hout hin hHout hHin error hbase
  have hparent := marked_retained_load_after_host_modification P π d m hm a c j p k q s z σ' H' w B hB hw
    hu loss hloss hout hin hHout hHin error hbase
  exact marked_modified_parent_load_bound_relabel F f hf g π ρ hc P d m c j p k q s
    (error+11*((m:ℝ)+1)^4*B*loss/Fintype.card V) σ' H' w hparent
end Oberwolfach
