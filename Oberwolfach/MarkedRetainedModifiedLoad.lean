module

public import Oberwolfach.MarkedPotentialModifiedHost
public import Oberwolfach.MarkedRetainedPotentialLoadRelabel

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [Nonempty V] [LinearOrder V] [DecidableEq U]

theorem marked_retained_load_after_host_modification
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (hm:3≤m)
    (a c:Γ) (j:Color) (p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ)
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
    (∀ x,(∑ e,if ¬(R e↔R' e) ∧ Sum.elim Prod.fst Prod.fst e=x then (1:ℝ) else 0)≤loss) →
    (∀ x,(∑ e,if ¬(R e↔R' e) ∧ Sum.elim Prod.snd Prod.snd e=x then (1:ℝ) else 0)≤loss) →
    (∀ b x,(∑ u,bipAdj (fun x u=>¬(H b x u↔H' b x u)) x u)≤loss) →
    (∀ b u,(∑ x,bipAdj (fun x u=>¬(H b x u↔H' b x u)) x u)≤loss) →
    ∀ error:ℝ,
    (∀ root,rawMarkedWheelMarginal P π d p k q s c j root≠0 →
      |typedMarkedPotentialLoad w R H root-1|≤error) →
    ∀ root,rawMarkedWheelMarginal P π d p k q s c j root≠0 →
      |typedMarkedPotentialLoad w R' H' root-1|≤
        error+11*((m:ℝ)+1)^4*B*loss/Fintype.card V := by
  intro H R R' hout hin hHout hHin error hbase
  exact marked_potential_load_after_host_modification hm Fintype.card_pos hu w B hB hw R R' H H'
    loss hloss hout hin hHout hHin (fun root=>rawMarkedWheelMarginal P π d p k q s c j root≠0) error hbase
end Oberwolfach
