module

public import Oberwolfach.OrderedOrdinaryWheelExpectation
public import Oberwolfach.OrderedOrdinaryWheelProducts

@[expose] public section
/-! The candidate marginal uses the supplied spoke probability of its own hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U] {r:ℕ} {π:Equiv.Perm V}

theorem cycleNext_ne_self (hr:3≤r) (i:Fin r):cycleNext i≠i:=by
  intro h
  apply cycleNext_two_ne hr i
  rw [h,h]

theorem orderedOrdinary_marginal_on_candidate (P:SimpleGraph V) (d:ℕ) (hr:3≤r)
    (W:OrderedOrdinaryWheel (U:=U) π (3*d) r)
    (hP:∀ i:Fin r,P.Adj (W.1.val i) (W.1.val (cycleNext i)))
    (p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color)
    (a:(V×V)⊕(V×U)) (ha:a∈orderedOrdinaryResources W):
    rawMarkedWheelMarginal P π d p k q s g j (orderedOrdinaryResourceEmbedding a)=
      Sum.elim (fun _=>p) (fun _=>s W.2 j) a:=by
  cases a with
  | inl e=>
    obtain ⟨i,hi⟩:=(orderedOrdinaryResources_rim W e).mp ha
    have hc:¬PermutationClose π (3*d) (W.1.val i) (W.1.val (cycleNext i)):=
      W.1.property i (cycleNext i) (Ne.symm (cycleNext_ne_self hr i))
    rw [←hi]
    simp [orderedOrdinaryResourceEmbedding,rawMarkedWheelMarginal,hc,hP i]
  | inr a=>
    obtain ⟨i,hi⟩:=(orderedOrdinaryResources_spoke W a).mp ha
    have hu:W.2=a.2:=congrArg Prod.snd hi
    simp [orderedOrdinaryResourceEmbedding,rawMarkedWheelMarginal,←hu]
end Oberwolfach
