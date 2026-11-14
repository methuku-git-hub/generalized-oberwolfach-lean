module

public import Oberwolfach.RawMarkedWheelInterval
public import Oberwolfach.RawIntervalActualReservedMatching

@[expose] public section
/-! The nonroot labels of every sampled marked wheel are ordinary spokes
of the same raw interval outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_marked_wheel_nonroot_spokes_ordinary
    {V U Γ Color E L:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [Fintype Color] (tail head:E→V) (ktail khead:L→V)
    (π:Equiv.Perm V) (d m b:ℕ) (σ:RawMarkedOutcome V U Γ Color) (g:Γ) (j:Color)
    (W:MarkedWheel tail head ktail khead m π b (rawMarkedPairSpokes π d σ g j false)
      (rawMarkedPairSpokes π d σ g j true)) (w:U) (hw:W.2.val=w)
    (a:Fin (m+1)) (ha:a.val≠0):
    W.1.val a∈rawIntervalOrdinaryOuter π d (fun e=>σ (Sum.inr e)) j w:=by
  refine Fin.cases ?_ (fun k _=>?_) a ha
  · simp
  · have hs:=W.2.property.2 k
    simpa only [rawIntervalOrdinaryOuter,Finset.mem_filter,Finset.mem_univ,true_and,
      rawMarkedPairSpokes,rawMarkedSpokes,hw] using hs
end Oberwolfach
