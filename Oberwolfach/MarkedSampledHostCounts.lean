module

public import Oberwolfach.MarkedPreparedHostCounts
public import Oberwolfach.MarkedSampleHostInterfaces
public import Oberwolfach.MarkedProfileMonotonicity

@[expose] public section

/-! Convert one row/index event on the actual sampled arcs to the
extension counts used by the absorber, with both counts scaled by |V|. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_sampled_host_extension_counts
    (P:SimpleGraph V) (π:Equiv.Perm V) (d l:ℕ)
    (p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color) (ε γ pstar ω:ℝ)
    (hpstar:0<pstar) (hpstar1:pstar≤1) (hγ:0<γ) (hγ1:γ≤1)
    (hp:pstar≤p) (hk:pstar≤k) (hq:∀ u,pstar≤q u g) (hs:∀ u,pstar≤s u j)
    (hε:ε≤pstar^4*γ/4) (hεh:ε≤pstar^(l+11)/2)
    (hloss:2*(2*(3*d:ℕ)+1:ℝ)≤γ*Fintype.card V/2)
    (hdeg:∀ x,(1/2+γ/2)*Fintype.card V≤(P.degree x:ℝ))
    (hU:ω*Fintype.card V≤(Fintype.card U:ℝ))
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hrows:MarkedRowsWithSpokes P π d (l+11) Finset.univ p k q s g j (ε*Fintype.card V) σ H)
    (hindices:MarkedIndicesWithSpokes π d (l+11) Finset.univ q s g j (ε*Fintype.card U) σ H):
    MarkedHostExtensionCounts
      (fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
      (fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
      (H false) (H true) π (3*d) l
      ((pstar^4*γ/4)*Fintype.card V) ((pstar^(l+11)*ω/2)*Fintype.card V):=by
  have hH:(fun t v u=>if t then H true v u else H false v u)=H:=by
    funext t v u
    cases t <;> rfl
  have hcount:=marked_prepared_host_counts P π d l p k q s g j ε γ pstar hpstar hpstar1 hγ hγ1
    hp hk hq hs hε hεh hloss hdeg σ (H false) (H true) _ _ _ _
    (marked_sample_host_arc_present P π d σ)
    (by simpa only [hH] using hrows) (by simpa only [hH] using hindices)
  apply hcount.lowerBounds le_rfl
  have hh:=mul_le_mul_of_nonneg_left hU (show 0≤pstar^(l+11)/2 by positivity)
  convert hh using 1 <;> ring

end Oberwolfach
