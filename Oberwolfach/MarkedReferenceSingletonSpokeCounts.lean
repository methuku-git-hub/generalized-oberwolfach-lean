module

public import Oberwolfach.MarkedNeighbourhoodSpokeChanges

@[expose] public section
/-! The common row and index tests include the one-spoke degree estimates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_reference_singleton_spoke_counts
    (P:SimpleGraph V) (π:Equiv.Perm V) (d h:ℕ) (hh:1≤h)
    (p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color) (εrow εcol:ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hrows:MarkedRowsWithSpokes P π d h Finset.univ p k q s g j εcol σ H)
    (hindices:MarkedIndicesWithSpokes π d h Finset.univ q s g j εrow σ H):
    (∀b v,|((Finset.univ.filter (fun u=>H b v u)).card:ℝ)-∑u,if b then q u g else s u j|<εrow) ∧
    (∀b u,|((Finset.univ.filter (fun v=>H b v u)).card:ℝ)-(if b then q u g else s u j)*Fintype.card V|<εcol):=by
  constructor
  · intro b v
    have hs:=hindices {(b,v)} (by simpa using hh) (by
      intro a ha c hc hac
      simp only [Finset.mem_singleton] at ha hc
      exact False.elim (hac (ha.trans hc.symm)))
    simpa only [markedIndexCountWithSpokes,Finset.mem_singleton,forall_eq,Finset.prod_singleton,
      Finset.sum_boole,Prod.fst,Prod.snd] using hs
  · intro b u
    have hinj:Set.InjOn (fun a:Bool×U=>a.2) ({(b,u)}:Finset (Bool×U)):=by
      intro a ha c hc _
      have ha':a=(b,u):=by simpa using ha
      have hc':c=(b,u):=by simpa using hc
      exact ha'.trans hc'.symm
    have hs:=hrows ∅ ∅ {(b,u)} (by simp) (by simp) (by simpa using hh) hinj
    have hdom:markedRowDomain P π (3*d) Finset.univ ∅ ∅=Finset.univ:=by
      ext v
      simp [markedRowDomain,Set.InjOn]
    rw [hdom] at hs
    simpa [markedRowCountWithSpokes,Finset.sum_boole] using hs
end Oberwolfach
