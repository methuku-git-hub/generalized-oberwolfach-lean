module

public import Oberwolfach.MarkedIntervalBoundaryIdentity
public import Oberwolfach.BufferedPathBoundaryCompletion

@[expose] public section
/-! A buffered source path following a cycle orientation is the corresponding
permutation orbit interval. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem buffered_path_follows_permutation
    {X I:Type*} [Fintype I] [DecidableEq X]
    (n:I→ℕ) (inner:∀i,Fin (n i+1)↪X) (σ:Equiv.Perm X)
    (hstep:∀i (p:Fin (n i)),σ (inner i p.castSucc)=inner i p.succ):
    ∀i (p:Fin (n i+1)),inner i p=(σ^p.val) (inner i 0):=by
  intro i p
  induction p using Fin.induction with
  | zero => simp
  | succ p ih =>
    calc
      inner i p.succ = σ (inner i p.castSucc):=(hstep i p).symm
      _ = σ ((σ^p.val) (inner i 0)):=by rw [ih]; rfl
      _ = (σ^(p.val+1)) (inner i 0):=by rw [pow_succ',Equiv.Perm.mul_apply]

theorem buffered_oriented_path_boundary_identity
    {X I:Type*} [Fintype X] [DecidableEq X] [Fintype I]
    (n:I→ℕ) (inner:∀i,Fin (n i+1)↪X) (σ:Equiv.Perm X)
    (hn:∀i,0<n i)
    (hstep:∀i (p:Fin (n i)),σ (inner i p.castSucc)=inner i p.succ):
    let Y:=markedIntervalRootSet σ n (fun i=>inner i 0)
    Y ∪ Finset.univ.image (fun i=>inner i (Fin.last (n i))) =
      Y.image σ ∪ Finset.univ.image (fun i=>inner i 0):=by
  have he:∀i,(σ^(n i)) (inner i 0)=inner i (Fin.last (n i)):=by
    intro i
    simpa using (buffered_path_follows_permutation n inner σ hstep i (Fin.last (n i))).symm
  simpa only [he] using marked_interval_boundary_identity σ n (fun i=>inner i 0) hn
end Oberwolfach
