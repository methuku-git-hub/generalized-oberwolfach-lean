module

public import Oberwolfach.LongSeedBoundsFromPreparation

@[expose] public section
/-! The fixed marked and ordinary seed weights in the long-class recipe. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]

def longAssignedMarkedSeed
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2) (K m d:ℕ) (θ D:ℝ)
    (π:Equiv.Perm (Fin n)) (weight:(Fin (m+1)→Fin n)→ℝ):
    MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ :=fun W=>
  let s:=longAssignedApproxOrdinaryWeight F hF K m θ
  let a:=longAssignedApproxMarkedWeight F hF K m θ
  let p:=(∑u,s u)/D
  let k:=(∑u,a u)/D
  weight W.1.val/(D*p^m*k*(s W.2.val)^m)

def longAssignedOrdinarySeed
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2) (K m d:ℕ) (θ D:ℝ)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (ni:Fin K→ℕ) (hni:∀i,1≤ni i)
    (w:∀i,OrdinaryCycle P (ni i+2)→ℝ):
    ∀i,OrderedOrdinaryWheel (U:=U) π (3*d) (ni i+2)→ℝ :=fun i W=>
  let s:=longAssignedApproxOrdinaryWeight F hF K m θ
  let p:=(∑u,s u)/D
  let η:=longAssignedKeptOrdinaryContribution F hF K θ i W.2/s W.2
  η*physicalOrdinaryTupleWeight (π:=π) (b:=3*d) (hni i) (w i) W.1.val/
    (((ni i+2:ℕ):ℝ)*D*p^(ni i+2)*(s W.2)^(ni i+1))
end Oberwolfach
