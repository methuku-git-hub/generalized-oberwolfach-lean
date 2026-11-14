module

public import Oberwolfach.LongOrdinaryPhysicalDeletionLoad
public import Oberwolfach.LongAssignedSeedFunctionBounds

@[expose] public section
/-! The original assigned ordinary seed weights retain their target-load
estimates under every later bounded physical-rim deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_assigned_ordinary_seed_load_after_physical_deletion
    (hn:0<n) (hu:Fintype.card U≤n)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (m d:ℕ) (θ D:ℝ) (P Del:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (ni:Fin K→ℕ) (hni:∀i,1≤ni i)
    (w:∀i,OrdinaryCycle P (ni i+2)→ℝ) (B:Fin K→ℝ) (hB:∀i,0≤B i)
    (hw:∀i W,0≤longAssignedOrdinarySeed F hF K m d θ D P π ni hni w i W ∧
      longAssignedOrdinarySeed F hF K m d θ D P π ni hni w i W≤B i/(n:ℝ)^(ni i+1))
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool) (δ:ℝ)
    (hDel:∀x,(Del.degree x:ℝ)≤δ) (i:Fin K) (root:LongRawHubResource n U) (target:ℝ):
    let W:=longAssignedOrdinarySeed F hF K m d θ D P π ni hni w i
    let R:=fun C=>(orderedOrdinaryResources C).map ordinaryMarkedResourceEmbedding
    let state:=longRawHubState P π d raw g j
    let S:=longRawSurvivingResources P π d raw g j Del.edgeFinset
    let survived:=fun z=>decide (z∈S)
    |resourcePatternLoad R W (fun _ _=>true) root survived-target|≤
      |resourcePatternLoad R W (fun _ _=>true) root state-target|+
        10*δ*((ni i:ℝ)+2)^4*B i/(n:ℝ) :=by
  intro W R state S survived
  have hh:=long_ordinary_fixed_load_after_physical_deletion_uniform P Del π d raw g j
    (m:=ni i+1) (b:=3*d) (by have h:=hni i;omega) hn hu W (B i) (hB i) (hw i) root target δ hDel
  dsimp only at hh
  simp only [Nat.cast_add,Nat.cast_one] at hh
  convert hh using 1 <;> congr 3
  all_goals first | exact Subsingleton.elim _ _ | ring
end Oberwolfach
