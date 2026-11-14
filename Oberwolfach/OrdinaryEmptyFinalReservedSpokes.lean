module

public import Oberwolfach.OrdinaryResidualAvoidsReservedSpokes
public import Oberwolfach.BufferedPathInteriorCompletion

@[expose] public section
/-! When the final marked index is empty, the old-image avoidance proved by
the matching applies to the entire glued complement embedding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X V U K J I Γ Color:Type} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V]
  [Fintype U] [DecidableEq U] [DecidableEq K] [DecidableEq J] [Fintype I]
  [Fintype Γ] [DecidableEq Γ] [Fintype Color]

theorem ordinary_empty_final_residual_avoids_reserved_spokes
    (F:SimpleGraph X) (a:ActualResidualData (K:=K) (J:=J) F)
    (hCycle:a.t.biUnion (fun j=>(a.C j).support.toFinset)⊆a.Cembed)
    (len:I→ℕ) (inner:∀i,Fin (len i+1)↪X) (hempty:IsEmpty I)
    (π:Equiv.Perm V) (d:ℕ) (hd:1≤d) (σ:RawIntervalFamilyOutcome V U Γ Color)
    (g₀ g₁:Γ) (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d σ g₀) t)
    (u:U) (color:Color) (ψ:X→V) (f:X↪V)
    (Φ g:{x:X // x∈a.remaining}→V) (B:Finset {x:X // x∈a.remaining}) (Ends:Finset V)
    (hOld:∀x∈a.oldDomain,f x=ψ x)
    (hRem:∀x:{x:X // x∈a.remaining},f x.val=Φ x)
    (hOn:∀x∈B,Φ x=g x)
    (hOutside:∀x∉B,Φ x∈rawIntervalProtectedUnassignedList π d σ g₀ g₁ t Jret u)
    (hImage:B.image g=(residualSubtypeSet a.remaining a.prescribed).image (fun x=>ψ x.val)∪Ends)
    (hEnds:Ends⊆rawIntervalProtectedUnassignedList π d σ g₀ g₁ t Jret u)
    (hOldBad:Disjoint ((a.oldDomain\bufferedPathStrictInterior len inner).image ψ)
      (rawIntervalOrdinaryOuter π d σ color u)):
    ∀x,rawIntervalFamilyState π d σ (f x,u)≠some (Sum.inr color):=by
  have hInt:bufferedPathStrictInterior len inner=∅:=by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨i,_,_⟩:=Finset.mem_biUnion.mp hx
    exact hempty.false i
  apply ordinary_residual_embedding_avoids_reserved_spokes F a hCycle π d hd σ g₀ g₁ t Jret u color
    ψ f Φ g B Ends hOld hRem hOn hOutside hImage hEnds
  simpa only [hInt,Finset.sdiff_empty] using hOldBad
end Oberwolfach
