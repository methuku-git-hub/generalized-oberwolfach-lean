module

public import Oberwolfach.BufferedEmbeddingAvoidsLabels
public import Oberwolfach.ResidualActualData
public import Oberwolfach.RawIntervalProtectedUnassignedList

@[expose] public section
/-! If the already embedded source avoids the reserved ordinary labels,
then the glued residual embedding avoids them as well. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X V U K J Γ Color:Type} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V]
  [Fintype U] [DecidableEq U] [DecidableEq K] [DecidableEq J]
  [Fintype Γ] [DecidableEq Γ] [Fintype Color]

theorem ordinary_residual_embedding_avoids_reserved_spokes
    (F:SimpleGraph X) (a:ActualResidualData (K:=K) (J:=J) F)
    (hCycle:a.t.biUnion (fun j=>(a.C j).support.toFinset)⊆a.Cembed)
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
    (hOldBad:Disjoint (a.oldDomain.image ψ) (rawIntervalOrdinaryOuter π d σ color u)):
    ∀x,rawIntervalFamilyState π d σ (f x,u)≠some (Sum.inr color):=by
  have hPres:a.prescribed⊆a.oldDomain:=by
    intro x hx
    simp only [ActualResidualData.oldDomain,Finset.mem_union]
    exact Or.inl (Or.inl (Or.inl hx))
  have hList:Disjoint (rawIntervalProtectedUnassignedList π d σ g₀ g₁ t Jret u)
      (rawIntervalOrdinaryOuter π d σ color u):=
    (raw_interval_protected_unassigned_avoids_labels π d hd σ g₀ g₁ t Jret u color).1
  have hh:=buffered_embedding_avoids_labels a.oldDomain a.remaining a.prescribed
    (a.old_domain_union_remaining hCycle) hPres ψ f Φ g B Ends
    (rawIntervalProtectedUnassignedList π d σ g₀ g₁ t Jret u)
    (rawIntervalOrdinaryOuter π d σ color u) hOld hRem hOn hOutside hImage hEnds hOldBad hList
  intro x hx
  apply hh x
  simp only [rawIntervalOrdinaryOuter,Finset.mem_filter,Finset.mem_univ,true_and]
  exact hx
end Oberwolfach
