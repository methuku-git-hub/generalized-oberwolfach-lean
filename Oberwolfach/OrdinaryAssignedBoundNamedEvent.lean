module

public import Oberwolfach.OrdinaryAssignedNamedClassEvent

@[expose] public section
/-! Restate the proved fixed-length event with its probability predicate
named, without changing the product law or its parameter order. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) namedBoundFiniteEquality (n:ℕ) : DecidableEq (Fin n) := Classical.decEq (Fin n)

theorem ordinary_assigned_bound_named_class_event
    (m d K:ℕ) (hm:3≤m) (hd:2≤d)
    (θhost α ρ₀ s₀ ω βP ηP row ηH L:ℝ) (hρ₀:0<ρ₀) (hs₀:0<s₀)
    (kH:ℕ) (βH c B:ℝ) (N:ℕ)
    (hbound:ordinaryAssignedClassAtBound m d K hm hd θhost α ρ₀ s₀ ω βP ηP row ηH L hρ₀ hs₀ kH βH c B N):
    ∀(n:ℕ),N≤n→0<n→∀(R:SimpleGraph (Fin n)) (D:ℕ),
      R.IsRegularOfDegree D→(∀v,(θhost+α)*n≤(R.degree v:ℝ))→
    ∃weight:OrdinaryCycle R (m+1)→ℝ,
      (∀C,c/(n:ℝ)^((m+1)-2)≤weight C ∧ weight C≤B/(n:ℝ)^((m+1)-2)) ∧
      (∀x y,(∑C,if C.val.val.Adj x y then weight C else 0)=if R.Adj x y then 1 else 0) ∧
    ∀(U:Type) [Fintype U] [DecidableEq U],ω*n≤(Fintype.card U:ℝ)→Fintype.card U≤n→
    ∀(i₀:Fin K) (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
      (Allowed:Set ℕ) (hAllowed:∀w,AllowedCycleLengths (F w) Allowed)
      (hclass:∀w,factorPreparationClass (F w) K=some i₀)
      (sOrd θfreq caux:ℝ) (hslo:s₀/2≤sOrd) (hshi:sOrd≤s₀)
      (hsclass:sOrd≤1/(2*(K:ℝ))) (hθfreq:0<θfreq) (hθfreq1:θfreq≤1/100)
      (hcaux:8≤caux) (hda:1/θfreq≤d),
    let ρ:=initialIndexDensity U D;
    ρ₀≤ρ→ρ≤1→
    ∀(Conflict:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)),
      (∀v,(Conflict.degree v:ℝ)≤L)→permutationConflictGraph π (3*d)≤Conflict→
      (∀x l,0<l→l<2*d+1→(π^l) x≠x)→
    ordinaryAssignedNamedClassEvent m d K hm hd i₀ θhost α ρ₀ s₀ βP ηP row ηH βH c B hρ₀ hs₀ kH
      R Conflict π F hF sOrd θfreq caux ρ weight :=by
  intro n hn hn0 R D hR hgraph
  obtain ⟨weight,hw,he,hrest⟩:=hbound n hn hn0 R D hR hgraph
  refine ⟨weight,hw,he,?_⟩
  intro U _ _ hUlo hUhi i₀ F hF Allowed hAllowed hclass sOrd θfreq caux hslo hshi hsclass hθfreq hθfreq1 hcaux hda ρ hρlo hρhi Conflict π hConflict hsub hshort
  exact hrest U hUlo hUhi i₀ F hF Allowed hAllowed hclass sOrd θfreq caux hslo hshi hsclass
    hθfreq hθfreq1 hcaux hda hρlo hρhi Conflict π hConflict hsub hshort
end Oberwolfach
