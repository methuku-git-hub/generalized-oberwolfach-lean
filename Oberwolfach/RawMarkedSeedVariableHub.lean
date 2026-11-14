module

public import Oberwolfach.RawMarkedSeedExpectations

@[expose] public section
/-! Root-omitted candidate products with hub-dependent interval and spoke
marginals. Zero marked probability is allowed away from the tested positive
root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
  {m d:ℕ} {π:Equiv.Perm V} {H₀ Hₖ:V→U→Prop}

theorem rawMarkedWheelMarginal_eq_at_hub
    (P:SimpleGraph V)
    (W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d) H₀ Hₖ)
    (p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color)
    (root:((V×V)⊕(V×V))⊕(Bool×V×U)) (hroot:root∈typedMarkedOccurrenceResources W):
    rawMarkedWheelMarginal P π d p k q s g j root=
    rawMarkedWheelMarginal P π d p k (fun _ _=>q W.2.val g) (fun _ _=>s W.2.val j) g j root:=by
  cases root with
  | inl e=>cases e <;> rfl
  | inr x=>
    obtain ⟨i,hi⟩:=(typedMarkedOccurrenceResources_spoke W x).mp hroot
    subst x
    simp [rawMarkedWheelMarginal]

theorem rawMarkedSeed_candidate_variable_hub_mean
    (P:SimpleGraph V) (hm:1≤m)
    (W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d) H₀ Hₖ)
    (p k D w₀:ℝ) (hp:p≠0) (hk:k≠0) (hD:D≠0)
    (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color) (hs:s W.2.val j≠0)
    (hP:∀ i:Fin m,P.Adj (W.1.val i.castSucc) (W.1.val i.succ))
    (hK:P.Adj (W.1.val (Fin.last m)) (π (W.1.val 0)))
    (root:((V×V)⊕(V×V))⊕(Bool×V×U)) (hroot:root∈typedMarkedOccurrenceResources W)
    (hφ:rawMarkedWheelMarginal P π d p k q s g j root≠0):
    (w₀/(D*p^m*k*(s W.2.val j)^m)) *
      (∏ a∈typedMarkedOccurrenceResources W\{root},rawMarkedWheelMarginal P π d p k q s g j a)=
      w₀*q W.2.val g/(D*rawMarkedWheelMarginal P π d p k q s g j root):=by
  let q₀:U→Γ→ℝ:=fun _ _=>q W.2.val g
  let s₀:U→Color→ℝ:=fun _ _=>s W.2.val j
  have hmarg (a:((V×V)⊕(V×V))⊕(Bool×V×U)) (ha:a∈typedMarkedOccurrenceResources W):
      rawMarkedWheelMarginal P π d p k q s g j a=rawMarkedWheelMarginal P π d p k q₀ s₀ g j a:=
    rawMarkedWheelMarginal_eq_at_hub P W p k q s g j a ha
  have hφ₀:rawMarkedWheelMarginal P π d p k q₀ s₀ g j root≠0:=by rw [←hmarg root hroot];exact hφ
  have hh:=rawMarkedSeed_candidate_mean P hm W p k (s W.2.val j) (q W.2.val g) D w₀
    hp hk hs hD q₀ s₀ g j (by intro u;rfl) (by intro u;rfl) hP hK root hroot hφ₀
  have hprod:(∏ a∈typedMarkedOccurrenceResources W\{root},rawMarkedWheelMarginal P π d p k q s g j a)=
      ∏ a∈typedMarkedOccurrenceResources W\{root},rawMarkedWheelMarginal P π d p k q₀ s₀ g j a:=by
    apply Finset.prod_congr rfl
    intro a ha
    exact hmarg a (Finset.mem_sdiff.mp ha).1
  rw [hprod,hmarg root hroot]
  exact hh
end Oberwolfach
