module

public import Oberwolfach.OrdinarySampledMarginsSmallerBeta
public import Oberwolfach.OrdinarySampledProfileJointExists
public import Oberwolfach.OrdinarySampledProfileMarginsFixedBeta
public import Oberwolfach.OrdinarySampledProfileExists
public import Oberwolfach.OrdinarySampledProfileMargins

@[expose] public section
/-! Choose all error constants before the order threshold, then obtain an
actual sample supplying all two-hub profile inputs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_uniform_sampled_profile_property_joint_small_beta
    (r d:ℕ) (hr:2≤r) (hd:2≤d) (α pmin smin β η a b L:ℝ)
    (hα:0<α) (hpmin:0<pmin) (hsmin:0<smin) (hsmin1:smin≤1)
    (hβ:0<β) (hβmax:β≤α*pmin^2*smin^2) (hη:0<η) (ha:0≤a) (hb:0<b) (hL:0≤L):
    ∃ ε:ℝ,0<ε ∧ ∃ N:ℕ,
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],
    N≤Fintype.card V → Fintype.card U≤Fintype.card V →
    ∀ (P F:SimpleGraph V) (π:Equiv.Perm V),
    permutationConflictGraph π (3*d)≤F →
    (∀ x k,0<k→k<2*d+1→(π^k) x≠x) →
    ∀ weight:OrdinaryCycle P r→ℝ,(∀ C,0≤weight C) →
    (∀ C,a/(Fintype.card V:ℝ)^(r-2)≤weight C) →
    (∀ C,weight C≤b/(Fintype.card V:ℝ)^(r-2)) →
    (∀ v,(F.degree v:ℝ)≤L) →
    (∀ v,(1/2+α)*Fintype.card V≤(P.degree v:ℝ)) →
    (∀ x y,(∑ C,if C.val.val.Adj x y then weight C else 0)=if P.Adj x y then 1 else 0) →
    ∀ D:ℝ,(Fintype.card V:ℝ)/2≤D → D≤2*Fintype.card V →
    (∀ v,|(P.degree v:ℝ)-D|≤ε*Fintype.card V) →
    ∀ (p:ℝ) (hp:pmin≤p) (hp1:p≤1),
    ∀ (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g)) (j:Color),
    (∀ u,smin≤s u j) → (∀ u,s u j≤1) →
    let μ:=FiniteLaw.pi (rawWheelLaw (fun _ : Sym2 V=>p) (fun _=>le_trans (le_of_lt hpmin) hp) (fun _=>hp1) d hd q hq hQ s hs hS);
    ∀ E:RawWheelOutcome V U Γ Color→Prop,
    2/(Fintype.card V:ℝ)^2 < μ.probability E →
    ∃ σ:RawWheelOutcome V U Γ Color, E σ ∧ ordinarySampledProfileProperty (r:=r) P F π d σ pmin smin j β η a b := by
  obtain ⟨ρ,t,ε,hρ,ht,hε,Nmargin,hmargin⟩:=ordinary_sampled_profile_margins_smaller_beta r α pmin smin β η b L hα hpmin hsmin hβ hβmax hη hb.le hL
  obtain ⟨Nsample,hSample⟩:=ordinary_sampled_profile_property_joint_exists r d hr hd b t ρ hb ht hρ
  refine ⟨ε,hε,max Nmargin Nsample,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hu P F π hF hnoshort weight hweight hwlo hwhi hdeg hP he D hD hDhi hnear p hp hp1 q hq hQ s hs hS j hslo hshi μ E hE
  have hm:=hmargin (Fintype.card V) (by exact_mod_cast (show Nmargin≤Fintype.card V by omega)) D hD
  exact hSample V U Γ Color (by omega) hu P F π hF hnoshort weight hweight a ha hwlo hwhi
    L α hL hα.le hdeg hP he D ε hD hDhi hnear p pmin smin hpmin hp hp1 hsmin hsmin1 q hq hQ s hs hS j hslo hshi β η hm.1 hm.2 E hE
end Oberwolfach
