module

public import Oberwolfach.OrdinaryRawGlobalDegreeFromProfiles
public import Oberwolfach.OrdinaryPhysicalDegreeFromSampleEdit

@[expose] public section
/-! The original full-domain singleton tests and one actual physical edit
bound give an explicit maximum-degree cap for the edited ordinary host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_physical_degree_cap_from_global_profiles
    (P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ) (pR pH tR tH L:ℝ)
    (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color)
    (hpR:0≤pR) (hpH:0≤pH) (htR:0≤tR) (htH:0≤tH) (hL:0≤L)
    (hs:∀u,s u j=pH)
    (hrows:RawOrdinaryRows P π d 3 Finset.univ pR s j tR raw)
    (hindices:RawOrdinaryDomainIndices F π d 3 Finset.univ pH j tH raw)
    (hedit:∀w:V⊕U,((changed ((ordinaryPhysicalGraph (rawWheelGraph P raw) (rawWheelSpokes π d raw j)).neighborFinset w)
      ((ordinaryPhysicalGraph Q H).neighborFinset w)).card:ℝ)≤L):
    ∃D:ℕ,(∀w:V⊕U,(ordinaryPhysicalGraph Q H).degree w≤D) ∧
      (D:ℝ)≤max ((pR*Fintype.card V+tR)+(pH*Fintype.card U+tH))
        (pH*Fintype.card V+tR)+L+1:=by
  have hraw:=ordinary_raw_global_degree_from_profiles P F π d pR pH tR tH s j raw hs hrows hindices
  have hr:∀v,((rawWheelGraph P raw).degree v:ℝ)≤pR*Fintype.card V+tR:=by
    intro v
    have hv:(P.degree v:ℝ)≤Fintype.card V:=by exact_mod_cast (P.degree_lt_card_verts v).le
    have hh:=mul_le_mul_of_nonneg_left hv hpR
    linarith only [hraw.1 v,hh]
  have hb:0≤max ((pR*Fintype.card V+tR)+(pH*Fintype.card U+tH))
      (pH*Fintype.card V+tR)+L:=by positivity
  exact ordinary_physical_degree_cap_from_sample_edit (rawWheelGraph P raw) Q (rawWheelSpokes π d raw j) H
    (pR*Fintype.card V+tR) (pH*Fintype.card U+tH) (pH*Fintype.card V+tR) L
    hr hraw.2.1 hraw.2.2 hedit hb
end Oberwolfach
