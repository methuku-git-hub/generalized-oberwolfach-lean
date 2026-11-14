module

public import Oberwolfach.RawOrdinaryHubCounts
public import Oberwolfach.BoundedFinsetCardinality
public import Oberwolfach.EndpointRelativeCounts

@[expose] public section

/-! A single event for all independent index tests of bounded size,
under the same raw law as the rim/spoke row counts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]

def RawOrdinaryIndices (F:SimpleGraph V) (π:Equiv.Perm V) (d h:ℕ) (pH:ℝ)
    (j:Color) (t:ℝ) (σ:RawWheelOutcome V U Γ Color):Prop:=
  ∀ S:Finset V,S.card≤h → (∀ v∈S,∀ w∈S,¬F.Adj v w) →
    |((common Finset.univ S (fun v=>Finset.univ.filter (rawWheelSpokes π d σ j v))).card:ℝ)-
      pH^S.card*Fintype.card U|<t

theorem rawOrdinaryIndices_common_event (F:SimpleGraph V) (π:Equiv.Perm V)
    (ρ:Sym2 V→ℝ) (hρ:∀ e,0≤ρ e) (hρ1:∀ e,ρ e≤1)
    (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
    (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort:∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
    (hF:permutationConflictGraph π (3*d)≤F)
    (hm:0<Fintype.card U) (h:ℕ) (j:Color) (pH:ℝ) (hj:∀ u,s u j=pH) (t:ℝ) (ht:0<t):
    1-(Fintype.card V+1:ℝ)^h*
      (2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*((h+1:ℝ)*Fintype.card U))))≤
    (FiniteLaw.pi (rawWheelLaw ρ hρ hρ1 d hd q hq hQ s hs hS)).probability
      (RawOrdinaryIndices F π d h pH j t):=by
  let I:={S:Finset V//S.card≤h ∧ S.Nonempty ∧ (∀ v∈S,∀ w∈S,¬F.Adj v w)}
  have hsep (i:I):∀ x∈i.val,∀ y∈i.val,x≠y → ¬PermutationClose π (3*d) x y:=by
    intros x hx y hy hxy hclose
    exact i.property.2.2 x hx y hy (hF ⟨hxy,hclose⟩)
  have hh:=rawIntervalCommonHubs_common_event π d hd q hq hQ s hs hS hnoshort hm j pH hj
    (fun i:I=>i.val) hsep (fun i=>i.property.2.1) (h+1) (by omega) (fun i=>by have hh:=i.property.1;omega) t ht
  let μ:=rawWheelLaw ρ hρ hρ1 d hd q hq hQ s hs hS
  have hproj:=finiteLaw_pi_injective_projection_event μ Sum.inr Sum.inr_injective
    (fun ω=>∀ i:I,|(Fintype.card {u:U//∀ v∈i.val,rawIntervalFamilyState π d ω (v,u)=some (Sum.inr j)}:ℝ)-
      pH^i.val.card*Fintype.card U|<t)
  erw [←hproj] at hh
  have hc:Fintype.card I≤(Fintype.card V+1)^h:=by
    let f:I→{S:Finset V//S.card≤h}:=fun i=>⟨i.val,i.property.1⟩
    have hf:Function.Injective f:=by intro i j he;exact Subtype.ext (congrArg (fun a:{S:Finset V//S.card≤h}=>a.val) he)
    exact (Fintype.card_le_of_injective f hf).trans (boundedFinset_card h)
  have hcr:(Fintype.card I:ℝ)≤(Fintype.card V+1:ℝ)^h:=by exact_mod_cast hc
  have herr:=mul_le_mul_of_nonneg_right hcr
    (by positivity:(0:ℝ)≤2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*((h+1:ℝ)*Fintype.card U))))
  have hh':1-(Fintype.card V+1:ℝ)^h*(2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*((h+1:ℝ)*Fintype.card U))))≤
      (FiniteLaw.pi μ).probability (fun σ=>∀ i:I,
        |(Fintype.card {u:U//∀ v∈i.val,rawWheelSpokes π d σ j v u}:ℝ)-pH^i.val.card*Fintype.card U|<t):=by
    apply (sub_le_sub_left herr 1).trans
    convert hh using 1 <;> congr! <;> norm_num
  apply hh'.trans
  apply finiteLaw_probability_mono
  intro σ hσ S hS hI
  by_cases hne:S.Nonempty
  · have hi:=hσ ⟨S,hS,hne,hI⟩
    have heq:(common Finset.univ S (fun v=>Finset.univ.filter (rawWheelSpokes π d σ j v))).card=
        Fintype.card {u:U//∀ v∈S,rawWheelSpokes π d σ j v u}:=by
      rw [Fintype.card_subtype]
      congr 1
      ext u;simp [mem_common_iff]
    simpa only [heq] using hi
  · have he:S=∅:=Finset.not_nonempty_iff_eq_empty.mp hne
    subst S
    have heq:common (Finset.univ:Finset U) (∅:Finset V) (fun v=>Finset.univ.filter (rawWheelSpokes π d σ j v))=Finset.univ:=by
      ext u;simp [mem_common_iff]
    simpa only [heq,Finset.card_empty,pow_zero,one_mul,Finset.card_univ,sub_self,abs_zero] using ht

end Oberwolfach
