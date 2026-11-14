module

public import Oberwolfach.RawOrdinaryRowCounts
public import Oberwolfach.BoundedFinsetCardinality
public import Oberwolfach.ConditionalRealization

@[expose] public section

/-! One event controls every bounded ordinary row test on a fixed domain,
including the empty test. The test enumeration precedes the sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]

def RawOrdinaryRows (P:SimpleGraph V) (π:Equiv.Perm V) (d h:ℕ) (A:Finset V)
    (p:ℝ) (s:U→Color→ℝ) (j:Color) (t:ℝ) (σ:RawWheelOutcome V U Γ Color):Prop:=
  ∀ (S:Finset V) (J:Finset U),S.card≤h → J.card≤h →
    |((common (common A S (fun x=>(rawWheelGraph P σ).neighborFinset x)) J
      (fun u=>Finset.univ.filter (fun z=>rawWheelSpokes π d σ j z u))).card:ℝ)-
      p^S.card*(∏ u∈J,s u j)*(common A S (fun x=>P.neighborFinset x)).card|<t

theorem rawOrdinaryRows_common_event (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (p:ℝ) (hp:0≤p) (hp1:p≤1)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
    (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort:∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
    (A:Finset V) (hA:A.Nonempty) (h:ℕ) (j:Color) (t:ℝ) (ht:0<t):
    1-(Fintype.card V+1:ℝ)^h*(Fintype.card U+1:ℝ)^h*
      (2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(2*(2*(h:ℝ)+1)*A.card))))≤
    (FiniteLaw.pi (rawWheelLaw (fun _=>p) (fun _=>hp) (fun _=>hp1) d hd q hq hQ s hs hS)).probability
      (RawOrdinaryRows P π d h A p s j t):=by
  let I:={S:Finset V//S.card≤h}×{J:Finset U//J.card≤h}
  let Bad:=fun (i:I) (σ:RawWheelOutcome V U Γ Color)=>t≤
    |((common (common A i.1.val (fun x=>(rawWheelGraph P σ).neighborFinset x)) i.2.val
      (fun u=>Finset.univ.filter (fun z=>rawWheelSpokes π d σ j z u))).card:ℝ)-
      p^i.1.val.card*(∏ u∈i.2.val,s u j)*(common A i.1.val (fun x=>P.neighborFinset x)).card|
  let err:=2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(2*(2*(h:ℝ)+1)*A.card)))
  have htail (i:I):
    (FiniteLaw.pi (rawWheelLaw (fun _=>p) (fun _=>hp) (fun _=>hp1) d hd q hq hQ s hs hS)).probability (Bad i)≤err:=by
    have hh:=rawOrdinaryRowCount_tail P π d hd p hp hp1 q hq hQ s hs hS hnoshort A hA i.1.val i.2.val
      (2*h) (by have h1:=i.1.property;have h2:=i.2.property;omega) j t ht
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hh
  have hcard:Fintype.card I≤(Fintype.card V+1)^h*(Fintype.card U+1)^h:=by
    rw [Fintype.card_prod]
    exact Nat.mul_le_mul (boundedFinset_card h) (boundedFinset_card h)
  have hc:(Fintype.card I:ℝ)≤(Fintype.card V+1:ℝ)^h*(Fintype.card U+1:ℝ)^h:=by exact_mod_cast hcard
  have hh:=finiteLaw_common_event_lower
    (FiniteLaw.pi (rawWheelLaw (fun _=>p) (fun _=>hp) (fun _=>hp1) d hd q hq hQ s hs hS))
    Finset.univ Bad (fun _=>err) (fun i _=>htail i)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.mem_univ,true_implies] at hh
  apply (sub_le_sub_left (mul_le_mul_of_nonneg_right hc (by dsimp [err];positivity)) 1 |>.trans hh).trans
  apply finiteLaw_probability_mono
  intro σ hσ S J hS hJ
  exact not_le.mp (hσ (⟨S,hS⟩,⟨J,hJ⟩))

end Oberwolfach
