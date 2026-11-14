module

public import Oberwolfach.OrdinaryInducedColourCutProbability
public import Oberwolfach.RawPhysicalOrientation

@[expose] public section
/-! The induced rim cut holds with high probability under the original
    ambient wheel law and its independent physical direction coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_induced_rim_cut_high_probability
    (α pstar:ℝ) (hα:0<α) (hα1:α≤1/2) (hpstar:0<pstar) (q₀:ℕ):
    ∃N:ℕ,∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀(P:SimpleGraph V) (I:Finset V),N≤I.card→
      (∀v:I,(1/2+α)*I.card≤((P.induce (I:Set V)).degree v:ℝ))→
    ∀(p:ℝ) (hp:0≤p) (hp1:p≤1),pstar≤p→
    ∀d:ℕ,∀hd:2≤d,
    ∀(q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
      (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
      (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g)),
    1-1/(I.card:ℝ)^q₀≤
      ((FiniteLaw.pi (rawWheelLaw (fun _:Sym2 V=>p) (fun _=>hp) (fun _=>hp1) d hd q hq hQ s hs hS)).prod
        (FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.fairCoin))).probability (fun z=>
      OrdinaryInducedRimCutEvent I (sampledOrientation (rawWheelGraph P z.1) z.2) α pstar):=by
  obtain ⟨N,hN⟩:=ordinary_induced_colour_cut_probability α pstar hα hα1 hpstar q₀
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P I hn hP p hp hp1 hplo d hd q hq hQ s hs hS
  have hh:=hN V P I hn hP (retentionColourProbability p) (retentionColourProbability_nonneg p hp hp1)
    (retentionColourProbability_sum p) (by simpa [retentionColourProbability] using hplo)
  rw [rawWheel_orientation_probability P p hp hp1 d hd q hq hQ s hs hS (fun A=>OrdinaryInducedRimCutEvent I A α pstar)]
  convert hh using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
end Oberwolfach
