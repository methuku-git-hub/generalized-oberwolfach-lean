module

public import Oberwolfach.ExpandedOrdinarySelectedLaw
public import Oberwolfach.OrdinaryRawWheelLawCongruence
public import Oberwolfach.ExpandedSamplePhysicalClassLaw
public import Oberwolfach.FiniteSigmaFirstMap
public import Oberwolfach.FiniteLawIntersectionLower

@[expose] public section
/-! The ordinary reference layer and the full retained class are views of
one expanded sample, even after a dependent second sampling stage. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_expanded_shared_sample_events
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (p₁ p₂ u ρ:ℝ)
    (hp₁:0≤p₁) (hp₂:0≤p₂) (hu:0≤u) (hρ:ρ≤1) (hsum:p₁+p₂+u=ρ)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
    (A:(∀e:RawWheelCoordinate V U,RawWheelCoordinateState Γ Color e)→Prop)
    (B:SimpleGraph V→Prop) (εA εB:ℝ)
    (hA:1-εA≤(FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>p₁)
      (fun _=>hp₁) (fun _=>by linarith) d hd q hq hQ s hs hS)).probability A)
    (hB:1-εB≤(FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.retentionCoin ρ (by linarith) hρ)).probability
      (fun σ=>B (retainedGraph P σ))):
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) (p₁/2) 0 (p₂/2) 0 u
      (by positivity) (by norm_num) (by positivity) (by norm_num) hu (by linarith) d hd q hq hQ s hs hS);
    1-(εA+εB)≤(μ.sigma ν).probability (fun z=>
      A (fun e=>expandedOrdinarySelectedCollapse e (z.1 e)) ∧
      B (longPhysicalStateGraph P z.1 {0,1,2,3,4})) :=by
  intro μ
  let ref:=fun (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>expandedOrdinarySelectedCollapse e (σ e)
  have hRefLaw:μ.map ref=
      FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>p₁) (fun _=>hp₁) (fun _=>by linarith) d hd q hq hQ s hs hS):=by
    have hh:=expanded_ordinary_selected_wheel_law (V:=V) (U:=U) (Γ:=Γ) (Color:=Color)
      (p₁/2) 0 (p₂/2) 0 u (by positivity) (by norm_num) (by positivity) (by norm_num) hu (by linarith) d hd q hq hQ s hs hS
    have hLaw:=ordinary_raw_wheel_law_congr (V:=V) (U:=U) (Γ:=Γ) (Color:=Color)
      (fun _=>2*(p₁/2)) (fun _=>p₁) (fun _=>by positivity) (fun _=>by linarith)
      (fun _=>hp₁) (fun _=>by linarith) (fun _=>by ring) d hd q hq hQ s hs hS
    rw [hLaw] at hh
    simpa only [μ,ref] using hh
  have hAraw:1-εA≤μ.probability (fun σ=>A (ref σ)):=by
    have hh:=finiteLaw_map_probability μ ref A
    rw [hRefLaw] at hh
    exact hh.symm ▸ hA
  have hAready:1-εA≤(μ.sigma ν).probability (fun z=>A (ref z.1)):=by
    have hh:=finiteLaw_sigma_first_probability μ ν (fun σ=>A (ref σ))
    exact hh.symm ▸ hAraw
  have hBready:1-εB≤(μ.sigma ν).probability (fun z=>B (longPhysicalStateGraph P z.1 {0,1,2,3,4})):=by
    have hh:=expanded_sample_physical_class_probability P (p₁/2) 0 (p₂/2) 0 u
      (by positivity) (by norm_num) (by positivity) (by norm_num) hu (by linarith) d hd q hq hQ s hs hS ν B
    have hprob:1-εB≤(FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.retentionCoin
        (2*(p₁/2)+2*0+2*(p₂/2)+2*0+u) (by positivity) (by linarith))).probability
        (fun σ=>B (retainedGraph P σ)):=by
      have heq:2*(p₁/2)+2*0+2*(p₂/2)+2*0+u=ρ:=by linarith
      simpa only [heq] using hB
    exact hh.symm ▸ hprob
  simpa only [sub_add_eq_sub_sub,ref] using
    finiteLaw_intersection_lower (μ.sigma ν) _ _ εA εB hAready hBready
end Oberwolfach
