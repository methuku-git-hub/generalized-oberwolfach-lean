module

public import Oberwolfach.RawIntervalHubStartInvCard
public import Oberwolfach.FiniteLawSigmaProjection
public import Oberwolfach.MarkedExpandedRawLaw

@[expose] public section
/-! The uniform raw hub-start count is a high-probability event already in
the original retained experiment, and can therefore join any prior event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_marked_hub_starts_high_probability
    (d:ℕ) (hd:2≤d) (δ:ℝ) (hδ:0<δ):
    ∃N:ℕ,∀(V:Type) [Fintype V] [LinearOrder V],N≤Fintype.card V→
    ∀(U Γ Color:Type) [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq U],
    Fintype.card U≤Fintype.card V→Fintype.card Γ≤2→
    ∀(π:Equiv.Perm V) (p k:ℝ) (hp:0≤p) (hk:0≤k) (hsum:2*p+2*k≤1)
    (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (F:RawMarkedOutcome V U Γ Color→Type) [∀a,Fintype (F a)] (ν:∀a,FiniteLaw (F a)),
    1-δ≤((FiniteLaw.pi (rawMarkedWheelLaw (V:=V) p k hp hk hsum d hd q hq hQ s hs hS)).sigma ν).probability
      (fun z=>∀u g,|rawIntervalHubStartCount π d g (fun e=>z.1 (Sum.inr e)) u-(Fintype.card V:ℝ)*q u g/d|<
        (Fintype.card V:ℝ)^(3/4:ℝ)/d):=by
  obtain ⟨N₀,hN₀⟩:=raw_expanded_hub_starts_highProbability_invCard d hd
  obtain ⟨N₁,hN₁⟩:=exists_nat_gt (1/δ)
  refine ⟨max N₀ N₁,?_⟩
  intro V _ _ hn U Γ Color _ _ _ _ hU hΓ π p k hp hk hsum q hq hQ s hs hS hnoshort F _ ν
  have hn1:(1/δ:ℝ)<Fintype.card V:=lt_of_lt_of_le hN₁ (by exact_mod_cast (le_trans (le_max_right N₀ N₁) hn))
  have hnpos:(0:ℝ)<Fintype.card V:=lt_trans (by positivity) hn1
  have hsmall:1/(Fintype.card V:ℝ)≤δ:=by
    apply (div_le_iff₀ hnpos).2
    have hh:1<δ*(Fintype.card V:ℝ):=by
      have :=(div_lt_iff₀ hδ).1 hn1
      nlinarith
    linarith
  have hsum':2*p+2*k+2*(0:ℝ)+2*(0:ℝ)+0≤1:=by linarith
  let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k 0 0 0 hp hk (by norm_num) (by norm_num) (by norm_num)
    hsum' d hd q hq hQ s hs hS)
  let f:=fun (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
  let E:=fun z:(Σa:RawMarkedOutcome V U Γ Color,F a)=>∀u g,
    |rawIntervalHubStartCount π d g (fun e=>z.1 (Sum.inr e)) u-(Fintype.card V:ℝ)*q u g/d|<
      (Fintype.card V:ℝ)^(3/4:ℝ)/d
  have hh:=hN₀ V (le_trans (le_max_left N₀ N₁) hn) U Γ Color hU hΓ π p k 0 0 0 hp hk
    (by norm_num) (by norm_num) (by norm_num) hsum' q hq hQ s hs hS hnoshort F ν
  have hproj:μ.map f=FiniteLaw.pi (rawMarkedWheelLaw (V:=V) p k hp hk hsum d hd q hq hQ s hs hS):=by
    convert raw_expanded_marked_wheel_law_projection (V:=V) p k 0 0 0 hp hk
      (by norm_num) (by norm_num) (by norm_num) hsum' d hd q hq hQ s hs hS using 1 <;> congr 3 <;> exact Subsingleton.elim _ _
  have hevent:(fun z:(Σω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,F (f ω))=>E ⟨f z.1,z.2⟩)=
      (fun z=>∀u g,|rawIntervalHubStartCount π d g (fun e=>z.1 (Sum.inr e)) u-(Fintype.card V:ℝ)*q u g/d|<
        (Fintype.card V:ℝ)^(3/4:ℝ)/d):=by rfl
  have hprojection:=finiteLaw_sigma_projection_probability μ f ν E
  rw [hproj,hevent] at hprojection
  rw [←hprojection]
  exact (sub_le_sub_left hsmall 1).trans hh
end Oberwolfach
