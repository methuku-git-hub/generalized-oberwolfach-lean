module

public import Oberwolfach.RawMarkedRetentionLocalProjection
public import Oberwolfach.RawUniformRetentionLocalEvent

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_marked_retention_local_event
    (d:ℕ) (hd:2≤d) (p ζ c δ:ℝ) (hp:0<p) (hζ:0<ζ) (hc:0<c) (hδ:0<δ):
    ∃m N:ℕ,1≤m ∧ 1≤N ∧ ∀(V U Γ Color:Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [Nonempty V]
      [LinearOrder V] [DecidableEq U],
    N≤Fintype.card V → Fintype.card U≤Fintype.card V →
    ∀(I:Type) (T:Finset I) (A:I→Finset V) (H:I→Finset U),
    (∀i∈T,m≤(A i).card) → Set.InjOn (fun i=>(A i).card) T →
    (∀i∈T,(H i).card≤(A i).card) → (∀i∈T,c*((A i).card:ℝ)≤(H i).card) →
    ∀(π:Equiv.Perm V) (p₁ k₁:ℝ) (hp₁:0≤p₁) (hk₁:0≤k₁) (hphys:2*p₁+2*k₁≤1) (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j ≤ intervalUncoveredProbability d (∑g,q u g))
    (g:Γ) (t₀:ℝ), (∀u,q u g=t₀) → p*Fintype.card V≤t₀*Fintype.card U →
    (∀i∈T,∀x,π x∈A i↔x∈A i) →
    1-δ≤(rawMarkedRetentionLaw π d hd g p₁ k₁ hp₁ hk₁ hphys q hq hQ s hs hS).probability
      (fun z=>∀i∈T,RetainedRestrictionLocalGood π d (fun e=>z.1 (Sum.inr e)) g
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g)) (A i) (H i) ζ z.2):=by
  obtain ⟨m,N,hm,hN,hraw⟩:=raw_uniform_retention_local_event d hd p ζ c δ hp hζ hc hδ
  refine ⟨m,N,hm,hN,?_⟩
  intro V U Γ Color _ _ _ _ _ _ _ hn hu I T A H hmin hinj hHup hHlo π p₁ k₁ hp₁ hk₁ hphys hnoshort q hq hQ s hs hS g t₀ hg hmass hInv
  have hh:=hraw V U Γ Color hn hu I T A H hmin hinj hHup hHlo π hnoshort q hq hQ s hs hS g t₀ hg hmass hInv
  have hproj:=raw_marked_retention_local_projection_probability π d hd g p₁ k₁ hp₁ hk₁ hphys q hq hQ s hs hS I T A H ζ
  rw [hproj]
  exact hh
end Oberwolfach
