module

public import Oberwolfach.ExpandedBinaryColourProjection
public import Oberwolfach.ExpandedBinaryClassGraph
public import Oberwolfach.ClassColourRetainedGraphAlignment

@[expose] public section
/-! The physical selected class of the retained expanded construction has
exactly the independent edge-retention law, even after dependent retention. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem expanded_sample_physical_class_probability
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)) (Good:SimpleGraph V→Prop):
    ((FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)).sigma ν).probability
      (fun z=>Good (longPhysicalStateGraph P z.1 {0,1,2,3,4}))=
    (FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.retentionCoin (2*p+2*k+2*p₂+2*k₂+u)
      (by positivity) hsum)).probability (fun σ=>Good (retainedGraph P σ)) :=by
  let ρ:=expandedBinaryProbability p k p₂ k₂ u
  let hρ:=expanded_binary_probability_nonneg p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum
  let htotal:=expanded_binary_probability_sum p k p₂ k₂ u
  let μ:=FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.categorical ρ hρ htotal)
  have hproj:=expanded_binary_colour_probability_after_retention p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS ν
    (fun c=>Good (edgeColourGraph P c 0))
  have hmap:=finiteLaw_map_probability μ (fun c e=>classColourMembership 0 (c e)) (fun σ=>Good (retainedGraph P σ))
  have hL:((FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)).sigma ν).probability
      (fun z=>Good (longPhysicalStateGraph P z.1 {0,1,2,3,4}))=μ.probability (fun c:Sym2 V→Fin 2=>Good (edgeColourGraph P c 0)):=by
    convert hproj using 1
    congr 1
    funext z
    rw [expanded_binary_class_graph P z.1]
  have hR:μ.probability (fun c=>Good (edgeColourGraph P c 0))=
      (FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.retentionCoin (2*p+2*k+2*p₂+2*k₂+u) (by positivity) hsum)).probability
        (fun σ=>Good (retainedGraph P σ)):=by
    have hh:=categorical_class_membership_product (E:=Sym2 V) ρ hρ htotal 0
    have hm:=hmap
    rw [hh] at hm
    have hevent:(fun c:Sym2 V→Fin 2=>Good (retainedGraph P (fun e=>classColourMembership 0 (c e))))=
        (fun c:Sym2 V→Fin 2=>Good (edgeColourGraph P c 0)):=by
      funext c
      rw [class_colour_membership_retained_graph]
    rw [hevent] at hm
    simpa only [ρ,expandedBinaryProbability,Matrix.cons_val_zero] using hm.symm
  exact hL.trans hR
end Oberwolfach
