module

public import Oberwolfach.OrdinaryRawPairRestrictionGeometry

@[expose] public section
/-! Extend the interval laws to unused dummy hub vertices. The actual hub
restriction keeps exactly the original law, while the dummy vertices have
the same required reference-colour probability. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [LinearOrder U]

def ordinaryTwoDomainStart (q:U→Γ→ℝ):V⊕U→Γ→ℝ:=
  Sum.elim (fun _ _=>0) q

def ordinaryTwoDomainColour (s:U→Color→ℝ) (j:Color) (p:ℝ):V⊕U→Color→ℝ:=
  Sum.elim (fun _ k=>if k=j then p else 0) s

theorem ordinary_two_domain_sampling_extension (d:ℕ) (p:ℝ) (hp:0≤p) (hp1:p≤1)
    (q:U→Γ→ℝ) (hq:∀u a,0≤q u a) (hQ:∀u,∑a,q u a≤1/8)
    (s:U→Color→ℝ) (hs:∀u a,0≤s u a)
    (hS:∀u,∑a,s u a≤ intervalUncoveredProbability d (∑a,q u a))
    (j:Color) (hj:∀u,s u j=p):
    let Q:=ordinaryTwoDomainStart (V:=V) q
    let S:=ordinaryTwoDomainColour (V:=V) s j p;
    (∀u a,0≤Q u a) ∧ (∀u,∑a,Q u a≤1/8) ∧
    (∀u a,0≤S u a) ∧ (∀u,∑a,S u a≤ intervalUncoveredProbability d (∑a,Q u a)) ∧
    (∀u,S u j=p) ∧ (∀u,Q (Sum.inr u)=q u) ∧ (∀u,S (Sum.inr u)=s u):=by
  intro Q S
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro u a;cases u with
    | inl v=>simp [Q,ordinaryTwoDomainStart]
    | inr u=>exact hq u a
  · intro u;cases u with
    | inl v=>simp [Q,ordinaryTwoDomainStart]
    | inr u=>exact hQ u
  · intro u a;cases u with
    | inl v=>simp only [S,ordinaryTwoDomainColour,Sum.elim_inl]; split <;> linarith
    | inr u=>exact hs u a
  · intro u;cases u with
    | inl v=>simpa [S,Q,ordinaryTwoDomainColour,ordinaryTwoDomainStart,intervalUncoveredProbability] using hp1
    | inr u=>exact hS u
  · intro u;cases u with
    | inl v=>simp [S,ordinaryTwoDomainColour]
    | inr u=>exact hj u
  · intro u;rfl
  · intro u;rfl
end Oberwolfach
