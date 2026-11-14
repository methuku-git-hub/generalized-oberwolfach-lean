module

public import Oberwolfach.ResidualFullSelectionArithmetic
public import Oberwolfach.ResidualRunFamilyCounts

@[expose] public section
/-! Compare the actual remainder with the remainder for which every
segment is selected. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V I J:Type} [Fintype V] [DecidableEq V] [DecidableEq I] [DecidableEq J]

theorem residual_actual_full_selection_comparison (F:SimpleGraph V)
    (s₁ s₂:Finset I) (hs:Disjoint s₁ s₂) (u v:I→V) (P:∀i,F.Walk (u i) (v i))
    (hp:∀i∈s₁∪s₂,(P i).IsPath)
    (hP:(↑(s₁∪s₂):Set I).PairwiseDisjoint (fun i=>(P i).support.toFinset))
    (c d:ℕ) (hc:1≤c) (hd:0<d) (hlen:∀i∈s₁∪s₂,(P i).length=c*d+4)
    (T:I→Finset ℕ) (hT:∀i,T i⊆Finset.range d)
    (t:Finset J) (root:J→V) (C:∀j,F.Walk (root j) (root j))
    (hcross:∀i∈s₁∪s₂,∀j∈t,Disjoint (P i).support.toFinset (C j).support.toFinset):
    let rem:=fun (S:I→Finset ℕ) (hS:∀i∈s₂,S i⊆Finset.range d)=>
      let Z:=DeletedPathIndex s₁ s₂ d S
      let U:Z→V:=deletedPathStart F s₁ s₂ u v P c d S
      let W:Z→V:=deletedPathEnd F s₁ s₂ u v P c d S
      let paths:∀z:Z,F.Walk (U z) (W z):=deletedPathWalk F s₁ s₂ u v P c d S hS
      Finset.univ \ ((t.biUnion (fun j=>(C j).support.toFinset)) ∪
        Finset.univ.biUnion (fun z=>(paths z).support.toFinset \ {U z,W z}))
    let full:=fun _ : I=>Finset.range d
    let R:=rem T (fun i _=>hT i)
    let Rfull:=rem full (fun _ _ x hx=>hx)
    let missing:=∑i∈s₂,(d-(T i).card);
    Rfull.card+(t.biUnion (fun j=>(C j).support.toFinset)).card+
        (c*d-1)*(s₁.card+s₂.card)=Fintype.card V ∧
      Rfull.card≤R.card ∧ R.card≤Rfull.card+(c+1)*missing := by
  let full:I→Finset ℕ:=fun _=>Finset.range d
  have hT':∀i∈s₂,T i⊆Finset.range d:=fun i _=>hT i
  have hfull':∀i∈s₂,full i⊆Finset.range d:=fun _ _ x hx=>hx
  let rem:=fun (S:I→Finset ℕ) (hS:∀i∈s₂,S i⊆Finset.range d)=>
    let Z:=DeletedPathIndex s₁ s₂ d S
    let U:Z→V:=deletedPathStart F s₁ s₂ u v P c d S
    let W:Z→V:=deletedPathEnd F s₁ s₂ u v P c d S
    let paths:∀z:Z,F.Walk (U z) (W z):=deletedPathWalk F s₁ s₂ u v P c d S hS
    Finset.univ \ ((t.biUnion (fun j=>(C j).support.toFinset)) ∪
      Finset.univ.biUnion (fun z=>(paths z).support.toFinset \ {U z,W z}))
  let R:=rem T hT'
  let Rfull:=rem full hfull'
  let q:=∑i∈s₂,(T i).card
  let missing:=∑i∈s₂,(d-(T i).card)
  let runs:=∑i∈s₂,(selectedSegmentRuns d (T i)).card
  let Ccard:=(t.biUnion (fun j=>(C j).support.toFinset)).card
  have hR:=residual_actual_vertex_count F s₁ s₂ hs u v P hp hP c d (by omega) hd hlen T hT' t root C hcross
  have hfull:=residual_actual_vertex_count F s₁ s₂ hs u v P hp hP c d (by omega) hd hlen full hfull' t root C hcross
  have hruns:=maximal_run_family_counts s₂ d hd T hT'
  have hrunsfull:=maximal_run_family_counts s₂ d hd full hfull'
  dsimp only at hR hfull hruns hrunsfull
  have hmissingfull:(∑i∈s₂,(d-(full i).card))=0:=by simp [full]
  have hqfull:(∑i∈s₂,(full i).card)=d*s₂.card:=by simp [full,Nat.mul_comm]
  rw [hmissingfull] at hrunsfull
  have hrunfull:(∑i∈s₂,(selectedSegmentRuns d (full i)).card)=s₂.card:=by omega
  rw [hqfull,hrunfull] at hfull
  have hqle:q≤d*s₂.card:=by
    dsimp [q]
    calc
      _ ≤ ∑ _i∈s₂,d := by
        apply Finset.sum_le_sum
        intro i hi
        have hh:=Finset.card_le_card (hT i)
        simpa using hh
      _ = _ := by simp [Nat.mul_comm]
  have hq:q+missing=d*s₂.card:=by
    dsimp [q,missing]
    have hh:=hruns.2.2.2
    omega
  have hupper:runs≤s₂.card+missing:=hruns.2.1
  have hlower:s₂.card≤runs+missing:=hruns.2.2.1
  change R.card+Ccard+c*d*s₁.card+c*q=Fintype.card V+s₁.card+runs at hR
  change Rfull.card+Ccard+c*d*s₁.card+c*(d*s₂.card)=Fintype.card V+s₁.card+s₂.card at hfull
  have result:=residual_full_selection_comparison_arithmetic R.card Rfull.card
    (Fintype.card V+s₁.card) Ccard (c*d*s₁.card) q s₂.card runs missing c d hc hR hfull hq hupper hlower
  have hcpos:0<c*d:=Nat.mul_pos (by omega) hd
  have hcd:c*d-1+1=c*d:=by omega
  have hbase:Rfull.card+Ccard+(c*d-1)*(s₁.card+s₂.card)=Fintype.card V := by
    nlinarith
  exact ⟨hbase,result⟩
end Oberwolfach
