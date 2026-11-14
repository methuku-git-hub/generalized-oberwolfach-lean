module

public import Oberwolfach.LocalMatchingTestDefect

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def longLocalVertexSpokeIncidence {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (S:Finset (LongRawHubResource n U)) (g:Bool) (v:Fin n) (H:Finset U):Finset S :=
  (longRawIncidenceSet S (.inr (g,.inl v))).filter (fun z=>∃w∈H,z.val=Sum.inr (g,v,w))

def longLocalHubSpokeIncidence {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (S:Finset (LongRawHubResource n U)) (g:Bool) (w:U) (A:Finset (Fin n)):Finset S :=
  (longRawIncidenceSet S (.inr (g,.inr w))).filter (fun z=>∃v∈A,z.val=Sum.inr (g,v,w))

theorem long_local_vertex_spoke_defects_eq_sdiff {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (S:Finset (LongRawHubResource n U)) (C:Finset S) (g:Bool) (v:Fin n) (H:Finset U):
    longLocalVertexSpokeDefects S C g v H = longLocalVertexSpokeIncidence S g v H\C:=by
  ext z
  simp only [longLocalVertexSpokeDefects,longLocalVertexSpokeIncidence,Finset.mem_filter,Finset.mem_sdiff]
  tauto

theorem long_local_hub_spoke_defects_eq_sdiff {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (S:Finset (LongRawHubResource n U)) (C:Finset S) (g:Bool) (w:U) (A:Finset (Fin n)):
    longLocalHubSpokeDefects S C g w A = longLocalHubSpokeIncidence S g w A\C:=by
  ext z
  simp only [longLocalHubSpokeDefects,longLocalHubSpokeIncidence,Finset.mem_filter,Finset.mem_sdiff]
  tauto

theorem long_local_vertex_spoke_defect_from_matching_test
    {n:ℕ} {U C:Type} [Fintype U] [DecidableEq U] [Fintype C] [DecidableEq C]
    (S:Finset (LongRawHubResource n U)) (g:Bool) (v:Fin n) (H:Finset U)
    (M:Finset C) (Q:C→Finset S) (weight:C→ℝ) (ε γ:ℝ)
    (hγ:0≤γ) (hγ1:γ≤1) (hε:0≤ε)
    (hdis:∀c∈M,∀d∈M,c≠d→Disjoint (Q c) (Q d)):
    let I:=longLocalVertexSpokeIncidence S g v H
    (1-ε)*(I.card:ℝ)≤∑c,weight c*((Q c∩I).card:ℝ)→
    (1-γ)*(∑c,weight c*((Q c∩I).card:ℝ))≤∑c∈M,((Q c∩I).card:ℝ)→
    ((longLocalVertexSpokeDefects S (M.biUnion Q) g v H).card:ℝ)≤(ε+γ)*I.card:=by
  intro I hmass htest
  rw [long_local_vertex_spoke_defects_eq_sdiff]
  exact local_matching_test_defect I M Q weight ε γ hγ hγ1 hε hdis hmass htest

theorem long_local_hub_spoke_defect_from_matching_test
    {n:ℕ} {U C:Type} [Fintype U] [DecidableEq U] [Fintype C] [DecidableEq C]
    (S:Finset (LongRawHubResource n U)) (g:Bool) (w:U) (A:Finset (Fin n))
    (M:Finset C) (Q:C→Finset S) (weight:C→ℝ) (ε γ:ℝ)
    (hγ:0≤γ) (hγ1:γ≤1) (hε:0≤ε)
    (hdis:∀c∈M,∀d∈M,c≠d→Disjoint (Q c) (Q d)):
    let I:=longLocalHubSpokeIncidence S g w A
    (1-ε)*(I.card:ℝ)≤∑c,weight c*((Q c∩I).card:ℝ)→
    (1-γ)*(∑c,weight c*((Q c∩I).card:ℝ))≤∑c∈M,((Q c∩I).card:ℝ)→
    ((longLocalHubSpokeDefects S (M.biUnion Q) g w A).card:ℝ)≤(ε+γ)*I.card:=by
  intro I hmass htest
  rw [long_local_hub_spoke_defects_eq_sdiff]
  exact local_matching_test_defect I M Q weight ε γ hγ hγ1 hε hdis hmass htest
end Oberwolfach
