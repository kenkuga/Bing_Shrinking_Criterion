(**** LemmasForBSC.v ****)
Require Import ssreflect ssrbool.
Require Import MetricSpaces.
Require Export Compactness.
Require Import Completeness.
Require Import SubspaceTopology.
Require Import WeakTopology.
Require Export Subbases.
Require Import Fourier.

Section CompactComplete.

Open Scope R_scope.

Variable X:Type.
Variable d:X->X->R.

Hypothesis d_metric: metric d.
Let Xt:=  MetricTopology d d_metric. 

Lemma compact_complete : compact Xt -> complete d d_metric. 
Proof.
move=> cpt.  
red.
move=> xn xn_cchy.
set xN:Net nat_DS Xt := xn.
have cluster_pt: exists x0: point_set Xt, net_cluster_point xN x0. 
  apply compact_impl_net_cluster_point.
  apply cpt.
  constructor.
  by apply O.
destruct cluster_pt as [x0 x0_cluster].
exists x0. 
apply metric_space_net_limit with d.
apply MetricTopology_metrizable.
move=> eps eps_pos.
apply metric_space_net_cluster_point_converse 
          with (d:=d) (eps:=/2 * eps) in x0_cluster.
destruct xn_cchy with (eps:= /2 * eps) as [i0 H_cchy].
fourier.
destruct x0_cluster with i0 as [j0 [H_i0j0 H_cluster]].
exists j0.
move=> j H_j0j.
rewrite/xN.
rewrite/xN in H_cluster.
apply Rle_lt_trans with (d x0 (xn j0) + d (xn j0) (xn j)).
apply triangle_inequality.
apply d_metric.
apply Rlt_le_trans with (/2 * eps + /2 * eps).
apply Rplus_lt_compat.
apply H_cluster.
apply H_cchy.
red. 
by apply H_i0j0.
red.
apply le_trans with j0.
by apply H_i0j0.
by apply H_j0j.
fourier.
by apply MetricTopology_metrizable.
fourier.
Qed.

End CompactComplete.

(********)

Section InvImage.
Print inverse_image.

Variables X Y:Type.
Variable f:X->Y.
Variable T:Ensemble Y.

Lemma inverse_image_image: forall x:X, In (inverse_image f T) x -> In T (f x). 
Proof.
move=>x Ix.
by destruct Ix.
Qed.

End InvImage.


Section SubB.

Variable X: TopologicalSpace.
Variable SB:Family (point_set X).

Record my_subbasis : Prop:= {
  subbasis_elements : forall U:Ensemble (point_set X),
    In SB U -> open U;
  subbasis_cover: forall (U: Ensemble (point_set X)) (x :point_set X),
  In U x -> open U ->
  exists A:Type, FiniteT A /\
  exists V:A -> Ensemble (point_set X),
    (forall a:A, In SB (V a) ) /\
    In (IndexedIntersection V) x /\
    Included (IndexedIntersection V) U
}.

Print open.
Check subbasis_elements.
Check subbasis_cover.

Check open_basis_is_subbasis.
Lemma open_basis_is_subbasis: open_basis SB -> my_subbasis.
Proof. 
intros.
destruct H.
constructor.
exact open_basis_elements.
intros.
destruct (open_basis_cover x U H0 H).
destruct H1 as [? [? ?]].
exists True.
split. 
Print True_finite.
apply True_finite.
Print True_rect.
exists (True_rect x0).
repeat split;intros.
destruct a.
simpl.
assumption.
destruct a.
simpl.
assumption.
red.
intros.
destruct H4.
apply H2.
exact (H4 I).
Qed.
 
              
End SubB.

Implicit Arguments subbasis [[X]].

Section BFS.

Variable X:Type.
Variable S:Family X.

Require Import FiniteIntersections.
Check Build_TopologicalSpace_from_subbasis_subbasis.
Check @subbasis.
Print open_neighborhood_basis.


End BFS. 
 
Open Scope R_scope.

Section OpenBallinOpen.

Variable X:Type.
Variable d:X->X->R.

Hypothesis d_metric: metric d.

Let Xt := MetricTopology d d_metric.

Variable A : Ensemble (point_set Xt).

Let At := SubspaceTopology  A.
Let d_A := fun x y: point_set At =>
   d (proj1_sig x) (proj1_sig y).

Lemma d_A_metric : metric d_A.
Proof.
by apply d_restriction_metric.
Qed.


Lemma open_ball_in_open: 
 forall (x: point_set Xt) (U:Ensemble (point_set Xt)),In U x -> open U ->
          exists r:R, r>0 /\ Included (open_ball (point_set Xt) d x r) U.
Proof.
move=>x U InUx Uopen.
destruct Uopen.
destruct InUx.
have SasU: In (IndexedUnion (metric_topology_neighborhood_basis d)) S by apply H.
clear H.
Print IndexedUnion.
destruct SasU as [x' D].
destruct H.
set r0:= r - d x' x.
exists r0.
split.
destruct H1.
rewrite/r0.
fourier.
apply Inclusion_is_transitive with (open_ball X d x' r).
constructor.
apply Rle_lt_trans with (d x' x + d x x0).
by apply triangle_inequality.
have rr0: r = d x' x + r0.
rewrite/r0.
field.
rewrite rr0.
apply Rplus_lt_compat_l.
by destruct H2.
red.
move=>x0 Inob'x0.
Print FamilyUnion.
apply family_union_intro with (open_ball X d x' r).
assumption.
assumption.
Qed.

Lemma open_ball_in_subspace_open: 
 forall (a: point_set At) (U:Ensemble (point_set At)), In U a -> open U ->
          exists r:R, r>0 /\ Included (open_ball (point_set At) d_A a r) U.
Proof.
move=> a U InUa U_open.
have ExtU: exists V: Ensemble (point_set Xt), open V /\
  U = inverse_image (subspace_inc A) V.
by apply subspace_topology_topology.
destruct ExtU as [V [V_open U_invV]].
have Xball: exists r:R, r>0 /\ Included (open_ball (point_set Xt) d (proj1_sig a) r) V.
apply open_ball_in_open.
have pr_inc: proj1_sig a = subspace_inc A a by [].
rewrite pr_inc.
apply inverse_image_image.
by rewrite <- U_invV.
assumption.
destruct Xball as [r [r_pos IncOB_V]].
exists r.
apply conj.
assumption.
red.
move=>a' InOBa.
destruct InOBa as [daa'_r].
rewrite/d_A in daa'_r.
have InOBpra': In (open_ball (point_set Xt) d (proj1_sig a) r) (proj1_sig a').
by constructor.
have InVpra': In V (proj1_sig a').
apply IncOB_V.
by apply InOBpra'.
rewrite U_invV.
constructor.
have inc_proj: subspace_inc A a' = proj1_sig a' by [].
by rewrite inc_proj.
Qed.

End OpenBallinOpen.

Section MetricRestrictionMetrizes.

Variable X:Type.
Variable d:X->X->R.

Hypothesis d_metric: metric d.

Let Xt := MetricTopology d d_metric.

Variable A : Ensemble (point_set Xt).

Let At := SubspaceTopology  A.
Let d_A := fun x y: point_set At =>
   d (proj1_sig x) (proj1_sig y).


Lemma d_restriction_metrizes: metrizes At d_A. 
constructor.
move=> U MNBU.
destruct MNBU. 
constructor.
Print subspace_inc.
have inv_oball: open_ball (point_set At) d_A x r = 
 inverse_image (@subspace_inc Xt A) (open_ball (point_set Xt) d (proj1_sig x) r).
apply Extensionality_Ensembles;split;red;intros.
constructor.
simpl.
destruct H0.
rewrite/d_A in H0.
rewrite/subspace_inc.
constructor.
assumption.
constructor.
rewrite/d_A.
destruct H0.
destruct H0.
rewrite/subspace_inc in H0.
assumption.
rewrite inv_oball.
apply (subspace_inc_continuous  Xt A).
have ob_oN: 
In (metric_topology_neighborhood_basis d (proj1_sig x))
    (open_ball (point_set Xt) d (proj1_sig x) r).
apply intro_open_ball. 
assumption.
have d_metrizes: metrizes Xt d.
by apply MetricTopology_metrizable.
Print open_neighborhood_basis.
have onb: open_neighborhood (open_ball (point_set Xt) d (proj1_sig x) r) (proj1_sig x).
apply d_metrizes.
assumption.
destruct onb.
assumption.
constructor.
rewrite metric_zero.
red in H.
assumption.
apply d_restriction_metric.
assumption.
move=> U onUx.
destruct onUx.
have U': exists U':Ensemble (point_set Xt), open U' /\ 
   U = inverse_image (@subspace_inc Xt A) U'
by apply subspace_topology_topology.
destruct U' as [U' [U'open U_U']]. 
have ObX: exists r:R, r>0 /\ Included (open_ball (point_set Xt) d (proj1_sig x) r) U'.
apply open_ball_in_open.
rewrite/(subspace_inc A) in U_U'.
apply inverse_image_image.
simpl.
simpl in U_U'.
by rewrite<- U_U'.
assumption.
destruct ObX as [r [r_pos IobU']].
Print open_ball.
set V:= open_ball (point_set At) d_A x r.
exists V.
split.
rewrite/V.
constructor.
assumption.
red.
move=>a InVa.
destruct InVa as [dxar].
rewrite/d_A in dxar.
have pra:
 In (open_ball (point_set Xt) d (proj1_sig x) r) 
    (proj1_sig a).
by constructor.
have praU': In U' (proj1_sig a).
by apply IobU'. 
rewrite U_U'.
constructor.
by rewrite/subspace_inc.
Qed.

End MetricRestrictionMetrizes.
