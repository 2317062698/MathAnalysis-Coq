Require Export A_6_5.

Module A8_1.


(* 定义：原函数 *)
Definition Primitive_f (f F: Fun) (D : sR) := Function f /\ Function F /\
D ⊂ dom[f] /\ D ⊂ dom[F] /\ 
(∀ x : R, x ∈ D -> derivative F x (F '[x]) /\ F '[x] = f[x]).


(* 定理8.1 原函存在定理 *)

(* 定理8.2  *)
Theorem Theorem8_2 : ∀ (f F : Fun)(D : sR), Primitive_f f F D ->
∀C :R, Primitive_f f  \{\λ x y, y = F [x] + \{\ λ x y, y = C \}\[x] \}\ D.
Proof. 
  intros. 
  assert(H':∀x : R, \{\ λ x y, y = C \}\[x] = C).
  { intros. Function_ass. }
  destruct H as [H[H1[H2 [H3 H4]]]].
  unfold Primitive_f in *. 
  split; auto. split.
  QED_function. split; auto.
  split. red. intros. 
  apply AxiomII. 
  exists (F[z] + C). apply AxiomII'.
  rewrite H'. auto. intros. 
  pose proof (Lemma5_12 C x).
  apply derEqual in H5 as H5'.
  assert(derivative \{\ λ x0 y,y = F [x0] + \{\ λ _ y0,y0 = C \}\ 
  [x0] \}\ x  f[x]).
  { replace f[x] with (f[x] + \{\ λ _ y,y = C \}\ '[ x]).
  apply H4 in H0 as [H0' H6].
  rewrite <- H6.
  apply Theorem5_4_1; red.
  exists (F '[x]); auto. 
  exists 0. apply Lemma5_12.
  rewrite H5'; lra. } 
  apply derEqual in H6 as H6'.
  rewrite H6'; split; auto.
Qed.






Theorem Theorem8_2': ∀ (f : Fun)(a b : R), a < b -> 
(∀F G : Fun,Primitive_f f F \(a,b\) /\ Primitive_f f G \(a, b\) -> 
∃C : R, ∀x, x ∈ \(a,b\) -> F[x] - G[x] = C).
Proof.
  intros. destruct H0. 
  red in H0, H1. destruct H0 as [_[H0[_[H7 H8]]]]. 
  destruct H1 as [_[H6[_[H9 H10]]]].
  assert(∀x : R,x ∈ \(a,b\) -> derivative \{\λ x0 y,y = F[x0] - G[x0]\}\ x 0). 
  { intros. apply H8 in H1 as H8'. destruct H8'.
    apply H10 in H1 as H10'. destruct H10'. 
    cut((F '[ x]) - (G '[ x]) = 0); intros. 
    rewrite <- H11. 
    apply Theorem5_4_2; red;[exists (F '[ x])|exists (G '[ x])]; auto.
    lra.  }
  assert(∃x1 : R, x1 ∈ \( a, b \)).
  { exists ((a+b)/2). apply AxiomII; lra. }
  destruct H2 as [x1]. 
  exists (F [x1] - G [x1]). intros. 
  destruct(classic (x = x1)).
  rewrite H4; auto. 
  assert(∃h : Fun, h = \{\ λ x0 y,y = F [x0] - G [x0] \}\).
  { exists \{\ λ x0 y,y = F [x0] - G [x0] \}\; auto. }
  destruct H5 as [h]. 
  assert(∀x : R,x ∈ \( a, b \) -> Continuous h x).
  { intros. rewrite H5. apply Theorem5_1.
    red. exists 0; auto. }
  apply H11 in H2 as H2'; apply Theorem4_1 in H2'.
  apply H11 in H3 as H3'; apply Theorem4_1 in H3'. 
  applyAxiomII H2. applyAxiomII H3. 
  assert(∀x : R, h[x] = F [x] - G [x]).
  { intros. rewrite H5. Function_ass.  }  
  apply Rdichotomy in H4. 
  destruct H4.
  - assert(ContinuousClose h x x1).
    { red; split. red. intros. 
      apply H11. apply AxiomII. lra.
      split; tauto. }
    assert(∀ x0, x < x0 < x1 -> derivable h x0).
    { intros. rewrite H5. red. exists 0. 
      apply H1; apply AxiomII; lra. } 
    apply (Theorem6_2 h x x1) in H13; auto.
    destruct H13 as [ξ[H13 H15]].
    cut(ξ ∈ \( a, b \)). intros.
    apply H1 in H16. 
    rewrite <- H5 in H16. 
    apply (derivativeUnique _ _ ((h [x1] - h [x]) / (x1 - x)) 0) in H15; auto.
    symmetry in H15.   
    apply LemmaRdiv in H15;[|lra].
    rewrite H12 in H15. rewrite H12 in H15.
    lra. apply AxiomII. lra. 
  - assert(ContinuousClose h x1 x).
    { red; split. red. intros. 
      apply H11. apply AxiomII. lra.
      split; tauto. }
    assert(∀ x0, x1 < x0 < x -> derivable h x0).
    { intros. rewrite H5. red. exists 0. 
      apply H1; apply AxiomII; lra. } 
    apply (Theorem6_2 h x1 x) in H13; auto.
    destruct H13 as [ξ[H13 H15]].
    cut(ξ ∈ \( a, b \)). intros.
    apply H1 in H16. 
    rewrite <- H5 in H16. 
    apply (derivativeUnique _ _ ((h [x] - h [x1]) / (x - x1)) 0) in H15; auto.
    symmetry in H15.   
    apply LemmaRdiv in H15;[|lra].
    rewrite H12 in H15. rewrite H12 in H15.
    lra. apply AxiomII. lra.
Qed. 
  
Definition cF (x : (set Fun)) : Fun := c x \{\ λ x y, y = 0 \}\.
  
(* 定义：区间D上的不定积分 *)
Definition Indef_integral_f (f : Fun) (D : sR) := \{ λ F, Primitive_f f F D \}.

Definition Indef_integral (f :Fun)(D : sR) := cF(Indef_integral_f f D).

Notation "∫ D f 'xdx'" := (Indef_integral f D)(at level 200).

Theorem AxiomcF : ∀ (x : (set Fun)), NotEmpty x -> (cF x) ∈ x.
Proof. intros x H0. unfold cF. apply Axiomc. auto. Qed.

Lemma Lemma8_1: ∀(f F: Fun) (D : sR), Primitive_f f F D -> 
(Primitive_f f (cF (Indef_integral_f f D)) D).
Proof. 
  intros. 
  assert(cF (Indef_integral_f f D) ∈ (Indef_integral_f f D)).
  { apply AxiomcF. exists F. apply AxiomII; auto. }
  applyAxiomII H0; auto.
Qed.


Lemma Lemma8_2 :∀(f F: Fun) (a b : R),a < b -> Primitive_f f F \(a,b\) 
-> (∃C : R,∀x : R,x ∈ \( a, b \) -> (cF (Indef_integral_f f \( a, b \)))[x] = F [x] + C).
Proof.
  intros. pose proof H0 as H0'.
  destruct H0 as [H0[H1[H2[H3 H4]]]].
  apply Lemma8_1 in H0' as H6.
  assert(∃C : R,∀x : R,x ∈ \( a, b \) -> (cF (Indef_integral_f f \( a, b \))) [x] - F [x] = C).
  apply (Theorem8_2' f); auto.
  destruct H5 as [C]. exists C.
  intros. apply H5 in H7.
  lra.
Qed.
 
 
Theorem Lemma8_3 :∀(f : Fun) (D : sR), Function (cF (Indef_integral_f f D)).
Proof. 
  intros.
  destruct (classic (NotEmpty (Indef_integral_f f D))).
  - apply AxiomcF in H.  unfold Indef_integral in H.
    applyAxiomII H. red in H. tauto.
  - assert(cF (Indef_integral_f f D) = \{\ λ x y, y = 0 \}\).
    { unfold cF. unfold c. destruct tf. contradiction.
      auto. }
    rewrite H0. QED_function.
Qed.  
  
Lemma Lemma8_4 : ∀(f F: Fun) (D : sR), Primitive_f f F D -> (∀x : R, x ∈ D -> derivative (cF (Indef_integral_f f D)) x f[x]).
Proof.
  intros. pose proof H as H'.
  red in H. destruct H as [H[H1[H2[H3 H4]]]].
  apply H4 in H0 as H0'. destruct H0' as [H5 H6].
  rewrite H6 in H5. 
  assert(cF (Indef_integral_f f D) ∈ (Indef_integral_f f D)).
  { apply AxiomcF. exists F. apply AxiomII; auto. }
  applyAxiomII H7. red in H7.
  destruct H7 as [_[_[_[H7 H8]]]].
  apply H8 in H0 as H0'. clear H8. destruct H0' as [H0' H8].
  rewrite <- H8; auto.
Qed.
  


 
Theorem Theorem8_3 : ∀(f g F G: Fun) (D : sR)(k1 k2 : R), Primitive_f f F D /\ Primitive_f g G D -> (∃P, Primitive_f \{\ λ x y, y = k1 * f[x] + k2 * g[x] \}\ P D).
Proof.
  intros. destruct H.
  exists \{\ λ x y, y = k1 * F[x] + k2 * G[x] \}\.
  destruct H as [H[H1[H2[H3 H4]]]].
  destruct H0 as [H0[H5[H6[H7 H8]]]]. 
  split. QED_function. split. QED_function.
  split. intros z H'. apply AxiomII. 
  exists (k1 * f [z] + k2 * g [z]).
  apply AxiomII'; auto. split. 
  intros z H'. apply AxiomII. exists (k1 * F [z] + k2 * G [z]).
  apply AxiomII'; auto. intros. 
  apply H4 in H9 as H4'. apply H8 in H9 as H8'.
  destruct H8'. destruct H4'.  
  cut(derivable F x); intros. 
  apply (Lemma5_3 F k1 x) in H14. 
  cut(derivable G x); intros.
  apply (Lemma5_3 G k2 x) in H15. 
  assert(∀x : R,\{\ λ x y,y = k1 * F [x] \}\[x] = k1* F[x]).
  { intros. Function_ass. }
  assert(∀x : R,\{\ λ x y,y = k2 * G [x] \}\[x] = k2* G[x]).
  { intros. Function_ass. } 
  assert(\{\ λ x0 y,y = k1 * F [x0] + k2 * G [x0] \}\ = \{\ λ x0 y,y = \{\ λ x y,y = k1 * F [x] \}\[x0] + \{\ λ x y,y = k2 * G [x] \}\[x0] \}\).
  { apply AxiomI. split; intros.
    - applyAxiomII H18. destruct H18 as [x'[y'[H18 H19]]].
      apply AxiomII. exists x',y'. split; auto.
      rewrite H16. rewrite H17. auto.
    - applyAxiomII H18. destruct H18 as [x'[y'[H18 H19]]].
      apply AxiomII. exists x',y'. split; auto.
      rewrite H16 in H19. rewrite H17 in H19. auto. }
  assert(derivative \{\ λ x0 y,y = k1 * F [x0] + k2 * G [x0] \}\ x  
  (\{\ λ x y,y = k1 * F [x] \}\ '[x] + \{\ λ x y,y = k2 * G [x] \}\'[x])).
  { rewrite H18.
    apply Theorem5_4_1. red. exists ((k1 * F '[ x])); auto.
    red. exists ((k2 * G '[ x])); auto. }
  apply derEqual in H19 as H19'. split.
  rewrite H19'; auto. rewrite H19'.
  apply derEqual in H14. rewrite H14.
  apply derEqual in H15. rewrite H15.     
  rewrite H11. rewrite H13. 
  symmetry. Function_ass. 
  red. exists (G '[ x]); auto.
  red. exists (F '[ x]); auto.
Qed.
 


 
Lemma Lemma5_82 : ∀ (f h : Fun),  Function f -> Function h -> Function (f ◦ h).
Proof.
  intros. red. intros. applyAxiomII' H1;
  applyAxiomII' H2. destruct H2 as [y0[H2 H2']].
  destruct H1 as [y1[H3 H3']].
  assert(y0 = y1). 
  apply (H0 x _ _); auto.
  rewrite H1 in H2'. 
  apply(H y1); auto.
Qed. 
  

(* 第一分部积分 *)
Theorem Theorem8_4 : ∀(f ψ F:Fun) (D J : sR), D ⊂ dom[f] -> Function ψ ->
J ⊂ dom[ψ] ->  (∀t:R, t ∈ J -> derivable ψ t /\ ψ[t] ∈ D) -> Comp F ψ  
-> Primitive_f f F D -> Primitive_f \{\λ t y,y = f[ψ[t]] * ψ '[t] \}\ (F ◦ ψ) J.
Proof.
  intros. red in H4. 
  red. destruct H4 as [H7[H5[H6[H8 H4]]]].
  assert(H10:∀z : R,z ∈ J -> (F ◦ ψ) [z] = F[ψ[z]]).
  { intros. apply f_x. apply Lemma5_82; tauto.
    apply AxiomII'. exists  ψ[z].
    split. apply x_fx; auto. apply x_fx; auto.
    apply H8. apply H2; auto. }
  split. QED_function. split.
  apply Lemma5_82; auto. split.
  red. intros. apply AxiomII. 
  exists(f [ψ [z]] * ψ '[ z]).
  apply AxiomII'; auto. split.
  intros z H9. apply AxiomII. 
  exists (F ◦ ψ)[z]. apply AxiomII'. 
  exists (ψ[z]). split. apply x_fx; auto.
  rewrite H10; auto.
  apply x_fx; auto. apply H8. apply H2; auto.
  intros.
  assert(∃u : R, u = ψ[x]).
  { exists ψ[x]; auto. } 
  destruct H11 as [u]. 
  assert(derivative (F ◦ ψ) x (F '[u] * ψ '[x])).
  { apply Theorem5_8; auto. apply H2; auto.
    red. exists (F '[u]). apply H4.
    rewrite H11; apply H2; auto. }
  apply derEqual in H12 as H13.
  rewrite H13; split; auto. 
  symmetry. apply f_x. QED_function.
  apply AxiomII'. 
  cut(F '[ u] = f [ψ [x]]).
  intros. rewrite H14; auto.
  rewrite H11. apply H4.
  apply H2; auto.
Qed.



  
  
  
  
  
  
  
  






























