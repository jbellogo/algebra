
(** Load required packages.  Not all of these packages are needed right away,
but they may be useful later. **)

Require Export Setoid List Sorted Constructive_sets Utf8_core Wf_nat
ProofIrrelevance Permutation IndefiniteDescription ChoiceFacts
Description Classical_Prop Utf8.


(** Math symbols for cut and paste: ∀ ∃ → ↔ ∧ ∨ ¬ ≠ ≤ ≥ ∅ ℕ ℤ ∈ ∉ ⊂ ∑ ∏ λ **)

(** Axioms for the integers. **)

Parameter Z : Set.

Parameter add mult : Z → Z → Z.
Parameter neg : Z → Z.
Parameter zero one : Z.
Notation "0" := zero.
Notation "1" := one.
Infix "+" := add.
Infix "*" := mult.
Notation "- x" := (neg x).
Notation "- 0" := (neg 0).
Notation "- 1" := (neg 1).
Definition sub a b := a + -b.
Infix "-" := sub.

Axiom A1 : ∀ a b   : Z, a + b = b + a.
Axiom A2 : ∀ a b c : Z, a + (b + c) = (a + b) + c.
Axiom A3 : ∀ a     : Z, a + 0 = a.
Axiom A4 : ∀ a     : Z, a + -a = 0.
Axiom M1 : ∀ a b   : Z, a * b = b * a.
Axiom M2 : ∀ a b c : Z, a * (b * c) = (a * b) * c.
Axiom M3 : ∀ a     : Z, a * 1 = a.
Axiom D1 : ∀ a b c : Z, (a + b) * c = a * c + b * c.

(** Some useful lemmas. **)
Lemma S1 : ∀ a b c : Z, a = b → a + c = b + c.
Proof.
intros a b c H.
rewrite H.
reflexivity.
Qed.

Lemma S2 : ∀ a b c : Z, a = b → a * c = b * c.
Proof.
intros a b c H.
rewrite H.
reflexivity.
Qed.



Theorem A1P1 : ∀ a : Z, 0 + a = a.
Proof.
intros.
pose proof (A3 a).
rewrite (A1 a 0) in H.
exact H.
Qed.


Theorem A1P2 : ∀ a : Z, -a + a = 0.
Proof.
intros.
pose proof (A4 a).
rewrite (A1) in H.
exact H.
Qed.


Theorem A1P3 : ∀ a : Z, 1 * a = a.
Proof.
intros.
pose proof (M3 a).
rewrite (M1 a 1) in H.
exact H.
Qed.


Theorem A1P4 : ∀ a b : Z, a + b = 0 → b = -a.
Proof.
intros.
rewrite (A1) in H.
pose proof (S1 (b+a) 0 (-a)).
pose (J := H0 H).
rewrite <-(A2 b a (-a)) in J.
rewrite (A4 a) in J.
rewrite (A3 b) in J.
rewrite (A1 0 (-a)) in J.
rewrite (A3 (-a)) in J.
exact J.
Qed.



Theorem A1P5 : forall a : Z, -(-a) = a.
intros.
symmetry.
apply A1P4.
rewrite A1.
pose proof (A4 a).
exact H.
Qed.



Theorem A1P6 : ∀ a : Z, 0 * a = 0.
Proof.
intros.
pose proof (A3 (0*a)).
rewrite <-(A4 a) in H at 2.
rewrite <-(M3 a) in H at 2.
rewrite (M1 a 1) in H.
rewrite A2 in H.
rewrite <-D1 in H.
rewrite (A1 0 1) in H.
rewrite A3 in H.
rewrite M1 in H.
rewrite M3 in H.
rewrite A4 in H.   
symmetry.
trivial.
Qed.




Theorem A1P7 : ∀ a : Z, -1 * a = -a.
Proof.
intros.
pose proof (A3 (-1*a)).
rewrite <-(A4 a) in H.
rewrite (A2 (-1*a) a (-a)) in H.
rewrite <-(M3 a) in H at 2.
rewrite (M1 a 1) in H.
rewrite <-(D1) in H.
rewrite (A1 (-1) 1) in H.
rewrite (A4 1) in H.
rewrite A1P6 in H.
rewrite A1P1 in H.
symmetry.
trivial.
Qed.



Theorem A1P8 : ∀ a b : Z, -a * -b = a * b.
Proof.
intros.
pose proof (A1P7 (-a * b)).
rewrite <-(A1P7 a) in H at 1.
rewrite (M1 (-1) a) in H.  
rewrite (A1P7) in H.
rewrite <-(M2 a (-1) b) in H.
rewrite <-(A1P7) in H at 1.
rewrite M2 in H.
rewrite A1P7 in H.
rewrite A1P7 in H.
rewrite <-(A1P7 a) in H at 2.
rewrite <-M2 in H.
rewrite (A1P7 (a * b)) in H.
rewrite (A1P5) in H.
trivial.
Qed.



Theorem A1P9 : ∀ a b : Z, a + b = a → b = 0.
Proof.
intros.
apply (S1 (a+b) a (-a)) in H.
rewrite (A1 a b) in H.
rewrite <-A2 in H.
rewrite (A4 a) in H.
rewrite A3 in H.
trivial.
Qed.





(*
Theorem A1P11yeet : ∀ a b : Z, a * b = 0 → a = 0 ∨ b = 0.
Proof.
intros a b H.
apply (S1 (a*b) 0 (1*b)) in H.
rewrite <-D1 in H.
rewrite A1P3 in H.
rewrite A1P1 in H.
rewrite M1 in H.
apply A1P10 in H.
destruct H.  
apply (S1 (a+1) 1 (-1)) in H.
rewrite <-A2 in H.
rewrite A4 in H.
rewrite A3 in H.
left.
exact H.
right.
exact H.
Qed.


Theorem A1P11_v2 : ∀ a b : Z, a * b = 0 → a = 0 ∨ b = 0.
Proof.
intros a b H.
apply (S1 (a*b) 0 (1*b)) in H.
rewrite <-D1 in H.
rewrite A1P3 in H.
rewrite A1P1 in H.
rewrite M1 in H.
apply A1P10 in H.
destruct H.
apply (S1 (a+1) 1 (-1)) in H.
rewrite <-A2 in H.
rewrite A4 in H.
rewrite A3 in H.
left.
exact H.
right.
exact H.
Qed.   *)


(** Definition of divides. In the course notes, the notation is
slightly different: "a|b" instead of "(a|b)". Coq requires
extra parentheses or else this notation would conflict with
set notation. **)

Definition divide (x y : Z) := ∃ z : Z, y = z * x.
Notation "( x | y )" := (divide x y).

(**
Definition of ℕ. You need to fill in the content of the definition.
If you wish to declare ℕ as an axiom, change "Definition" to "Parameter".
**)

Parameter ℕ : Ensemble Z.
Infix "∋" := (In Z) (at level 70).
Notation "x ∈ S" := (S ∋ x) (at level 70).
Infix "⊂" := (Included Z) (at level 70).
Notation "{ x : A | P }" := (λ x : A, P).

Check {x : Z | x = x+1}.
Infix "∋" := (In Z) (at level 70).
Notation "x ∈ S" := (S ∋ x) (at level 70).
Infix "⊂" := (Included Z) (at level 70).
Notation "{ x : A | P }" := (λ x : A, P).


(******************************Axioms for natural numbers****************)

Axiom N1 : 1 ∈ ℕ.
Axiom N2 : ∀ a b : Z, a ∈ ℕ → b ∈ ℕ → a+b ∈ ℕ. (*closure*)
Axiom N3 : ∀ a : Z, a ∈ ℕ -> ¬(-a ∈ ℕ).
Axiom O8 : forall a b : Z, a ∈ ℕ -> b ∈ ℕ -> a*b ∈  ℕ.


Axiom T : ∀ a : Z, (a ∈ ℕ ∧ a ≠ 0 ∧ ¬(-a ∈ ℕ))
∨ a=0 /\(¬(a ∈ ℕ) ∧ ¬(-a ∈ ℕ))
∨ -a ∈ ℕ /\(¬(a ∈ ℕ) ∧ a ≠ 0).


(*************************************************************************************************************************************************************************************************************************************)
(* ℕ = {x : Z | x > 0} *)
Definition lt (a b : Z) := b-a ∈ ℕ.
Definition le (a b : Z) := ((lt a b) ∨ a = b).

Infix "<" := lt.
Notation "a > b" := (b < a) (only parsing).
Infix "≤" := le (at level 70).
Notation "a ≥ b" := (b ≤ a) (at level 70, only parsing).



Theorem S1converse : forall a b c: Z, a+c = b+c -> a=b.
intros.
apply (S1 (a+c) (b+c) (-c)) in H.
rewrite <-A2, <-A2, A4, 2 A3 in H.
auto.
Qed.

Theorem neqadd : forall a b c : Z, a≠b -> a+c≠b+c.
Proof.
intros.
unfold not in *.
pose (S1 a b c).
intros.
apply S1converse in H0.
pose (H H0).
auto.
Qed.

Theorem T2 : ∀ a b : Z, b<a ∧ a≠b ∧ ¬a<b ∨ a<b ∧ a≠b ∧ ¬b<a ∨ a=b ∧ ¬b<a ∧ ¬a<b.
Proof.
intros.
pose (T (a-b)).
unfold lt.
destruct (T a) as [[H3 [H4 H5]]| [[H6 [H7 H8]]| [H9 [H10 H11]]]].
Admitted.
(***********
Theorem T2 : ∀ a b : Z, b<a ∧ a≠b ∧ ¬a<b ∨ a<b ∧ a≠b ∧ ¬b<a ∨ a=b ∧ ¬b<a ∧ ¬a<b.
Proof.
intros.
destruct (T (a-b)) as [[K3 [K4 K5]]| [[K6 [K7 K8]]| [K9 [K10 K11]]]].
unfold lt.
left.
split.
exact K3.
split.
apply (neqadd (a-b) 0 b) in K4.
unfold sub in K4.
rewrite <-A2, A1P2, A1P1, A3 in K4.
exact K4.
unfold sub in K5.
rewrite A1, <-A1P7, M1, D1, A1P8, M1, A1P3, M1, A1P7 in K5.
unfold sub.
exact K5.
unfold lt.
rewrite <-A1P7, <-A1P7 in K8. M1, D1 in K8.
tauto.
Admitted.
******************************************)

Theorem zeronotnat : 0 ∈ ℕ -> False.
Proof.
pose proof (T 0).
tauto.
Qed.


Theorem negzero : -0 = 0.
Proof.
rewrite <-A1P7.
rewrite M1.
rewrite A1P6.
reflexivity.
Qed.


Theorem A1P11 : ∀ a b : Z, a * b = 0 → a = 0 ∨ b = 0.
Proof.
intros.
destruct (T a) as [[H3 [H4 H5]]| [[H6 [H7 H8]]| [H9 [H10 H11]]]].
destruct (T b) as [[s3 [s4 s5]]| [[s6 [s7 s8]]| [s9 [s10 s11]]]].
pose ((O8 a b) H3 s3).
rewrite H in i.
now pose zeronotnat.
auto.
pose ((O8 a (-b)) H3 s9).
rewrite <-A1P7, M2, (M1 a (-1)), <-M2, H, M1, A1P6  in i.
now pose zeronotnat.
auto.
destruct (T b) as [[s3 [s4 s5]]| [[s6 [s7 s8]]| [s9 [s10 s11]]]].
pose ((O8 (-a) b) H9 s3).
rewrite <-A1P7, <-M2, H, M1, A1P6 in i.
now pose zeronotnat.
auto.
pose ((O8 (-a) (-b)) H9 s9).
rewrite A1P8, H in i.
now pose zeronotnat.
Qed.


Theorem C1 : forall a b c : Z, a * c = b * c -> a = b \/ c = 0.
Proof.
intros.
eapply S1 in H.
rewrite (A4 (b*c)) in H.
rewrite <-A1P7, M2, A1P7, <-D1 in H.
apply A1P11 in H.
destruct H.
eapply S1 in H.
rewrite <-A2, A1P2, A3, A1P1 in H.
auto.
auto.
Qed.



Theorem A1P10 : ∀ a b : Z, a * b = a → b = 1 \/ a = 0.
Proof.
intros.
pose proof (C1 b 1 a).
rewrite A1P3 in H0.
rewrite M1 in H.
pose (J := H0 H).
exact J.
Qed.




Theorem am0 : forall a : Z, a - 0=a.
Proof.
intros.
unfold sub.
rewrite negzero, A3.
reflexivity.
Qed.

Theorem am02: forall a : Z, 0 - a = -a.
Proof.
intros.
unfold sub.
rewrite A1, A3.
reflexivity.
Qed.



Theorem O9 : forall a : Z, a ∈ ℕ <->  0 < a.
Proof.
intros.
unfold lt.
rewrite am0.
reflexivity.
Qed.

Theorem O92 : forall a : Z, a<0 -> ¬(a ∈ ℕ).
Proof.
intros.
pose (T a).
unfold lt in H.
rewrite am02 in H.
tauto.
Qed.


Theorem O1 : ∀ a b : Z, a < b → a ≠ b.
intros.
pose (T2 a b).
tauto.
Qed.

Theorem O1_V2 : ∀ a b : Z, a < b → a ≠ b. (*Old*)
intros.
unfold lt in *.
pose (T (b-a)).
pose (J := (N3 (b-a)) H).
intuition.
apply (S1 a b (-a)) in H0.
symmetry in H0.
rewrite A4 in H0.
unfold sub in *.
pose (K := H1 H0).
exact K.
Qed.


Theorem O2 : ∀ a b c : Z, a < b → a+c < b+c.
Proof.
intros.
unfold lt, sub in *.
rewrite <-A1P7.
rewrite M1.
rewrite D1.
rewrite 2 (M1 _ (-1)).
rewrite 2 A1P7.
rewrite (A1 (-a)).
rewrite A2.
rewrite <-(A2 b).
rewrite A4.
rewrite A3.
exact H.
Qed.

Print Assumptions O2. (*prints out all of the axioms used in proving theorem 02*)

Theorem lttrans : ∀ a b c : Z, a < b → b < c → a < c. (*old O3*)
Proof.
intros.
unfold lt, sub in *.
rewrite <-A3.
rewrite <-(A4 b).
rewrite (A1 b (-b)).
rewrite A2.
rewrite <-(A2 c (-a) (-b)).
rewrite (A1 (-a) (-b)).
rewrite A2.
rewrite <-(A2 (c + -b) (-a) b).
rewrite (A1 (-a) b) .
apply (N2 (c+ -b) (b + -a)). 
exact H0.
exact H.
Qed.



Theorem O4 : 0 < 1.
Proof.
unfold lt, sub.
pose N1.
rewrite <-A3 in i.
rewrite negzero.
exact i.
Qed.

Lemma L2P1 : ∀ a m x : Z, (a | m) → (a | m * x).
Proof.
intros.
unfold divide in *.
destruct H.
apply (S2 m (x0*a) x) in H.
rewrite <-M2 in H.
rewrite (M1 a x) in H.
rewrite M2 in H.
exists (x0*x).
exact H.
Qed.


Theorem A2P1 : ∀ a m n x y : Z, (a | m) → (a | n) → (a | m * x + n * y).
Proof.
intros a m n x y [k H] [l H0].
exists (k*x+l*y).
rewrite H,H0, ? (M1 _ a), <-? M2, ? (M1 a), D1.
reflexivity.
Qed.


Theorem A2P2: ∀ x a b c : Z, (a | b) → (b | c) → (a | c).
Proof.
intros.
unfold divide in *.
destruct H.
rewrite H in H0.
destruct H0.
rewrite H0.
rewrite M2.
exists (x1*x0).
trivial.
Qed.

Theorem O5 : forall a b : Z, a = b \/ a ≠ b.
intros.
pose (T2 a b).
tauto.
Qed.

Theorem O7 : forall a b : Z, a ≠ b -> a > b \/ a < b.
intros.
pose (T2 a b).
tauto.
Qed.


Theorem A2P3 : ∀ a b : Z, a < b ∨ a = b ∨ a > b.
intros.
pose (T2 a b).
tauto.
Qed.


Theorem A2P3_old : ∀ a b : Z, a < b ∨ a = b ∨ a > b.
Proof.
intros a b.
destruct (classic (a < b)), (classic (a=b)), (classic (b < a)).
left.
exact H.
right; left; exact H0.
right; right; exact H1.
left; exact H.
right; left; exact H0.
right; left; exact H0.
right; right; exact H1.
pose proof (O7 a b).
pose (J := H2 H0).
destruct J.
contradiction.
contradiction.
Qed.

Theorem A2P4 : ∀ a b c : Z, a < b → c > 0 -> a * c < b * c.
Proof.
intros.
unfold lt, sub in H.
unfold lt, sub.
rewrite <-A1P7.
rewrite M2.  
rewrite <-D1.
rewrite A1P7.
apply O8.
exact H.
apply (O9 c) in H0.  
exact H0.
Qed.

Theorem A2P5 : ∀ a b c : Z, a * c = b * c → c ≠ 0 → a = b.
Proof.
intros.
pose proof S1 (a*c) (b*c) (-b*c).
rewrite <-D1 in H1.
rewrite <-D1 in H1.
rewrite A4 in H1.
rewrite A1P6 in H1.
apply A1P11 in H1.
destruct H1.
apply (S1 (a+-b) 0 b) in H1.
rewrite <-A2 in H1.
rewrite A1P2 in H1.
rewrite A3, A1P1 in H1.
exact H1.
contradiction.
exact H.
Qed.


Definition pm (a b : Z) := (a = b ∨ a = -b).
Notation "a = ± b" := (pm a b) (at level 60).
Definition assoc (a b : Z) := (a | b) ∧ (b | a).
Infix "~" := assoc (at level 70).


Theorem A3P1 : 0 ≠ 1.
Proof.
pose proof (O1 0 1).
pose proof O4.
pose (J := H H0).
exact J.   
Qed.

Lemma symm : forall a b : Z, (a=b) -> (b=a).
Proof.
intros.
symmetry.
trivial.
Qed.

Theorem NTP : forall a b : Z, (a>0) -> (b<0) -> (a*b<0).
Proof.
intros.    
Admitted.


Theorem O13 : forall a b : Z, a < b -> ¬((a=b)\/(b<a)).
Admitted.

Theorem O14 : forall a b : Z, a<b -> (-a)>(-b).
Proof.
intros.
pose (J:= (O2 a b (-a + -b)) H).
rewrite (A1 (-a) (-b)) in J at 2.  
rewrite ? A2 in *.
rewrite 2 A4 in J.
rewrite 2 A1P1 in J.
exact J.
Qed.

Theorem O15 : forall a b : Z, a>0 -> b<0 -> a*b<0.
Admitted.

Theorem O16 : forall b : Z, ¬ 0<b -> b=0\/b<0. 
Admitted.

Lemma N_0_lt : ∀ x : Z, x ∈ ℕ ↔ 0 < x.
Admitted.

Lemma le_lt_opp : ∀ a b : Z, a ≤ b ↔ ¬ b < a.
Admitted.

Lemma lt_trans : ∀ a b c : Z, a < b → b < c → a < c.
Admitted.



Lemma mult_0 : ∀n m, n * m = 0 ↔ n = 0 ∨ m = 0.
Admitted.
Lemma mult_0_3 :
∀n m p, n * m * p = 0 ↔ n = 0 ∨ m = 0 ∨ p = 0.
Proof.
intros n m p.
rewrite mult_0.
rewrite mult_0. rewrite or_assoc.
reflexivity.
Qed.

Theorem ONN : forall a : Z,  a=0 -> ¬ a ∈ ℕ.
Admitted.

Theorem NNT : forall a : Z,  ¬ a∈ ℕ/\a≠ 0 -> -a∈ ℕ.
Admitted.

Theorem NTNN : forall a b : Z, a∈ℕ-> ¬b∈ℕ ->  ¬a*b∈ℕ.
Admitted.



Theorem facsofNat : forall a b : Z, 0<a*b -> 0<a/\0<b \/ a<0/\ b<0. (*need an axiom that separates int from mod*)
Proof.
intros.
destruct (O9 (a*b)).
pose (H1 H).
destruct (T a) as [[K3 [K4 K5]]| [[K6 [K7 K8]]| [K9 [K10 K11]]]].
destruct (T b) as [[H3 [H4 H5]]| [[H6 [H7 H8]]| [H9 [H10 H11]]]].
unfold lt in *.
rewrite ? am0, ? am02 in *.
auto.
rewrite M1, H6, A1P6 in i.
pose zeronotnat.
contradiction.
pose ((O8 a (-b)) K3 H9).
apply N3 in i0.
rewrite M1, <-A1P7 in i0.
rewrite <-(A1P7 b), 2 M2, A1P7, A1P5, A1P3, M1 in i0.
contradiction.
rewrite K6,A1P6 in i.
pose zeronotnat.
contradiction.
destruct (T b) as [[H3 [H4 H5]]| [[H6 [H7 H8]]| [H9 [H10 H11]]]].
pose ((O8 (-a) b) K9 H3).
apply N3 in i0.
rewrite <-A1P7 in i0.
rewrite <-(A1P7 a) in i0.
rewrite 2 M2, A1P7, A1P5, A1P3  in i0.
contradiction.
rewrite H6, M1, A1P6 in i.
pose zeronotnat.
contradiction.
right.
unfold lt.
rewrite ? am02.
auto.
Qed.


Theorem MN : forall a b : Z, a*b∈ℕ -> a≠0/\b≠0.
intros.
rewrite O9 in H.
pose ((facsofNat a b) H).
pose (T a).
rewrite O9 in *.
split.
destruct o as [[m1 m2] | [m3 m4]].
tauto.
destruct o0 as [[H3 [H4 H5]]| [[H6 [H7 H8]]| [H9 [H10 H11]]]].
auto.
unfold lt in m3.
rewrite am02 in m3.
contradiction.
auto.
clear o0.
destruct (T b) as [[H3 [H4 H5]]| [[H6 [H7 H8]]| [H9 [H10 H11]]]].
auto.
destruct o as [[m1 m2] | [m3 m4]].
unfold lt in m2; rewrite am0 in m2.
contradiction.
unfold lt in m4; rewrite am02 in m4; contradiction.
auto.
Qed.

Theorem albNbla : forall a b : Z, a<b ->  ¬ b<a.
intros.
pose (T2 a b).
tauto.
Qed.


Theorem albNblea : forall a b : Z, a<b -> ¬ b≤a.
intros.
destruct (T2 a b) as [[H3 [H4 H5]]| [[H6 [H7 H8]]| [H9 [H10 H11]]]].
contradiction.
unfold le, not.
intros.
destruct H0.
contradiction.
symmetry in H0; contradiction.
contradiction.
Qed.


Theorem A3P2 : ∀ a b : Z, 0 < a → (0 < b ↔ 0 < a * b).
Proof.
intros.
unfold iff, lt in *.
split.
rewrite ? am0 in *.
pose ((O8 a b) H).
exact i.
rewrite ? am0 in *.
intros.
rewrite O9 in *.
apply facsofNat in H0.
destruct H0 as [[k1 k2] | [k3 k4]].
auto.
apply albNbla in k3.
contradiction.
Qed.

(*********************************SETS**********************************************************************************************************)

Notation "x < y < z" := (x < y ∧ y < z).
Notation "x ≤ y < z" :=
(x ≤ y ∧ y < z) (at level 70, y at next level).

Infix "∋" := (In Z) (at level 70).
Notation "x ∈ S" := (S ∋ x) (at level 70).
Notation "x ∉ S" := (¬(x ∈ S)) (at level 70).
Infix "⊂" := (Included Z) (at level 70).
Notation "∅" := (Empty_set Z).
Notation "{ x : A | P }" := (λ x : A, P).

Axiom WOP : ∀ S, S ≠ ∅ →
S ⊂ ℕ → ∃ x, x ∈ S ∧ ∀ y, y ∈ S → x ≤ y.



(*Messiest, luckiest thing*)
Theorem A3P3_me : ∀ a : Z, 0 < a → a < 1 → False.
Proof.
intros.
destruct (WOP {x:Z | 0<x<1}).
unfold not.
intros.
assert (a∈∅).
rewrite <-H1.
unfold In.
auto.
contradiction.
unfold Included.
intros.
destruct H1.
rewrite <-O9 in H1.
auto.
destruct H1.
unfold In in H1.
pose (H2 (x*x)).
destruct H1.
pose ((A2P4 x 1 x) H3 H1).
rewrite (A1P3 x) in l0.  
apply albNblea in l0.
unfold In in *.
contradiction l0. (*even when contradiction is from H1: P->Q, and H2 : not Q *)
destruct l.
assert (x*x<x).
{eapply A2P4 in H3.
erewrite A1P3 in H3.
eauto.
auto. }  
eapply A2P4 in H1.
rewrite A1P6 in H1.
split.
eauto.
eauto using lttrans.
auto.
unfold le in l0.
destruct l0.
left.
auto.
destruct l0.
right.
auto.
Qed.
(*contradiction between rationals and integers... naturalrationals  are screaming to come to the suface in X*x<1 from x<1**)  

Theorem A3P3 : ∀ a : Z, 0 < a → a < 1 → False.
Proof.
intros.
destruct (WOP {x : Z | 0 < x < 1}).
- unfold not.
intros.
assert (a ∈ ∅).
{ rewrite <-H1.
(* Locate "∈". *)
unfold In.
tauto. }
contradiction.
- unfold Included.
intros.
unfold In in H1.
rewrite N_0_lt.
tauto.
- unfold In in H1.
destruct H1 as [[H1 H2] H3].
pose proof (H3 (x*x)).
assert (x*x < x).
{ eapply A2P4 in H2.
rewrite A1P3 in H2.
exact H2.
exact H1. }
rewrite le_lt_opp in H4.
contradiction H4.
split.
+ eapply A2P4 in H1.
* rewrite A1P6 in H1.
eauto.
* auto.
+ eauto using lt_trans.
Qed.


Theorem MxP : forall a b : Z, a∈ℕ-> ¬b∈ℕ -> ¬a*b∈ℕ.
Proof.
intros.
destruct (T b) as [[K3 [K4 K5]]| [[K6 [K7 K8]]| [K9 [K10 K11]]]].
contradiction.
pose (A1P6 a).
rewrite <-K6 in e at 1.
rewrite M1 in e.
pose (T (a*b)).
tauto.
Admitted.


Theorem A3P4 : ∀ a b : Z, (a | b) -> 0<b → a ≤ b.
Proof.
intros.
unfold le,lt, divide in *.
rewrite am0 in *.
elim H; intros.
destruct (T2 a b) as [[H3 [H4 H5]]| [[H6 [H7 H8]]| [H9 [H10 H11]]]]. 
destruct (T2 x 1) as [[K3 [K4 K5]]| [[K6 [K7 K8]]| [K9 [K10 K11]]]].
rewrite ? O9 in *.
pose ((lttrans 0 b a) H0 H3).
apply (A2P4 1 x a) in K3.
rewrite <-H1, A1P3 in K3.
contradiction.
exact l.
rewrite O9 in H0.
pose ((lttrans  0 b a) H0 H3).
destruct (facsofNat x a).
rewrite <-H1.
auto.
destruct H2.
pose ((A3P3 x) H2 K6).
contradiction.
destruct H2.
apply albNbla in H6.
contradiction.
rewrite K9, A1P3 in H1.
symmetry in H1.
right.
auto.
unfold lt in H6.
left; auto.
right;auto.
Qed.



Theorem div1 : forall a : Z, (1|a).
Proof.
intros.
exists a.
rewrite M3.
trivial.
Qed.


Theorem aa : forall a : Z, ¬a<a.
Proof.
intros.
unfold lt, sub.
rewrite A4.
exact zeronotnat.  
Qed.

Theorem lt_x_neg : forall a b c : Z, a<b -> c<0 -> b*c < a*c.
Proof.
intros.
Admitted.

Theorem help1 : forall x: Z, x<0 -> 1≤-x.
Proof.
intros.
pose O4.
apply (O2 0 1 (-1)) in l. 
rewrite A4, A1P1 in l.
pose ((lt_x_neg x 0 (-1)) H l).
rewrite A1P6, M1, A1P7 in l0.
pose (div1 (-x)).
pose ((A3P4 1 (-x)) d l0).
exact l1.
Qed.

Theorem help2 : forall x : Z, 0<x -> 1≤x.
intros.
destruct (T x) as [[K3 [K4 K5]]| [[K6 [K7 K8]]| [K9 [K10 K11]]]].
rewrite O9 in K3.
pose (div1 x).
pose ((A3P4 1 x) d H).
exact l.
rewrite K6 in H.
pose (aa 0). 
contradiction.
rewrite <-O9 in H.
contradiction.
Qed.

Theorem lts : forall a b : Z, a<b -> ¬b<a.
Proof.
intros.
pose (T2 a b).
tauto.
Qed.

Theorem gtg0 : forall a : Z, 1<a -> 0<a.
intros.
pose ((lttrans 0 1 a) O4 H).
auto.
Qed.

(*can apply things in goal if P->Q, P Q is the goal*)

Lemma aleblea : forall a b : Z,  a ≤ b-> b ≤ a -> a=b.
intros.
destruct H.
unfold le in *.
pose (A2P3 a b).
destruct o, H0.
apply albNbla in H.
contradiction.
symmetry in H0; exact H0.
apply albNbla in H0.
contradiction.
symmetry; auto.
destruct H0.
pose (T2 a b).
tauto.
auto.
Qed.

Lemma alt0ltnega : forall a : Z, a<0 -> 0< -a.
intros.
eapply O2 in H.
rewrite A4, A1P1 in H.
auto.
Qed.

Lemma negdiv : forall a b : Z, (b | a) -> (-b | -a).
intros.
unfold divide in *.
destruct H.
eapply S2 in H.
erewrite (M1 a (-1))  in H.
erewrite <-M2, (M1 b _), 2 A1P7 in H.
exists x.
auto.
Qed.

Theorem negeqneg : forall a b: Z, -a=-b -> a =b.
intros.
apply (S2 _ _ (-1)) in H.
rewrite 2 (M1 _ (-1)), ? A1P7, ? A1P5 in H.
easy.
Qed.


Theorem facsofNat2 : forall a b : Z, a*b<0 -> a<0/\0<b \/0<a/\b<0.
intros.
unfold lt.
apply O14 in H.
rewrite <-(A1P7 (a*b)), M2, (M1 (-1) _), <-M2, A1P7 in H.
rewrite negzero in H.
pose ((facsofNat a (-b)) H).
unfold lt in o.
rewrite ? am0, ? am02 in *.
rewrite A1P5 in o.
tauto.
Qed.


Theorem S2le : forall a b c: Z, a≤b -> 0<c -> a*c≤b*c.
Proof.
intros.
destruct H.
pose ((A2P4 a b c) H H0).
unfold le.
left.
auto.
apply (S2 a b c) in H.
unfold le.
right.
auto.
Qed.


Theorem negLe : forall a b: Z, -a≤b -> -b≤a.
Proof.
intros.
unfold le in *.
destruct H.
apply (O2 (-a) b (a + -b)) in H.
rewrite (A1 a (-b))  in H at 2.
rewrite 2 A2 in H.
rewrite A4, A1P2, 2 A1P1 in H.
left.
auto.
apply (S2 (-a) b (-1)) in H.
rewrite <-A1P7, 3 M1, (M1 b (-1)) in H.
rewrite 3 A1P7, A1P5 in H.
right.
auto.
Qed.




Lemma Ordering12 : ∀ a : Z, 0 < -a ↔ a < 0.
Admitted.

Lemma Ordering13 : ∀ a b : Z, a ≤ b → b ≤ a → a = b.
Admitted.
Theorem A3P5 : ∀ a b : Z, a ~ b → a = ± b.
Proof.
intros a b [H H0].
assert (-a | -b).
{ destruct H.
exists (x).
now rewrite <-(A1P7 a), M2, (M1 x), <-M2, A1P7, H. }
assert (-b | -a).
{ destruct H0.
exists (x).
now rewrite <-(A1P7 b), M2, (M1 x), <-M2, A1P7, H0. } 
destruct (A2P3 a 0) as [H3 | [H3 | H3]], (A2P3 b 0) as [H4 | [H4 | H4]].
- rewrite <-Ordering12 in *.
apply A3P4 in H1; auto.
apply A3P4 in H2; auto.
left.
apply Ordering13 in H1; auto.
apply (S2 _ _ (-1)) in H1.
rewrite ? (M1 _ (-1)), ? A1P7, ? A1P5 in H1.
congruence. 
- 
Admitted.



Lemma lexlt1 : forall a : Z,  1≤-a -> a<1.
intros.
destruct H.
apply O14 in H.
rewrite A1P5 in H.
pose O4.
apply (O2 0 1 (-1)) in l.
rewrite A1P1, A4 in l.
pose  ((lttrans a (-1) 0) H l).
pose  ((lttrans a 0 1) l0 O4).
exact l1.
eapply S2 in H.
rewrite (A1P8 _ 1), A1P3, M3 in H.
rewrite <-H.
pose ((O2 0 1 (-1)) O4).
rewrite A1, A3, A4 in l.
pose ((lttrans (-1) 0 1) l O4).
exact l0.
Qed.

Theorem S2leneg : forall a b c : Z, a≤b ->  c<0 -> b*c ≤a*c.
Proof.
intros.
unfold le in *.
destruct H.
eapply lt_x_neg in H.
left.
eauto.
auto.
eapply S2 in H.
right.
eauto.
Qed.



Theorem A3P5_me : ∀ a b : Z, a ~ b → a = ± b.
Proof.
intros.
(*a and b are less than 0*)
destruct (A2P3 a 0) as [H1 H2| H2].
destruct (A2P3 b 0) as [h1 h2| h2].
(*a and b are less than 0*)
destruct H.
destruct H, H0.
rewrite H in h1.
pose ((facsofNat2 x a) h1).
destruct o as [[k]|[k2 k3]].
apply albNbla in H2.
contradiction.
apply help2 in k2.
eapply S2leneg in k2.
rewrite <-H, A1P3 in k2.
(*make b le a*)
rewrite H0 in H1.
pose ((facsofNat2 x0 b) H1).
destruct o as [[l]|[l2 l3]].
apply albNbla in H2.
rewrite H in H2.
contradiction.
apply help2 in l2.
eapply S2leneg in l2.   (*b is negative tho!! still works by multiplying by (-b)*)
rewrite A1P3, <-H0 in l2.
pose ((aleblea a b) l2 k2).
left; auto.
auto.
auto.
(*now for b=0 and 0<b*)

destruct H.
pose negdiv.
pose ((negdiv a b) H0).
apply A3P4 in d0.
destruct H0.
destruct (facsofNat2 x b).
rewrite <-H0.
auto.
destruct H2.
apply help1 in H2.
eapply S2le in H2.
rewrite <-A1P7, <-M2, <-H0, A1P7, A1P3  in H2.
eapply S2le in H2.
rewrite M1, A1P7, A1P8, M3 in H2.
apply negLe in H2.
destruct d0, H2.
pose ((lttrans (-b) (-a) b) H4 H2). 

destruct H0, H.
destruct h2.
Admitted.



Theorem A3P5_d : ∀ a b : Z, a ~ b → a = ± b.
Proof.
intros.
unfold pm, assoc in *.
destruct H; destruct H; destruct H0.
pose (help1 x).
pose (help2 x).
pose (help1 x0).
pose (help2 x0).
destruct (T x) as [[K3 [K4 K5]]| [[K6 [K7 K8]]| [K9 [K10 K11]]]].

destruct (T x0) as [[J3 [J4 J5]]| [[J6 [J7 J8]]| [J9 [J10 J11]]]].
rewrite <-O9 in *.
pose (l0 K3). (*1 le x*)
pose (l2 J3).
destruct l3, l4.
pose ((A2P4 1 x a) H1).
pose ((A2P4 1 x0 b) H2).
rewrite ? A1P3 in *.
destruct (classic (0<a)).
destruct (classic (0<b)).
pose (l4 H4).
pose (l3 H3).
rewrite <-H in l6.
rewrite <-H0 in l5.
pose (lts a b).
pose (n l6).
contradiction.
assert ( ¬ 0 < b -> b=0\/b<0).
{intros.
pose (T2 b 0).
tauto.
  } 
  pose (H5 H4).
  destruct o.
  rewrite H6 in H0.
  rewrite M1, A1P6 in H0.
  left.
  rewrite <-H0 in H6.
  auto.

  apply O92 in H6.
  pose ((NTNN x0 b) J3 H6).
  rewrite <-O9 in H3.
  rewrite  <-H0 in n.
  contradiction.
  apply gtg0 in H2.
  Admitted.

  Definition unit (a : Z) := (a | 1).

  Notation "x < y < z" := (x < y ∧ y < z).
  Notation "x ≤ y < z" :=
  (x ≤ y ∧ y < z) (at level 70, y at next level).
  Notation "x ≠ ± y" := (¬ (x = ± y)) (at level 60).

  Infix "∋" := (In Z) (at level 70).
  Notation "x ∈ S" := (S ∋ x) (at level 70).
  Notation "x ∉ S" := (¬(x ∈ S)) (at level 70).
  Infix "⊂" := (Included Z) (at level 70).
  Notation "∅" := (Empty_set Z).
  Notation "{ x : A | P }" := (λ x : A, P).

  Notation "2" := (1+1).

  Definition prime (p : Z) :=
  p ≠ ± 1 ∧ ∀ d : Z, (d | p) → d = ± 1 ∨ d = ± p.

  Theorem m1m0 : forall a : Z, 1<a -> 0<a.
  Proof.
  intros.
  pose N1.
  rewrite O9 in i.
  eauto using lttrans.
  Qed.


  Theorem l1le0 : forall a : Z, a<1 -> a≤0.
  Proof.
  intros.
  pose (A3P3 a).
  destruct (T a) as [[H3 [H4 H5]]| [[H6 [H7 H8]]| [H9 [H10 H11]]]].
  rewrite <-O9 in *.
  unfold le.
  pose (f H3 H).
  contradiction. 
  unfold le.
  right.
  exact H6.
  rewrite O9 in *.
  apply O14 in H9.
  rewrite A1P5 in H9.
  unfold le; left.
  rewrite negzero in H9.
  exact H9.
  Qed.


  Theorem l0nN : forall a : Z, a<0 -> a∉ℕ.
  Proof.
  intros.
  unfold lt in H.
  rewrite am02 in H.
  apply N3 in H.
  rewrite A1P5 in H.
  auto.
  Qed.


  Lemma S1le : forall a b c : Z, a≤ b -> a+c≤b+c.
  Proof.
  intros.
  destruct H.
  apply (O2 a b c) in H. 
  unfold le; left.
  exact H.
  apply (S1 a b c) in H.
  unfold le; right; exact H.
  Qed.

  Theorem Ns : forall a : Z, 0<a -> -a∉ℕ.
  Proof.
  intros.
  rewrite <-O9 in H.
  pose (T a).
  tauto.
  Qed.

  Lemma l0P :  forall a b : Z, a<0 -> b*a<0 -> 0<b.
  Proof.
  intros.
  pose (T b).
  rewrite <-O9 in *.
  rewrite O9 in *.
  apply l0nN in H.  
  pose (T a).
  pose (T (a*b)).
  apply l0nN in H0.
  intuition.
  Admitted.


  Lemma nN : forall a : Z, a∉ℕ -> a<0\/a=0.
  Proof.
  intros.
  pose (T a).
  unfold lt, sub.
  rewrite A1P1.
  tauto.
  Qed.  

  Lemma leNm : forall a b : Z, a≤b -> ¬b<a.
  Proof.
  intros.
  unfold le in H.
  pose (T2 a b).
  tauto.
  Qed.

  Theorem A4P1 : ∀ a : Z, a ∈ unit ↔ a = ± 1.
  Proof.
  unfold iff, In, pm, unit, divide.
  split.
  intros.
  destruct H.
  destruct (T2 x 1) as [[K3 [K4 K5]]| [[K6 [K7 K8]]| [K9 [K10 K11]]]].
  destruct (T a) as [[H3 [H4 H5]]| [[H6 [H7 H8]]| [H9 [H10 H11]]]].
  rewrite O9 in H3.
  apply (A2P4 1 x a) in K3.
  rewrite A1P3, <-H in K3.
  pose ((A3P3 a) H3).
  contradiction.
  exact H3.
  rewrite H6,M1, A1P6 in H.
  pose A3P1.
  symmetry in H.
  contradiction.
  apply m1m0 in K3.
  apply O9 in K3.
  pose ((NTNN x a) K3 H10).
  rewrite <-H in n.
  pose N1.
  contradiction.
  destruct (T a) as [[H3 [H4 H5]]| [[H6 [H7 H8]]| [H9 [H10 H11]]]].
  apply l1le0 in K6.
  destruct K6.
  apply l0nN in H0.
  pose ((NTNN a x) H3 H0).
  rewrite M1, <-H in n.
  pose N1.
  contradiction.
  rewrite H0, A1P6 in H.
  pose A3P1.
  symmetry in H.
  contradiction.
  rewrite H6, M1, A1P6 in H.
  pose A3P1.
  symmetry in H.
  contradiction.
  apply l1le0 in K6.
  destruct K6. 
  pose ((help1 x) H0).
  rewrite H in l.
  apply (S1le (x*a) (-x) x) in l.
  rewrite A1P2, M1 in l.
  rewrite <-(A1P3 x) in l at 2.
  rewrite <-D1 in l.
  destruct l.
  pose ((l0P x (a+1)) H0 H1).
  pose ((nN a) H10).
  destruct o.
  apply help1 in H2.
  apply (S1le 1 (-a) a) in H2.
  rewrite A1P2 in H2.
  apply leNm in H2.
  rewrite A1 in H2.
  contradiction.
  contradiction.
  pose (A1P11 (a+1) x).
  destruct o.
  exact H1.
  apply (S1 (a+1) 0 (-1)) in H2.
  rewrite <-A2, A4, A1P1, A3 in H2.
  right.
  auto.
  rewrite H2 in H.
  rewrite A1P6 in H.
  pose A3P1.
  symmetry in H.
  contradiction.
  rewrite H0 in H.
  rewrite A1P6 in H.
  pose A3P1.
  symmetry in H.
  contradiction.
  rewrite K9, A1P3 in H.
  left.
  auto.
  intros.
  destruct H.
  exists 1.
  rewrite A1P3.
  auto.
  exists (-1).
  rewrite A1P7.
  apply (S2 a (-1) (-1)) in H.
  rewrite M1, 2 A1P7, A1P5 in H.
  auto.
  Qed.


  Theorem beqnega : forall a b : Z, a=-b -> b=-a.
  Proof.
  intros.
  apply (S2 a (-b) (-1)) in H.
  rewrite M1, A1P7 in H.
  rewrite M1, A1P7, A1P5 in H.
  auto.
  Qed.


  Theorem A4P2 : ∀ a b : Z, a ~ b ↔ ∃ u : Z, u ∈ unit ∧ b = a * u.
  Proof.
  unfold iff.
  split.
  intros.
  apply A3P5 in H.
  destruct H.
  exists 1.
  assert (1∈unit).
  {exists 1.
  rewrite M3.
  trivial. }
  rewrite <-(M3 a) in H.
  auto.
  exists (-1).
  assert (-1∈unit).
  {exists (-1).
  rewrite A1P7, A1P5.
  trivial. }
  apply (S2 a (-b) (-1)) in H.
  rewrite (M1 (-b) (-1)) in H.
  rewrite (A1P7 (-b))  in H.
  rewrite A1P5 in H.
  auto.      (*second part of the proof.*)
  intros; destruct H.
  unfold assoc.
  split.
  exists x.
  rewrite M1.
  tauto.
  destruct H.
  apply A4P1 in H.
  unfold pm in H.
  destruct H.
  rewrite H, M3 in H0.
  exists 1.
  rewrite A1P3.
  auto.
  rewrite H, M1, A1P7 in H0.
  exists (-1).
  rewrite A1P7.
  apply beqnega in H0.
  auto.
  Qed.



  Theorem m0me1 : forall a : Z,  0<a -> 1≤a.
  Proof.
  intros.
  destruct (T2 1 a) as [[K3 [K4 K5]]| [[K6 [K7 K8]]| [K9 [K10 K11]]]].
  pose ((A3P3 a) H K3).
  contradiction.
  unfold le; left; auto.
  unfold le; right; auto.
  Qed.


  Theorem ltle : forall a b : Z, a<b -> a≤b-1.
  Proof.
  intros.
  pose (m0me1 (b-a)).
  apply (O2 a b (-a)) in H.
  rewrite A4 in H.
  unfold sub in l.
  pose (l H).
  apply (S1le 1 (b + -a) (a + -1)) in l0.
  rewrite A1 in l0.
  rewrite A2 in l0.
  rewrite <-A2 in l0.
  rewrite A1P2, A3 in l0.
  rewrite A1 in l0.
  rewrite  <-A2, A1P2, A3, A1  in l0.
  trivial.
  Qed.


  Theorem twominus1 : (2-1 = 1).
  Proof.
  unfold sub.
  now rewrite <-A2, A4, A3. 
  Qed.

  Theorem m1me0 : forall a : Z, 1≤a -> 0<a.
  Proof.
  intros.
  unfold le in H.
  destruct H.
  pose ((lttrans 0 1 a) O4 H).
  auto.
  pose O4.
  rewrite H in l.
  auto.
  Qed.


  Theorem A4P3 : forall a : Z,  a= 1 -> a + 1∈ prime.
  Proof.
  unfold In, prime, pm.
  intros.
  split.
  pose A3P1.
  destruct (classic (a+1=1)).
  apply (S1 (a+1) 1 (-1)) in H0.
  rewrite <-A2, ? A4, A3 in H0.
  rewrite H in H0.
  symmetry in H0.
  contradiction.
  pose (N2 a 1).
  rewrite <-H in i.
  rewrite H in i at 4.
  pose ((N3 1) N1).
  destruct (classic (a+1 = -1)).
  rewrite H1 in i.
  rewrite H in i.
  pose (i N1 N1).
  contradiction.
  tauto. (* 2 is not pm 1 done proving*)
  intros.
  rewrite H in H0. (*might need to change*)
  assert (2 ∈ ℕ).
  {pose ((N2 1 1) N1 N1).
  auto. }  (*2 is nat proof*)
  rewrite O9 in H1.
  pose ((A3P4 d 2) H0 H1).
  destruct H0.
  pose (facsofNat x d).
  rewrite <-e in o.
  pose (o H1).
  destruct o as [[o1 o2]|[o3 o4]]. (*instances*)  (*0< d <= 2*)
  destruct l as [l1 |l2].
  pose ((help2 d) o2).
  destruct l as [l3 | l4].
  pose (A3P3 d).
  apply ltle in l1.
  rewrite twominus1 in l1.
  destruct l1.
  tauto.
  left; left.
  exact H0.
  pose ((help2 d) o2).
  apply ltle in l1.
  rewrite twominus1 in l1.
  destruct l1, l.
  apply (O13 1 d) in H2.
  auto.
  apply (O13 d 1) in H0.
  auto.
  auto.
  auto.
  right; left.
  rewrite H.
  auto. (*now show true when both negative*)
  pose ((help1 x) o3).
  pose ((help1 d) o4).
  pose ((m1me0 (-d)) l1).
  apply (S2le 1 (-x) (-d)) in l0.
  rewrite <-A1P7 in l0 at 2.
  rewrite <-(A1P7 x) in l0.
  rewrite M2  in l0.
  rewrite <-M2, <-M2  in l0.
  rewrite (M1 (-1)  (x * (-1 * d))) in l0.
  rewrite (M1 (-1) d) in l0.
  rewrite M2 in l0.
  rewrite <-M2 in l0.
  rewrite A1P7, A1P5 in l0.
  rewrite <-A1P7, M2, (M1 1 (-1)), ? A1P7, M3, <-e in l0.
  apply (negLe d 2) in l0.
  destruct l0.
  assert (-(2)<d -> -1≤d).
  {
	  intros.
	  apply ltle in H2.
	  apply (S1le (- (2)) (d-1) 1) in H2.
	  unfold sub in H2.
	  rewrite <-A2, A1P2, A3 in H2.
	  (*bruh*)

	  rewrite <-twominus1 in H2 at 2.
	  unfold sub in H2.
	  rewrite (A1 2 (-1)), A2 in H2.    
	  rewrite A4 in H2.
	  admit. }
	  pose (H2 H0).
	  destruct l0. (*-1<=d*)
	  assert (-1<d /\ d<0 -> False).
	  admit.
	  tauto.
	  left; right.
	  auto.
	  rewrite H.
	  right. right.
	  auto.
	  auto.
	  Admitted.







	  Theorem A4P4 :
	  ∀ p : Z, 1 < p → p ∉ prime → ∃ n, 1 < n < p ∧ (n | p).
	  Proof.
	  Admitted.

	  Theorem A4P5 : ∀ a b : Z,
	  0 < a → 0 < b → (∃ q r : Z, a = b * q + r ∧ 0 ≤ r < b).
	  Proof.
	  Admitted.


	  Theorem abeq1 :
	  ∀ a b : Z, a * b = 1 → (a = 1 ∧ b = 1) ∨ (a = -1 ∧ b = -1).
	  Proof.
	  intros a b H.
	  assert (a ∈ unit).
	  - unfold unit, In.
	  unfold divide.
	  exists b.
	  rewrite M1.
	  congruence.
	  - apply A4P1 in H0.
	  destruct H0.
	  + left.
	  split; auto.
	  rewrite H0, A1P3 in H.
	  trivial.
	  + right.
	  split; auto.
	  apply (S2 _ _ (-1)) in H.
	  rewrite H0, A1P3, A1P7, M1, A1P7, A1P5 in H.
	  trivial.
	  Qed.

	  Theorem A3P5_v100 : ∀ a b : Z, a ~ b → a = ± b.
	  Proof.
	  intros.
	  unfold pm, assoc in *.
	  destruct H.
	  destruct H, H0.
	  rewrite <-(A1P3 a), H, M2 in H0.
	  apply C1 in H0.
	  destruct H0.
	  symmetry in H0.
	  apply abeq1 in H0.
	  destruct H0 as [[h1 h2] |[h3 h4]].  
	  rewrite h2, A1P3 in H.
	  auto.
	  rewrite h4, A1P7 in H.
	  apply beqnega in H.
	  auto.
	  rewrite H0, M1, A1P6, <-H0 in H.
	  auto.
	  Qed.




	  Definition gcd (a b d : Z) :=
	  (d | a) ∧ (d | b) ∧ ∀ x : Z, (x | a) → (x | b) → (x | d).

	  Notation "'gcd' ( a , b )  = d" := (gcd a b d) (at level 80).



	  Theorem A5P1 : ∀ a b : Z, gcd (a,b) = 1 → a≠0 -> b≠0  -> ∃ x y : Z, 1 = a * x + b * y.
	  Proof.
	  intros.
	  destruct H as [w1 [w2 w3]].
	  destruct (WOP {d : Z | exists x y : Z, d = a*x + b*y/\ d>0}).
	  unfold not.
	  intros.
	  destruct (T a) as [[K3 [K4 K5]]| [[K6 [K7 K8]]| [K9 [K10 K11]]]].
	  - assert (a∈∅).
	  intros.
	  rewrite <-H.
	  unfold In.
	  exists 1, 0.
	  apply O9 in K3.
	  now rewrite M3, M1, A1P6, A3.
	  contradiction.
	  - contradiction.  
	  - assert (-a∈∅).
	  rewrite <-H.
	  intros; unfold In.
	  exists (-1), 0.
	  rewrite M1, A1P7, M1, A1P6, A3.
	  rewrite O9 in K9.
	  firstorder.
	  contradiction. (*done with non empty*)
	  - unfold Included.
	  intros.
	  unfold In in H.
	  destruct H; destruct H; destruct H.
	  now rewrite O9.
	  - destruct H.
	  unfold In in H2, H.
	  (*assert (x ∈ unit).*  its a differnt x tho!*)
	  pose (A4P5 x 1).
	  destruct e.
	  destruct H; destruct H; now destruct H.             
	  now pose O4.
	  destruct H3.  (* how to change name of remainder*)
	  assert (x1=0).
	  + destruct H3 as [H4 [H5 H6]].
	  destruct H5.
	  now destruct (A3P3 x1); auto.
	  now symmetry. (*remainder is 0*) (* now prove gcd=1 is the least*)
	  + destruct H; destruct H.
	  pose ((A2P1 1 a b x2 x3) w1 w2).
	  apply A3P4 in d. (*1<= least element*)
	  destruct H.
	  rewrite <-H in d.
	  pose (H2 1).
	  apply aleblea in d.
	  rewrite <-d.
	  now exists x2, x3.
	  destruct l.


	  pose ((A2P1 1 a b x2 x3) w1 w2).
	  unfold divide in d0.
	  destruct d0.
	  eapply S1 in H6.
	  rewrite <-A2, A4, A3 in H6.
	  pose A4P5.


	  rewrite <-H in H6.
	  destruct w1.


	  + Pose A3P4.

	  Admitted.





	  Theorem A5P2 : ∀ a b c : Z, gcd (a,b) = 1 → (a | b * c) → (a | c).
	  Proof.
	  intros.
	  apply A5P1 in H.
	  unfold divide in *.
	  destruct H.
	  destruct H.
	  destruct H0.
	  eapply S2 in H.
	  rewrite (A1P3 c), D1, <-(M2 b x0 c), (M1 x0 c), M2, H0 in H.
	  rewrite <-(M2 x1 _ _), (M1 a x0) in H.
	  rewrite <-M2, (M1 a _), M2, <-D1 in H.
	  now exists (x * c + x1 * x0).
	  Qed.

	  Theorem A6P1 : ∀ p a : Z, p ∈ prime → ¬ (p | a) → gcd (a,p) = 1.
	  Proof.


	  Theorem A6P2 : ∀ a b p : Z, p ∈ prime → (p | a * b) → (p | a) ∨ (p | b).
	  Proof.
	  Admitted.


