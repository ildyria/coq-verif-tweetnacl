Require Export Tweetnacl.Libs.LibTactics.

Lemma orFalse : forall (P:Prop), P \/ False <-> P.
Proof. boum. Qed.

Lemma Falseor : forall (P:Prop), False \/ P <-> P.
Proof. boum. Qed.

Lemma andTrue : forall (P:Prop), P /\ True <-> P.
Proof. boum. Qed.

Lemma Trueand : forall (P:Prop), True /\ P <-> P.
Proof. boum. Qed.