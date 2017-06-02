Require Import PocklingtonRefl.

Open Local Scope positive_scope.

Lemma myPrime : prime 17.
Proof.
 apply (Pocklington_refl
         (Pock_certif 17 3 ((2,4)::nil) 1)
        ((Proof_certif 2 prime2) ::
          nil)).
 exact_vm_no_check (refl_equal true).
Qed.

