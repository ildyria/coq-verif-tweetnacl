Require Import PocklingtonRefl.

Open Local Scope positive_scope.

Lemma myPrime : prime 179.
Proof.
 apply (Pocklington_refl
         (Pock_certif 179 2 ((89, 1)::(2,1)::nil) 1)
        ((Proof_certif 89 prime89) ::
         (Proof_certif 2 prime2) ::
          nil)).
 vm_cast_no_check (refl_equal true).
Qed.

