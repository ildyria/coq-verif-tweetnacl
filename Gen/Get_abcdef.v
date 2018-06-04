Require Import Tweetnacl.Libs.Export.

Section get.

Context {T:Type}.

Definition get_a (t:(T * T * T * T * T * T)) : T := match t with
  (a,b,c,d,e,f) => a
end.
Definition get_b (t:(T * T * T * T * T * T)) : T := match t with
  (a,b,c,d,e,f) => b
end.
Definition get_c (t:(T * T * T * T * T * T)) : T := match t with
  (a,b,c,d,e,f) => c
end.
Definition get_d (t:(T * T * T * T * T * T)) : T := match t with
  (a,b,c,d,e,f) => d
end.
Definition get_e (t:(T * T * T * T * T * T)) : T := match t with
  (a,b,c,d,e,f) => e
end.
Definition get_f (t:(T * T * T * T * T * T)) : T := match t with
  (a,b,c,d,e,f) => f
end.

End get.
