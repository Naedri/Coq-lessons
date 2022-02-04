(*DEFINITION INDUCTIVE EN COQ*)

(* JOURS *)
Inductive day : Type :=
| monday
| tuesday.

Definition next_day (d: day) : day :=
match d with 
| monday => tuesday
| tuesday => monday
end.

Compute (next_day monday).

Example test_next_day :
  (next_day (monday)) = tuesday.


(* ENTIERS NATURELS *)

Proposition inductionNat : 
  forall P : nat -> Prop, 
    (P 0) 
    -> (forall n, (P n) -> (P (S n))) 
    -> forall x : nat, P x.
(* Pour tout prédicat P sur les naturels, si 0 vérifie P et si pour tout n, (n vérifie P) implique ((S n) vérifie P), alors pour tout naturel x, x vérifie P. *)
Proof.
  intros P H0 HSucc.
  (* Soient P le prédicat sur les naturels, H0 la preuve que 0 vérifie P et HSucc la preuve que pour tout n, (P n) implique (P (S n)).*)
  fix HR 1.
  (* Raisonnons récursivement sur le premier paramètre x. Appelons HR l'hypothèse de récurrence. *)
  intro x.
  (* Soit x un entier naturel. *)
  case x as [ | px].
  (* Examinons les deux cas pour x.*)
  - (* cas x := 0. *)
    exact H0.
    (* Appliquons l'hypothèse H0 pour montrer (P 0). *)  
  - (* cas x := S px. *)
    apply HSucc.
    (* Appliquons l'hypothèse HSucc pour montrer (P (S px)) : le nouveau but devient (P px). *)
    apply HR. 
    (* Appliquons l'hypothèse de récurrence pour montrer (P px).*)
Qed.