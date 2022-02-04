(*LES FONCTIONS EN COQ*)

(* Check verifie les types des expressions*)
Check fun x => x + 2.
Check (fun x => x + 2) 3.
Check 3.

(*Compute teste les fonctions*)
Compute (fun x => x+2) 3.
Compute (fun x => x+2) 3.

Eval vm_compute in (fun x => x + 2) 4.

(*Definition permet de donner un nom a la fonction*)
Definition add2 := fun x => x+2.
Compute add2 4.
(*shortcut*)
Definition add3 x := x+2.
Compute add3 4.


(*JOUER AVEC LES FONCTIONS*)

(*fonctions avec deux arguments*)
Check fun x => fun y => y + (x+2).
Check fun x y => y + (x+2).

(*ORDRES SUPERIEURS*)


(**)