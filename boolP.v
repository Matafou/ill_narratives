Inductive boolP : Prop := trueP | falseP.

Definition eq_boolP a b := 
  match a,b with
    | trueP,trueP => trueP
    | falseP,falseP => trueP
    | _,_ => falseP
  end.

Infix "?=" := eq_boolP (at level 80).

Definition orP a b :=
  match a with
    | trueP => trueP
    | falseP => b
  end.


Definition andP a b :=
  match a with
    | falseP => falseP
    | trueP => b
  end.

Infix "ORP" := orP (at level 70).
Infix "ANDP" := andP (at level 70).
