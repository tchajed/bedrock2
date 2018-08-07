Module map.
  Class map {key value : Type} := {
    rep : Type;
     
    empty : rep;
    get : rep -> key -> option value;
    put : rep -> key -> value -> rep;
  }.
  Arguments map : clear implicits.

  Section ListOperations.
    Context {key value} {map : map key value}.
    Fixpoint putmany (keys : list key) (values : list value) (m : rep) {struct keys} : option rep :=
      match keys, values with
      | nil, nil => Some m
      | cons b binders, cons v values =>
        match putmany binders values m with
        | Some m => Some (put m b v)
        | None => None
        end
      | _, _ => None
      end.
  End ListOperations.

End map. Notation map := map.map.
Global Coercion map.rep : map >-> Sortclass.