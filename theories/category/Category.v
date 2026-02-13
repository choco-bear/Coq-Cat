Require Import Program Axioms.
From stdpp Require Import ssreflect.

Class Category (Obj : Type) := mk_Category {
  Arrow : Obj → Obj → Type;
  
  Arrow_equiv x y :: Equiv (Arrow x y);
  Arrow_equivalence x y :: Equivalence (≡@{Arrow x y});

  comp {x y z} : Arrow y z → Arrow x y → Arrow x z;
  comp_proper {x y z} :: Proper ((≡) ==> (≡) ==> (≡)) (@comp x y z);
  comp_assoc {x y z w} (f : Arrow z w) (g : Arrow y z) (h : Arrow x y) :
    comp (comp f g) h ≡ comp f (comp g h);

  cat_id x : Arrow x x;
  cat_id_left {x y} (f : Arrow x y) : comp (cat_id y) f ≡ f;
  cat_id_right {x y} (f : Arrow x y) : comp f (cat_id x) ≡ f;
}.

Local Definition _dom `{!Category Obj} `{Arrow x y} : Obj := x.
Local Definition _cod `{!Category Obj} `{Arrow x y} : Obj := y.