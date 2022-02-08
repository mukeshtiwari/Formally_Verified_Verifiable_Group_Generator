From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo99:
  prime  13107020770889572211807501728929751498893742409207476846128088902943553557920454752107436684514701536106933372290772003299254150406131->
  prime  350352631258993898657446292339551597028154568659477237218530735589016606525393678614887829996595548402897161752194637768070672479597847004327.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      350352631258993898657446292339551597028154568659477237218530735589016606525393678614887829996595548402897161752194637768070672479597847004327
      26730150
      ((13107020770889572211807501728929751498893742409207476846128088902943553557920454752107436684514701536106933372290772003299254150406131,1)::nil)
      255349129222180056488858132102787861361744996113970752982298820827091660823963549042117497812349847457736143124703015110538213390666189884211
      227294401478461391457202744683281555230667676325417378375116550751591732393656752251790505413748755874996383944001766968190125781364714428317
      0
      230735605602913863832330922866667806478571524566487492403177801889450672191876594054263742216592419569488508777987241303556474114423961603996)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
