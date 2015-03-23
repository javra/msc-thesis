import .gamma ..dbl_gpd.functor ..xmod.morphism

open eq function category iso dbl_gpd xmod is_trunc

namespace gamma

  protected definition on_morphisms (G H : Dbl_gpd) (F : dbl_functor G H) :
    xmod_morphism (gamma.on_objects G) (gamma.on_objects H) :=
  begin
    cases F,
    fapply xmod_morphism.mk,
      apply catF,
      { esimp{gamma.on_objects, gamma.xmod, gamma.M_bundled},
        intros (p, x),
      },
  end

end gamma
