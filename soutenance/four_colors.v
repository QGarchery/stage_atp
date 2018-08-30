Variable R : real_model.
Theorem four_color (m : map R) :
  simple_map m -> map_colorable 4 m.
Proof.
  exact (compactness_extension four_color_finite).
Qed.

