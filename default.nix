{ mkDerivation, aeson, base, bifunctors, constraints
, constraints-extras, dependent-monoidal-map, dependent-sum
, dependent-sum-aeson-orphans, reflex, stdenv, these
}:
mkDerivation {
  pname = "vessel";
  version = "0.1.0.0";
  src = ./.;
  libraryHaskellDepends = [
    aeson base bifunctors constraints constraints-extras
    dependent-monoidal-map dependent-sum dependent-sum-aeson-orphans
    reflex these
  ];
  license = stdenv.lib.licenses.bsd3;
}
