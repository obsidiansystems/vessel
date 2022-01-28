let
  haskellOverlaysPost = [
    (self: super: {
      base-orphans = self.callHackage "base-orphans" "0.8.5" {};
      dependent-sum-aeson-orphans = self.callHackage "dependent-sum-aeson-orphans" "0.3.1.0" {};
    })
  ];
  rp = import ./reflex-platform { inherit haskellOverlaysPost; };
in
{ ghc = rp.ghc.callCabal2nix "vessel" ./. {};
  ghcjs = rp.ghcjs.callCabal2nix "vessel" ./. {};
}
