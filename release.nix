let
  haskellOverlaysPost = [
    (self: super: {
      base-orphans = self.callHackage "base-orphans" "0.8.6" {};
      dependent-sum-aeson-orphans = self.callHackageDirect {
        pkg = "dependent-sum-aeson-orphans";
        ver = "0.3.1.1";
        sha256 = "14i74c268xpmz03nqa0ll3inf0lncn6hzhil1fiqwrqk25yfah2m";
      } {};
      aeson-gadt-th = self.callHackageDirect {
        pkg = "aeson-gadt-th";
        ver = "0.2.5.1";
        sha256 = "1r3gx226jqs7l5jp8gmgaa2p49lnsnlzdhsxj6h47m0rnfc36qm5";
      } {};
      dependent-monoidal-map = self.callCabal2nix "dependent-monoidal-map" ../dependent-monoidal-map {};
    })
  ];
  rp = import ./reflex-platform { inherit haskellOverlaysPost; __useNewerCompiler = true; };
in
{ ghc = rp.ghc.callCabal2nix "vessel" ./. {};
  ghcjs = rp.ghcjs.callCabal2nix "vessel" ./. {};
}
