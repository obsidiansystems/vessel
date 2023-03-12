let
  haskellOverlaysPost = [
    (self: super: {
      aeson-gadt-th = self.callHackageDirect {
        pkg = "aeson-gadt-th";
        ver = "0.2.5.1";
        sha256 = "1r3gx226jqs7l5jp8gmgaa2p49lnsnlzdhsxj6h47m0rnfc36qm5";
      } {};
    })
  ];
  rp = import ./reflex-platform { inherit haskellOverlaysPost; __useNewerCompiler = true; };
in
{ ghc = rp.ghc.callCabal2nix "vessel" ./. {};
  ghcjs = rp.ghcjs.callCabal2nix "vessel" ./. {};
}
