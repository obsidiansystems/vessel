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
      dependent-monoidal-map = self.callHackageDirect {
        pkg = "dependent-monoidal-map";
        ver = "0.1.1.3";
        sha256 = "13vglclw93vgrb52gwxklzh6lww0pn1i0b5nk6kw0vg1jdzjxvwj";
      } {};
      reflex = self.callHackageDirect {
        pkg = "reflex";
        ver = "0.8.2.2";
        sha256 = "04z7cjg0qfzpq4fhvsq0v04psny6pg8j4nns56v3hg06jf8akw6q";
      } {};
    })
  ];
  rp = import ./reflex-platform { inherit haskellOverlaysPost; __useNewerCompiler = true; };
in
{ ghc = rp.ghc.callCabal2nix "vessel" ./. {};
  ghcjs = rp.ghcjs.callCabal2nix "vessel" ./. {};
}
