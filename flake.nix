{
  description = "flat-theory";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/master";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        lib = pkgs.lib;
        coq = pkgs.coq_8_20;
        ocamlPkgs = coq.ocamlPackages;
        coqPkgs = pkgs.coqPackages_8_20;
        version = "flat-theory:main";
      in {
        packages.default =
          (pkgs.callPackage ./release.nix (ocamlPkgs // coqPkgs // { inherit coq version; })).flat;
      });
}