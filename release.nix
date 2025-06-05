{ lib,
  mkCoqDerivation,
  version ? null,
  coq,
  dune_3,
  ocaml,
  ocamlbuild,
  stdpp, 
  vscoq-language-server, ... }:

{ flat =
    mkCoqDerivation {
      namePrefix = [ "coq" ];
      pname = "flat";
      owner = "flat";

      inherit version;

      propagatedBuildInputs =
        [ coq
          dune_3
        ] ++
        # Coq libraries
        [ stdpp
          vscoq-language-server
        ] ++
        # Ocaml
        [ ocaml
          ocamlbuild
        ];

      src = ./.;

      buildPhase = ''
        make
      '';

      installPhase = ''
        make doc
        mkdir -p $out/share
        mv doc $out/share/
      '';

      meta = {
        description = "Coq formulation on the meta-theories of regular languages";
      };
    };
}