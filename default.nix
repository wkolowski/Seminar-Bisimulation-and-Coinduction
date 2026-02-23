{ pkgs ? import <nixpkgs> {} }:

let
  coq = pkgs.stdenv.mkDerivation
  {
    name = "BisimCoind";

    src = pkgs.lib.cleanSource ./src;

    enableParallelBuilding = true;

    buildInputs = with pkgs;
    [
      coq_9_1
      rocqPackages_9_1.stdlib
    ];

    buildPhase =
    ''
      patchShebangs ./build.sh
      ./build.sh
    '';

    installPhase =
    ''
      INSTALLPATH=$out/lib/coq/${pkgs.coq_9_1.coq-version}/user-contrib/BisimCoind

      mkdir -p $INSTALLPATH
      cp -r * $INSTALLPATH/

      # Remove .vos, .vok and .aux files.
      find $INSTALLPATH -name "*.vos" -o -name "*.vok" -o -name ".*.aux" | xargs rm -f
    '';
  };

  slides = pkgs.stdenv.mkDerivation
  {
    name = "BisimCoind";

    src = pkgs.lib.cleanSource ./slides;

    buildInputs =
    [
      (pkgs.texlive.combine
      {
        inherit (pkgs.texlive) scheme-basic latexmk beamer;
      })
    ];

    buildPhase =
    ''
      patchShebangs ./build.sh
      ./build.sh
    '';

    installPhase =
    ''
      INSTALLPATH=$out/share/slides/

      mkdir -p $INSTALLPATH
      cp *.pdf $INSTALLPATH/
    '';
  };

  all = pkgs.symlinkJoin
  {
    name = "BisimCoind";

    paths =
    [
      coq
      slides
    ];
  };

in
{
  inherit coq slides all;

  default = all;
}
