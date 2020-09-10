let
  pkgs = import <nixpkgs> {};
in
pkgs.mkShell {
  buildInputs = [
    pkgs.pandoc
    pkgs.entr
    pkgs.hugo
    pkgs.haskellPackages.pandoc-crossref
    pkgs.texlive.combined.scheme-full
  ];
}
