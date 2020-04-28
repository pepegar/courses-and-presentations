let
  pkgs = import <nixpkgs> {};
in
pkgs.mkShell {
  buildInputs = [
    pkgs.pandoc
    pkgs.entr
    pkgs.hugo
  ];
}
