{
  description =
    "Different courses I teach, and some individual presentations too";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    flake-utils = {
      url = "github:numtide/flake-utils";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    nix-pandoc = {
      url = "github:serokell/nix-pandoc";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    pre-commit-hooks.url = "github:cachix/pre-commit-hooks.nix";
  };

  outputs = { self, nixpkgs, flake-utils, nix-pandoc, pre-commit-hooks }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};

        texlive-packages = {
          inherit (pkgs.texlive)
            scheme-small noto mweights cm-super cmbright fontaxes beamer fvextra
            catchfile xstring framed;
        };

        texlive-combined = pkgs.texlive.combine texlive-packages;
        pandocOpts = ''
          --include-in-header=./style.tex \
          --pdf-engine-opt=-output-directory=_output \
          --pdf-engine-opt=-shell-escape \
          --pdf-engine=xelatex \
          --standalone \
          --variable theme=Madrid \
          -t beamer \
        '';

        buildSlides = name: system:
          nix-pandoc.mkDoc.${system} {
            src = ./.;
            inherit texlive-combined name;
            phases = [ "unpackPhase" "buildPhase" "installPhase" ];
            buildPhase =
              "pandoc ${pandocOpts} -o $name.pdf ./slides-md/$name.md";
            installPhase = "mkdir -p $out; cp $name.pdf $out";
            extraBuildInputs = [ pkgs.which ];
          };
      in rec {
        packages = flake-utils.lib.flattenTree {
          "pt/00-intro" = buildSlides "00-intro" system;
          "pt/01-hardware" = buildSlides "01-hardware" system;
          "pt/02-datatypes-operators" =
            buildSlides "02-datatypes-operators" system;
          "pt/03-booleans-control-flow" =
            buildSlides "03-booleans-control-flow" system;
          "pt/04-lists-iteration" = buildSlides "04-lists-iteration" system;
          "pt/05-dictionaries" = buildSlides "05-dictionaries" system;
        };
        checks = {
          pre-commit-check = pre-commit-hooks.lib.${system}.run {
            src = ./.;
            hooks = {
              nixfmt.enable = true;
              nix-linter.enable = true;
            };
          };
        };
        devShell = pkgs.mkShell {
          inherit (self.checks.${system}.pre-commit-check) shellHook;
          buildInputs = [
            pkgs.pandoc
            pkgs.entr
            pkgs.hugo
            pkgs.python38
            pkgs.gnumake
            texlive-combined
          ];
        };
      });
}
