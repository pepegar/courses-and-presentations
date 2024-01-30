{
  description =
    "Different courses I teach, and some individual presentations too";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
    pre-commit-hooks.url = "github:cachix/pre-commit-hooks.nix";
  };

  outputs = { self, nixpkgs, flake-utils, pre-commit-hooks }:
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
          --variable theme=Madrid \
          -t beamer \
        '';

        pandocOptsWithStyle = ''
          --include-in-header=./style.tex \
          ${pandocOpts}
        '';

        buildSlides = folder: slidesName: system:
          pkgs.stdenvNoCC.mkDerivation {
            src = ./.;
            name = slidesName;
            buildInputs = [ texlive-combined pkgs.pandoc pkgs.coreutils ];
            phases = [ "unpackPhase" "buildPhase" ];
            buildPhase = ''
              mkdir -p $out/${folder}
              ls -la
              ${pkgs.pandoc}/bin/pandoc -o $out/${folder}/${slidesName}.pdf ./slides-md/${folder}/${slidesName}.md ${pandocOptsWithStyle}
            '';
          };

        buildSlidesSkippingStyles = folder: slidesName: system:
          pkgs.stdenv.mkDerivation {
            src = ./.;
            name = slidesName;
            nativeBuildInputs = [ texlive-combined pkgs.pandoc ];
            phases = [ "unpackPhase" "buildPhase" ];
            buildPhase = ''
              mkdir -p $out/${folder}
              ${pkgs.pandoc}/bin/pandoc -o $out/${folder}/${slidesName}.pdf ./slides-md/${folder}/${slidesName}.md
            '';
          };
      in rec {
        packages = flake-utils.lib.flattenTree {
          "pt/00-intro" = buildSlides "pt" "00-intro" system;
          "pt/01-hardware" = buildSlides "pt" "01-hardware" system;
          "pt/02-datatypes-operators" =
            buildSlides "pt" "02-datatypes-operators" system;
          "pt/03-booleans-control-flow" =
            buildSlides "pt" "03-booleans-control-flow" system;
          "pt/04-lists-iteration" =
            buildSlides "pt" "04-lists-iteration" system;
          "pt/05-dictionaries" = buildSlides "pt" "05-dictionaries" system;
          "pfp/00-cli-git" = buildSlides "pfp" "00-cli-git" system;
          "pfp/01-github" = buildSlides "pfp" "01-github" system;
          "pfp/02-files" = buildSlides "pfp" "02-files" system;
          "pfp/03-modules" = buildSlides "pfp" "03-modules" system;
          "pfp/04-pip" = buildSlides "pfp" "04-pip" system;
          "pfp/05-oop" = buildSlides "pfp" "05-oop" system;
          "app/00-intro" = buildSlides "app" "00-intro" system;
          "app/01-http-basics" = buildSlides "app" "01-http-basics" system;
          "app/02-http-more" = buildSlides "app" "02-http-more" system;
          "app/03-templates" = buildSlides "app" "03-templates" system;
          "app/04-sessions-and-cookies" =
            buildSlides "app" "04-sessions-and-cookies" system;
          "app/05-dbs" = buildSlides "app" "05-dbs" system;
          "app/06-rest" = buildSlides "app" "06-rest" system;
          "app/07-dash" = buildSlides "app" "07-dash" system;
          "presentations/tla/tla-intro" =
            buildSlidesSkippingStyles "presentations/tla" "tla-intro" system;
        };
        checks = {
          pre-commit-check = pre-commit-hooks.lib.${system}.run {
            src = ./.;
            hooks = { nixfmt.enable = true; };
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
