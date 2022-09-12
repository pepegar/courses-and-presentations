{
  description = "Intro to programming course";

  inputs = {
    flake-utils = {
      url = "github:numtide/flake-utils";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    nix-pandoc = {
      url = "github:serokell/nix-pandoc";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, nixpkgs, flake-utils, nix-pandoc }:
    let
      system = "aarch64-darwin";

      pandocOpts = ''
      --variable monofont="PragmataPro Mono" \
      --variable fontsize=12pt \
      --variable theme=Madrid \
      --include-in-header=./style.tex \
      --standalone \
      -t beamer \
      --highlight-style tango \
      '';

      buildSlides = title : system : nix-pandoc.mkDoc.${system} {
        name = title;
        src = ./.;
        phases = [ "unpackPhase" "buildPhase" "installPhase" ];
        buildPhase = "pandoc ${pandocOpts} -o $name.pdf ./slides-md/$name.md";
        installPhase = "mkdir -p $out; cp $name.pdf $out";
      };
    in {
      packages = {
        ${system}."00-intro" = buildSlides "00-intro";
      };
    } // flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
      in rec {
        devShell = pkgs.mkShell {
          buildInputs = [
            pkgs.pandoc
            pkgs.entr
            pkgs.hugo
            pkgs.texlive.combined.scheme-full
            pkgs.python38
            pkgs.gnumake
          ];
        };
      }
    );
}
